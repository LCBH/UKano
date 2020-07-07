(*************************************************************
 *                                                           *
 *  Cryptographic protocol verifier                          *
 *                                                           *
 *  Bruno Blanchet, Vincent Cheval, and Marc Sylvestre       *
 *                                                           *
 *  Copyright (C) INRIA, CNRS 2000-2020                      *
 *                                                           *
 *************************************************************)

(*

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details (in file LICENSE).

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

*)
open Types
open Terms

(* Equality *)

let rec equal_terms_with_links t1 t2 = (t1 == t2) || (match (t1,t2) with
  Var { link = TLink t }, t' -> equal_terms_with_links t t'
| Var { link = VLink v }, t' -> equal_terms_with_links (Var v) t'
| t, Var { link = TLink t' } -> equal_terms_with_links t t'
| t, Var { link = VLink v' } -> equal_terms_with_links t (Var v')
| Var v, Var v' -> v == v'
| FunApp(f,l),FunApp(f',l') ->
   (f == f') && (List.for_all2 equal_terms_with_links l l')
| _,_ -> false)

let equal_facts_with_links f f' = (f == f') || (match (f,f') with
  Pred(p,l), Pred(p',l') -> (p == p') && (List.for_all2 equal_terms_with_links l l'))

let rec equal_closed_terms t1 t2 = match (t1,t2) with
  Var v, t' ->
    begin
      match v.link with
	TLink t -> equal_closed_terms t t'
      |	_ -> Parsing_helper.internal_error "unexpected link in equal_closed_terms (reduction.ml)"
    end
| t, Var v' ->
    begin
      match v'.link with
	TLink t' -> equal_closed_terms t t'
      |	_ -> Parsing_helper.internal_error "unexpected link in equal_closed_terms (reduction.ml)"
    end
| FunApp(f,l),FunApp(f',l') ->
   (f == f') && (List.for_all2 equal_closed_terms l l')


let equal_tags t1 t2 =
  match (t1,t2) with
    ProcessRule(h1, tl1), ProcessRule(h2,tl2) ->
      (List.length h1 == List.length h2) && (List.for_all2 (=) h1 h2) &&
      (List.length tl1 == List.length tl2) &&
      (List.for_all2 equal_terms_with_links tl1 tl2)
  | Apply(f1,p1), Apply(f2,p2) -> (f1 == f2) && (p1 == p2)
  | TestApply(f1,p1), TestApply(f2,p2) -> (f1 == f2) && (p1 == p2)
  | TestEq p1, TestEq p2 -> p1 == p2
  | Rl(p1,p1'), Rl(p2,p2') -> p1 == p2 && p1' == p2'
  | Rs(p1,p1'), Rs(p2,p2') -> p1 == p2 && p1' == p2'
  | Ri(p1,p1'), Ri(p2,p2') -> p1 == p2 && p1' == p2'
  | Ro(p1,p1'), Ro(p2,p2') -> p1 == p2 && p1' == p2'
  | TestComm(p1,p1'), TestComm(p2,p2') -> p1 == p2 && p1' == p2'
  | Elem(pl1,p1), Elem(pl2,p2) ->
      (List.length pl1 == List.length pl2) &&
      (List.for_all2 (==) pl1 pl2) &&
      (p1 == p2)
  | LblEquiv, LblEquiv -> true
  | LblClause, LblClause -> true
  | LblEq, LblEq -> true
  | WeakSecr, WeakSecr -> true
  | Rn p1, Rn p2 -> p1 == p2
  | Init, Init -> true
  | PhaseChange, PhaseChange -> true
  | TblPhaseChange, TblPhaseChange -> true
  | LblComp, LblComp -> true
  | LblNone, LblNone -> true
  | TestUnif, TestUnif -> true
  | _ -> false

let equal_constra c1 c2 =
  List.length c1.neq == List.length c2.neq &&
  List.length c1.is_nat == List.length c2.is_nat &&
  List.length c1.is_not_nat == List.length c2.is_not_nat &&
  List.length c1.geq == List.length c2.geq &&

  List.for_all2 (fun l1 l2 ->
    List.length l1 == List.length l2 &&
    List.for_all2 (fun (t1,t1') (t2,t2') ->
      equal_terms_with_links t1 t2 &&
      equal_terms_with_links t1' t2'
    ) l1 l2
  ) c1.neq c2.neq &&

  List.for_all2 equal_terms_with_links c1.is_nat c2.is_nat &&
  List.for_all2 equal_terms_with_links c1.is_not_nat c2.is_not_nat &&
  List.for_all2 (fun (t1,n1,t1') (t2,n2,t2') ->
    n1 == n2 &&
    equal_terms_with_links t1 t2 &&
    equal_terms_with_links t1' t2'
  ) c1.geq c2.geq

(* Matching *)

let rec match_terms t1 t2 =
  if not (Param.get_ignore_types()) then
    if (get_term_type t1 != get_term_type t2) then
      assert false;
  match (t1,t2) with
     (Var { link = TLink t1' }, _) -> match_terms t1' t2
   | (_, Var { link = TLink t2' }) -> match_terms t1 t2'
   | (_, Var _) -> Parsing_helper.internal_error "Bad link in match_terms (1)"
   | (Var v), t ->
       begin
	 match v.link with
           NoLink ->
             if v.unfailing
             then link v (TLink t)
             else
	       begin
	       	 match t with
	           | FunApp(f_symb,_) when f_symb.f_cat = Failure -> raise Unify
	           | _ -> link v (TLink t)
	       end
	 | _ -> Parsing_helper.internal_error "Bad link in match_terms (2)"
       end
   | (FunApp (f1,l1')), (FunApp (f2,l2')) ->
          if f1 != f2 then raise Unify;
          List.iter2 match_terms l1' l2'

(* Retrieve variables *)

let rec get_vars vars = function
  | Var { link = TLink t; _ } -> get_vars vars t
  | Var v ->
      if not (List.memq v !vars)
      then vars := v :: !vars
  | FunApp(_,args) -> List.iter (get_vars vars) args

(* Test whether a term has a variable *)
let rec has_vars = function
  | Var v ->
      begin match v.link with
        | NoLink -> true
        | TLink t -> has_vars t
        | _ -> Parsing_helper.internal_error "[Termslinks.ml >> has_vars] Unexpected link"
      end
  | FunApp(_,args) -> List.exists has_vars args
