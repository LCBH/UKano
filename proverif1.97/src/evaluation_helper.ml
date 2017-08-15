(*************************************************************
 *                                                           *
 *  Cryptographic protocol verifier                          *
 *                                                           *
 *  Bruno Blanchet, Vincent Cheval, and Marc Sylvestre       *
 *                                                           *
 *  Copyright (C) INRIA, CNRS 2000-2017                      *
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
open Pitypes
open Terms
open Reduction_helper


let rec term_evaluation = function
    Var v ->
    begin
      match v.link with
        TLink t -> term_evaluation t
      | _ -> Parsing_helper.internal_error "Error: term should be closed in attack reconstruction";
    end
  | FunApp(f,l) ->
    (* for speed, use the initial definition of destructors, not the one enriched with the equational theory *)
    match f.f_initial_cat with
      Eq _ | Tuple ->
      let l' = List.map term_evaluation l in
      if List.exists is_fail l' then
	Terms.get_fail_term (snd f.f_type)
      else
	FunApp(f, l')
    | Name _ | Failure -> FunApp(f,[])
    | Red redl ->
      let l' = List.map term_evaluation l in
      let rec try_red_list = function
	  [] ->
	  Parsing_helper.internal_error "Term evaluation should always succeeds (perhaps returning Fail)"
	| (red1::redl) ->
	  let (left, right, side_c) = auto_cleanup (fun () -> Terms.copy_red red1) in
	  try
	    auto_cleanup (fun () ->
		match_modulo_list (fun () ->
		    if List.for_all disequation_evaluation side_c then
		      begin
		        (* TO DO (for speed) should I remove_syntactic, or keep it,
			   but take it into account elsewhere (when doing
			   function symbol comparisons, accept functions that
			   differ by their syntactic status) *)
			close_term right;
 			TermsEq.remove_syntactic_term right
		      end
		    else
		      raise Unify
		  ) left l')
	  with Unify -> try_red_list redl
      in
      try_red_list redl
    | _ -> Parsing_helper.internal_error "unexpected function symbol in term_evaluation"

(* Evaluates t1 and tests if it is equal to t2. *)

let equal_terms_modulo_eval t1 t2 =
  let t1' = term_evaluation t1 in
  if is_fail t1' then false else equal_terms_modulo t1' t2


(* Evaluates a term. Raises Unify when the result is fail. *)

let term_evaluation_fail t =
  let r = term_evaluation t in
  if is_fail r then
    raise Unify
  else
    r

let rec term_evaluation_letfilter = function
Var { link = TLink t } -> term_evaluation_letfilter t
  | Var v ->  Var v
  | FunApp(f,l) ->
    match f.f_cat with
      Eq _ | Tuple -> FunApp(f, term_evaluation_list_letfilter l)
    | Name _ -> FunApp(f,[])
    |	Failure -> raise Unify
    | Red redl -> term_evaluation_fail (FunApp(f,l))
    | _ -> Parsing_helper.internal_error "unexpected function symbol in term_evaluation_letfilter"

and term_evaluation_list_letfilter l =
  List.map term_evaluation_letfilter l

let term_evaluation_letfilter occ l name_params =
  let may_have_several_types = reduction_check_several_patterns occ in
  let l' = term_evaluation_list_letfilter l in
  if may_have_several_types then
    l', ((List.map (fun t -> (MUnknown,t,Always)) l') @ name_params)
  else
    l', name_params


(* Match a pattern
   Raises Unify when the matching fails *)

let rec match_pattern p t =
  match p with
    PatVar b ->
      if Terms.equal_types b.btype (Terms.get_term_type t) then
	Terms.link b (TLink t)
      else
	raise Unify
  | PatTuple(f,l) ->
    let vl = Terms.var_gen (fst f.f_type) in
    let tl =
      match_modulo (fun () ->
	  List.map copy_closed_remove_syntactic vl
	) (FunApp(f, vl)) t
    in
    List.iter2 match_pattern l tl
  | PatEqual t' ->
    let t'' = term_evaluation_fail t' in
    match_modulo (fun () -> ()) t'' t

(* Decompose tuples *)

let rec decompose_term ((calcul, t) as pair) =
  match t with
    FunApp({f_cat = Tuple } as f,l) ->
      let projs = get_all_projection_fun f in
      decompose_list (List.map2 (fun fi ti -> FunApp(fi, [calcul]), ti) projs l)
  | t -> [pair]

and decompose_list = function
    [] -> []
  | (a::l) -> (decompose_term a) @ (decompose_list l)

let rec decompose_term_rev (binder, t) =
  match t with
    FunApp({f_cat = Tuple} as f, l) ->
      let new_list = List.map (fun x -> ((new_var "~M" (Terms.get_term_type x)), x)) l in
      link binder (TLink (FunApp(f, (List.map (fun (x, y) -> Var x) new_list))));
      decompose_list_rev new_list
  | t -> [(binder, t)]

and decompose_list_rev = function
    [] -> []
  | (a::l) -> (decompose_term_rev a) @ (decompose_list_rev l)

(* Test if a term is public *)

let rec is_in_public public = function
  | FunApp({f_cat = Tuple} as f, l) ->
      (match is_in_public_list public l with
        | None -> None
        | Some lst -> Some(FunApp(f, lst)))
  | t ->
      try
        let (ca, _) = List.find (fun (_, t') -> equal_terms_modulo t t') public in
        Some ca
      with Not_found ->
        None

and is_in_public_list public = function
    [] -> Some []
  | hd::tail ->
      match is_in_public public hd with
	None -> None
      | Some ca ->
        match is_in_public_list public tail with
	  None -> None
	| Some catail -> Some (ca::catail)


let rec remove_first_in_public public = function
    [] -> []
  | (((c, a)::l) as l') ->
    try
      let (ca, _) = List.find (fun (_, t) -> equal_terms_modulo a t) public in
      link c (TLink ca);
      remove_first_in_public public l
    with Not_found ->
      l'


let update_term_list oldpub public tc_list =
  match tc_list with
    [] -> []
  | ((c0, t0)::l0) ->
    let rec is_in_until = function
	[] -> false
      | (((ca, a)::l) as public) ->
	if public == oldpub then false else
          if equal_terms_modulo a t0
          then
            begin
              Terms.link c0 (TLink ca);
              true
            end
          else
	    is_in_until l
    in
    if is_in_until public then
      remove_first_in_public public l0
    else
      tc_list


let rec add_public_and_close state l (* l contains a list of recipe and the corresponding term *)=
  let queue = ref l in
  let rec remove_from_att_rules public ((calcul, t) as pair) = function
      [] -> []
    | (p, hyp_terms, (calc_concl, concl_term))::attacker_rules ->
      let attacker_rules' = remove_from_att_rules public pair attacker_rules in
      if getphase p < state.current_phase then attacker_rules' else
	let hyp_terms' =
	  match hyp_terms with
	    [] -> []
	  | (c0,t0)::l0 ->
	    if equal_terms_modulo t0 t then
	      begin
		link c0 (TLink calcul);
		remove_first_in_public public l0
	      end
	    else
	      hyp_terms
	in
	if (hyp_terms' = []) && (getphase p = state.current_phase) then
	  begin
            queue := (decompose_term (Terms.copy_term4 calc_concl, concl_term)) @ (!queue);
	    attacker_rules'
	  end
	else
          (* Keep the rule, removing hypotheses that are already in *)
	  (p, hyp_terms', (calc_concl, concl_term)) :: attacker_rules'
  in
  let rec do_close state =
    match !queue with
      [] -> state
    | ((c, t)::l) ->
      queue := l;
      if List.exists (fun (_, t') -> equal_terms_modulo t t') state.public then
	do_close state
      else
	let public' = (c, t) :: state.public in
	do_close { state with
                   public = public';
                   prepared_attacker_rule = remove_from_att_rules public' (c, t) state.prepared_attacker_rule }
  in
  do_close state

let rec add_public_with_calc state (calcul, t) =
  match t with
    FunApp({ f_cat = Tuple } as f, l) ->
    let projs = get_all_projection_fun f in
    add_public_list state (List.map2 (fun fi ti -> (FunApp(fi, [calcul]), ti)) projs l)
  | t -> add_public_and_close state [(calcul, t)]

and add_public_list state = function
    [] -> state
  | (a::l) -> add_public_list (add_public_with_calc state a) l

let reclose_public state =
  add_public_list { state with public = [] } state.public

let add_public state t =
  let new_calcul = new_var "~M" (get_term_type t) in
  let l = decompose_term_rev (new_calcul, t) in
  let l' = List.map (fun (b,t) -> (Var b, t)) l in
  let state' = add_public_and_close state l' in
  (Terms.copy_term4 (Var new_calcul), state')

let rec extract_phase n = function
    [] -> []
  | (Phase(n',p,occ),name_params,occs, facts, cache_info)::r ->
    let r' = extract_phase n r in
    if n = n' then (p,name_params,occs, facts, Nothing)::r' else
    if n<n' then (Phase(n',p,occ),name_params,occs, facts, Nothing)::r' else r'
  | _::r -> extract_phase n r
