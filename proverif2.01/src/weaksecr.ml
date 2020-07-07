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

let weaksecret_mode = ref false
let attrulenum = ref []
let max_used_phase = ref 0

let initialize = function
    Solve_WeakSecret(v_attrulenum, v_max_used_phase) ->
     weaksecret_mode := true;
     attrulenum := v_attrulenum;
     max_used_phase := v_max_used_phase
  | Solve_Equivalence ->
     weaksecret_mode := true;
     attrulenum := [];
     max_used_phase := 0
  | _ ->
     weaksecret_mode := false;
     attrulenum := [];
     max_used_phase := 0

let detect_atteq = function
    ([Pred(p1, [Var v1; Var v2]); Pred(p2, [Var v3; Var v4])],
     (Pred(p4, [])), _, { neq = [[(Var v5, Var v6)]]; is_nat = []; is_not_nat = []; geq = [] })
      when p1.p_prop land Param.pred_ELIMVAR != 0
      && p2.p_prop land Param.pred_ELIMVAR != 0
      && p4 == Param.bad_pred
      && v1 == v3
      && ((v2 == v5 && v4 == v6) || (v2 == v6 && v4 == v5)) -> true
  | _ -> false

let detect_atteq2 = function
    ([Pred(p1, [Var v1; Var v2]); Pred(p2, [Var v3; Var v4])],
     (Pred(p4, [])), _, { neq = [[(Var v5, Var v6)]]; is_nat = []; is_not_nat = []; geq = [] })
      when p1.p_prop land Param.pred_ELIMVAR != 0
      && p2.p_prop land Param.pred_ELIMVAR != 0
      && p4 == Param.bad_pred
      && v2 == v4
      && ((v1 == v5 && v3 == v6) || (v1 == v6 && v3 == v5)) -> true
  | _ -> false

let detect_atteq3 = function
    ([Pred(p1, [Var v1]); Pred(p2, [Var v3; Var v4])],
     (Pred(p4, [])), _, { neq = [[(Var v5, Var v6)]]; is_nat = []; is_not_nat = []; geq = [] })
      when p1.p_prop land Param.pred_ATTACKER != 0
      && p2.p_prop land Param.pred_ELIMVAR != 0
      && p4 == Param.bad_pred
      && v1 == v3
      && ((v3 == v5 && v4 == v6) || (v3 == v6 && v4 == v5)) -> true
  | _ -> false

let detect_atteq4 = function
    ([Pred(p1, [Var v1]); Pred(p2, [Var v3; Var v4])],
     (Pred(p4, [])), _, { neq = [[(Var v5, Var v6)]]; is_nat = []; is_not_nat = []; geq = [] })
      when p1.p_prop land Param.pred_ATTACKER != 0
      && p2.p_prop land Param.pred_ELIMVAR != 0
      && p4 == Param.bad_pred
      && v1 == v4
      && ((v3 == v5 && v4 == v6) || (v3 == v6 && v4 == v5)) -> true
  | _ -> false

let is_bad = function
    Pred(p, []) -> p==Param.bad_pred
  | _ -> false

let elim_att_guess_xx next_stage repeat_next_stage (hyp, concl, hist, constra) =
  let redo_all_optim = ref false in
  let hist' = ref hist in
  let rec f n = function
      [] -> []
    | (Pred({ p_info = [AttackerGuess _]}, [Var v1; Var v2])) :: l when v1 == v2 ->
        redo_all_optim := true;
        hist' := Resolution(List.assq (Param.get_type v1.btype) (!attrulenum), n, !hist');
        (Pred(Param.get_pred (Attacker(!max_used_phase, v1.btype)), [Var v1])) :: (f (n+1) l)
    | fact :: l -> fact :: (f (n+1) l)
  in
  let hyp' = f 0 hyp in
  let r' = (hyp', concl, !hist', constra) in
  if !redo_all_optim then
    repeat_next_stage r'
  else
    next_stage r'

let rec follow_link v =
  match v.link with
    TLink (Var v') -> follow_link v'
  | NoLink -> v
  | _ -> Parsing_helper.internal_error "unexpected link in follow_link (weaksecr)"

(* [remove_equiv_events] removes H in clauses H -> bad when H just contains events
   and we are dealing with a proof of equivalence. In this case, events just serve
   for triggering lemmas, we do not need them in such a clause.

   Note that the history [hist] is not updated. This is ok because we are not
   going to perform further resolutions on this clause. As a consequence,
   the reconstructed derivation will be for a clause with the events H in
   hypothesis.
   Still, the clause displayed as "goal reachable" and the one used for
   proving security properties will just be "bad". This is important for
   soundness: if it were H -> bad, it could give the impression
   that the events in H needs to be executed in order to derive bad,
   which is not necessarily true: there may be other clauses H' -> bad,
   with H' not containing H, which are removed by subsumption with the
   clause "bad" generated by this simplification. *)

let remove_equiv_events next_stage ((hyp,concl,hist,constra) as r) =
  if !weaksecret_mode && is_bad concl && List.for_all (function Pred(p,_) -> Param.begin2_pred == p) hyp
  then next_stage ([],concl,hist,constra)
  else next_stage r


let simplify next_stage repeat_next_stage ((hyp, concl, hist, constra) as r) =
  if (not (!weaksecret_mode)) || (detect_atteq r) || (detect_atteq2 r) ||
     (detect_atteq3 r) || (detect_atteq4 r) (* || (not (is_bad concl)) *)
  then
    next_stage r
  else
    let rec find_att x = function
        [] -> false
      | (Pred(p', [t])) :: _ when p'.p_prop land Param.pred_ATTACKER != 0 && Terms.equal_terms t x -> true
      | _ :: l -> find_att x l
    in
    let rec find_right x y = function
        [] -> None
      | (Pred(p', [t1; t2])) :: _ when p'.p_prop land Param.pred_ELIMVAR != 0 && Terms.equal_terms t1 x && not (Terms.equal_terms t2 y) -> Some t2
      | _ :: l -> find_right x y l
    in
    let rec find_left x y = function
        [] -> None
      | (Pred(p', [t1; t2])) :: _ when p'.p_prop land Param.pred_ELIMVAR != 0 && Terms.equal_terms t2 x && not (Terms.equal_terms t1 y) -> Some t1
      | _ :: l -> find_left x y l
    in

    let nat_vars = TermsEq.gather_nat_vars constra in
    let rec is_nat = function
      | Var v ->
          Terms.equal_types v.btype Param.nat_type &&
          (not (Param.get_ignore_types ()) || List.memq v nat_vars)
      | FunApp(f,[t]) when f == Terms.succ_fun -> is_nat t
      | _ -> false
    in

    let rec inst = function
        [] -> ()
      | (h::r) ->
          begin
          match h with
          (* A previous version asked t1 t2 t1', t2' to be variables; we now to it with terms. *)
          | Pred(p, [t1; t2]) when p.p_prop land Param.pred_ELIMVAR != 0 ->
              begin
                (* pred_ELIMVAR means AttackerBin or AttackerGuess
                   attacker'(M,M) is true for all natural numbers M.
                   So if attacker'(M,M') is true and M is a natural number,
                   then either M <> M' and we derive bad by attacker'(x,y) && attacker'(x,y') && y <> y' -> bad
                   or M = M' => we can unify M and M'. *)
                if is_nat t1 || is_nat t2 then
                  Terms.unify t1 t2
                else
                (* If attacker'(M,M') and attacker'(M,M'') are in the hypothesis of the
                   clause, either M' <> M'' and we derive bad by attacker'(x,y) && attacker'(x,y') && y <> y' -> bad
                   or M' = M'' => we can unify M' and M''.
                   attacker(M) is the same as attacker(M,M). *)
                if find_att t1 hyp || find_att t2 hyp then
                  Terms.unify t1 t2
                else
                  match find_right t1 t2 r with
                    Some t2' -> Terms.unify t2' t2
                  | None ->
                      match find_left t2 t1 r with
                        Some t1' -> Terms.unify t1' t1
                      | None -> ()
              end
          | _ -> ()
          end;
          inst r
    in
    try
      assert ((!Terms.current_bound_vars) == []);
      inst hyp;
      if ((!Terms.current_bound_vars) != []) then
        begin
	  (* A variable has been linked *)
          let hyp' = List.map Terms.copy_fact2 hyp in
          let concl' = Terms.copy_fact2 concl in
          let constra' = Terms.copy_constra2 constra in
          Terms.cleanup();
          repeat_next_stage (hyp', concl', hist, constra')
        end
      else
	(* Nothing has changed *)
        elim_att_guess_xx next_stage repeat_next_stage r
    with Unify ->
      Terms.cleanup()

(* Selection function: called when the standard selection function says
   to select the conclusion *)

let selfun ((hyp, concl, hist, constra) as r) =
  if not ((!weaksecret_mode) && (is_bad concl) && (hyp != []) && List.exists (function Pred(p,_) -> Param.begin2_pred != p) hyp) then -1
  else
  if (detect_atteq r) || (detect_atteq2 r) then 0 else
  begin
    print_string "Warning: selection not found in Weaksecr.selfun in rule\n";
    Display.Text.display_rule_indep r;
    -1
  end
