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
open Parsing_helper
open Types
open Terms

(* Debug verification *)

let debug_check_ordered_rule msg ord_rule = match ord_rule.order_data with
  | None -> ()
  | Some ord_data ->
      let (hypl,concl,_,_) = ord_rule.rule in
      if List.length ord_data != List.length hypl
      then internal_error (Printf.sprintf "[%s >> debug_check_ordered_rule] The number of hyp differs from the number of order data." msg);

      let nb_pred = match concl with
        | Pred({ p_info = [Combined pl]; _ }, _) -> List.length pl
        | _ -> 1
      in
      List.iter (fun (ord_fun,_) ->
        if List.exists (fun (i,_) -> i < 0 || i > nb_pred) ord_fun
        then internal_error (Printf.sprintf "[%s >> debug_check_ordered_rule] The ordering function is out of scope" msg);
      ) ord_data

(* let resol_step = ref 0 *)

(* Global variables. *)

let sound_mode = ref false
let is_inside_query = ref false
let initialized = ref false
let not_set = ref ([]: fact list)
let elimtrue_set = ref ([]: (int * fact) list)
let close_with_equations = ref false
let events_only_for_lemmas = ref []
let all_original_lemmas = ref []

(* Predicates to prove *)

type predicates_to_prove_t =
  {
    mutable tp_attacker : int; (* The maximal phase for the attacker predicate *)
    mutable tp_table : int; (* The maximal phase for the table predicate *)
    mutable tp_others : predicate list
  }

(* For attacker facts that occur in the conclusion of queries, we need
   to add all attacker facts of previous phases and of any type to the predicates to prove.
   For attacker facts that occur in hypotheses of lemmas, we need to add
   all attacker facts of previous phases to predicates to prove
   (because the lemma matching allows matching attacker phase n in the hypothesis of the clause
   with attacker phase n' for n'>=n in the hypothesis of the lemma).
   For simplicity, in both cases, we add all attacker facts of previous phases and of any type
   to the predicates to prove, and we remember only the maximum phase in field [tp_attacker].
*)

let pred_to_prove = { tp_attacker = -1; tp_table = -1; tp_others = [] }

let initialise_pred_to_prove pred_list =
  pred_to_prove.tp_attacker <- -1;
  pred_to_prove.tp_table <- -1;
  pred_to_prove.tp_others <- [];

  List.iter (fun p -> match p.p_info with
    | [(Attacker(n,_) | AttackerBin(n,_))] -> pred_to_prove.tp_attacker <- max pred_to_prove.tp_attacker n
    | [(Table n | TableBin n)] -> pred_to_prove.tp_table <- max pred_to_prove.tp_table n
    | _ ->
        if not (List.memq p pred_to_prove.tp_others)
        then pred_to_prove.tp_others <- p :: pred_to_prove.tp_others
  ) pred_list

let reset_pred_to_prove () =
  pred_to_prove.tp_attacker <- -1;
  pred_to_prove.tp_table <- -1;
  pred_to_prove.tp_others <- []

let is_pred_to_prove p = match p.p_info with
  | [(Attacker(n,_) | AttackerBin(n,_))] -> pred_to_prove.tp_attacker >= n
  | [(Table n | TableBin n)] -> pred_to_prove.tp_table >= n
  | _ ->
      p == Param.begin_pred || p == Param.begin_pred_inj || p == Param.begin2_pred ||
      p == Param.end_pred || p == Param.end_pred_inj || p == Param.end2_pred ||
      List.memq p pred_to_prove.tp_others

let is_pred_to_prove_fact = function
  | Pred(p,_) -> is_pred_to_prove p

(* Ordered reduction *)

let get_order_data ord_rule = match ord_rule.order_data with
  | None -> internal_error "[rules.ml >> get_order_data] Should only be applied when there are ordering data."
  | Some ord_data -> ord_data

let strict_ordering_function (ord_fun:ordering_function) =
  List.map (function (i,Leq) -> (i,Less) | t -> t) ord_fun

let can_pred_have_ordering_fun p =
  if p == Param.begin_pred || p == Param.begin2_pred || p == Param.begin_pred_inj || p == Param.end_pred || p == Param.end2_pred || p == Param.end_pred_inj
  then true
  else
    match p.p_info with
      | [Attacker _ | Mess _ | Table _ | AttackerBin _ | MessBin _ | TableBin _] -> true
      | _ -> false

let can_fact_have_ordering_fun = function
  | Pred(p,_) -> can_pred_have_ordering_fun p

let create_ordered_fact (ord_fun:ordering_function) f =
  if can_fact_have_ordering_fun f then ord_fun else []

let rec implies_ordering_function (ord_fun1:ordering_function) (ord_fun2:ordering_function) =
  match ord_fun1, ord_fun2 with
  | [], _ -> ()
  | _, [] -> raise NoMatch
  | (i1,_)::q1, (i2,_)::q2 when i2 > i1 -> raise NoMatch
  | (i1,_)::q1, (i2,_)::q2 when i2 < i1 -> implies_ordering_function ord_fun1 q2
      (* At this point, both lists start with (i,_) for the same i *)
  | (_,Less)::q1, (_,Leq)::q2 -> raise NoMatch
  | _::q1, _::q2 -> implies_ordering_function q1 q2

let implies_ordering_function_bool ord_fun1 ord_fun2 =
  try implies_ordering_function ord_fun1 ord_fun2; true with NoMatch -> false

(* Generate the ordering function corresponding to the intersection of ord_fun1 and ord_fun2.
   I.E. \tau \delta(i) \tau' iff \tau \delta1(i) \tau' && \tau \delta2(i) \tau' *)
let rec inter_ordering_fun ord_fun1 ord_fun2 =
  match ord_fun1, ord_fun2 with
  | [], _ -> ord_fun2
  | _, [] -> ord_fun1
  | (i1,ord1)::q1, (i2,_)::q2 when i1 < i2 -> (i1,ord1) :: (inter_ordering_fun q1 ord_fun2)
  | (i1,_)::q1, (i2,ord2)::q2 when i1 > i2 -> (i2,ord2) :: (inter_ordering_fun ord_fun1 q2)
      (* At this point, both lists start with (i,_) for the same i *)
  | (i,Less)::q1, _::q2
  | _::q1, (i,Less)::q2 -> (i,Less)::(inter_ordering_fun q1 q2)
  | t::q1, _::q2 -> t :: (inter_ordering_fun q1 q2)

type saturated_reduction =
  {
    sat_rule : reduction;
    sat_generate_ordering_data : (ordering_function * bool) -> (ordering_function * bool) list
  }

let saturated_reduction_of_reduction ((hypl, _, _, _) as rule) =

  let (application_result, strict_order_to_compute) =
    List.fold_right (fun fact (accu_ord,accu_strict) ->
      if can_fact_have_ordering_fun fact
      then
        let to_prove = is_pred_to_prove_fact fact in
        (Some to_prove :: accu_ord, to_prove || accu_strict)
      else
	(None :: accu_ord,accu_strict)
	  ) hypl ([],false)
  in

  let generate_ordering_data (ord_fun,nounif_sel) =
    let strict_ord_fun =
      if strict_order_to_compute
      then strict_ordering_function ord_fun
      else [] (* In this case, it will be never used *)
    in
    List.map (function
      | None -> ([],nounif_sel)
      | Some true -> (strict_ord_fun,nounif_sel)
      | _ -> (ord_fun,nounif_sel)
    ) application_result
  in

  {
    sat_rule = rule;
    sat_generate_ordering_data = generate_ordering_data
  }

(*****************************************************************
        Analysis of the history for ordered clauses
******************************************************************)

type analysed_history =
  {
    a_hist : history;
    a_order_data : (ordering_function * bool) list
  }

let get_order_data_from_analyed_history_op = function
  | None -> internal_error "[rules.ml >> get_order_data_from_analyed_history_op] This function should only be applied when order data exist."
  | Some ana_hist -> ana_hist.a_order_data

(* [replace_nth_list l1 n l2] returns a list obtained by replacing the [n]-th element of list [l2] with list [l1]. *)
let rec replace_nth_list l1 n = function
    [] -> internal_error "replace_nth_list error"
  | (a::l) -> if n = 0 then l1 @ l else a::(replace_nth_list l1 (n-1) l)

(* [generate_subsuming_ordering_fun \delta1 \delta2 generates an ordering function \delta such
   that \delta subsumes \delta1 and \delta subsumes \delta2 *)
let rec generate_subsuming_ordering_fun ord_fun1 ord_fun2 =
  match ord_fun1, ord_fun2 with
  | [], _ | _, [] -> []
  | (i1,_)::q1, (i2,_)::_ when i1 < i2 -> generate_subsuming_ordering_fun q1 ord_fun2
  | (i1,_)::_, (i2,_)::q2 when i1 > i2 -> generate_subsuming_ordering_fun ord_fun1 q2
    (* At this point, both lists start with (i,_) for the same i *)
  | (i,Leq)::q1, _::q2
  | _::q1, (i,Leq)::q2 -> (i,Leq)::(generate_subsuming_ordering_fun q1 q2)
  | t::q1, _::q2 -> t::(generate_subsuming_ordering_fun q1 q2)

(* [generate_ordering_fun_from_lemma ord_data_list matched_hyp] returns an ordering function
   that is guaranteed to hold for facts added by a lemma, knowing that the facts of the clause
   matched by the hypotheses of the lemma are specified by [matched_hyp] and the ordering
   information for the clause is given by [ord_data_list]. *)
let generate_ordering_fun_from_lemma ord_data_list matched_hyp =
  let get_ord_from_one_matched_hyp (i,_) =
    if i < 0 then
      (* Corresponds to the -i th fact of the conclusion. *)
      [-i,Leq]
    else
      (* Corresponds to the i th fact of the hypotheses. *)
      fst (List.nth ord_data_list i)
  in

  let rec go_through_matched_hyp accu = function
    | [] -> accu
    | h::q ->
	let ord_fun = get_ord_from_one_matched_hyp h in
        go_through_matched_hyp (generate_subsuming_ordering_fun accu ord_fun) q
  in

  match matched_hyp with
    | [] -> internal_error "[rules.ml >> generate_ordering_fun_from_lemma] A lemma should have at least one fact in its premise."
    | h::q ->
        let ord_fun = get_ord_from_one_matched_hyp h in
        go_through_matched_hyp ord_fun q

(* [analyse_history] analyzes the history [hist]
   of the rule to retrieve the order information list of the hypotheses of the clauses.

   History:
    - Any : Basic removal.
    - Removed : Corresponds to the transformation rule Red_o
        -> We need to compute the intersection of ordering function and nounif selection
    - Resolution(hist1,n,hist2) : Corresponds to either the transformation rule DataHyp,
        element simplification or equiv set.
          -> For Data Hyp, we must have hist1 of the form Rule(-1,Apply f ,_,_,_) with f of cat Tuple
          -> For Element simplification, hist1 is of the form Rule(-1, Elem _ ,_,_,_)
          -> For Equiv Set, hist1 is of the form Rule(_, LbLEquiv,_,_,_)
    - HLemma : Corresponds to the application of Lemmas
    - HCaseDistinction : Corresponds to the generation of set of clauses completely covering
        our initial set of clauses.
        -> Does not modify the order nor the nounif selection
*)

let ordered_rule_of_analysed_history_op ana_hist_op ((_,_,hist,_) as rule) =
  match ana_hist_op with
  | None -> { rule = rule; order_data = None }
  | Some ana_hist ->
      assert (hist == ana_hist.a_hist);
      { rule = rule; order_data = Some ana_hist.a_order_data }

let analyse_history last_analysed_history_op ((_,_,hist,_):reduction) =
  match last_analysed_history_op with
  | None ->
      (* Corresponds to the case where there is no induction, no nested queries
         and no option IgnoreOnce *)
      None
  | Some last_analysed_history ->
      let rec sub_analyse hist =
        if hist == last_analysed_history.a_hist
        then last_analysed_history.a_order_data
        else
          match hist with
            | Any(i,hist') | HMaxHyp(i,hist') ->
                let ord_data_list' = sub_analyse hist' in
                Reduction_helper.remove_at i ord_data_list'
            | Removed(i_rm,i_dup,hist') ->
                (* We replace the duplicated ordering function with the intersection of the
                   duplicated ordering function and removed ordering function *)
                let ord_data_list1 = sub_analyse hist' in
                let (ord_fun_rm,nounif_sel_rm) = List.nth ord_data_list1 i_rm
                and (ord_fun_dup,nounif_sel_dup) = List.nth ord_data_list1 i_dup in
                let new_ord_fun = inter_ordering_fun ord_fun_rm ord_fun_dup in
                let new_nounif_sel = nounif_sel_rm && nounif_sel_dup in
                let ord_data_list2 = Reduction_helper.replace_at i_dup (new_ord_fun,new_nounif_sel) ord_data_list1 in
                Reduction_helper.remove_at i_rm ord_data_list2
            | HEquation(_,_,_,hist')
            | HCaseDistinction(_,_,_,_,hist') -> sub_analyse hist'
            | Resolution(hist1,n,hist2) ->
                let ord_data_list1 = sub_analyse hist2 in
                let (ord_fun,nounif_sel) = List.nth ord_data_list1 n in
                begin match hist1 with
                  | Rule(-1,Elem _,hyp,_,_)
                  | Rule(_,LblEquiv,hyp,_,_) ->
                      let ord_data_hyp = List.map (fun _ -> ([],nounif_sel)) hyp in
                      replace_nth_list ord_data_hyp n ord_data_list1
                  | Rule(_,LblClause,[],_,_) ->
                      Reduction_helper.remove_at n ord_data_list1
                  | Rule(-1,Apply (_,p),hyp,_,_) ->
                      (* Corresponds to Data Hyp so p must be an attacker predicate. *)
                      let new_ord_fun =
                        if is_pred_to_prove p
                        then strict_ordering_function ord_fun
                        else ord_fun
                      in
                      let ord_data_hyp = List.map (fun _ -> (new_ord_fun,nounif_sel)) hyp in
                      replace_nth_list ord_data_hyp n ord_data_list1
                  | _ -> Parsing_helper.internal_error "[rules.ml >> analyse_history] Unexpected history (1)."
                end
            | HLemma(_,_,([],_,_),hist') -> sub_analyse hist'
            | HLemma(_,hyp_m,(hyp,_,_),hist') ->
                let ord_data_list1 = sub_analyse hist' in
                let ord_fun_lem = generate_ordering_fun_from_lemma ord_data_list1 hyp_m in
                let ord_data_lem = List.map (fun fact -> create_ordered_fact ord_fun_lem fact, false) hyp in
                ord_data_list1 @ ord_data_lem
            | _ -> Parsing_helper.internal_error "[rules.ml >> analyse_history] Unexpected history (2)."
      in

      Some { a_hist = hist; a_order_data = sub_analyse hist }

let analysed_history_op_of_ordered_rule = function
  | { order_data = None } -> None
  | { order_data = Some ord_data; rule = (_,_,hist,_) } ->
      Some { a_hist = hist; a_order_data = ord_data }

(*****************************************************************
        Set Equiv
******************************************************************)

(* Check that two facts are smaller for all instances *)

let rec get_vars_rep vlist = function
    Var v -> vlist := v :: (!vlist)
  | FunApp(_,l) ->
      List.iter (get_vars_rep vlist) l

let get_vars_rep_fact vlist = function
    Pred(p,l) -> List.iter (get_vars_rep vlist) l

(* [remove_first vlist v] removes the first occurrence of
   [v] in [vlist]. Raise [Not_found] when [v] does not occur in [vlist] *)

let remove_first vlist v =
  let rec remove_first_rec v = function
      [] -> raise Not_found
    | (v'::l) -> if v' == v then l else v' :: (remove_first_rec v l)
  in
  vlist := remove_first_rec v (!vlist)

let is_smaller f1 f2 =
  (Terms.fact_size f1 < Terms.fact_size f2) &&
  (let v1 = ref [] in
  let v2 = ref [] in
  get_vars_rep_fact v1 f1;
  get_vars_rep_fact v2 f2;
  try
    List.iter (remove_first v2) (!v1);
    true
  with Not_found ->
    false)

let equiv_set = ref ([]: (fact list * fact * int) list)

let check_equiv (hyp, concl, n) =
  (* Check that \sigma h smaller than \sigma concl for all \sigma, for all h in hyp.
     This implies termination of the replacement process *)
  if not (List.for_all (fun h -> is_smaller h concl) hyp) then
    Parsing_helper.user_error "For equivalences, the conclusion must be larger than the hypotheses\nand this must be true for all instances of these facts.";
  (* Check that only ONE replacement rule applies to a given fact.
     This implies confluence of the replacement process *)
  List.iter (fun (_, concl',_) ->
    try
      Terms.auto_cleanup (fun () -> Terms.unify_facts concl concl');
      Parsing_helper.user_error "Conflict between equivalences: two of them apply to the same fact.";
    with Unify -> ()
        ) (!equiv_set);
  match concl with
    Pred(p,((FunApp(f,_) :: _) as l)) when
         p.p_prop land Param.pred_TUPLE != 0 &&
           f.f_cat = Tuple ->
     begin
       try
         let _ = reorganize_fun_app f l in
         Parsing_helper.user_error "Conflict between an equivalence and the decomposition of data constructors:\nan equivalence applies to a fact which is also decomposable by data constructors."
       with Not_found -> ()
     end
  | _ -> ()

let set_equiv set =
  (* Verify that the rules are ok *)
  List.iter check_equiv set;
  (* Store the replacement rules *)
  equiv_set := set

(*****************************************************************
        Limiting the depth of terms and number of hypotheses to
                        enforce termination. Disabled in sound mode.

        The limit function replace subterm with depth egal to
        Param.max_deph by fresh variable.
        Furthermore, the rule can have a limited number of hypothesis,
        depending of Param.max_hyp.
******************************************************************)

(* Limiting the induction size *)

let rec cancel_induction restwork vl hyp hist n = match hyp with
  | [] -> restwork hyp hist
  | pred::q_hyp  when List.exists (fun v -> occurs_var_fact v pred) vl ->
      cancel_induction (fun hyp1 hist1 ->
        restwork hyp1 (HMaxHyp(n,hist1))
      ) vl q_hyp hist (n+1)
  | pred::q_hyp ->
      cancel_induction (fun hyp1 hist1 ->
        restwork (pred::hyp1) hist1
      ) vl q_hyp hist (n+1)

let limit_induction f_next f_next_again ((hyp,concl,hist,constra) as r) =
  if !sound_mode
  then f_next r
  else
    try
      Selfun.find_inductive_variable_to_remove (fun vl ->
        cancel_induction (fun hyp1 hist1 ->
          TermsEq.simplify_constraints_rule f_next f_next_again (hyp1,concl,hist1,constra)
        ) vl hyp hist 0
      ) r
    with Not_found -> f_next r

let rec limit_depth n t =
   if n = 0 then
      Terms.new_var_def_term (Terms.get_term_type t)
   else
      match t with
      | Var v -> t
      | FunApp(f,l) -> FunApp(f, List.map (limit_depth (n-1)) l)

let limit_depth_occ n = function
  | FunApp(f,args) -> FunApp(f,List.map (limit_depth n) args)
  | _ -> Parsing_helper.internal_error "[Rules.ml >> limit_depth_occ] Should be a name."

let limit_depth_fact n = function
  | Pred(chann,[t;tocc]) when chann == Param.begin_pred_inj ->
     (* We do not want that the occurrence name be replaced with a variable. *)
     Pred(chann,[limit_depth n t; limit_depth_occ n tocc])
  | Pred(chann,t) -> Pred(chann, List.map (limit_depth n) t)

let rec max_length n = function
    [] -> []
  | (a::l) -> if n = 0 then [] else a::(max_length (n-1) l)

let limit_length_constraints n c =
  {
    is_nat = max_length n c.is_nat;
    neq = List.map (max_length n) (max_length n c.neq);
    is_not_nat = max_length n c.is_not_nat;
    geq = max_length n c.geq
  }

let rec cancel_history n maxn h =
  if maxn <= n then h else
  cancel_history n (maxn-1) (HMaxHyp(n,h))

let limit_depth_rule r =
  if !sound_mode then r else
  let r =
    let max_hyp = !Param.max_hyp in
    if max_hyp < 0 then r else
    let (hyp, concl, hist,constra) = r in
    (* remove some hypotheses/constraints if they are too numerous
       Adjust the history hist accordingly *)
    (max_length max_hyp hyp, concl,
     cancel_history max_hyp (List.length hyp) hist,
     limit_length_constraints max_hyp constra)
  in
   let max_depth = ! Param.max_depth in
   if max_depth < 0 then r else
   let (hyp, concl, hist,constra) = r in
   (List.map (limit_depth_fact max_depth) hyp,
    limit_depth_fact max_depth concl, hist,
    Terms.map_constraints (limit_depth max_depth) constra)

(******************************************************************
        Decompose tuples and data constructors in hypotheses of rules.
        It is important for the correctness of this optimization that
        p:x is never selected when p is a predicate on which we
        perform the decomposition of data constructors, except
        when there are only such facts in the clause.

        Also eliminates duplicate hypotheses.
******************************************************************)

let rec pos_in_list init f = function
    [] -> -1
  | (a::l) -> if f a then init else pos_in_list (init+1) f l

(* is_name_proj 0 s returns true when s starts with numbers,
   followed by "-proj-".
   The name of projections as generated by Terms.projection_fun
   satisfies this condition, and no other function does.
   (In particular, identifiers chosen by the user cannot
   satisfy it, because they cannot contain "-".) *)

let rec is_name_proj n s =
  if String.length s < n+6 then false else
  if ('0' <= s.[n]) && ('9' >= s.[n]) then is_name_proj (n+1) s else
  (String.sub s n 6) = "-proj-"

let is_exempt_from_dectuple (_,_,h,_) =
  match h with
    Rule (_,Apply(f,p),_,_,_) ->
      (* rules that apply constructors ... *)
      (f.f_cat = Tuple) ||
      (* or their projections *)
        (match f.f_name with
         | Fixed s -> is_name_proj 0 s
         | Renamable _ -> false)
  | Rule (_,LblEquiv,_,_,_) -> true
  | _ -> false

let rec decompose_hyp_rec accu hypl =
  List.fold_right (fun hyp1 (hypl,nl,histl) ->
    let default() =
      let count = pos_in_list (nl+1) (equal_facts hyp1) hypl in
      if count >= 0 then
        (hypl, nl-1, Removed(nl, count, histl))
      else
        (hyp1::hypl, nl-1, histl)
    in
    match hyp1 with
      | Pred(chann,_) when chann == Param.begin_pred || chann == Param.begin_pred_inj || chann == Param.begin2_pred -> default ()
      | Pred(chann,l0) ->
        let rec try_equiv_set = function
            [] ->
              if chann.p_prop land Param.pred_TUPLE != 0 then
                try
                  match l0 with
                    (FunApp(f,_) :: _) when f.f_cat = Tuple ->
                      let l = reorganize_fun_app f l0 in
                      begin match History.get_rule_hist (RApplyFunc(f,chann)) with
                        | Rule(_, _, hyp, _, _) as hist_dec ->
                            decompose_hyp_rec (hypl, nl+(List.length l)-1, (Resolution(hist_dec, nl, histl)))
                              (List.map2 (fun (Pred(p',_)) x -> Pred(p', x)) hyp l)
                        | _ -> Parsing_helper.internal_error "[rules.ml >> decompose_hyp_rec] Unexpected history."
                      end
                  | _ -> default()
                with Not_found -> default()
              else default()
          | (hypeq, concleq, neq)::l ->
              try
                let hypeq' =
                  Terms.auto_cleanup (fun () ->
                    Terms.match_facts concleq hyp1;
                    List.map copy_fact3 hypeq)
                in
                let hist_dec = Rule(neq, LblEquiv, hypeq, concleq, true_constraints) in
                decompose_hyp_rec (hypl, nl+(List.length hypeq')-1, (Resolution(hist_dec, nl, histl))) hypeq'
              with NoMatch ->
                try_equiv_set l
        in
        try_equiv_set (!equiv_set)
      ) hypl accu

let decompose_hyp_tuples ((hypl, concl, hist, constra) as rule) =
  if is_exempt_from_dectuple rule then
    rule
  else
   let (hypl', nl', histl') =
     decompose_hyp_rec ([], (List.length hypl)-1, hist) hypl
   in
   (hypl', concl, histl',constra)

(**********************************************************************
        Counts occurrences of a variable in a list of facts
        [occur_count v l]
        returns the number of occurrences of v in the list of facts l
***********************************************************************)

let rec list_add f = function
    [] -> 0
  | (a::l) -> (f a) + (list_add f l)

(** [term_occur_count v t] return the number of occurrence of [v] in [t] *)
let rec term_occur_count v = function
    Var v' -> if v == v' then 1 else 0
  | FunApp(f,l) -> list_add (term_occur_count v) l

let fact_occur_count v = function
    Pred(chann, l) -> list_add (term_occur_count v) l

let occur_count v l = list_add (fact_occur_count v) l

let constra_occur_count v (t1,t2) = term_occur_count v t1 + term_occur_count v t2

(** [occur_count_constra v f] returns the number of occurrences of [v] in the formula [f]. *)
let occur_count_constra v c =
  (list_add (list_add (constra_occur_count v)) c.neq) +
  (list_add (term_occur_count v) c.is_nat) +
  (list_add (term_occur_count v) c.is_not_nat) +
  (list_add (fun (t1,_,t2) -> term_occur_count v t1 + term_occur_count v t2) c.geq)

(**********************************************************************
        Eliminate hypotheses p(x1...xn) where p has been declared "elimVar"
        or "elimVarStrict" and x1...xn do not occur elsewhere.
        Such a declaration means that p(x...x) is true for some value of x.
        This is correct in particular when p = attacker. When p is declared
        elimVar and we are not in sound_mode, x1...xn are allowed to occur
        in inequalities.

        In sound_mode, we always require that x1...xn do not occur in
        inequalities.
***********************************************************************)

let elim_any_x (hypl', concl, histl', constra) =
  let (hypl'', _, histl'') = List.fold_right (fun hyp1 (hypl, nl, histl) ->
     match hyp1 with
      | Pred(chann, l) ->
         begin
           try
             let (n, ff) = List.find (fun (_, ff) ->
               let hyp1vlist = ref [] in
               Terms.get_vars_fact hyp1vlist hyp1;
               try
                 Terms.auto_cleanup (fun () ->
                   Terms.unify_facts ff hyp1;
               (* check that all modified variables of hyp1 do not
                  occur in the rest of R including inequalities *)
                   List.iter (fun v ->
                     let vt = Terms.follow_link (fun x -> Var x) (Var v) in
                     match vt with
                       Var v' when v' == v -> ()
                     | _ ->
                         if (occur_count v (concl :: hypl') > fact_occur_count v hyp1)
                       || (occur_count_constra v constra > 0) then raise Unify
                             ) (!hyp1vlist);
               (* all checks successful *)
                   true
                     )
               with Unify ->
                 false
                   ) (!elimtrue_set)
             in
             (hypl, nl-1, (Resolution(Rule(n, LblClause, [], ff, true_constraints), nl, histl)))
           with Not_found ->
             if
               (chann.p_prop land Param.pred_ANY != 0 &&
                List.for_all (function
                    Var v -> (occur_count v (concl :: hypl') == fact_occur_count v hyp1)
                        && ((not (!sound_mode)) || (occur_count_constra v constra == 0))
                  | _ -> false) l)
             ||
               (chann.p_prop land Param.pred_ANY_STRICT != 0 &&
                List.for_all (function
                    Var v -> (occur_count v (concl :: hypl') == fact_occur_count v hyp1)
                        && (occur_count_constra v constra == 0)
                  | _ -> false) l)
             then
               (hypl, nl-1, (Any(nl, histl)))
             else
               (hyp1 :: hypl, nl-1, histl)
         end
           ) hypl' ([], (List.length hypl')-1, histl')
   in
   (hypl'', concl, histl'',constra)

(**********************************************
Subsumption test between rules:
H -> F (C) => H' -> F' (C') iff exists \sigma,
   \sigma H \subseteq H', \sigma F = F', C' => sigma C

This section consists of:
   1- Matching between hypotheses
   2- Reordering of the hypothesis
   3- Final function : [implies rule1 rule2]
***********************************************)

(* 1. Matching between hypotheses. Try all possible orderings
      of the hypotheses *)

(**Test \sigma H \subseteq H' for multiset inclusion *)
let rec match_fact_with_hyp nextf fact1 hyp2 passed_hyp =
  match hyp2 with
  | [] -> raise NoMatch
  | (fact2::fact_l) ->
      try
        Terms.auto_cleanup (fun () ->
          Terms.match_facts fact1 fact2;
          nextf (passed_hyp @ fact_l)
        )
      with NoMatch ->
        match_fact_with_hyp nextf fact1 fact_l (fact2 :: passed_hyp)

let rec match_hyp nextf hyp1 hyp2 =
  match hyp1 with
  | [] -> nextf ()
  | (fact1 :: fact_l1) ->
      match_fact_with_hyp
        (match_hyp nextf fact_l1) fact1 hyp2 []

let match_hyp_implies = match_hyp

let rec match_fact_with_hyp_ordered nextf fact1 ord1 ord_hyp2 passed_hyp =
  match ord_hyp2 with
  | [] -> raise NoMatch
  | ((fact2,(ord2,_)) as ord_fact2) :: fact_l ->
      try
        Terms.auto_cleanup (fun () ->
          Terms.match_facts fact1 fact2;
          implies_ordering_function ord1 ord2;
          nextf (passed_hyp @ fact_l)
        )
      with NoMatch ->
        match_fact_with_hyp_ordered nextf fact1 ord1 fact_l (ord_fact2 :: passed_hyp)

let rec match_hyp_ordered nextf ord_hyp1 ord_hyp2 =
  match ord_hyp1 with
  | [] -> nextf ()
  | (fact1,(ord1,_)) :: fact_l1 ->
      match_fact_with_hyp_ordered
        (match_hyp_ordered nextf fact_l1) fact1 ord1 ord_hyp2 []

let match_hyp_ordered_implies = match_hyp_ordered

(* 2. Try to reorder hypotheses to speed up the subsumption test.
      Put first constant hypotheses (no unbound variable. They
      can contain variables already bound by matching the conclusion.)
      Then put other hypotheses in decreasing size order. *)

let rec has_unbound_var = function
    Var v ->
      begin
        match v.link with
          NoLink -> true
        | TLink _ -> false
        | VLink _ -> false
        | _ -> internal_error "unexpected link in has_unbound_var"
      end
  | FunApp(_,l) -> List.exists has_unbound_var l

let fact_has_unbound_var = function
    Pred(_, tl) -> List.exists has_unbound_var tl

let rank f =
  if fact_has_unbound_var f then
    fact_size f
  else
    1000000 (* Something probably bigger than all sizes of terms *)

let rank_compare (_,r1) (_,r2) = r2 - r1

let reorder hyp =
  if List.length hyp > 4 then
    let hyp_rank = List.map (fun f -> (f, rank f)) hyp in
    let hyp_sorted = List.sort rank_compare hyp_rank in
    List.map (fun (f,_) -> f) hyp_sorted
  else
    hyp

let reorder_ordered hyp =
  if List.length hyp > 4 then
    let hyp_rank = List.map (fun f -> (f, rank (fst f))) hyp in
    let hyp_sorted = List.sort rank_compare hyp_rank in
    List.map (fun (f,_) -> f) hyp_sorted
  else
    hyp

(* 3. The final function for subsumption test *)

let implies (hyp1, concl1, _, constr1) (hyp2, concl2, _, constr2) =
  if List.length hyp1 > List.length hyp2 then false else
  try
    Terms.auto_cleanup (fun () ->
      begin
        match concl1 with
        | Pred(p, []) when p == Param.bad_pred -> ()
        | _ -> Terms.match_facts concl1 concl2
      end;
      match_hyp (fun () -> TermsEq.implies_constraints_keepvars3 (concl2 :: hyp2) constr2 constr1) (reorder hyp1) hyp2;
      true
    )
  with NoMatch -> false

let implies_ordered ord_rule1 ord_rule2 =
  if ord_rule1.order_data = None
  then implies ord_rule1.rule ord_rule2.rule
  else
    let ((hyp1, concl1, _, constr1),ord_data1) = (ord_rule1.rule,get_order_data ord_rule1)
    and ((hyp2, concl2, _, constr2),ord_data2) = (ord_rule2.rule,get_order_data ord_rule2) in

    if List.length hyp1 > List.length hyp2
    then false
    else
      begin
        try
          Terms.auto_cleanup (fun () ->
            begin
              match concl1 with
              | Pred(p, []) when p == Param.bad_pred -> ()
              | _ -> Terms.match_facts concl1 concl2
            end;
            let ord_hyp1 = List.combine hyp1 ord_data1
            and ord_hyp2 = List.combine hyp2 ord_data2 in
            match_hyp_ordered (fun () -> TermsEq.implies_constraints_keepvars3 (concl2 :: hyp2) constr2 constr1) (reorder_ordered ord_hyp1) ord_hyp2;
            true
          )
        with NoMatch -> false
      end

(********************************************
Check usage of may-fail variables and fail
*********************************************)

let rec check_no_fail = function
    Var v -> assert(not v.unfailing)
  | FunApp(f,l) ->
      assert(f.f_cat != Failure);
      List.iter check_no_fail l

let check_top_fail = function
    Var v -> ()
  | FunApp(f,l) -> List.iter check_no_fail l

let check_fact_fail = function
    Pred({p_info = [TestUnifP _]}, [t1;t2]) ->
      begin
        (* testunif: allow fail at the top, plus possibly inside a tuple *)
        match (t1,t2) with
          FunApp(f1,l1), FunApp(f2,l2) when f1 == f2 && f1.f_cat == Tuple ->
            List.iter check_top_fail l1;
            List.iter check_top_fail l2
        | _ ->
            check_top_fail t1;
            check_top_fail t2
      end
  | Pred(p,l) ->
      (* attacker predicates: allow fail at the top
         other predicates: don't allow fail at all *)
      begin
        match p.p_info with
          [Attacker _ | AttackerBin _ | AttackerGuess _ ] (* attacker *) ->
            List.iter check_top_fail l
        | [PolymPred _] (* user-defined *)
        | [] (* user-defined + plus a few others: end_pred, end_pred_inj, bad_pred, ... *)
        | [Equal _] (* equal; used in user-defined clauses *)
        | [Mess _ | InputP _ | OutputP _ | MessBin _ | InputPBin _
           | OutputPBin _ | Table _ | TableBin _ | Compromise _ | Combined _ | NegationPred _ ] ->
            List.iter check_no_fail l
        | _ -> Parsing_helper.internal_error "Terms.check_rule: unexpected predicate info"
      end

let check_rule ((hyp, concl, hist, constra) as r) =
  try
    List.iter check_fact_fail hyp;
    check_fact_fail concl;
    iter_constraints check_no_fail constra
  with x ->
    Display.Text.display_rule_indep r;
    raise x

let check_rule_ordered ord_rule = check_rule ord_rule.rule

(* The rule base. We distinguish rules that have no selected hypothesis
   [base_ns] and rules that have a selected hypothesis [base_sel].
   The number of the selected hypothesis is stored with the rule
   in the second case. *)

type 'a database =
  {
    queue : 'a Pvqueue.q;
    mutable count : int;
    mutable base_ns : 'a list;
    mutable base_sel : ('a * int) list
  }

let new_database () =
  {
    queue = Pvqueue.new_queue ();
    count = 0;
    base_ns = [];
    base_sel = []
  }

(* [add_rule] adds the rule in the rule base.
   It also eliminates subsumed rules. *)

let main_add_rule database implies check_rule rule =
  (* Check that the rule is not already in the rule base or in the queue *)
  let test_impl = fun r -> implies r rule in
  if (List.exists test_impl database.base_ns) ||
     (List.exists (function (r,_) -> implies r rule) database.base_sel) ||
     (Pvqueue.exists database.queue test_impl) then () else
    begin
      (* eliminates from the rule_base the rules implied by rule *)
      let test_impl = fun r -> not (implies rule r) in
      database.base_ns <- List.filter test_impl database.base_ns;
      database.base_sel <- List.filter (function (r,_) -> not (implies rule r)) database.base_sel;
      Pvqueue.filter database.queue test_impl;
      check_rule rule;
      Pvqueue.add database.queue rule
    end

let add_rule database (rule:reduction) = main_add_rule database implies check_rule rule

let add_rule_solving database rule = main_add_rule database implies_ordered check_rule_ordered rule

(* Several simplification functions for rules *)

(* 1. Simplify the constraints *)

let simplify_rule_constra = TermsEq.simplify_constraints_rule

(* 2. eliminate rules that have in hypothesis a "not" fact
      (secrecy assumption) *)

let elim_not next_stage ((hyp', _, _,_) as r) =
  if (List.exists (fun h -> List.exists (matchafact h) (!not_set)) hyp') then
    ()
  else
    next_stage r

let elim_not_solving apply_not next_stage ((hyp', _, _,_) as r) =
  if apply_not && (List.exists (fun h -> List.exists (matchafact h) (!not_set)) hyp') then
    ()
  else
    next_stage r

(* 3. eliminate tautologies (rules that conclude a fact already in their
      hypothesis) *)

let elim_taut next_stage ((hyp', concl, _,_) as r) =
  if List.exists (equal_facts concl) hyp' then
    ()
  else
    next_stage r

(* 4. eliminate hypotheses p(x1...xn) where p has been declared "elimVar"
   or "elimVarStrict" and x1...xn do not occur elsewhere.
   Such a declaration means that p(x...x) is true for some value of x.
   This is correct in particular when p = attacker. When p is declared
   elimVar and we are not in sound_mode, x1...xn are allowed to occur
   in inequalities.

   In sound_mode, we always require that x1...xn do not occur in
   inequalities. *)

let elim_any_x2 next_stage r =
  next_stage (elim_any_x r)

(* 5. decompose tuples and data constructors in hypotheses
   It is important for the correctness of this optimization that
   p:x is never selected when p is a predicate on which we
   perform the decomposition of data constructors, except
   when there are only such facts in the clause.

   Also eliminates duplicate hypotheses.
 *)

let decompose_hyp_tuples2 next_stage r =
  next_stage (decompose_hyp_tuples r)

(* 6. decompose tuples and data constructors in conclusion
   It is important for the correctness of this optimization that
   p:x is never selected when p is a predicate on which we
   perform the decomposition of data constructors. *)

let decompose_concl_tuples next_stage ((hyp', concl, hist', constra) as r) =
  if is_exempt_from_dectuple r then
    next_stage r
  else
    let put_clause first_fact hist =
      assert (!current_bound_vars == []);
      let r = (List.map copy_fact hyp', copy_fact first_fact, hist, copy_constra constra) in
      cleanup();
      next_stage r
    in
    let rec tuple_dec hist concl =
      match concl with
        Pred(chann, l0) ->
          let rec try_equiv_set = function
              [] ->
                if chann.p_prop land Param.pred_TUPLE != 0 then
                  match l0 with
                    FunApp(f,_) :: _ when f.f_cat = Tuple ->
                      let l = reorganize_fun_app f l0 in
                      List.iteri (fun n first ->
                        match History.get_rule_hist (RApplyProj(f, n, chann)) with
                          | Rule(_,_,_,Pred(p',_), _) as hist_dec ->
                              let concl' = Pred(p', first) in
                              let hist'' = Resolution(hist, 0, hist_dec) in
                              rec_call concl' hist''
                          | _ -> Parsing_helper.internal_error "[rules.ml >> decompose_concl_tuples] Unexpected history"
                        ) l
                  | _ -> raise Not_found
                else
                  raise Not_found
            | (hypeq, concleq, neq)::l ->
                try
                  let hypeq' =
                    Terms.auto_cleanup (fun () ->
                      Terms.match_facts concleq concl;
                      List.map copy_fact3 hypeq)
                  in
                  List.iteri (fun n concl' ->
                    let hist_dec = Rule(neq + n + 1, LblEquiv, [concleq], List.nth hypeq n, true_constraints) in
                    let hist'' = Resolution(hist, 0, hist_dec) in
                    rec_call concl' hist''
                        ) hypeq'
                with NoMatch ->
                  try_equiv_set l
          in
          try_equiv_set (!equiv_set)
    and rec_call concl hist =
      try
        tuple_dec hist concl
      with Not_found ->
        put_clause concl hist
    in
    begin
      try
        tuple_dec hist' concl
      with Not_found ->
        next_stage r
    end

(* 7. Element simplification
     att(x) /\ elem(M_1, x) /\ ... /\ elem(M_n, x)
   becomes
     att(M_1) /\ ... /\ att(M_n)
   when x does not occur elsewhere in the clause.
   When x occurs elsewhere, the simplification can be done when the
   clause has no selected fact. It leads to a loss of precision in
   this case. (So the latter case is disabled in sound mode.)

   "att" can be any predicate declared with data decomposition (pred_TUPLE).
   The predicate "elem" must be declared pred_ELEM.
   *)

let rec collect_preds v = function
    [] -> []
  | (f::l) ->
      match f with
        Pred(p, [Var v']) when p.p_prop land Param.pred_TUPLE != 0
            && v' == v ->
              p :: (collect_preds v l)
      | _ -> collect_preds v l

let rec transform_hyp preds v hist n = function
    [] -> ([], hist)
  | (f::l) ->
      match f with
        Pred(p, [t1; Var v']) when p.p_prop land Param.pred_ELEM != 0 && v == v' ->
          begin match History.get_rule_hist (RElem(preds, p)) with
            | Rule(_, _, hyp, _, _) as hist_dec ->
                let hist' = Resolution(hist_dec, n,  hist) in
                let (l', hist'') = transform_hyp preds v hist' (n + List.length preds) l in
                ((List.map (function
                    (Pred(p',_)) -> Pred(p', [t1])
                  ) hyp) @ l', hist'')
            | _ -> Parsing_helper.internal_error "[rules.ml >> transform_hyp] Unexpected history"
          end
      | _ ->
          let (l', hist') = transform_hyp preds v hist (n+1) l in
          (f :: l', hist')

let transform_rule v (hyp, concl, hist, constra) =
  let preds = collect_preds v hyp in
  let (hyp', hist') = transform_hyp preds v hist 0 hyp in
  (hyp', concl, hist', constra)

let check_occurs_fact p0 v = function
    Pred(p, [Var v']) when p.p_prop land Param.pred_TUPLE != 0
              && v == v' -> false
  | Pred(p, [t1; Var v']) when p.p_prop land Param.pred_ELEM != 0 && p == p0
              && v == v' -> occurs_var v t1
  | Pred(p, tl) -> List.exists (occurs_var v) tl

let check_occurs_concl v = function
  | Pred(p, tl) -> List.exists (occurs_var v) tl

let check_occurs_rule p0 v (hyp, concl, hist, constra) =
  List.exists (check_occurs_fact p0 v) hyp ||
  (check_occurs_concl v concl) ||
  exists_constraints (occurs_var v) constra

(* 8.1 Apply the simplification only when x does not occur
   in bad positions. No loss of precision in this case *)

let rec elem_simplif next_stage repeat_next_stage ((hyp, concl, hist, constra) as r) =
  let rec find_optim seen_vars = function
      [] -> next_stage r
    | (f::l) ->
        match f with
          Pred(p,[t1;Var v]) when p.p_prop land Param.pred_ELEM != 0
              && not (List.memq v seen_vars) ->
                if check_occurs_rule p v r then
                  find_optim (v::seen_vars) l
                else
                  repeat_next_stage (transform_rule v r)
        | _ -> find_optim seen_vars l
  in
  find_optim [] hyp

(* 8.2 When the conclusion is selected, apply the simplification
   event at the cost of a loss of precision
   Disabled in sound mode. *)

let rec elem_simplif2 next_stage repeat_next_stage ((hyp, concl, hist, constra) as r) =
  let rec find_optim = function
      [] -> next_stage r
    | (f::l) ->
        match f with
          Pred(p,[t1;Var v]) when (p.p_prop land Param.pred_ELEM != 0)
            && (collect_preds v hyp <> []) ->
            if Selfun.selection_fun r = -1 then
              let r' = transform_rule v r in
              print_string "Warning: simplifying ";
              Display.Text.display_rule_indep r;
              print_string "into ";
              Display.Text.display_rule_indep r';
              print_string "with loss of precision.\n";
              repeat_next_stage r'
            else
              next_stage r
        | _ -> find_optim l
  in
  if !sound_mode then
    next_stage r
  else
    find_optim hyp

(* 9. Eliminate redundant hypotheses
   When R = H /\ H' -> C, and there exists \sigma such that
   \sigma H \subseteq H' and \sigma does not modify variables
   of H' and C, then R can be replaced with R' = H' -> C.
   This is a generalization of elimination of duplicate hypotheses.
   The function below does not really remove redundant hypotheses,
   but transforms them into duplicate hypotheses, so that
   they will be removed by the elimination of duplicate hypotheses.
   (In particular, in the history, they are coded as duplicate hypotheses.)

   Redundant hypotheses appear in particular when there are
   begin facts. They can slow down the subsumption test
   considerably.

   Note: it is important that elim_redundant_hyp comes as last
   simplification. In particular, it should come after elimination
   of attacker(x) (so that we don't have many hypotheses attacker(x)
   remaining, which can be mapped to any hypothesis attacker(..) in
   the instantiated clause) and after simplification of inequalities
   (so that we don't have inequalities with variables not
   used elsewhere, which cause problems for the subsumption test).
 *)

let rec is_marked_term = function
  | Var { link = VLink _ ; _ } -> true
  | Var _ -> false
  | FunApp(_,args) -> List.for_all is_marked_term args

let is_marked_fact = function
  | Pred(_,args) -> List.for_all is_marked_term args

let rec mark_variables = function
  | Var v ->
      begin match v.link with
        | TLink _ -> raise NoMatch
        | VLink _ -> ()
        | NoLink -> link v (VLink v)
        | _ -> Parsing_helper.internal_error "[rules.ml >> mark_variables] Unexpected links"
      end
  | FunApp(f,args) -> List.iter mark_variables args

let mark_variables_fact = function
  | Pred(_,args) -> List.iter mark_variables args

let rec match_redundant_terms apply_mark t1 t2 = match t1, t2 with
  | Var v, Var v' when v == v' -> if apply_mark then mark_variables t2
  | Var v, _ ->
      begin match v.link with
        | NoLink ->
            if v.unfailing
            then
              begin
                link v (TLink t2);
                if apply_mark then mark_variables t2
              end
            else
              begin match t2 with
                | Var v' when v'.unfailing -> raise NoMatch
                | FunApp(f_symb,_) when f_symb.f_cat = Failure -> raise NoMatch
                | _ ->
                    link v (TLink t2);
                    if apply_mark then mark_variables t2
              end
        | TLink t' ->
            (* Variables of [t'] have already been marked. *)
            if not (equal_terms t' t2)
            then raise NoMatch
        | VLink _ ->
            (* Since the variable has been marked, it can't be used in the substitution.
               The only possible case is when t1 = t2 which is already covered. *)
            raise NoMatch
        | _ -> Parsing_helper.internal_error "[rules.ml >> mark_variables] Unexpected links"
      end
  | FunApp (f1,args1), FunApp (f2,args2) ->
      if f1 != f2 then raise NoMatch;
      List.iter2 (match_redundant_terms apply_mark) args1 args2
  | _,_ -> raise NoMatch

let match_redundant_facts apply_mark f1 f2 = match f1, f2 with
  | Pred(p1,t1), Pred(p2,t2) ->
      if p1 != p2 then raise NoMatch;
      List.iter2 (match_redundant_terms apply_mark) t1 t2

(* 9.a For non ordered clauses *)

let rec match_redundant_fact_with_kept_facts restwork fact1 = function
  | [] -> raise NoMatch
  | fact2 :: q2 ->
      try
        Terms.auto_cleanup (fun () ->
          match_redundant_facts false fact1 fact2;
          restwork ()
        )
      with NoMatch ->
        match_redundant_fact_with_kept_facts restwork fact1 q2

let rec match_redundant_fact_with_hyp restwork fact1 passed_hyp = function
  | [] -> raise NoMatch
  | fact2 :: q2 ->
      try
        Terms.auto_cleanup (fun () ->
          match_redundant_facts true fact1 fact2;

          (* At that point, we need to keep fact2 *)
          restwork fact2 (List.rev_append passed_hyp q2)
        )
      with NoMatch ->
        match_redundant_fact_with_hyp restwork fact1 (fact2::passed_hyp) q2

let rec match_redundant_hyp restwork kept_hyp = function
  | [] -> restwork ()
  | fact :: q ->
      (* We first test if fact only contain marked variables *)
      if is_marked_fact fact
      then match_redundant_hyp restwork (fact::kept_hyp) q
      else
        try
          (* We first try by matching fact and kept_hyp *)
          match_redundant_fact_with_kept_facts (fun () ->
            match_redundant_hyp restwork kept_hyp q
          ) fact kept_hyp
        with NoMatch ->
          (* Since we did not find a match with kept facts,
             we try with the rest of the facts. *)
          try
            match_redundant_fact_with_hyp (fun fact' passed_hyp ->
              match_redundant_hyp restwork (fact'::kept_hyp) passed_hyp
            ) fact [] q
          with NoMatch ->
            (* No match was found hence [fact] must be kept and we mark it. *)
            mark_variables_fact fact;
            match_redundant_hyp restwork (fact::kept_hyp) q

let elim_redundant_hyp next_stage repeat_next_stage ((hyp,concl,hist,constra) as r) =
  if (!Param.redundant_hyp_elim) &&
    ((not (!Param.redundant_hyp_elim_begin_only)) ||
     (List.exists (function
         Pred({p_info = [TestUnifP _]}, _) -> false
       | Pred(p,_) -> p.p_prop land Param.pred_BLOCKING != 0
      ) hyp))
  then
    try
      Terms.auto_cleanup (fun () ->
        (* We first gather the variables of the clause *)
        let vars = ref [] in
        Terms.get_vars_fact vars concl;
        List.iter (Terms.get_vars_fact vars) hyp;

        (* We mark the variables of the conclusion *)
        mark_variables_fact concl;

        (* We look for a matching *)
        match_redundant_hyp (fun () ->
          (* We check wether some match was found *)
          let success = List.exists (fun v -> match v.link with TLink _ -> true | _ -> false) !vars in

          if success
          then
            begin
              (* It remains to check the disequalities and inequalities *)

              (* We first save the links and remove the VLink *)
              let saved_links =
                List.map (fun v ->
                  let v_link = v.link in
                  begin match v_link with
                    | VLink _ -> v.link <- NoLink
                    | _ -> ()
                  end;
                  (v,v_link)
                ) !vars
              in

              (* We first copy the constraints without renaming variables. *)
              let constra_inst = copy_constra3 constra in

              (* We now remove the all the links *)
              List.iter (fun v -> v.link <- NoLink) !vars;

              (* We compare *)
              try
                (* We check the implication of constraints. *)
                TermsEq.implies_constraints_keepvars (concl::hyp) constra constra_inst;

                (* We found a proper matching so we restore the TLink, copy the rule and run next_stage *)
                List.iter (function (v,TLink t) -> v.link <- TLink t | (v,_) -> v.link <- NoLink) saved_links;

                let rule' = copy_rule2 (hyp,concl,hist,constra_inst) in

                Terms.auto_cleanup (fun () -> repeat_next_stage rule');

                List.iter (fun (v,link) -> v.link <- link) saved_links;
              with NoMatch ->
                (* Restore link and raise Nomatch *)
                List.iter (fun (v,link) -> v.link <- link) saved_links;
                raise NoMatch
            end
          else raise NoMatch
        ) [] (reorder hyp)
      )
    with NoMatch -> next_stage r
  else next_stage r

(* 9.b For ordered clauses *)

let match_redundant_facts_ordered apply_mark (fact1, (ord1,_)) (fact2, (ord2,_)) =
  match_redundant_facts apply_mark fact1 fact2;
  if not (Terms.equal_facts fact1 fact2)
  then implies_ordering_function ord1 ord2

let rec match_redundant_fact_with_kept_facts_ordered restwork fact1 = function
  | [] -> raise NoMatch
  | fact2 :: q2 ->
      try
        Terms.auto_cleanup (fun () ->
          match_redundant_facts_ordered false fact1 fact2;
          restwork ()
        )
      with NoMatch ->
        match_redundant_fact_with_kept_facts_ordered restwork fact1 q2

let rec match_redundant_fact_with_hyp_ordered restwork fact1 passed_hyp = function
  | [] -> raise NoMatch
  | fact2 :: q2 ->
      try
        Terms.auto_cleanup (fun () ->
          match_redundant_facts_ordered true fact1 fact2;
          (* At that point, we need to keep fact2 *)
          restwork fact2 (List.rev_append passed_hyp q2)
        )
      with NoMatch ->
        match_redundant_fact_with_hyp_ordered restwork fact1 (fact2::passed_hyp) q2

let rec match_redundant_hyp_ordered restwork kept_hyp = function
  | [] -> restwork ()
  | ((fact,_) as o_fact) :: q ->
      (* We first test if fact only contain marked variables *)
      if is_marked_fact fact
      then match_redundant_hyp_ordered restwork (o_fact::kept_hyp) q
      else
        try
          (* We first try by matching fact and kept_hyp *)
          match_redundant_fact_with_kept_facts_ordered (fun () ->
            match_redundant_hyp_ordered restwork kept_hyp q
          ) o_fact kept_hyp
        with NoMatch ->
          (* Since we did not find a match with kept facts,
             we try with the rest of the facts. *)
          try
            match_redundant_fact_with_hyp_ordered (fun o_fact' passed_hyp ->
              match_redundant_hyp_ordered restwork (o_fact'::kept_hyp) passed_hyp
            ) o_fact [] q
          with NoMatch ->
            (* No match was found hence [fact] must be kept and we mark it. *)
            mark_variables_fact fact;
            match_redundant_hyp_ordered restwork (o_fact::kept_hyp) q

let elim_redundant_hyp_ordered next_stage repeat_next_stage ahist_op ((hyp, concl, hist, constra) as rule) =
  match ahist_op with
  | None -> elim_redundant_hyp next_stage repeat_next_stage rule
  | Some ana_hist ->
      if (!Param.redundant_hyp_elim) &&
       ((not (!Param.redundant_hyp_elim_begin_only)) ||
        (List.exists (function
            Pred({p_info = [TestUnifP _]}, _) -> false
          | Pred(p,_) -> p.p_prop land Param.pred_BLOCKING != 0
         ) hyp))
      then
        try
          Terms.auto_cleanup (fun () ->
            (* We first gather the variables of the clause *)
            let vars = ref [] in
            Terms.get_vars_fact vars concl;
            List.iter (Terms.get_vars_fact vars) hyp;

            (* We mark the variables of the conclusion *)
            mark_variables_fact concl;

            let ord_hyp = List.combine hyp ana_hist.a_order_data in

            (* We look for a matching *)
            match_redundant_hyp_ordered (fun () ->
              (* We check wether some match was found *)
              let success = List.exists (fun v -> match v.link with TLink _ -> true | _ -> false) !vars in

              if success
              then
                begin
                  (* It remains to check the disequalities and inequalities *)

                  (* We first save the links and remove the VLink *)
                  let saved_links =
                    List.map (fun v ->
                      let v_link = v.link in
                      begin match v_link with
                        | VLink _ -> v.link <- NoLink
                        | _ -> ()
                      end;
                      (v,v_link)
                    ) !vars
                  in

                  (* We first copy the constraints without renaming variables. *)
                  let constra_inst = copy_constra3 constra in

                  (* We now remove the all the links *)
                  List.iter (fun v -> v.link <- NoLink) !vars;

                  (* We compare *)
                  try
                    (* We check the implication of constraints. *)
                    TermsEq.implies_constraints_keepvars (concl::hyp) constra constra_inst;

                    (* We found a proper matching so we restore the TLink, copy the rule and run next_stage *)
                    List.iter (function (v,TLink t) -> v.link <- TLink t | (v,_) -> v.link <- NoLink) saved_links;

                    let rule' = copy_rule2 (hyp,concl,hist,constra_inst) in

                    Terms.auto_cleanup (fun () -> repeat_next_stage rule');

                    List.iter (fun (v,link) -> v.link <- link) saved_links;
                  with NoMatch ->
                    (* Restore link and raise Nomatch *)
                    List.iter (fun (v,link) -> v.link <- link) saved_links;
                    raise NoMatch
                end
              else raise NoMatch
            ) [] (reorder_ordered ord_hyp)
          )
        with NoMatch -> next_stage rule
      else next_stage rule

(* 10. Simplification using the equational theory *)

let simp_eq_rule next_stage repeat_next_stage ((hyp, concl, hist, constra) as rule) =
  if TermsEq.hasEquations() then
    try
      let redo_all_optim = ref false in
      let simp_eq_fact = function
          Pred(p,l) when p.p_prop land Param.pred_SIMPEQ != 0 ->
            Pred(p, List.map (fun t ->
              let t' = TermsEq.simp_eq t in
              if not (Terms.equal_terms t t') then redo_all_optim := true;
              t') l)
        | f -> f
      in
      let rule' = (List.map simp_eq_fact hyp, simp_eq_fact concl, hist, constra) in
      if !redo_all_optim then
        repeat_next_stage rule'
      else
        next_stage rule'
    with TermsEq.Reduces ->
      () (* Remove the clause when Param.simpeq_remove is true and an argument
            of attacker2 reduces. *)
  else
    next_stage rule

(* 11. Simplification using lemmas

We apply lemmas when
1/ they instantiate or remove the clause (does not hurt)
2/ they use the selected hypothesis (this hypothesis will disappear
by resolution, so we have to apply the lemma now, otherwise it will be too late)
3/ no hypothesis is selected (this is a clause at the end of saturation.
Applying the lemma may make it more precise).

These conditions are combined with conditions given by the user
(apply lemmas only when remove the clause; apply lemmas
only when they instantiate or remove the clause).
*)

let is_standard_clause (_,_,hist,_) =
  match hist with
  | Rule(_,tag,_,_,_) ->
      begin
	match tag with
	| PhaseChange (* phase clause *)
	| Rl _ (* listening clause *)
	| Apply({ f_cat = Tuple }, _) (* data constructor clause *) -> true
	| Apply({ f_name = Fixed s }, _) -> is_name_proj 0 s (* projection clause *)
	| _ -> false
      end
  | _ -> false

(* Main application of lemmas *)

let get_option_lemma in_solving lem =
  if in_solving
  then lem.l_verif_app
  else lem.l_sat_app

let rec extract_selected_fact index = function
  | [] -> Parsing_helper.internal_error "[rules.ml >> extract_selected_fact] Index should corresponds to an element of the list of facts."
  | f::q when index = 0 -> f, q
  | f::q ->
      let (f_sel,hyp) = extract_selected_fact (index-1) q in
      (f_sel,f::hyp)

let inj_event_to_event = function
  | Pred(p,[t;_]) when p == Param.begin_pred_inj -> Pred(Param.begin_pred,[t])
  | pred -> pred

let to_begin_non_inj_event = function
  | Pred(p,[_;t]) when p == Param.end_pred_inj -> Pred(Param.begin_pred,[t])
  | Pred(p,args) when p == Param.end_pred -> Pred(Param.begin_pred,args)
  | Pred(p,args) when p == Param.end2_pred -> Pred(Param.begin2_pred,args)
  | fact -> fact

let is_not_bad = function
  | Pred(p,_) when p == Param.bad_pred -> false
  | _ -> true

let are_facts_syntactically_unifiable fact1 fact2 =
  try
    Terms.auto_cleanup (fun () ->
      Terms.unify_facts fact1 fact2;
      true
    )
  with Unify -> false

let are_ordering_fun_n_strict n (order_fun_list:ordering_function list) =

  if List.for_all (List.exists (function (_,Less) -> true | _ -> false)) order_fun_list
  then true
  else
    let nb_order_fun = List.length order_fun_list in
    if nb_order_fun > n
    then false
    else if nb_order_fun < n
    then
      (* We check that each matched hypothesis are pairwise less or equal to one of a premise of the query. *)
      let rec all_distinct accu = function
        | [] -> true
        | ord_fun::q -> all_distinct_one accu q ord_fun

      and all_distinct_one accu rest = function
        | [] -> false
        | (n,_)::q ->
            if List.mem n accu
            then all_distinct_one accu rest q
            else
              if all_distinct (n::accu) rest
              then true
              else all_distinct_one accu rest q
      in

      all_distinct [] order_fun_list
    else
      (* We check that each matched hypothesis are pairwise less or equal to one of a premise of the query and at least one is strictly less. *)
      let rec all_distinct one_less accu = function
        | [] -> one_less
        | ord_fun::q -> all_distinct_one one_less accu q ord_fun

      and all_distinct_one one_less accu rest = function
        | [] -> false
        | (n,order)::q ->
            if List.mem n accu
            then all_distinct_one one_less accu rest q
            else
              if all_distinct (one_less || order = Less) (n::accu) rest
              then true
              else all_distinct_one one_less accu rest q
      in
      all_distinct false [] order_fun_list

let verify_application_condition last_analysed_hist nb_fact_concl matched_facts ((_,concl,_,_) as rule) induction in_solving =
  if in_solving
  then
    if induction
    then
      (* We need to check that the ordering function are n-strict. *)
      let last_analysed_hist' = analyse_history last_analysed_hist rule in
      let order_data = get_order_data_from_analyed_history_op last_analysed_hist' in
      let order_funs =
        List.map (fun (i,_) ->
          if i < 0
          then [-i,Leq]
          else fst (List.nth order_data i)
        ) matched_facts
      in
      (are_ordering_fun_n_strict nb_fact_concl order_funs,last_analysed_hist')
    else
      (* No additional condition to verify *)
      (true,last_analysed_hist)
  else
    (* During the saturation procedure *)
    if induction
    then
      (* No additional condition. We assume here that the matching did not use
         the conclusion: Should be guaranteed by [match_and_apply_lemma] *)
      (true,last_analysed_hist)
    else
      (* We need to check that if the conclusion of the clause was used then all
         events in conclusion of the lemma are not unifiable with the conclusion
         of the clause *)
      match concl with
        | Pred(p,args) when p == Param.end_pred || p == Param.end2_pred || p == Param.end_pred_inj ->
            if List.exists (fun (i,_) -> i = -1) matched_facts
            then
              let concl_with_begin = to_begin_non_inj_event concl in
              let exists_unif =
                List.exists (fun (_,fact) ->
                  are_facts_syntactically_unifiable fact concl_with_begin
                ) matched_facts
              in
              (not exists_unif,last_analysed_hist)
            else (true,last_analysed_hist)
        | _ ->
            (* Facts in the conclusion of a lemma are events *)
            (true,last_analysed_hist)

let match_and_apply_lemma next_stage_no_match next_stage_match last_analyzed_hist ((hyp,concl,hist,constra) as rule) sel_index induction in_verification lemma =
  if !current_bound_vars <> []
  then Parsing_helper.internal_error "[rules.ml >> match_lemma] No variables should be linked.";

  let app_op = get_option_lemma in_verification lemma in

  let premise_lem1, l_conclusion1 =
    Terms.auto_cleanup (fun () ->
      let conclusion1 =
        List.map (fun (hyp_lem,constra_lem, eqs_lem) ->
          (List.map Terms.copy_fact hyp_lem,Terms.copy_constra constra_lem, List.map (fun (t1,t2) -> Terms.copy_term t1, Terms.copy_term t2) eqs_lem)
        ) lemma.l_conclusion
      in
      (List.map Terms.copy_fact lemma.l_premise, conclusion1)
    )
  in

  let hyp_index = List.mapi (fun i f -> (i,Reduction_helper.begin_of_end_event_fact f)) hyp in
  let (nb_fact_concl,fact_added_from_concl) =
    if in_verification
    then
      let fact_concl = Terms.fact_list_of_conclusion concl in
      let m_hist, nb =
        List.fold_left (fun (hist,n) f -> match f with
          | Pred({ p_info = [Attacker _]; _},_)
          | Pred({ p_info = [Mess _]; _},_)
          | Pred({ p_info = [Table _]; _},_)
          | Pred({ p_info = [AttackerBin _]; _},_)
          | Pred({ p_info = [MessBin _]; _},_)
          | Pred({ p_info = [TableBin _]; _},_) -> ((n,f)::hist), n-1
          | Pred(p,[ev]) when p == Param.end_pred -> ((n,Pred(Param.begin_pred,[ev]))::hist), n-1
          | Pred(p,[ev1;ev2]) when p == Param.end2_pred -> ((n,Pred(Param.begin2_pred,[ev1;ev2]))::hist), n-1
          | Pred(p,[occ;ev]) when p == Param.end_pred_inj -> ((n,Pred(Param.begin_pred_inj,[ev;occ]))::hist), n-1
          | _ -> hist, n-1
        ) ([],-1) fact_concl
      in
      (-nb - 1),m_hist
    else
      if induction then
        0, []
      else
        1, [(-1,to_begin_non_inj_event concl)]
  in

  (* [check_substitution [] variables] returns [true] when the substitution
     defined by links in [variables] only instantiates variables in [exist_vars],
     that is, existential variables of the lemma that we are applying.
     In that case, the lemma is not considered to instantiate the clause. *)
  let exists_vars =
    let vars = ref [] in
    List.iter (Terms.get_vars_fact vars) premise_lem1;
    let vars_conclu = ref [] in
    List.iter (fun (fact_lem, constra_lem,eqs_lem) ->
      List.iter (fun (t1,t2) -> Terms.get_vars vars_conclu t1; Terms.get_vars vars_conclu t2) eqs_lem;
      iter_constraints (Terms.get_vars vars_conclu) constra_lem;
      List.iter (Terms.get_vars_fact vars_conclu) fact_lem;
    ) l_conclusion1;
    List.filter (fun v -> not (List.memq v !vars)) !vars_conclu
  in
  let rec check_substitution prev_subst = function
    | [] -> true
    | v::q when List.memq v exists_vars -> check_substitution prev_subst q
    | v::q ->
        match v.link with
          | TLink (Var v') ->
              if List.memq v' exists_vars && not (List.memq v' prev_subst)
              then check_substitution (v'::prev_subst) q
              else false
          | TLink t -> false
          | _ -> Parsing_helper.internal_error "Error Variables."
  in
  let instantiates_only_existential_vars vars =
    (vars == []) || (check_substitution [] vars)
  in

  (* The content of [last_analyzed_hist] is typically the order information
    of either the rule [rule], meaning that it was previously computed by
    previous application of [match_and_apply_lemma] or of one of the "ancestor"
    rule of [rule], i.e. a rule which after some normalisation steps produced [rule].

    If [verify_induction_condition] is applied in the function [match_all] below,
    [last_ordered_rule'] corresponds necessarily to [rule] thus we update
    [last_ordered_rule_ref]. This allows us to minimizing the analysis of a rule's
    history to produce the order information.
  *)
  let last_analyzed_hist_ref = ref last_analyzed_hist in

  (* Add specific application when l_sat_app = LAOnlyWhenRemove. *)
  (* Raise NoMatch when the conditions for applying the lemme are not satisfied. *)
  let apply_lemma_if_options_allow selected match_hyp =
    let accu_rule = ref [] in

    let generate_new_rule fact_lem constra_lem eqs_lem =
      let (fact_lem1,constra_lem1,hyp1,concl1,constra1) =
        Terms.auto_cleanup (fun () ->
          List.map Terms.copy_fact2 fact_lem,
          Terms.copy_constra2 constra_lem,
          List.map Terms.copy_fact2 hyp,
          Terms.copy_fact2 concl,
          Terms.copy_constra2 constra
        )
      in

      let hyp2 = hyp1 @ fact_lem1
      and hist2 = HLemma(lemma.l_index,match_hyp,(fact_lem,constra_lem,eqs_lem),hist)
      and constra2 = Terms.wedge_constraints constra1 constra_lem1 in

      TermsEq.simplify_constraints_rule (fun rule ->
        (* We are adding a clause, so we cannot apply the lemma when
           lemma.l_sat_app = LAOnlyWhenRemove *)
        if app_op = LAOnlyWhenRemove then raise NoMatch;
        accu_rule := rule :: !accu_rule
      ) (fun rule  ->
        (* We are adding a clause, so we cannot apply the lemma when
           lemma.l_sat_app = LAOnlyWhenRemove *)

        if app_op = LAOnlyWhenRemove then raise NoMatch;
        accu_rule := rule :: !accu_rule
      ) (hyp2,concl1,hist2,constra2)
    in

    if (not selected && sel_index <> -1 && not (app_op = LAOnlyWhenRemove) && is_not_bad concl) || app_op = LAOnlyWhenInstantiate
    then
      begin
        (* The only possible application case is when variables are instantiated *)
        List.iter (fun (fact_lem, constra_lem,eqs_lem) ->
          try
            Terms.auto_cleanup (fun () ->
              List.iter (fun (t1,t2) -> Terms.unify t1 t2) eqs_lem;

              if instantiates_only_existential_vars (!current_bound_vars)
              then
                begin
                  TermsEq.check_constraints constra_lem;
                  raise NoMatch
                end
              else generate_new_rule fact_lem constra_lem eqs_lem
            )
          with Unify | TermsEq.FalseConstraint -> ()
        ) l_conclusion1
      end
    else
      begin
        (* Check that the application of the lemma is not identity for this rule *)
        List.iter (fun (fact_lem, constra_lem,eqs_lem) ->
          try
            Terms.auto_cleanup (fun () ->
              List.iter (fun (t1,t2) -> Terms.unify t1 t2) eqs_lem;

              if instantiates_only_existential_vars (!current_bound_vars)
              then
                begin
                  (* Check if all facts are included. Since the unification did not unify anything, all linked variables comes from matching. *)
                  let is_implied =
                    if exists_vars = []
                    then
                      ((* facts implied *)
                        last_analyzed_hist_ref := analyse_history !last_analyzed_hist_ref rule;
                        match !last_analyzed_hist_ref with
                          | None ->
                              List.for_all (fun fact ->
                                let fact1 = Terms.copy_fact4 fact in
                                List.exists (Terms.equal_facts fact1) hyp
                              ) fact_lem
                          | Some ana_hist ->
                              let ord_fun_lem = generate_ordering_fun_from_lemma ana_hist.a_order_data match_hyp in
                              List.for_all (fun fact ->
                                let fact1 = Terms.copy_fact4 fact in
                                List.exists2 (fun fact_hyp (ord_fun_hyp,_) ->
                                  Terms.equal_facts fact1 fact_hyp && implies_ordering_function_bool ord_fun_lem ord_fun_hyp
                                ) hyp ana_hist.a_order_data
                              ) fact_lem
                      )
                      &&
                      ((* constraints implied *)
                       try
                         (* Check that implies_constra_list does not link new variables *)
                         TermsEq.implies_constraints_keepvars4 (concl::hyp) constra constra_lem;
                         true
                       with NoMatch -> false)
                    else
                      Terms.auto_cleanup (fun () ->
                        (* Due to the presence of existential variables, we need to check that the conclusion
                           of the lemma is not redundant with the hypotheses of the clause.

                           Since the condition [instantiates_only_existential_vars (!current_bound_vars)] holds,
                           we know that no variables of the clause have been instantiated and only existential variable may
                           have been instantiated with TLinks.
                        *)

                        try
                          last_analyzed_hist_ref := analyse_history !last_analyzed_hist_ref rule;
                          match !last_analyzed_hist_ref with
                            | None ->
                                match_hyp_implies (fun () ->
                                  TermsEq.implies_constraints_keepvars4 (concl::hyp) constra constra_lem;
                                  true
                                ) (reorder fact_lem) hyp
                            | Some ana_hist ->
                                let ord_fun_lem = generate_ordering_fun_from_lemma ana_hist.a_order_data match_hyp in
                                let ord_fact_lem = List.map (fun f -> (f,(ord_fun_lem,false))) fact_lem in
                                let ord_hyp = List.map2 (fun f ord_data -> (f,ord_data)) hyp ana_hist.a_order_data in
                                match_hyp_ordered_implies (fun () ->
                                  TermsEq.implies_constraints_keepvars4 (concl::hyp) constra constra_lem;
                                  true
                                ) (reorder_ordered ord_fact_lem) ord_hyp
                        with NoMatch -> false
                      )
                  in

                  if is_implied
                  then raise NoMatch
                  else generate_new_rule fact_lem constra_lem eqs_lem
                end
              else generate_new_rule fact_lem constra_lem eqs_lem
            )
          with Unify -> ()
        ) l_conclusion1
      end;

    (* Now the new rules are accumulated in accu_rule, apply the next functions *)
    Terms.auto_cleanup (fun () ->
      List.iter (fun r -> next_stage_match !last_analyzed_hist_ref r) !accu_rule
    )
  in

  let rec match_all selected (matched_hyp:(int*fact) list) fl_hyp = function
    | [] ->
        let (lemma_applicable, last_analyzed_hist') = verify_application_condition !last_analyzed_hist_ref nb_fact_concl matched_hyp rule induction in_verification in
        last_analyzed_hist_ref := last_analyzed_hist';
        if lemma_applicable
        then apply_lemma_if_options_allow selected matched_hyp
        else raise NoMatch
    | fact_lem::q_lem -> match_one selected matched_hyp fact_lem q_lem [] fl_hyp

  and match_one selected (matched_hyp:(int*fact) list) fact_lem q_lem prev_hyp = function
    | [] -> raise NoMatch
    | (i_hyp,fact_hyp)::q_hyp ->
        try
          Terms.auto_cleanup (fun () ->
            match_facts_phase_geq fact_lem (inj_event_to_event fact_hyp);
            match_all selected ((i_hyp,fact_lem)::matched_hyp) (prev_hyp @ q_hyp) q_lem
          )
        with NoMatch ->
          match_one selected matched_hyp fact_lem q_lem ((i_hyp,fact_hyp)::prev_hyp) q_hyp
  in

  let rec match_selected fl_hyp fact_sel prev_lem = function
    | [] -> (* No match found for the selected fact *)
        match_all false [] fl_hyp prev_lem
    | fact_lem::q_lem ->
        try
          Terms.auto_cleanup (fun () ->
            match_facts_phase_geq fact_lem (inj_event_to_event fact_sel);
            match_all true [sel_index,fact_lem] fl_hyp (prev_lem @ q_lem)
          )
        with NoMatch ->
          match_selected fl_hyp fact_sel (fact_lem::prev_lem) q_lem
  in

  try
    if sel_index = -1
    then match_all false [] (fact_added_from_concl @ hyp_index) premise_lem1
    else
      let ((_,f_sel),hyp_rest) = extract_selected_fact sel_index hyp_index in
      match_selected (fact_added_from_concl @ hyp_rest) f_sel [] premise_lem1
  with NoMatch -> next_stage_no_match !last_analyzed_hist_ref

let simplify_lemmas next_stage_no_match next_stage in_solving lemmas inductive_lemmas last_analyzed_hist rule =

  let lemma_applied = ref false in

  let rec match_rule last_analyzed_hist rule =
    assert (!current_bound_vars == []);
    let sel_index = Selfun.selection_fun_nostatechange rule in
    match_and_apply_all last_analyzed_hist rule sel_index (lemmas,inductive_lemmas)

  and match_and_apply_all last_analyzed_hist ((hyp,concl,hist,constra) as rule) sel_index (lemmas,inductive_lemmas) =
    if lemmas = [] && inductive_lemmas = []
    then
      if !lemma_applied
      then next_stage last_analyzed_hist rule
      else next_stage_no_match last_analyzed_hist rule
    else
      let (induction,lemma,rest_lemmas) = match lemmas,inductive_lemmas with
        | lemma :: q_lem, ind_lemmas -> (false,lemma,(q_lem,ind_lemmas))
        | [], lemma :: q_lem -> (true,lemma,([],q_lem))
        | [],[] -> internal_error "[rules.ml >> simplify_lemmas] SHould have been caught before."
      in
      match_and_apply_lemma
        (fun last_analyzed_hist' -> match_and_apply_all last_analyzed_hist' rule sel_index rest_lemmas)
        (fun last_analysed_hist1 rule1 -> lemma_applied := true; match_rule last_analysed_hist1 rule1)
        last_analyzed_hist
        rule
        sel_index
        induction
        in_solving
        lemma
  in

  if (lemmas = [] && inductive_lemmas = []) || (not in_solving (*optimization: when in_solving is true, we never apply lemmas to standard clauses, because we apply lemmas to clauses we generate in the resolution for solving, which have as conclusion a conjunction fact, so we do not test [is_standard_clause] in this case*) && is_standard_clause rule)
  then next_stage_no_match last_analyzed_hist rule
  else match_rule last_analyzed_hist rule

let simplify_lemmas_saturation next_stage_no_match next_stage lemmas inductive_lemmas rule =
  simplify_lemmas (fun _ r -> next_stage_no_match r) (fun _ r -> next_stage r) false lemmas inductive_lemmas None rule

let simplify_lemmas_solving next_stage_no_match next_stage lemmas inductive_lemmas last_analysed_hist rule =
  simplify_lemmas next_stage_no_match next_stage true lemmas inductive_lemmas last_analysed_hist rule

(* 12. Simplification on natural numbers. *)

let detect_zero = function
  | ([],Pred({ p_info = [Attacker _]; _},[FunApp(f,[])]),_,{ neq = []; is_nat = []; is_not_nat = []; geq = []}) ->
      f == Terms.zero_cst
  | _ -> false

let detect_zero2 = function
  | ([],Pred({ p_info = [AttackerBin _]; _},[FunApp(f1,[]);FunApp(f2,[])]),_,{ neq = []; is_nat = []; is_not_nat = []; geq = []}) ->
      f1 == Terms.zero_cst &&
      f2 == Terms.zero_cst
  | _ -> false

let detect_plus = function
  | ([Pred(p1,[Var v1])], Pred(p2,[FunApp(f,[Var v2])]), _, { neq = []; is_nat = []; is_not_nat = []; geq = []}) ->
      p1.p_prop land Param.pred_ATTACKER != 0 &&
      p2.p_prop land Param.pred_ATTACKER != 0 &&
      f == Terms.succ_fun &&
      v1 == v2
  | _ -> false

let detect_plus2 = function
  | ([Pred({p_info = [AttackerBin _]; _},[Var v1;Var v2])], Pred({p_info = [AttackerBin _]; _},[FunApp(f1,[Var v3]);FunApp(f2,[Var v4])]), _, { neq = []; is_nat = []; is_not_nat = []; geq = []}) ->
      f1 == Terms.succ_fun &&
      f2 == Terms.succ_fun &&
      v1 == v3 &&
      v2 == v4
  | _ -> false

let rec may_be_nat_number = function
  | Var v -> true
  | FunApp(f,[t]) when f == Terms.succ_fun -> may_be_nat_number t
  | _ -> false

let simplify_natural_number next_stage ((_,concl,_,constra) as rule) = match concl with
  | Pred({p_info = [Attacker _]},[t]) when may_be_nat_number t ->
      if detect_zero rule || detect_plus rule
      then next_stage rule
      else
        begin
          try
            let constra' = Terms.constraints_of_is_nat t in
            TermsEq.implies_constraints_keepvars [concl] constra constra'
          with NoMatch -> next_stage rule
        end
  | Pred({p_info = [AttackerBin _]},[t1;t2]) when may_be_nat_number t1 && Terms.equal_terms t1 t2 ->
      if detect_zero2 rule || detect_plus2 rule
      then next_stage rule
      else
        begin
          try
            let constra' = Terms.constraints_of_is_nat t1 in
            TermsEq.implies_constraints_keepvars [concl] constra constra'
          with NoMatch -> next_stage rule
        end
  | _ -> next_stage rule

(* 13. Removal of useless events for lemmas *)

let initialise_useless_events_for_lemmas events_in_queries lemmas =
  events_only_for_lemmas := [];
  all_original_lemmas := [];

  (* We record first the lemmas that are used in either saturation or solving *)
  List.iter (fun lem ->
    if lem.l_sat_app <> LANone || lem.l_verif_app <> LANone
    then all_original_lemmas := lem :: !all_original_lemmas
  ) lemmas;

  List.iter (fun lemma ->
    List.iter (function
      | Pred(p,(FunApp(ev,_)::_)) when p == Param.begin_pred || p == Param.begin2_pred ->
          if not (List.memq ev events_in_queries) && not (List.memq ev !events_only_for_lemmas)
          then events_only_for_lemmas := ev :: !events_only_for_lemmas
      | _ -> ()
    ) lemma.l_premise
  ) !all_original_lemmas

let is_fact_only_for_lemma = function
  | Pred(p,(FunApp(ev,args)::_)) when (p == Param.begin_pred || p == Param.begin2_pred || p == Param.begin_pred_inj) && List.memq ev !events_only_for_lemmas -> true
  | _ -> false

let rec mark_variables_follow = function
  | Var { link = TLink t; _ } -> mark_variables_follow t
  | Var ({ link = NoLink; _ } as v)-> Terms.link v (VLink v)
  | Var _ -> ()
  | FunApp(_,args) -> List.iter mark_variables_follow args

let rec mark_variables_follow_fact = function
  | Pred(_,args) -> List.iter mark_variables_follow args

(* [inter_variables vars t] adds to [vars] to the marked variables in [t] *)
let rec inter_variables vars = function
  | Var { link = TLink t; _} -> inter_variables vars t
  | Var ({ link = VLink _; _ } as v)->
      if not (List.memq v !vars)
      then vars := v :: !vars
  | Var _ -> ()
  | FunApp(_,args) -> List.iter (inter_variables vars) args

let inter_variables_fact vars = function
  | Pred(_,args) -> List.iter (inter_variables vars) args

let rec remove_from_list x = function
  | [] -> []
  | x'::q when x' == x -> q
  | x'::q -> x' :: (remove_from_list x q)

(* [vars_not_in vars t] removes from [vars] the marked variables in [t].
   Raises [NoMatch] in case no variable remains in [vars]. *)
let rec vars_not_in vars = function
  | Var { link = TLink t; _} -> vars_not_in vars t
  | Var ({ link = NoLink; _ } as v)->
      Terms.link v (VLink v);
      vars := remove_from_list v !vars;
      if !vars = []
      then raise NoMatch
  | Var _ -> ()
  | FunApp(_,args) -> List.iter (vars_not_in vars) args

let vars_not_in_fact vars = function
  | Pred(_,args) -> List.iter (vars_not_in vars) args

let vars_not_in_nat vars constra =
  List.iter (vars_not_in vars) constra.is_nat;
  List.iter (fun (x,_,y) ->
    vars_not_in vars x;
    vars_not_in vars y;
  ) constra.geq

let remove_useless_events_for_lemma_main in_saturation lemmas ((hypl,concl,hist,constra) as rule) =
  let check_one_fact_vs_one_fact_lemma fact sel_fact_end_or_inj_event_list begin_ev_fact_list fact_lem fact_lem_list =
    (* We have a clause [fact && sel_fact_end_or_inj_event_list && begin_ev_fact_list && constra => concl]
       and a lemma [fact_lem && fact_lem_list => ... ]
       We try to apply the lemma to a clause obtained by resolution from the clause
       above by unifying [fact] and [fact_lem]. Let [\sigma] be their mgu.
       If [possible_vars] is non-empty at the end of this function, the lemma can
       never be applied in this way on a clause obtained by resolution for the current
       clause, so we remove the event [fact] (since it is also useful only for lemmas).
       However, this transformation is complete in full generality, because the
       current clause can also be transformed by applied other lemmas at some point,
       which may later make an applicationn of a lemma using [fact] possible.

       Proof sketch: Let x be a variable in [possible_vars].
       x occurs in [fact_lem\sigma = fact\sigma]. So there is a variable y
       such that y occurs in [fact] and x occurs in y\sigma.
       x does not occur in [sel_fact_end_or_inj_event_list\sigma], [concl\sigma] and [nat_constra\sigma],
       so y does not occur in [sel_fact_end_or_inj_event_list], [concl], and [nat_constra].
       Hence during resolution from the clause [fact && sel_fact_end_or_inj_event_list && begin_ev_fact_list && constra => concl],
       the variable y will never be instantiated, so the clause obtained by resolution
       is [fact' && H && begin_ev_fact_list' => C] where y occurs in [fact'] (which is an instance of [fact]),
       y does not occur in H,C, and [begin_ev_fact_list'] is an instance of [begin_ev_fact_list].
       When we apply the lemma on this clause, [fact'] must be an instance of [fact_lem],
       so in fact y is left unchanged, i.e. y = x.
       The variable x does not occur in the events of [begin_ev_fact_list\sigma && H, C] that may
       be used to match [fact_lem_list\sigma], so y does not occur in the events of
       [begin_ev_fact_list' && H,C] that may be used to match [fact_lem_list].
       However, y = x occurs in [fact_lem_list\sigma]. The matching is then impossible.
       *)
    Terms.auto_cleanup (fun () ->
      try
        Terms.unify_facts fact fact_lem;

        let possible_vars = ref [] in
        Terms.auto_cleanup (fun () ->
          (* We start by marking the variables of fact_lem\sigma*)
          mark_variables_follow_fact fact_lem;

          (* We retrieve the variables that are also in fact_lem_list\sigma *)
          List.iter (inter_variables_fact possible_vars) fact_lem_list
        );
        if !possible_vars = []
        then false
        else
          begin
            try
              (* We remove from possible_vars the variables that are in the conclusion
                 and the potentially selectable facts, as well as injective events
		 and end events. *)
              Terms.auto_cleanup (fun () ->
                List.iter (vars_not_in_fact possible_vars) (concl::sel_fact_end_or_inj_event_list);
                vars_not_in_nat possible_vars constra;
              );
              (* We remove from possible_vars the variables that are in the begin events
                 that can unify with the other premises of the lemma. Note that the application
		 of the lemma may also use the conclusion as well as end events and injective
		 events in the hypothesis. The variables of those have already been removed above. *)
              List.iter (fun fact_ev ->
                if List.exists (are_facts_syntactically_unifiable fact_ev) fact_lem_list
                then
                  Terms.auto_cleanup (fun () ->
                    vars_not_in_fact possible_vars fact_ev
                  )
              ) begin_ev_fact_list;
              true
            with NoMatch -> false
          end
      with Unify -> true
    )
  in

  let event_may_be_used = (Selfun.selection_fun_nostatechange rule = -1) in

  let check_one_fact_vs_lemma fact fact_list lemma =

    match lemma.l_premise with
      | [fact_lem] ->
          (* When there is only one fact in the premise of the lemma, we check that the lemma was already applied. The test is sound but not complete. *)
          if event_may_be_used && ((in_saturation && lemma.l_sat_app = LAFull) || (not in_saturation && lemma.l_verif_app = LAFull))
          then
            Terms.auto_cleanup (fun () ->
              try
                match_facts_phase_geq fact_lem (inj_event_to_event fact);
                true
              with NoMatch -> false
            )
          else false
      | _ ->
          (* When there is more than one fact in the premise of the lemma, we check that the lemma cannot be applied. The test is also not complete. *)
          let (sel_fact_end_or_inj_events,begin_ev_facts) = List.partition (function Pred(p,_) when p == Param.begin_pred || p == Param.begin2_pred -> false | _ -> true) fact_list in
          let rec go_through_premise fact_lem_list = function
            | [] -> true
            | fact_lem :: q_lem ->
                if check_one_fact_vs_one_fact_lemma fact sel_fact_end_or_inj_events begin_ev_facts fact_lem (List.rev_append fact_lem_list q_lem)
                then go_through_premise (fact_lem::fact_lem_list) q_lem
                else false
          in
          go_through_premise [] lemma.l_premise
  in

  let rec check_facts_in_hypl n rest_hypl hypl hist = match hypl with
    | [] -> ([],hist)
    | fact :: q_fact ->
        let (q_fact',hist') = check_facts_in_hypl (n+1) (fact::rest_hypl) q_fact hist in

        if is_fact_only_for_lemma fact
        then
          let fact' = inj_event_to_event fact in
          let hypl' = rest_hypl@q_fact' in
          if List.for_all (check_one_fact_vs_lemma fact' hypl') lemmas
          then
            (* The fact has been found useless. We use HMaxHyp for history but we should
               probably use a new one for clarity. *)
            (q_fact',HMaxHyp(n,hist'))
          else (fact::q_fact',hist')
        else (fact::q_fact',hist')
  in

  let (hypl',hist') = check_facts_in_hypl 0 [] hypl hist in
  (hypl',concl,hist',constra)

let remove_useless_events_for_lemma in_saturation lemmas rule =
  if !Param.event_lemma_simplification && lemmas <> [] && not (!sound_mode)
  then remove_useless_events_for_lemma_main in_saturation lemmas rule
  else rule


(* Combines the previous simplication functions, then add the
   simplified rule to the rule base *)

let normal_rule database lemmas inductive_lemmas r =

  let rec normal_rule r =
    assert (!Terms.current_bound_vars == []);
    decompose_hyp_tuples2 (
      simp_eq_rule (
        elim_not (
          Weaksecr.simplify (
            Noninterf.simplify (
              decompose_concl_tuples (
                elim_taut (
                  elim_any_x2 (
                    simplify_rule_constra (
                      simplify_natural_number (
                        elem_simplif (
                          elem_simplif2 (
                            elim_redundant_hyp (
                              simplify_lemmas_saturation (
                                Weaksecr.remove_equiv_events (limit_induction normal_rule_add_rule normal_rule)
                              ) normal_rule lemmas inductive_lemmas
                            ) normal_rule
                          ) normal_rule
                        ) normal_rule
                      )
                    ) normal_rule
                  )
                )
              )
            ) normal_rule
          ) normal_rule
        )
      ) normal_rule
    ) r

  (* Note that currently, we apply remove_useless_events_for_lemma on all clauses but we could as an
     alternative only apply it on clauses with the conclusion selected. *)
  and normal_rule_add_rule r = add_rule database (remove_useless_events_for_lemma true !all_original_lemmas (limit_depth_rule r)) in

  normal_rule r

let normal_rule_solving apply_not database lemmas inductive_lemmas ord_rule =

  let all_lemmas = lemmas @ inductive_lemmas in

  let rec normal_rule ana_hist_op rule =
    assert (!Terms.current_bound_vars == []);
    decompose_hyp_tuples2 (
      elim_not_solving  apply_not (
        Weaksecr.simplify (
          elim_any_x2 (
            simplify_rule_constra (
                elem_simplif (
                  elem_simplif2 (fun r' ->
                    let ana_hist_op' = analyse_history ana_hist_op r' in
                    elim_redundant_hyp_ordered (
                      simplify_lemmas_solving normal_rule_add_rule normal_rule lemmas inductive_lemmas ana_hist_op'
                    ) (normal_rule ana_hist_op') ana_hist_op' r'
                  ) (normal_rule ana_hist_op)
                ) (normal_rule ana_hist_op)
            ) (normal_rule ana_hist_op)
          )
        ) (normal_rule ana_hist_op)
      )
    ) rule

  and normal_rule_add_rule ana_hist_op rule =
    let rule' = remove_useless_events_for_lemma false all_lemmas rule in
    let ana_hist_op' = analyse_history ana_hist_op rule' in
    let ord_rule = ordered_rule_of_analysed_history_op ana_hist_op' rule' in
    add_rule_solving database ord_rule

  in

  let ana_hist_op = analysed_history_op_of_ordered_rule ord_rule in
  normal_rule ana_hist_op ord_rule.rule

(* Check whether hypothesis of the clause is unsatifiable *)

exception Satisfiable

let is_hypothesis_unsatisfiable r =
  assert (!Terms.current_bound_vars == []);

  let rec apply_normal_rule r =
    simp_eq_rule (
      simplify_rule_constra (fun _ -> raise Satisfiable) apply_normal_rule
    ) apply_normal_rule r
  in

  try
    apply_normal_rule r;
    true
  with Satisfiable -> false

(* [compos] unifies [concl1] with the selected hypothesis of [hyp2]
   and builds the resulting rule
   There must be no selected fact in [rule1], and a selected fact in [rule2]

   R = F1 & ... & Fn -> F0
   R' = F'1 & ... & F'n' -> F'0
can be composed into
      s F1 & ... & s Fn & s F'2 & ... & s F'n -> s F'0
where s is the most general unifier of F0 and F'1
if
    F'1 selected
and for all Fi, Fi not selected

*)

let compos next_stage (hyp1, concl1, hist1,constra1) ((hyp2, concl2, hist2,constra2), sel_index) =
  let a = List.nth hyp2 sel_index in
  (* compose with the selected fact *)
  assert (!current_bound_vars == []);
  try
    unify_facts concl1 a;
    let hyp' = List.map copy_fact2 (replace_nth_list hyp1 sel_index hyp2) in
    (* Careful ! The order of hypotheses is important for the history *)
    let concl' = copy_fact2 concl2 in
    let hist' = Resolution(hist1, sel_index, hist2) in
    let constra' = wedge_constraints (copy_constra2 constra1) (copy_constra2 constra2) in
    cleanup();
    next_stage (hyp', concl', hist', constra')
  with Unify ->
    cleanup()

let compos_solving next_stage sat_rule (ord_rule,sel_index) =
  compos (fun rule' ->
    let order_data_op = match ord_rule.order_data with
      | None -> None
      | Some ord_data_list ->
          let ord_data = List.nth ord_data_list sel_index in
          let ord_data_list' = replace_nth_list (sat_rule.sat_generate_ordering_data ord_data) sel_index ord_data_list in
          Some ord_data_list'
    in
    let ord_rule' = { rule = rule'; order_data = order_data_op } in
    next_stage ord_rule'
  ) sat_rule.sat_rule (ord_rule.rule,sel_index)

(* Redundancy test
   [rulelist] and [firstrulelist] must be lists of rules with empty selection
   [initrule] must be a rule with empty selection
   The test returns true if and only if the rule [initrule] can be derived
   with a derivation containing a rule in [firstrulelist] as top rule
   and other rules in [rulelist].
*)

let dummy_fact = Pred(Param.dummy_pred, [])

exception Redundant

let redundant rulelist firstrulelist ((_,initconcl,_,_) as initrule) =
  let rec redundant_rec firstrulelist ((hyp, concl, hist, constra) as rule) seen_list =
    if matchafact initconcl concl then
      let sel_index = Selfun.selection_fun (hyp, dummy_fact, hist, constra) in
      if (sel_index != -1) && (not (is_pred_to_prove_fact (List.nth hyp sel_index))) then
        if not (List.exists (fun r -> implies r rule) seen_list) then
          let seen_list = rule :: seen_list in
          List.iter (fun ((hyp1, _, _, _) as rule1) ->
	    (* Consider only clauses with unselectable hypotheses,
	       to help termination of the search for a derivation.
	       (In general, the termination of resolution is not guaranteed.
	       With this condition, assuming unary predicates, the facts usable by resolution
	       are smaller in the hypothesis than in the conclusion, which implies termination.
	       For predicates with several arguments, the situation is more complicated,
	       but termination remains extremely likely.) *)
            if List.for_all is_unselectable hyp1 then
            let check_fun r =
              let r' = elim_any_x (decompose_hyp_tuples r) in
              if implies r' initrule then
                raise Redundant
              else
                redundant_rec rulelist r' seen_list
            in
            compos (simplify_rule_constra check_fun check_fun) rule1 (rule,sel_index)
          ) firstrulelist
  in
  try
    redundant_rec firstrulelist ([initconcl], initconcl, Empty(initconcl), true_constraints) [];
    false
  with Redundant ->
    if !Param.verbose_redundant then
      begin
        print_string "Redundant rule eliminated:\n";
        Display.Text.display_rule_indep initrule
      end;
    true

let redundant_solving sat_rules first_rules ({ rule = (_,target_concl,_, _); _ } as target_rule) =

  let rec redundant_rec ({ rule = (hyp,concl,hist,constra); _ } as ord_rule) seen_list =
    if matchafact target_concl concl
    then
      let sel_index = Selfun.selection_fun (hyp, dummy_fact, hist, constra) in
      if (sel_index != -1) && (not (is_pred_to_prove_fact (List.nth hyp sel_index)))
      then
        if not (List.exists (fun r -> implies_ordered r ord_rule) seen_list)
        then
          let seen_list' = ord_rule :: seen_list in
          List.iter (fun sat_rule ->
	    (* [sat_rule] is filtered before calling [redundant_solving]
	       so that it contains only clauses with unselectable hypotheses.
	       So we do not need to test that here, in contrast with what
	       is done in [redundant] above. *)
            compos_solving (check_ord_rule seen_list') sat_rule (ord_rule,sel_index)
          ) sat_rules

  and check_ord_rule seen_list ord_rule =
    let ana_hist_op = analysed_history_op_of_ordered_rule ord_rule in

    let sub_check rule =
      let rule' = elim_any_x (decompose_hyp_tuples rule) in
      let ana_hist_op' = analyse_history ana_hist_op rule' in
      let ord_rule'' = ordered_rule_of_analysed_history_op ana_hist_op' rule' in
      if implies_ordered ord_rule'' target_rule
      then raise Redundant
      else redundant_rec ord_rule'' seen_list
    in

    simplify_rule_constra sub_check sub_check ord_rule.rule
  in

  try
    List.exists (fun ({ rule = (_, first_concl, _, _); _ } as first_rule) ->
      try
        let init_rule =
          auto_cleanup (fun () ->
            Terms.match_facts first_concl target_concl;
            { first_rule with rule = copy_rule2 first_rule.rule }
          )
        in
        check_ord_rule [] init_rule;
        false
      with NoMatch -> false
    ) first_rules
  with
    | Redundant ->
        if !Param.verbose_redundant then
          begin
            print_string "Redundant rule eliminated:\n";
            Display.Text.display_rule_indep target_rule.rule
          end;
        true

let redundant_glob database initrule =
  match !Param.redundancy_test with
    Param.NoRed -> false
  | Param.SimpleRed ->
      redundant database.base_ns database.base_ns initrule
  | Param.BestRed ->
      if redundant database.base_ns database.base_ns initrule then true else
      let rec all_redundant accu = function
          [] -> accu
        | (a::l) ->
            let rlist = initrule :: (accu @ l) in
            if redundant rlist rlist a then
              all_redundant accu l
            else
              all_redundant (a::accu) l
      in
      database.base_ns <- List.rev (all_redundant [] database.base_ns);
      false

let redundant_glob_solving database sat_rules target_rule =
  match !Param.redundancy_test with
  | Param.NoRed -> false
  | Param.SimpleRed -> redundant_solving sat_rules database.base_ns target_rule
  | Param.BestRed ->
      if redundant_solving sat_rules database.base_ns target_rule
      then true
      else
        begin
          let rec all_redundant accu = function
              [] -> accu
            | (ord_rule::l) ->
                let rlist = target_rule :: (accu @ l) in
                if redundant_solving sat_rules rlist ord_rule
                then all_redundant accu l
                else all_redundant (ord_rule::accu) l
          in
          database.base_ns <- List.rev (all_redundant [] database.base_ns);
          false
        end

(* Saturates the rule base, by repeatedly applying the composition [compos] *)

let previous_size_queue = ref 0

let display_initial_queue_main get_rule database =
  Display.Text.print_line "------------ Initial queue ----------";
  let count = ref 0 in
  Pvqueue.iter database.queue (fun rule ->
    Display.Text.print_string ((string_of_int (!count + 1))^" -- ");
    Display.Text.display_rule_indep rule;
    incr count;
  );
  previous_size_queue := !count;
  Display.Text.print_line "------------------------------------"

let display_base get_rule database =
  let rec display_base_sel n = function
    | [] -> ()
    | (rule,sel)::q ->
        let r = get_rule rule in
        Display.auto_cleanup_display (fun () ->
          let (hyp,_,_,_) = r in
          Display.Text.print_string ((string_of_int n)^" -- (hyp "^(string_of_int sel)^" selected: ");
          Display.Text.display_fact (List.nth hyp sel);
          Display.Text.print_line "):";
          Display.Text.display_rule r
        );
        display_base_sel (n+1) q
  in

  let rec display_base_ns n = function
    | [] -> ()
    | r::q ->
        Display.Text.print_string ((string_of_int n)^" -- ");
        Display.Text.display_rule_indep (get_rule r);
        display_base_ns (n+1) q
  in

  Display.Text.print_line "------------ Resulting base and rules added in queue ----------";
  Display.Text.print_line "****** Rules with the conclusion selected";
  let rev_ns = List.rev database.base_ns in
  let rev_sel = List.rev database.base_sel in
  display_base_ns 1 rev_ns;
  Display.Text.print_line "****** Rules with an hypothesis selected";
  display_base_sel 1 rev_sel;
  Display.Text.print_line "****** Rules added in queue";

  let index_to_display =
    if !previous_size_queue = 0
    then 0
    else !previous_size_queue - 1
  in

  let count = ref 0 in
  Pvqueue.iter database.queue (fun rule ->
    if !count >= index_to_display
    then
      begin
        Display.Text.print_string ((string_of_int (!count-index_to_display + 1))^" -- ");
        Display.Text.display_rule_indep (get_rule rule);
      end;
    incr count;
  );
  previous_size_queue := !count;
  Display.Text.print_line "------------------------------------"

let display_complete_verbose get_rule database (rule,sel_index) =
  (* display the rule *)
  if !Param.verbose_rules || !Param.verbose_base then
   begin
     Display.auto_cleanup_display (fun () ->
       let (hypl,concl,_,_) = get_rule rule in

       if sel_index >= 0
       then
         begin
           Display.Text.newline ();
           Display.Text.print_string ("Rule with hypothesis fact "^(string_of_int sel_index)^" selected: ");
           Display.Text.display_fact (List.nth hypl sel_index);
           Display.Text.newline ();
         end
       else
         begin
           Display.Text.newline ();
           Display.Text.print_line "Rule with conclusion selected:";
         end;

       Display.Text.display_rule (get_rule rule);
       database.count <- database.count + 1;
       print_string ((string_of_int database.count) ^
                     " rules inserted. The rule base contains " ^
                     (string_of_int ((List.length database.base_ns)
                       + (List.length database.base_sel))) ^
                     " rules. " ^
                     (string_of_int (Pvqueue.length database.queue)) ^
                     " rules in the queue.");
       Display.Text.newline();
     );

     if !Param.verbose_base then display_base get_rule database
   end
  else
    begin
      database.count <- database.count + 1;
      if database.count mod 200 = 0 then
        begin
          print_string ((string_of_int database.count) ^
                        " rules inserted. The rule base contains " ^
                        (string_of_int ((List.length database.base_ns)
                                      + (List.length database.base_sel))) ^
                        " rules. " ^
                        (string_of_int (Pvqueue.length database.queue)) ^
                        " rules in the queue.");
          Display.Text.newline()
        end
    end

let complete_rules database lemmas inductive_lemmas =
  let normal_rule = normal_rule database lemmas inductive_lemmas in
  let rec search_fix_point () = match Pvqueue.get database.queue with
    | None -> database.base_ns
    | Some rule ->
        let sel_index = Selfun.selection_fun rule in

        if sel_index == -1
        then
          begin
            if not (redundant_glob database rule)
            then
              begin
              database.base_ns <- rule :: database.base_ns;
              List.iter (compos normal_rule rule) database.base_sel
              end
          end
        else
          begin
            let rule_sel = (rule, sel_index) in
            database.base_sel <- rule_sel :: database.base_sel;
            List.iter (fun rule2 -> compos normal_rule rule2 rule_sel) database.base_ns
          end;

        display_complete_verbose (fun rule -> rule) database (rule,sel_index);
        search_fix_point ()
  in
  search_fix_point ()

let complete_rules_solving ?(apply_not=false) sat_rules database lemmas inductive_lemmas =
  let normal_rule = normal_rule_solving apply_not database lemmas inductive_lemmas in
  let sat_rules_for_redundant_glob =
    if !Param.redundancy_test = Param.NoRed
    then sat_rules
    else List.filter (fun { sat_rule = (hypl,_,_,_); _ } -> List.for_all is_unselectable hypl) sat_rules
  in

  let rec search_fix_point () = match Pvqueue.get database.queue with
    | None -> database.base_ns
    | Some ord_rule ->
        let (sel_index,ord_rule1) =
          let (hyp, _, hist, constra) = ord_rule.rule in
          let sel_index = Selfun.selection_fun (hyp, dummy_fact, hist, constra) in
          if sel_index == -1
          then
            match ord_rule.order_data with
              | None -> sel_index, ord_rule
              | Some order_data ->
                  let (hypl,_,_,_) = ord_rule.rule in
                  let (sel_index', order_data') = Selfun.selection_induction hypl order_data in
                  (sel_index',{ ord_rule with order_data = Some order_data'})
          else sel_index, ord_rule
        in

        if sel_index == -1
        then
          begin
            if not (redundant_glob_solving database sat_rules_for_redundant_glob ord_rule1)
            then database.base_ns <- ord_rule1 :: database.base_ns
          end
        else
          begin
            let rule_sel = (ord_rule1, sel_index) in
            database.base_sel <- rule_sel :: database.base_sel;
            List.iter (fun sat_rule -> compos_solving normal_rule sat_rule rule_sel) sat_rules
          end;

        display_complete_verbose (fun ord_rule -> ord_rule.rule) database (ord_rule1,sel_index);
        search_fix_point ()
  in
  search_fix_point ()

(* Solving request rule *)

let saturated_rules = ref []

let rec generate_initial_ord acc= function
  | 0 -> acc
  | n -> generate_initial_ord ([Leq,n]::acc) (n-1)

let solving_request_rule ?(close_equation=true) ?(apply_not=false) lemmas inductive_lemmas ord_rule =
  assert (!initialized);

  (* We reset the nounif_selection in ord_rule if necessary *)
  let ord_rule1 =
    if Selfun.induction_required ()
    then
      match ord_rule.order_data with
        | None ->
            let (hypl,_,_,_) = ord_rule.rule in
            let order_data = List.map (fun _ -> ([],true)) hypl in
            { ord_rule with order_data = Some order_data }
        | Some order_data ->
            let order_data' = List.map (fun (ord,_) -> (ord,true)) order_data in
            { ord_rule with order_data = Some order_data' }
    else ord_rule
  in

  let database = new_database () in

  let close_eq =
    if close_equation
    then TermsEq.close_rule_hyp_eq
    else (fun restwork r -> restwork r)
  in

  close_eq (fun rule ->
    let ord_rule2 = { ord_rule1 with rule = rule } in
    normal_rule_solving apply_not database lemmas inductive_lemmas ord_rule2
  ) ord_rule1.rule;

  complete_rules_solving ~apply_not:apply_not !saturated_rules database lemmas inductive_lemmas

(* Main functions *)

(* Only used in query_goal and query_goal_not. *)
let query_goal_std lemmas g =
  let ord_rule = { rule = ([g], g, Empty(g),true_constraints); order_data = None } in
  solving_request_rule lemmas [] ord_rule

(* Only used for Horn and typed Horn front-ends *)
let query_goal g =
  match query_goal_std [] g with
    [] ->
      print_string "RESULT goal unreachable: ";
      Display.auto_cleanup_display (fun () -> Display.Text.display_fact g);
      Display.Text.newline();
      if !Param.html_output then
        begin
          Display.Html.print_string "<span class=\"result\">RESULT <span class=\"trueresult\">goal unreachable</span>: ";
          Display.auto_cleanup_display (fun () -> Display.Html.display_fact g);
          Display.Html.print_string "</span>";
          Display.Html.newline();
        end
  | l ->
      List.iter (fun ord_rule ->
        print_string "goal reachable: ";
        Display.Text.display_rule_abbrev ord_rule.rule;
        if !Param.html_output then
          begin
            Display.Html.print_string "goal reachable: ";
            Display.Html.display_rule_abbrev ord_rule.rule
          end;
        begin
          try
            ignore (History.build_history None ord_rule.rule)
          with Not_found -> ()
        end;
        cleanup()
      ) l;
      print_string "RESULT goal reachable: ";
      Display.auto_cleanup_display (fun () -> Display.Text.display_fact g);
      Display.Text.newline();
      if !Param.html_output then
        begin
          Display.Html.print_string "<span class=\"result\">RESULT <span class=\"unknownresult\">goal reachable</span>: ";
          Display.auto_cleanup_display (fun () -> Display.Html.display_fact g);
          Display.Html.print_string "</span>";
          Display.Html.newline();
        end

let query_goal_not lemmas g =
  match query_goal_std lemmas g with
    [] ->
      print_string "ok, secrecy assumption verified: fact unreachable ";
      Display.auto_cleanup_display (fun () -> Display.Text.display_fact g);
      Display.Text.newline();
      if !Param.html_output then
        begin
          Display.Html.print_string "ok, secrecy assumption verified: fact unreachable ";
          Display.auto_cleanup_display (fun () -> Display.Html.display_fact g);
          Display.Html.newline()
        end
  | l ->
      List.iter (fun ord_rule ->
        print_string "goal reachable: ";
        Display.Text.display_rule_abbrev ord_rule.rule;
        if !Param.html_output then
          begin
            Display.Html.print_string "goal reachable: ";
            Display.Html.display_rule_abbrev ord_rule.rule
          end;
        begin
          try
            ignore (History.build_history None ord_rule.rule)
          with Not_found -> ()
        end;
        cleanup()
      ) l;
      if !Param.html_output then
        Display.Html.print_line "Error: you have given a secrecy assumption that I could not verify.";
      (* TO DO close HTML files properly before this error *)
      Parsing_helper.user_error "you have given a secrecy assumption that I could not verify."

let completion lemmas inductive_lemmas rulelist =
  (* Enter the rules given in "rulelist" in the rule base *)
  if !Param.html_output then
    begin
      let qs =
        if !is_inside_query then
          "inside" ^ (string_of_int (!Param.inside_query_number))
        else
          (string_of_int (!Param.current_query_number))
      in
      Display.LangHtml.openfile ((!Param.html_dir) ^ "/clauses" ^ qs ^ ".html") ("ProVerif: clauses for query " ^ qs);
      Display.Html.print_string "<H1>Initial clauses</H1>\n";
      Display.Html.display_initial_clauses rulelist;
      Display.LangHtml.close();
      Display.Html.print_string ("<A HREF=\"clauses" ^ qs ^ ".html\" TARGET=\"clauses\">Clauses</A><br>\n")
    end
  else if (!Param.verbose_explain_clauses != Param.NoClauses) ||
     (!Param.explain_derivation = false) then
    begin
      Display.Text.print_string "Initial clauses:";
      Display.Text.display_initial_clauses rulelist
    end;

  (* Reinit the rule database *)
  let database = new_database () in

  (* Insert the initial rules in the queue,
     possibly completing them with equations *)
  if (!close_with_equations) && (TermsEq.hasEquations()) then
  begin
    print_string "Completing with equations...\n";
    List.iter (fun rule ->
      if !Param.verbose_rules then
        begin
          print_string "Completing ";
          Display.Text.display_rule_indep rule
        end
      else
        begin
          database.count <- database.count + 1;
          if database.count mod 200 = 0 then
            begin
               print_string ((string_of_int database.count) ^ " rules completed.");
               Display.Text.newline()
            end
        end;
      TermsEq.close_rule_eq (normal_rule database lemmas inductive_lemmas) (copy_rule rule)
    ) rulelist;

    (* Convert the queue of rules into a list, to display it *)
    let rulelisteq =
      let l = ref [] in
      Pvqueue.iter database.queue (fun r -> l := r::(!l));
      !l
    in
    if !Param.html_output then
      begin
        Display.LangHtml.openfile ((!Param.html_dir) ^ "/eqclosure.html") "ProVerif: clauses completed with equations";
        Display.Html.print_string "<H1>Clauses completed with equations</H1>\n";
        Display.Html.display_item_list (fun r -> Display.auto_cleanup_display (fun () -> Display.Html.display_rule_nonewline r)) rulelisteq;
        Display.LangHtml.close();
        Display.Html.print_string "<A HREF=\"eqclosure.html\">Clauses completed with equations</A><br>\n"
      end
    else if !Param.verbose_completed then
      begin
        Display.Text.print_string "Clauses completed with equations:";
        Display.Text.display_item_list (fun r -> Display.auto_cleanup_display (fun () -> Display.Text.display_rule_nonewline r)) rulelisteq
      end
  end
  else
    List.iter (normal_rule database lemmas inductive_lemmas) rulelist;

  (* Initialize the selection function *)
  Selfun.guess_no_unif database.queue;

  (* Display initial queue *)
  if !Param.verbose_base
  then display_initial_queue_main (fun x -> x ) database;

  (* Complete the rule base *)
  print_string "Completing...\n";
  let completed_rules = complete_rules database lemmas inductive_lemmas in
  if !Param.html_output then
    begin
      let qs =
        if !is_inside_query then
          "inside" ^ (string_of_int (!Param.inside_query_number))
        else
          string_of_int (!Param.current_query_number)
      in
      Display.LangHtml.openfile ((!Param.html_dir) ^ "/compclauses" ^ qs ^ ".html") ("ProVerif: completed clauses for query " ^ qs);
      Display.Html.print_string "<H1>Completed clauses</H1>\n";
      Display.Html.display_item_list (fun r -> Display.auto_cleanup_display (fun () -> Display.Html.display_rule_nonewline r)) completed_rules;
      Display.LangHtml.close();
      Display.Html.print_string ("<A HREF=\"compclauses" ^ qs ^ ".html\">Completed clauses</A><br>\n")
    end
  else if !Param.verbose_completed then
    begin
      Display.Text.print_string "Completed clauses:";
      Display.Text.display_item_list (fun r -> Display.auto_cleanup_display (fun () -> Display.Text.display_rule_nonewline r)) completed_rules
    end;

  (* Initialise the ordered rules for the base *)
  saturated_rules := List.map saturated_reduction_of_reduction completed_rules;

  (* Query the goals *)
  List.iter (query_goal_not lemmas) (!not_set)

let initialize state =
  initialized := true;
  saturated_rules := [];
  not_set := state.h_not;
  elimtrue_set := state.h_elimtrue;
  initialise_pred_to_prove state.h_pred_prove;
  initialise_useless_events_for_lemmas state.h_event_in_queries state.h_lemmas;
  set_equiv state.h_equiv;
  Selfun.initialize state.h_nounif state.h_solver_kind;
  List.iter (fun r -> ignore (Selfun.selection_fun r)) state.h_clauses_to_initialize_selfun;
  Weaksecr.initialize state.h_solver_kind;
  Noninterf.initialize state.h_solver_kind;
  (* This assertions aims to check that equations have already been
     recorded *)
  assert ((state.h_equations != []) = (TermsEq.hasEquations()));
  close_with_equations := state.h_close_with_equations;

  (* Display all lemmas *)
  if state.h_lemmas != []
  then
    begin
      if !Param.html_output then
        begin
          let qs =
            if !is_inside_query then
              "inside" ^ (string_of_int (!Param.inside_query_number))
            else
              (string_of_int (!Param.current_query_number))
          in
          Display.LangHtml.openfile ((!Param.html_dir) ^ "/lemmas" ^ qs ^ ".html") ("ProVerif: lemmas for the verification of query " ^ qs);
          Display.Html.print_string "<H1>Lemmas</H1>\n";
          Display.Html.display_lemmas state.h_lemmas;
          Display.LangHtml.close();
          Display.Html.print_string ("<A HREF=\"lemmas" ^ qs ^ ".html\" TARGET=\"lemmas\">Lemmas</A><br>\n")
        end
      else if !Param.verbose_lemmas || not !Param.explain_derivation then
        begin
          Display.Text.print_string "Lemmas used in the verification of the query:";
          Display.Text.display_lemmas state.h_lemmas
        end
    end

let corresp_initialize state =
  (* Main be used also for correspondence queries
     on biprocesses, so with Solve_Equivalence as well *)
  initialize state;

  (* We gather the lemmas *)
  let (lemmas,inductive_lemmas) =
    List.fold_left (fun (acc_l,acc_i) lem ->
      if lem.l_sat_app <> LANone
      then
        if lem.l_induction = None
        then (lem::acc_l,acc_i)
        else (acc_l,lem::acc_i)
      else (acc_l,acc_i)
    ) ([],[]) state.h_lemmas
  in

  completion lemmas inductive_lemmas state.h_clauses

  (* We allow subsequent calls to resolve_hyp, query_goal_std,
     sound_bad_derivable after this initialization and completion *)

let reset () =
  initialized := false;
  not_set := [];
  elimtrue_set := [];
  set_equiv [];
  Selfun.initialize [] Solve_Standard;
  Weaksecr.initialize Solve_Standard;
  Noninterf.initialize Solve_Standard;
  saturated_rules := [];
  close_with_equations := false;
  reset_pred_to_prove ();
  events_only_for_lemmas := [];
  all_original_lemmas := []

let internal_bad_derivable lemmas rulelist =
  completion lemmas [] rulelist;
  List.filter (function
    | { sat_rule = (_, Pred(p, []), _, _); _} when p == Param.bad_pred -> true
    | _ -> false
  ) !saturated_rules

(* Test whether bad is derivable from rulelist;
   this function does not alter saturated_rules, so that it can be called
   even if I am calling query_goal_std afterwards to test whether some fact
   is derivable from other completed clauses.
   Furthermore, it is guaranteed to say that that bad is derivable only
   if it is actually derivable *)

let sound_bad_derivable lemmas rulelist =
  assert (!initialized);
  let old_saturated_rules = !saturated_rules in
  let old_sound_mode = !sound_mode in
  is_inside_query := true;
  sound_mode := true;
  let r = internal_bad_derivable lemmas rulelist in
  is_inside_query := false;
  sound_mode := old_sound_mode;
  saturated_rules :=  old_saturated_rules;
  List.map (fun sat_r -> sat_r.sat_rule) r

let bad_derivable state =
  assert (state.h_solver_kind <> Solve_Standard);
  initialize state;
  (* We gather the lemmas *)
  let lemmas =
    List.fold_left (fun acc_l lem ->
      if lem.l_sat_app <> LANone
      then
        begin
          if lem.l_induction <> None
          then internal_error "[rules.ml >> bad_derivable] There should not be any inductive lemma when proving equivalence.";
          (lem::acc_l)
        end
      else acc_l
    ) [] state.h_lemmas
  in
  let r = internal_bad_derivable lemmas state.h_clauses in
  reset();
  List.map (fun sat_r -> sat_r.sat_rule) r

let bad_in_saturated_database () =
  List.exists (function
    | { sat_rule = (_, Pred(p, []), _, _); _} when p == Param.bad_pred -> true
    | _ -> false
  ) !saturated_rules

let main_analysis state goal_set =
  assert (state.h_solver_kind = Solve_Standard);
  initialize state;
  completion [] [] state.h_clauses;
  List.iter query_goal goal_set;
  reset()
