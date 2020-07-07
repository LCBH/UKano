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
open Pitypes

(* Information computed by [transl], to add to the [pi_state] *)

let terms_to_add_in_name_params = ref []

(* Variables local to this module, used to store elements of the t_horn_state we are going to return *)

(** Indicates the number of rules created *)
let nrule = ref 0
(** List of the rules created *)
let red_rules = ref ([] : reduction list)
let no_gen_var = ref []
let no_unif_set = ref ([] : (fact_format * int * nounif_op) list)
(* List of precise action events used *)
let current_precise_actions = ref ([] : funsymb list)

let add_in_precise_actions ev =
  if List.memq ev !current_precise_actions
  then ()
  else current_precise_actions := ev :: !current_precise_actions

let add_rule hyp concl constra tags =
  red_rules := (hyp, concl,
                Rule (!nrule, tags, hyp, concl, constra), constra)
     :: (!red_rules);
  incr nrule

let add_no_unif f n for_hyp =
  no_unif_set := (f,n,for_hyp) ::(!no_unif_set)


(* For key compromise *)
let session0 = { f_name = Fixed "@session0";
                 f_type = [], Param.sid_type;
                 f_private = false;
                 f_options = 0;
                 f_cat = Eq [];
                 f_initial_cat = Eq []
               }
let compromised_session = FunApp(session0, [])

let session1 = Param.session1

(* Because [comp_session_var] is created at the very beginning,
   before parsing is initialized, it is named with [name = session, idx = 0]
   and other identifiers may have the same [name,idx]. At the display
   level, they will still be displayed differently, because the fields
   [name,idx] are no longer used for display. *)
let comp_session_var = Terms.new_var ~orig:false "session" Param.sid_type

(* For non-interference *)

let bad_pred = Param.bad_pred

(* Check that predicate calls are implementable *)

let rec get_other_vars other_vars vlist = function
    Var v ->
      if not (List.memq v vlist) then
        other_vars := v :: (!other_vars)
  | FunApp(f,l) ->
      List.iter (get_other_vars other_vars vlist) l

let rec is_ground bound_vars t =
  match t with
    Var v -> List.memq v bound_vars
  | FunApp(f,l) -> List.for_all (is_ground bound_vars) l

let check_constra error_message bound_vars c =
  Terms.iter_constraints (fun t ->
    if not (is_ground !bound_vars t)
    then
      begin
        error_message();
        user_error "In clauses, variables in inequalities, disequalities or equalities should all be bound."
      end
  ) c

let rec binds_vars error_message bound_vars = function
    FunApp(f,l) ->
      begin
        match f.f_cat with
          Tuple -> List.iter (binds_vars error_message bound_vars) l
        | _ ->
            if not (List.for_all (is_ground (!bound_vars)) l) then
              begin
                error_message();
                user_error ("Cannot bind variables under non-data constructors ("
                            ^ (Display.string_of_fsymb f) ^ ").")
              end
            (* Do not bind variables under non-data constructors *)
      end
  | Var v ->
      if not (List.memq v (!bound_vars)) then
        bound_vars := v :: (!bound_vars)

let rec check_fact pi_state error_message seen_pred_calls bound_vars = function
    Pred(p, l) ->
      check_pred pi_state error_message seen_pred_calls (p, List.map (is_ground (!bound_vars)) l);
      List.iter (binds_vars error_message bound_vars) l

and check_pred pi_state error_message seen_pred_calls (p, ground_list) =
  try
    let ground_list_seen = List.assq p seen_pred_calls  in
    if List.exists2 (fun g_seen g -> g_seen && (not g)) ground_list_seen ground_list then
      begin
        error_message();
        user_error ("Too many unbound vars in recursive call to predicate " ^ p.p_name)
      end
  with Not_found ->
    let seen_pred_calls' = (p, ground_list) :: seen_pred_calls in
    List.iter (function
        (hyp, (Pred(p', l') as concl), constra, _) ->
          if p == p' then
            let error_message' () =
              error_message();
              print_string "Clause ";
              Display.Text.display_rule (hyp, concl, Empty concl, constra)
            in
            let error_message'' () =
              error_message'();
              print_string "Conclusion ";
              Display.Text.display_fact concl;
              Display.Text.newline()
            in
            let bound_vars = ref [] in
            List.iter2 (fun t g ->
              if g then binds_vars error_message'' bound_vars t) l' ground_list;
            List.iter (fun f ->
              check_fact pi_state
                (fun () ->
                  error_message'();
                  print_string "Hypothesis ";
                  Display.Text.display_fact f;
                  Display.Text.newline()
                )
                seen_pred_calls' bound_vars f) hyp;
            check_constra
              (fun () ->
                error_message'();
                print_string "Hypothesis ";
                Display.Text.display_constraints constra;
                Display.Text.newline()
              ) bound_vars constra;
            List.iter (fun t ->
              if not (is_ground (!bound_vars) t) then
                begin
                  error_message''();
                  user_error "In the conclusion of a clause, all variables should have been bound by evaluating the hypothesis"
                end) l'
      ) pi_state.pi_input_clauses;
    List.iter (function
        (Pred(p', l') as concl) ->
          if p == p' then
            let error_message' () =
              error_message();
              print_string "Elimtrue fact ";
              Display.Text.display_fact concl;
              Display.Text.newline()
            in
            let bound_vars = ref [] in
            List.iter2 (fun t g ->
              if g then binds_vars error_message' bound_vars t) l' ground_list;
            List.iter (fun t ->
              if not (is_ground (!bound_vars) t) then
                begin
                  error_message'();
                  user_error "In a fact, all variables should have been bound"
                end) l'
      ) pi_state.pi_elimtrue

let check_first_fact pi_state vlist = function
    Pred(p,l) as f ->
      let bound_vars = ref [] in
      List.iter (get_other_vars bound_vars vlist) l;
      let error_message = fun () ->
        print_string "Error while checking implementability of \"";
        begin
          match vlist with
            [] ->
              Display.Text.display_keyword "if"
          | (a::restv) ->
              Display.Text.display_keyword "let";
              print_string (" " ^ (Display.string_of_binder a));
              List.iter (fun v -> print_string (", " ^ (Display.string_of_binder v))) restv;
              print_string " ";
              Display.Text.display_keyword "suchthat"
        end;
        print_string " ";
        Display.Text.display_fact2 f;
        print_string "\"";
        Display.Text.newline()
      in
      List.iter (fun v ->
        if not (List.exists (Terms.occurs_var v) l) then
          begin
            error_message();
            user_error ("Variable " ^ (Display.string_of_binder v) ^ " should occur in the fact.")
          end
                 ) vlist;
      check_fact pi_state error_message [] bound_vars f

type name_param_info =
    arg_meaning * binder * term * when_include
(* arg_meaning: meaning of the argument
   binder: variable for the first component of the environment in Out facts
   term: to put as parameter of name function symbol
*)


type transl_state =
    { tr_pi_state : t_pi_state; (* [pi_state] received as input *)
      hypothesis : fact list; (* Current hypotheses of the rule *)
      constra : constraints; (* Current constraints of the rule *)
      unif : (term * term) list; (* Current unifications.
         I keep the field unif here, since I use it for determining
         which variables should be generalized in end_destructor_group,
         although I perform unifications immediately when I add elements to unif. *)
      last_step_unif : (term * term) list;
      (* Unifications to do for the last group of destructor applications.
         last_step_unif will be appended to unif before emitting clauses.
         The separation between last_step_unif and unif is useful only
         for non-interference. *)
      last_step_constra : constraints;
      (* Constraints for the last group of destructor applications. *)
      neg_success_conditions : constraints ref option ref;
      (* List of constraints that should be false for the evaluation
         of destructors to succeed *)
      name_params : name_param_info list; (* List of parameters of names *)
      repl_count : int;
      (* Session identifier, to include in the parameter of
         end events for injective agreement *)
      current_session_id : binder option;
      is_below_begin : bool;
      cur_phase : int;
      input_pred : predicate;
      output_pred : predicate;
      hyp_tags : hypspec list
    }

let att_fact phase t =
  Pred(Param.get_pred (Attacker(phase, Terms.get_term_type t)), [t])

let mess_fact phase tc tm =
  Pred(Param.get_pred (Mess(phase, Terms.get_term_type tm)), [tc;tm])

let table_fact phase t =
  Pred(Param.get_pred (Table(phase)), [t])

let testunif_fact t1 t2 =
  Pred(Param.get_pred (TestUnifP(Terms.get_term_type t1)), [t1;t2])

let remove_snd_comp l = List.map (fun (x,_,y,z) -> (x,y,z)) l

let output_rule { hypothesis = prev_input; constra = constra; unif = unif;
                  last_step_unif = lsu;
                  hyp_tags = hyp_tags; name_params = name_params1 } out_fact =
   let name_params = Reduction_helper.extract_name_params_noneed (remove_snd_comp name_params1) in
   Terms.auto_cleanup (fun _ ->
     assert (lsu == []); (* "last_step_unif should have been appended to unif" *)
      (*Unification is now useless here since we unify when with
        add elements to unif
        List.iter (fun (p1,p2) -> Terms.unify p1 p2) unif;*)
      let hyp = List.map Terms.copy_fact2 prev_input in
      let concl = Terms.copy_fact2 out_fact in
      let constra2 = Terms.copy_constra2 constra in
      let name_params2 = List.map Terms.copy_term2 name_params in
      Terms.cleanup();
      begin
        try
          TermsEq.simplify_constraints (fun constra3 ->
            add_rule hyp concl constra3 (ProcessRule(hyp_tags, name_params2))
          ) (fun constra3 ->
            let hyp3 = List.map Terms.copy_fact4 hyp in
            let concl3 = Terms.copy_fact4 concl in
            let name_params3 = List.map Terms.copy_term4 name_params2 in
            add_rule hyp3 concl3 constra3 (ProcessRule(hyp_tags, name_params3))
          ) (concl::hyp) constra2
        with TermsEq.FalseConstraint -> ()
      end;
      if !Param.key_compromise = 2 then
        begin
          assert (!Terms.current_bound_vars == []);

          (* substitutes session1 for session0, attacker_p1 for
             attacker_p0 and mess_p1 for mess_p0 *)
          let rec copy_term3 = function
              FunApp(f,l) ->
                FunApp((if f == session0 then session1 else f),
                       List.map copy_term3 l)
            | Var v -> match v.link with
                NoLink ->
                  let r = Terms.copy_var v in
                  Terms.link v (VLink r);
                  Var r
              | TLink l -> copy_term3 l
              | VLink r -> Var r
              | _ -> internal_error "unexpected link in copy_term3"
          in
          let copy_fact3 = function
              Pred(chann, t) ->
                Pred((match chann.p_info with
                  [Attacker(0,ty)] -> Param.get_pred (Attacker(1,ty))
                | [Mess(0,ty)] -> Param.get_pred(Mess(1,ty))
                | [Table(0)] -> Param.get_pred(Table(1))
                | _ -> chann), List.map copy_term3 t)
          in

          (*List.iter (fun (p1,p2) -> Terms.unify p1 p2) unif;*)
          let hyp = List.map copy_fact3 prev_input in
          let concl = copy_fact3 out_fact in
          let constra3 = Terms.map_constraints copy_term3 constra in
          let name_params3 = List.map copy_term3 name_params in
          Terms.cleanup();
          try
            TermsEq.simplify_constraints (fun constra4 ->
              add_rule hyp concl constra4 (ProcessRule(hyp_tags, name_params3))
            ) (fun constra4 ->
              let hyp4 = List.map Terms.copy_fact4 hyp in
              let concl4 = Terms.copy_fact4 concl in
              let name_params4 = List.map Terms.copy_term4 name_params3 in
              add_rule hyp4 concl4 constra4 (ProcessRule(hyp_tags, name_params4))
            ) (concl::hyp) constra3
          with TermsEq.FalseConstraint -> ()
        end
          )

(* Raises Terms.Unify when cur_state does not need to be considered
   Do the unifications, but undo them immediately, before calling next_f,
   because we need to have non-unified variables in generalize_vars_not_in,
   called from end_destructor_group.
   Moreover, we cannot do basic syntactic unifications for two reasons:
   - In the case non-interference, we need to keep the
   branch if it unifies for some value of the secrets,
   not only when the secrets are names.
   - When we want to compute the negation of success conditions,
   we need to perform unification modulo the equational theory,
   because in the negation, the inequalities are modulo the
   equational theory. *)

let check_feasible cur_state =
  Terms.auto_cleanup (fun () ->
    match cur_state.tr_pi_state.pi_process_query with
    | SingleProcessSingleQuery(_, NonInterfQuery(secret_vars_with_sets)) ->
        (* In the case non-interference, we need to keep the
           branch if it unifies for some value of the secrets,
           so we replace the secrets with variables. *)
        let vlsecr = List.map (fun (f,_) -> (f,Terms.new_var ~orig:false (Terms.get_fsymb_basename f) (snd f.f_type))) secret_vars_with_sets in
        let rec replace_secr_var = function
          | Var v -> Var v
          | FunApp(f2,[]) ->
              begin
                try
                  Var (List.assq f2 vlsecr)
                with Not_found ->
                  FunApp(f2,[])
              end
        | FunApp(f2,l) -> FunApp(f2, List.map replace_secr_var l)
        in
        let (l1, l2) = List.split (List.map (fun (t1,t2) ->
          (replace_secr_var t1, replace_secr_var t2)
            ) cur_state.last_step_unif)
        in
        let constra' = Terms.map_constraints replace_secr_var (Terms.wedge_constraints cur_state.last_step_constra cur_state.constra) in
        TermsEq.unify_modulo_list (fun () ->
          try
            TermsEq.check_constraints constra'
          with TermsEq.FalseConstraint -> raise Terms.Unify) l1 l2
    | _ ->
        let l1, l2 = List.split cur_state.last_step_unif in
        let constra' = Terms.wedge_constraints cur_state.last_step_constra cur_state.constra in
        TermsEq.unify_modulo_list (fun () ->
          try
            TermsEq.check_constraints constra'
          with TermsEq.FalseConstraint -> raise Terms.Unify
        ) l1 l2
  )

(* For non-interference *)

let end_destructor_group_no_test_unif next_f cur_state =
  Terms.auto_cleanup (fun _ ->
    try
      List.iter (fun (t1,t2) -> Terms.unify t1 t2) cur_state.last_step_unif;
      (* Check that constraints are still satisfiable.
         We check all constraints and not only the new ones, because
         the old constraints may have been modified by unification,
         so they may no longer be satisfiable. *)
      let constra' = Terms.wedge_constraints cur_state.last_step_constra cur_state.constra in
      TermsEq.check_constraints constra';
      next_f { cur_state with
               unif = cur_state.last_step_unif @ cur_state.unif;
               constra = constra';
               last_step_unif = [];
               last_step_constra = Terms.true_constraints;
               neg_success_conditions = ref None }
    with Terms.Unify | TermsEq.FalseConstraint -> ()
        )

let end_destructor_group next_f occ cur_state =
  end_destructor_group_no_test_unif next_f cur_state;
  if (Param.is_noninterf cur_state.tr_pi_state) || (!(cur_state.neg_success_conditions) != None) then
    try
      check_feasible cur_state;

      (* First compute the generalization of last_step_unif *)
      let l1, l2 =
        if cur_state.last_step_unif != [] then
          (* Get all vars in cur_state.hypothesis/unif/constra *)
          let var_list = ref (!no_gen_var) in
          List.iter (Terms.get_vars_fact var_list) cur_state.hypothesis;
          List.iter (fun (t1,t2) -> Terms.get_vars var_list t1; Terms.get_vars var_list t2) cur_state.unif;
          Terms.iter_constraints (Terms.get_vars var_list) cur_state.constra;
          (* Generalize all vars not in cur_state.hypothesis/unif/constra *)
          Terms.auto_cleanup (fun _ ->
            List.map (fun (t,_) -> Terms.generalize_vars_not_in (!var_list) t) cur_state.last_step_unif,
            List.map (fun (_,t) -> Terms.generalize_vars_not_in (!var_list) t) cur_state.last_step_unif)
        else
          [], []
      in

      (* Update the success conditions *)
      begin
        match !(cur_state.neg_success_conditions) with
          None -> ()
        | Some r ->
            if Terms.is_true_constraints cur_state.last_step_constra then
              (* The success condition contains no inequality,
                 we store in cur_state.neg_success_conditions the
                 negation of the unifications, to serve to detect failure *)
              let new_neq_disj = List.map2 (fun t1 t2 -> (t1,t2)) l1 l2 in
              r:= { !r with neq = new_neq_disj :: (!r).neq }
            else
              (* The success condition contains an inequality.
                 Taking its negation is too complicated,
                 we forget about neg_success_conditions, and will
                 compute the failure condition in another way. *)
              cur_state.neg_success_conditions := None
      end;

      (* Treat the non-interference *)
      if Param.is_noninterf cur_state.tr_pi_state then
        begin
          if cur_state.last_step_unif != [] then
            begin
              let tuple_fun = Terms.get_tuple_fun (List.map Terms.get_term_type l1) in
              let new_hyp = testunif_fact (FunApp(tuple_fun, l1)) (FunApp(tuple_fun, l2)) in
              output_rule { cur_state with
                        hypothesis = new_hyp :: cur_state.hypothesis;
                        hyp_tags = TestUnifTag(occ) :: cur_state.hyp_tags;
                        last_step_unif = [];
                        last_step_constra = Terms.true_constraints } (Pred(bad_pred, []))
            end;

          (* Bruno : Need some help for the non-interference and natural number predicates. *)
          Terms.auto_cleanup (fun _ ->
            try
              if cur_state.last_step_constra.is_nat != [] || cur_state.last_step_constra.is_not_nat != [] || cur_state.last_step_constra.geq != []
              then Parsing_helper.user_error "Natural number is not working with non-interference yet.";

              List.iter (fun (t1,t2) -> Terms.unify t1 t2) cur_state.last_step_unif;
              List.iter (fun constra ->
                let (l1, l2) = List.split constra in
                let tuple_fun = Terms.get_tuple_fun (List.map Terms.get_term_type l1) in
                let new_hyp = testunif_fact (FunApp(tuple_fun, l1)) (FunApp(tuple_fun, l2)) in
                output_rule { cur_state with
                          hypothesis = new_hyp :: cur_state.hypothesis;
                          hyp_tags = TestUnifTag(occ) :: cur_state.hyp_tags;
                          unif = cur_state.last_step_unif @ cur_state.unif;
                          last_step_unif = [];
                          last_step_constra = Terms.true_constraints } (Pred(bad_pred, []))
                  ) cur_state.last_step_constra.neq
            with Terms.Unify -> ()
            )
        end
    with Terms.Unify -> ()

(* Decide when to optimize mess(c,M) into attacker(M) *)

let optimize_mess cur_state tc =
  !Param.active_attacker &&
  (match tc with
  | FunApp({ f_cat = Name _; f_private = false },_) -> true
  | _ -> false) &&
  ((not (!Param.allow_private_comm_on_public_free_names)) ||
   (not (Reduction_helper.prove_att_phase cur_state.tr_pi_state cur_state.cur_phase)))

(* Functions that modify last_step_unif, and that should
   therefore be followed by a call to end_destructor_group

   transl_term
   transl_term_list
   transl_term_incl_destructor
   transl_term_list_incl_destructor
   transl_pat
   transl_fact

*)

(* Translate term *)

(* next_f takes a state and a pattern as parameter *)
let rec transl_term next_f cur_state = function
    Var v ->
      begin
        match v.link with
          TLink t -> next_f cur_state t
        | _ -> internal_error "unexpected link in transl_term"
      end
  | FunApp(f,l) ->
      let transl_red red_rules =
        transl_term_list (fun cur_state1 term_list ->
          List.iter (fun red_rule ->
            (* Fresh rewrite rule *)
            let (left_list, right, side_c) = Terms.auto_cleanup (fun _ -> Terms.copy_red red_rule) in
            let cur_state2 =
              { cur_state1 with
                last_step_unif = (List.combine term_list left_list) @ cur_state1.last_step_unif;
                last_step_constra = Terms.wedge_constraints side_c cur_state1.last_step_constra }
            in
            (* Optimization: check that the branch is still feasible. *)
            try
              check_feasible cur_state2;
              next_f cur_state2 right
            with Terms.Unify -> ()
              ) red_rules
            ) cur_state l
      in

      match f.f_cat with
        Name n ->
          begin
            match n.prev_inputs with
              Some t -> next_f cur_state t
            | _ -> internal_error "unexpected prev_inputs in transl_term"
          end
      | Tuple | Eq _ | Red _ | Failure ->
          transl_red (Terms.red_rules_fun f)
      | _ ->
          Parsing_helper.internal_error "function symbols of these categories should not appear in input terms (pitransl)"


(* next_f takes a state and a list of patterns as parameter *)
and transl_term_list next_f cur_state = function
    [] -> next_f cur_state []
  | (a::l) ->
      transl_term (fun cur_state1 p ->
        transl_term_list (fun cur_state2 patlist ->
          next_f cur_state2 (p::patlist)) cur_state1 l) cur_state a

(* To associate a variable to a syntax element without creating
   a fresh variable everytime. Useful for the first component of
   the environment in Out facts *)
let var_cache_term = ref ([] : (term * binder) list)
let var_cache_process = ref ([] : (process * binder) list)

let get_var_for_term a =
  try
    List.assq a (!var_cache_term)
  with Not_found ->
    let r = Terms.new_var ~orig:false (if !Param.tulafale != 1 then "@destrv" else "destrv") (Terms.get_term_type a) in
    var_cache_term := (a, r) :: (!var_cache_term);
    r

let get_var_for_process a v =
  try
    List.assq a (!var_cache_process)
  with Not_found ->
    var_cache_process := (a, v) :: (!var_cache_process);
    v

let transl_term_incl_destructor f cur_state occ t =
  let may_have_several_types = Reduction_helper.transl_check_several_patterns terms_to_add_in_name_params occ t in
  transl_term (fun cur_state1 pat1 ->
    if may_have_several_types then
      f { cur_state1 with
                 name_params = (MUnknown, get_var_for_term t, pat1, Always)::cur_state1.name_params } pat1
    else
      f cur_state1 pat1
    ) cur_state t

let transl_term_list_incl_destructor f cur_state occ tl =
  let may_have_several_types = List.exists (Reduction_helper.transl_check_several_patterns terms_to_add_in_name_params occ) tl in
  transl_term_list (fun cur_state1 patlist ->
    if may_have_several_types then
      f { cur_state1 with
                    name_params = (List.map2 (fun t pat -> (MUnknown, get_var_for_term t, pat, Always)) tl patlist) @ cur_state1.name_params } patlist
    else
      f cur_state1 patlist
    ) cur_state tl

(* Detect failure *)

let no_fail next_f cur_state t =
  let x = Terms.new_var_def_term (Terms.get_term_type t) in
  next_f { cur_state with
           last_step_unif = (t,x)::cur_state.last_step_unif } t

let no_fail_list next_f cur_state tl =
  let unifl = List.map (fun t -> (t, Terms.new_var_def_term (Terms.get_term_type t))) tl in
  next_f { cur_state with
           last_step_unif = unifl @ cur_state.last_step_unif } tl

let must_fail next_f cur_state t =
  let fail = Terms.get_fail_term (Terms.get_term_type t) in
  next_f { cur_state with
           last_step_unif = (t,fail)::cur_state.last_step_unif }

(* Translate pattern *)

let rec transl_pat put_var f cur_state pat =
  match pat with
    PatVar b ->
      let b' = Terms.copy_var b in
      let pat' = Var b' in
      b.link <- TLink pat';
      f { cur_state with name_params = (MVar(b, None), b, pat', put_var) :: cur_state.name_params } (Var b');
      b.link <- NoLink
  | PatTuple (fsymb,pat_list) ->
      transl_pat_list put_var (fun cur_state2 term_list ->
        f cur_state2 (FunApp(fsymb, term_list))
          ) cur_state pat_list;
  | PatEqual t ->
      transl_term (no_fail f) cur_state t

and transl_pat_list put_var f cur_state = function
    [] -> f cur_state []
  | p::pl ->
      (* It is important to translate the head first, like the head is
         checked first in pisyntax.ml, because variables may be bound in the
         head and used in equality tests in the tail *)
      transl_pat put_var (fun cur_state2 term ->
        transl_pat_list put_var (fun cur_state3 term_list ->
          f cur_state3 (term::term_list)
            ) cur_state2 pl
          ) cur_state p

(* Function Not Used *)
(*
let rec transl_unif next_f cur_state accu = function
    [] -> next_f { cur_state with
                   last_step_constra = accu :: cur_state.last_step_constra }
  | (p,t)::l ->
      (* We have a term =t in the pattern, and its expected value is p *)
      transl_term (fun cur_state' t' ->
        (* t fails *)
        must_fail next_f cur_state' t';
        (* t does not fail, it is different from its expected value p *)
        no_fail (fun cur_state'' _ ->
          transl_unif next_f cur_state'' ((Neq(p, t'))::accu) l
            ) cur_state' t'
          ) cur_state t
*)

(* Handles the case in which one the terms =M in the pattern fails *)

let rec transl_pat_fail_term next_f cur_state = function
    PatVar b -> ()
  | PatTuple(f,l) ->
      List.iter (transl_pat_fail_term next_f cur_state) l
  | PatEqual t ->
      (* t fails *)
      transl_term (must_fail next_f) cur_state t

(* Handles the case in which the terms =M in the pattern succeed,
   but the result does not match
   [transl_pat_fail_rec] calls [next_f] with the current state
   and a term that represents the pattern, with general variables
   instead of variables bound by the pattern. *)

let rec transl_pat_fail_rec next_f cur_state = function
    PatVar b ->
      let gvar = Terms.new_gen_var b.btype false in
      next_f cur_state (FunApp(gvar, []));
  | PatTuple (fsymb,pat_list) ->
      transl_pat_fail_list (fun cur_state gen_list ->
        next_f cur_state (FunApp(fsymb, gen_list))
          ) cur_state pat_list
  | PatEqual t ->
      (* term t succeeds *)
      transl_term (no_fail next_f) cur_state t

and transl_pat_fail_list next_f cur_state = function
    [] -> next_f cur_state []
  | p::pl ->
      transl_pat_fail_rec (fun cur_state1 gen ->
        transl_pat_fail_list (fun cur_state2 gen_list ->
          next_f cur_state2 (gen::gen_list)
            ) cur_state1 pl
        ) cur_state p

let transl_pat_fail next_f cur_state pat pat' =
  (* one the terms =M in the pattern fails *)
  transl_pat_fail_term next_f cur_state pat;
  (* the terms =M in the pattern succeed, but the result does not match *)
  transl_pat_fail_rec (fun cur_state1 pat_gen ->
    next_f { cur_state1 with
             last_step_constra = { cur_state1.last_step_constra with neq = [pat_gen, pat']::cur_state1.last_step_constra.neq } };
      ) cur_state pat

(* Translate fact *)

let transl_fact next_fun cur_state occ f =
  match f with
  | Pred(p,tl) ->
      transl_term_list_incl_destructor (no_fail_list (fun cur_state1 patl ->
        next_fun (Pred(p,patl)) cur_state1)) cur_state occ tl

(* Translate process *)

let get_occurrence_name_for_precise cur_state occ =
  let name_params = remove_snd_comp cur_state.name_params in
  let (np, npm) =
    List.fold_right (fun (m,t,_) (acc_np,acc_npm) -> match m with
      | MSid _ -> (t::acc_np,m::acc_npm)
      | _ -> (acc_np,acc_npm)
    ) name_params ([],[])
  in
  let n = Reduction_helper.get_occ_name occ in
  (* Fix now how the name [n] is displayed, to avoid different
     displays in different clauses/derivations *)
  let n_string = Display.string_of_fsymb n in
  match n.f_cat with
    | Name r ->
        let nptype = List.map Terms.get_term_type np in
        if fst n.f_type == Param.tmp_type then
          begin
            n.f_type <- nptype, snd n.f_type;
            r.prev_inputs_meaning <- npm
          end
        else if Param.get_ignore_types() then
          begin
            (* When we ignore types, the types of the arguments may vary,
               only the number of arguments is preserved. *)
            if List.length (fst n.f_type) != List.length nptype then
              internal_error ("Name " ^ n_string ^ " has bad arity")
          end
        else
          begin
            if not (Terms.eq_lists (fst n.f_type) nptype) then
              internal_error ("Name " ^ n_string ^ " has bad type")
          end;

        FunApp(n,np)
    | _ -> internal_error "[pitransl.ml >> get_occurrence_name_for_precise] Unexpected function category in the translation of events."

let rec transl_process cur_state = function
   Nil -> ()
 | NamedProcess(_, _, p) -> transl_process cur_state p
 | Par(p,q) -> transl_process cur_state p;
               transl_process cur_state q
 | (Repl (p,occ)) as p' ->
     let cur_state = { cur_state with repl_count = cur_state.repl_count + 1 } in
     let sid_meaning = MSid cur_state.repl_count in
     (* Always introduce session identifiers ! *)
     let cur_state = { cur_state with is_below_begin = false } in
     let v = Terms.new_var ~orig:false (if !Param.tulafale != 1 then "@sid" else "sid") Param.sid_type in
     no_gen_var := v :: (!no_gen_var);
     let v' = get_var_for_process p' v in
     let count_params = Reduction_helper.count_name_params (remove_snd_comp cur_state.name_params) in
     begin
       if Param.is_noninterf cur_state.tr_pi_state then
         begin
           if (!Param.key_compromise == 0) then
             transl_process { cur_state with
                              hypothesis = (att_fact cur_state.cur_phase (Var v)) :: cur_state.hypothesis;
                              current_session_id = Some v;
                              name_params = (sid_meaning, v', Var v, Always) :: cur_state.name_params;
                              hyp_tags = (ReplTag(occ, count_params)) :: cur_state.hyp_tags
                            } p
           else if (!Param.key_compromise == 1) then
             transl_process { cur_state with
                              hypothesis = (att_fact cur_state.cur_phase (Var v)) :: (att_fact cur_state.cur_phase (Var comp_session_var)) :: cur_state.hypothesis;
                              current_session_id = Some v;
                              name_params = (MCompSid, comp_session_var, Var comp_session_var, Always) ::
                                 (sid_meaning, v', Var v, Always) :: cur_state.name_params;
                              hyp_tags = (ReplTag(occ, count_params)) :: cur_state.hyp_tags
                            } p
           else
             transl_process { cur_state with
                              hypothesis = (att_fact cur_state.cur_phase (Var v)) :: cur_state.hypothesis;
                              current_session_id = Some v;
                              name_params = (MCompSid, v', compromised_session, Always) ::
                                 (sid_meaning, v', Var v, Always) :: cur_state.name_params;
                              hyp_tags = (ReplTag(occ, count_params)) :: cur_state.hyp_tags
                            } p
         end
       else
         begin
           if (!Param.key_compromise == 0) then
             transl_process { cur_state with
                              current_session_id = Some v;
                              name_params = (sid_meaning, v', Var v, Always) :: cur_state.name_params;
                              hyp_tags = (ReplTag(occ, count_params)) :: cur_state.hyp_tags
                            } p
           else if (!Param.key_compromise == 1) then
             transl_process { cur_state with
                              current_session_id = Some v;
                              name_params = (MCompSid, comp_session_var, Var comp_session_var, Always) ::
                                 (sid_meaning, v', Var v, Always) :: cur_state.name_params;
                              hyp_tags = (ReplTag(occ, count_params)) :: cur_state.hyp_tags
                            } p
           else
             transl_process { cur_state with
                              current_session_id = Some v;
                              name_params = (MCompSid, v', compromised_session, Always) ::
                                 (sid_meaning, v', Var v, Always) :: cur_state.name_params;
                              hyp_tags = (ReplTag(occ, count_params)) :: cur_state.hyp_tags
                            } p
         end
     end;
 | Restr(n,(args, env),p,_) ->
     begin
       let need_list = Reduction_helper.get_need_vars cur_state.tr_pi_state n in
       let include_info = Reduction_helper.prepare_include_info env args need_list in
       let name_params = remove_snd_comp cur_state.name_params in
       let npm = Reduction_helper.extract_name_params_meaning n include_info name_params in
       let np = Reduction_helper.extract_name_params n include_info name_params in
     match n.f_cat with
       Name r ->
         let nptype = List.map Terms.get_term_type np in
         if fst n.f_type == Param.tmp_type then
           begin
             n.f_type <- nptype, snd n.f_type;
             r.prev_inputs_meaning <- npm
           end
         else if Param.get_ignore_types() then
           begin
             (* When we ignore types, the types of the arguments may vary,
                only the number of arguments is preserved. *)
             if List.length (fst n.f_type) != List.length nptype then
               internal_error ("Name " ^ (Display.string_of_fsymb n) ^ " has bad arity")
           end
         else
           begin
             if not (Terms.eq_lists (fst n.f_type) nptype) then
               internal_error ("Name " ^ (Display.string_of_fsymb n) ^ " has bad type")
           end;
         r.prev_inputs <- Some (FunApp(n, np));
         transl_process cur_state p;
         r.prev_inputs <- None
     | _ -> internal_error "A restriction should have a name as parameter"
     end
 | Test(t,p,q,occ) ->
     if q == Nil then
       (* We optimize the case q == Nil.
          In this case, the adversary cannot distinguish the situation
          in which t fails from the situation in which t is false. *)
       transl_term_incl_destructor (no_fail (fun cur_state1 pat1 ->
         end_destructor_group (fun cur_state2 ->
           transl_process { cur_state2 with
                            hyp_tags = (TestTag occ) :: cur_state2.hyp_tags } p
         ) occ { cur_state1 with
                 last_step_unif = (pat1,Terms.true_term) :: cur_state1.last_step_unif }
       )) cur_state (OTest(occ)) t
     else
       transl_term_incl_destructor (no_fail (fun cur_state1 pat1 ->
         end_destructor_group (fun cur_state2 ->
           if Param.is_noninterf cur_state2.tr_pi_state then
             output_rule { cur_state2 with
                           hypothesis = (testunif_fact pat1 Terms.true_term) :: cur_state2.hypothesis;
                           hyp_tags = TestUnifTag(occ) :: cur_state2.hyp_tags
                         } (Pred(bad_pred, []));
           Terms.auto_cleanup (fun _ ->
             try
               Terms.unify pat1 Terms.true_term;
               transl_process { cur_state2 with
                                unif = (pat1,Terms.true_term) :: cur_state2.unif;
                                hyp_tags = (TestTag occ) :: cur_state2.hyp_tags } p
             with Terms.Unify -> ()
           );
           Terms.auto_cleanup (fun _ ->
             try
               let constra' = { cur_state2.constra with neq = [pat1, Terms.true_term]::cur_state2.constra.neq } in
               TermsEq.check_constraints constra';
               transl_process { cur_state2 with
                                constra = constra';
                                hyp_tags = (TestTag occ) :: cur_state2.hyp_tags } q
             with Terms.Unify | TermsEq.FalseConstraint -> ()
           );
           ) occ cur_state1
       )) cur_state (OTest(occ)) t
 | Input(tc,pat,p,occ) ->
     if optimize_mess cur_state tc then
       begin
         let x = Reduction_helper.new_var_pat pat in
         transl_pat Always (fun cur_state1 pat1 ->
           let cur_state1' =
             if cur_state1.is_below_begin || occ.precise || !Param.precise_actions
             then
               begin
                 let occ_name = get_occurrence_name_for_precise cur_state1 occ in
                 let ev = Param.get_precise_event (Action (Terms.get_term_type x)) in
                 Reduction_helper.add_precise_info_occ occ (Action (Terms.get_term_type x));
                 add_in_precise_actions ev;
                 { cur_state1 with
                   last_step_unif = (pat1, x) :: cur_state1.last_step_unif;
                   hypothesis = (att_fact cur_state1.cur_phase x) :: (Pred(Param.begin_pred,[FunApp(ev,[occ_name;x])])) :: cur_state1.hypothesis;
                   hyp_tags = (InputTag(occ)) :: (PreciseTag(occ)) ::cur_state1.hyp_tags
                 }
               end
             else
               { cur_state1 with
                 last_step_unif = (pat1, x) :: cur_state1.last_step_unif;
                 hypothesis = (att_fact cur_state1.cur_phase x) :: cur_state1.hypothesis;
                 hyp_tags = (InputTag(occ)) :: cur_state1.hyp_tags
               }
           in

           end_destructor_group (fun cur_state2 -> transl_process cur_state2 p) occ cur_state1'
             ) cur_state pat;

         if Param.is_noninterf cur_state.tr_pi_state then
           transl_term_incl_destructor (no_fail (fun cur_state1 pat1 ->
             end_destructor_group (fun cur_state2 ->
               output_rule { cur_state2 with
                             hyp_tags = (InputPTag(occ)) :: cur_state.hyp_tags }
                 (Pred(cur_state.input_pred, [pat1]))
                 ) occ cur_state1
	       )) cur_state (OInChannel(occ)) tc
       end
     else
       begin
         transl_term_incl_destructor (no_fail (fun cur_state1 pat1 ->
           end_destructor_group (fun cur_state2 ->
             let x = Reduction_helper.new_var_pat pat in
             transl_pat Always (fun cur_state3 pat2 ->
               let cur_state4 =
                 if cur_state3.is_below_begin || occ.precise || !Param.precise_actions
                 then
                   begin
                     let occ_name = get_occurrence_name_for_precise cur_state3 occ in
                     let ev = Param.get_precise_event (Action (Terms.get_term_type x)) in
                     Reduction_helper.add_precise_info_occ occ (Action (Terms.get_term_type x));
                     add_in_precise_actions ev;
                     { cur_state3 with
                       last_step_unif = (pat2, x) :: cur_state3.last_step_unif;
                       hypothesis = (mess_fact cur_state3.cur_phase pat1 x) :: (Pred(Param.begin_pred,[FunApp(ev,[occ_name;x])])) :: cur_state3.hypothesis;
                       hyp_tags = (InputTag(occ)) :: (PreciseTag(occ)) ::cur_state3.hyp_tags
                     }
                   end
                 else
                   { cur_state3 with
                     last_step_unif = (pat2, x) :: cur_state3.last_step_unif;
                     hypothesis = (mess_fact cur_state3.cur_phase pat1 x) :: cur_state3.hypothesis;
                     hyp_tags = (InputTag(occ)) :: cur_state3.hyp_tags
                   }
               in
               end_destructor_group (fun cur_state5 -> transl_process cur_state5 p) occ cur_state4
                 ) cur_state2 pat;

             if Param.is_noninterf cur_state2.tr_pi_state then
               output_rule { cur_state2 with
                             hyp_tags = (InputPTag(occ)) :: cur_state.hyp_tags }
                 (Pred(cur_state.input_pred, [pat1]))
		 ) occ cur_state1
             )) cur_state (OInChannel(occ)) tc
       end
 | Output(tc,t,p,occ) ->
     begin
       if optimize_mess cur_state tc then
	 begin
           if Param.is_noninterf cur_state.tr_pi_state then
            begin
              transl_term (no_fail (fun cur_state1 patc ->
                end_destructor_group (fun cur_state2 ->
                   output_rule { cur_state2 with
                                hyp_tags = (OutputPTag occ) :: cur_state2.hyp_tags }
                    (Pred(cur_state.output_pred, [patc]))
                ) occ cur_state1
              )) cur_state tc
            end;
           transl_term (no_fail (fun cur_state1 pat1 ->
             end_destructor_group (fun cur_state2 ->
               output_rule { cur_state2 with
                              hyp_tags = (OutputTag occ) :: cur_state2.hyp_tags
                           } (att_fact cur_state.cur_phase pat1)
		 ) occ cur_state1
               )) cur_state t
	 end
       else
	 begin
           transl_term (no_fail (fun cur_state1 patc ->
                 transl_term (no_fail (fun cur_state2 pat1 ->
                   end_destructor_group (fun cur_state3 ->
                     if Param.is_noninterf cur_state3.tr_pi_state then
                       output_rule { cur_state3 with
                                     hyp_tags = (OutputPTag occ) :: cur_state3.hyp_tags }
                          (Pred(cur_state.output_pred, [patc]));
                     output_rule { cur_state3 with
                                   hyp_tags = (OutputTag occ) :: cur_state2.hyp_tags
                                 } (mess_fact cur_state.cur_phase patc pat1)
                   ) occ cur_state2
                 )) cur_state1 t
               )) cur_state tc
	 end
     end;
     transl_process { cur_state with
                      hyp_tags = (OutputTag occ) :: cur_state.hyp_tags } p
 | Let(pat,t,p,p',occ) ->
     assert (cur_state.last_step_unif == []); (* last_step_unif should have been appended to unif *)
     (* Case "in" branch taken *)
     let neg_success_conditions = ref (Some (ref Terms.true_constraints)) in
     transl_term_incl_destructor (no_fail (fun cur_state1 pat1 ->
       transl_pat IfQueryNeedsIt (fun cur_state2 pat2 ->
           end_destructor_group (fun cur_state3 -> transl_process cur_state3 p) occ
             { cur_state2 with
               last_step_unif = (pat1, pat2)::cur_state2.last_step_unif }
         ) cur_state1 pat
     )) { cur_state with
         neg_success_conditions = neg_success_conditions;
         hyp_tags = (LetTag occ) :: cur_state.hyp_tags } (OLet(occ)) t;
     (* Case "else" branch taken *)
     begin
       match !neg_success_conditions with
         None -> (* The neg_success_conditions have been forgotten because they
                    were too complicated to compute *)
           transl_term_incl_destructor (fun cur_state1 pat1 ->
             must_fail (end_destructor_group_no_test_unif (fun cur_state2 -> transl_process cur_state2 p')) cur_state1 pat1;
             no_fail (fun cur_state2 _ ->
               transl_pat_fail (end_destructor_group_no_test_unif (fun cur_state6 -> transl_process cur_state6 p'))
                 cur_state2 pat pat1
             ) cur_state1 pat1
           ) { cur_state with
               hyp_tags = (LetTag occ) :: cur_state.hyp_tags } (OLet(occ)) t
       | Some r -> (* Use the neg_success_conditions has condition for taking
                      the else branch *)
           transl_process { cur_state with
                            constra = Terms.wedge_constraints !r cur_state.constra;
                            hyp_tags = (LetTag occ) :: cur_state.hyp_tags } p'

     end
 | LetFilter(vlist,f,p,q,occ) ->
    (* TO DO Warning! LetFilter is currently not compatible with
       non-interference! We have to generate more "test" clauses.

       For a predicate clause:
         F1 & ... & Fn -> F
       we should add the clauses:
         testF -> testF1
         testF & F1 -> testF2
         ....
         testF & F1 ... & Fn-1 -> testFn
       where, if Fi = p(M1, ..., Mn), testFi = testp(M1, ..., Mn)

       The process let v1...vn suchthat p(M1,...,Mn) generates
         h -> testp(testM1, ..., testMn)
       where testMi is obtained from Mi by existentially quantifying
       variables v1...vn. (???)
     *)
     if Param.is_noninterf cur_state.tr_pi_state then
       user_error "Predicates are currently incompatible with non-interference.";
     if !Param.check_pred_calls then check_first_fact cur_state.tr_pi_state vlist f;
     let vlist' = List.map (fun v ->
       let v' = Var (Terms.copy_var v) in
       v.link <- TLink v';
       v') vlist in
     transl_fact (fun f1 cur_state1 ->
       end_destructor_group_no_test_unif (fun cur_state2 ->
         let cur_state3 =
           if cur_state2.is_below_begin || occ.precise || !Param.precise_actions
           then
             begin
               match vlist' with
                 | [] ->
                     { cur_state2 with
                       hypothesis = f1 :: cur_state2.hypothesis;
                       hyp_tags = LetFilterFact :: (LetFilterTag(occ)) :: cur_state2.hyp_tags
                     }
                 | [v] ->
                     let ty = Terms.get_term_type v in
                     let occ_name = get_occurrence_name_for_precise cur_state2 occ in
                     let ev = Param.get_precise_event (Action ty) in
                     Reduction_helper.add_precise_info_occ occ (Action ty);
                     add_in_precise_actions ev;
                     { cur_state2 with
                       hypothesis = f1 :: (Pred(Param.begin_pred,[FunApp(ev,[occ_name;v])])) :: cur_state2.hypothesis;
                       hyp_tags = LetFilterFact :: (LetFilterTag(occ)) :: (PreciseTag(occ)) :: cur_state2.hyp_tags
                     }
                 | _ ->
                     let ty_l = List.map Terms.get_term_type vlist' in
                     let f_tuple = Terms.get_tuple_fun ty_l in
                     let occ_name = get_occurrence_name_for_precise cur_state2 occ in
                     let ev = Param.get_precise_event (Action Param.bitstring_type) in
                     Reduction_helper.add_precise_info_occ occ (Action Param.bitstring_type);
                     add_in_precise_actions ev;
                     { cur_state2 with
                       hypothesis = f1 :: (Pred(Param.begin_pred,[FunApp(ev,[occ_name;FunApp(f_tuple,vlist')])])) :: cur_state2.hypothesis;
                       hyp_tags = LetFilterFact :: (LetFilterTag(occ)) :: (PreciseTag(occ)) :: cur_state2.hyp_tags
                     }
             end
          else
            { cur_state2 with
              hypothesis = f1 :: cur_state2.hypothesis;
              hyp_tags = LetFilterFact :: (LetFilterTag(occ)) :: cur_state2.hyp_tags
            }
         in
         transl_process cur_state3 p
       ) cur_state1
     ) { cur_state with name_params = (List.map2 (fun v v' -> (MVar(v, None), v, v', Always)) vlist vlist') @ cur_state.name_params } (OLetFilter(occ)) f;
     List.iter (fun v -> v.link <- NoLink) vlist;

     (* The else branch *)
     transl_process { cur_state with hyp_tags = LetFilterTag(occ) :: cur_state.hyp_tags } q
 | Event(FunApp(f,l) as lendbegin, (env_args, env), p,occ) ->
      begin
       if !Param.key_compromise == 0 then
         ()
       else
         match l with
           (Var v)::l' ->
             if !Param.key_compromise == 1 then
               v.link <- TLink (Var comp_session_var)
             else
               v.link <- TLink compromised_session
         | _ -> internal_error "Bad event format in queries"
      end;

      let fstatus = Pievent.get_event_status cur_state.tr_pi_state f in

      let get_occurrence_name cur_state =
        let n = Reduction_helper.get_occ_name occ in
        (* Fix now how the name [n] is displayed, to avoid different
	   displays in different clauses/derivations *)
	let n_string = Display.string_of_fsymb n in
        let include_info = Reduction_helper.prepare_include_info env env_args [] in
        let name_params = remove_snd_comp cur_state.name_params in
        let npm = Reduction_helper.extract_name_params_meaning n include_info name_params in
        let np = Reduction_helper.extract_name_params n include_info name_params in
        match n.f_cat with
          | Name r ->
              let nptype = List.map Terms.get_term_type np in
              if fst n.f_type == Param.tmp_type then
                begin
                  n.f_type <- nptype, snd n.f_type;
                  r.prev_inputs_meaning <- npm
                end
              else if Param.get_ignore_types() then
                begin
                  (* When we ignore types, the types of the arguments may vary,
                     only the number of arguments is preserved. *)
                  if List.length (fst n.f_type) != List.length nptype then
                    internal_error ("Name " ^ n_string ^ " has bad arity")
                end
              else
                begin
                  if not (Terms.eq_lists (fst n.f_type) nptype) then
                    internal_error ("Name " ^ n_string ^ " has bad type")
                end;

              FunApp(n,np)
          | _ -> internal_error "[pitransl.ml >> transl_process] Unexpected function category in the translation of events."
      in

      begin
      (* In the specific case where an event does not have an injective status for both begin and end,
         we do not put the begin event in the hypothesis of the end clause. *)
      match fstatus.begin_status with
        | No ->
            (* Even if the event does nothing, the term lendbegin is evaluated *)
            transl_term (
              no_fail (fun cur_state0 pat_begin ->
                end_destructor_group (fun cur_state1 ->
                  let cur_state_output = { cur_state1 with hyp_tags = (BeginEvent(occ)) :: cur_state1.hyp_tags } in
                  begin match fstatus.end_status with
                    | No -> ()
                    | Inj ->
                        let occ_name = get_occurrence_name cur_state_output in
                        output_rule cur_state_output (Pred(Param.end_pred_inj, [occ_name; pat_begin]))
                    | NonInj -> output_rule cur_state_output (Pred(Param.end_pred, [pat_begin]))
                  end;
                  transl_process cur_state_output p
                ) occ cur_state0
              )
            ) cur_state lendbegin
        | NonInj ->
            transl_term_incl_destructor (
              no_fail (fun cur_state0 pat_begin ->
                end_destructor_group (fun cur_state1 ->
                  let cur_state_output = { cur_state1 with hyp_tags = (BeginEvent(occ)) :: cur_state1.hyp_tags } in
                  begin match fstatus.end_status with
                    | No -> ()
                    | Inj ->
                        let occ_name = get_occurrence_name cur_state_output in
                        output_rule cur_state_output (Pred(Param.end_pred_inj, [occ_name; pat_begin]));
                    | NonInj ->
                        output_rule cur_state_output (Pred(Param.end_pred, [pat_begin]))
                  end;

                  let cur_state2 =
                    { cur_state_output with
                      hypothesis = Pred(Param.begin_pred,[pat_begin]) :: cur_state_output.hypothesis;
                      hyp_tags = BeginFact :: cur_state_output.hyp_tags
                    }
                  in
                  transl_process cur_state2 p
                ) occ cur_state0
              )
            ) cur_state (OEvent(occ)) lendbegin
        | Inj ->
            transl_term_incl_destructor (
              no_fail (fun cur_state0 pat_begin ->
                end_destructor_group (fun cur_state1 ->
                  let occ_name = get_occurrence_name cur_state1 in
                  let cur_state_output = { cur_state1 with hyp_tags = (BeginEvent(occ)) :: cur_state1.hyp_tags } in
                  begin match fstatus.end_status with
                    | No -> ()
                    | Inj -> output_rule cur_state_output (Pred(Param.end_pred_inj, [occ_name; pat_begin]))
                    | NonInj -> output_rule cur_state_output (Pred(Param.end_pred, [pat_begin]))
                  end;
                  let cur_state2 =
                    { cur_state_output with
                      hypothesis = Pred(Param.begin_pred_inj,[pat_begin;occ_name]) :: cur_state_output.hypothesis;
                      hyp_tags = BeginFact :: cur_state_output.hyp_tags
                    }
                  in
                  transl_process cur_state2 p
                ) occ cur_state0
              )
            ) { cur_state with is_below_begin = (env_args = None) || cur_state.is_below_begin } (OEvent(occ)) lendbegin
      end
 | Event(_,_,_,_) -> user_error ("Events should be function applications")
 | Insert(t,p,occ) ->
     transl_term (no_fail (fun cur_state1 pat1 ->
       end_destructor_group (fun cur_state2 ->
         output_rule { cur_state2 with
                       hyp_tags = (InsertTag occ) :: cur_state2.hyp_tags
                     } (table_fact cur_state.cur_phase pat1)
           ) occ cur_state1
         )) cur_state t;
      transl_process { cur_state with
                       hyp_tags = (InsertTag occ) :: cur_state.hyp_tags } p
 | Get(pat,t,p,q,occ) ->
      transl_pat Always (fun cur_state1 pat1 ->
        transl_term (no_fail (fun cur_state2 patt ->
          let cur_state2' =
            if cur_state2.is_below_begin || occ.precise || !Param.precise_actions
            then
              begin
                let occ_name = get_occurrence_name_for_precise cur_state2 occ in
                let ev = Param.get_precise_event (Action (Terms.get_term_type pat1)) in
                Reduction_helper.add_precise_info_occ occ (Action (Terms.get_term_type pat1));
                add_in_precise_actions ev;
                { cur_state2 with
                  hypothesis = (table_fact cur_state2.cur_phase pat1) :: (Pred(Param.begin_pred,[FunApp(ev,[occ_name;pat1])])) :: cur_state2.hypothesis;
                  hyp_tags = (GetTag(occ)) :: (PreciseTag(occ)) :: cur_state2.hyp_tags;
                  last_step_unif = (patt, Terms.true_term) :: cur_state2.last_step_unif
                }
              end
            else
              { cur_state2 with
                hypothesis = (table_fact cur_state2.cur_phase pat1) :: cur_state2.hypothesis;
                hyp_tags = (GetTag(occ)) :: cur_state2.hyp_tags;
                last_step_unif = (patt, Terms.true_term) :: cur_state2.last_step_unif
              }
          in
          end_destructor_group (fun cur_state3 -> transl_process cur_state3 p) occ cur_state2'
        )) cur_state1 t
      ) cur_state pat;
      transl_process { cur_state with hyp_tags = GetTagElse(occ) :: cur_state.hyp_tags } q
 | Phase(n,p,_) ->
     transl_process { cur_state with
                      cur_phase = n;
                      input_pred = Param.get_pred (InputP(n));
                      output_pred = Param.get_pred (OutputP(n)) } p
 | Barrier _ | AnnBarrier _ ->
     internal_error "Barriers should not appear here (3)"

(* [rules_for_red] does not need the rewrite rules f(...fail...) -> fail
   for categories Eq and Tuple in [red_rules]. Indeed, clauses
   that come from these rewrite rules are useless:
    1/ clauses att(u1) & ... & att(fail_ti) & ... & att(un) -> att(fail)
    are subsumed by att(fail).
    2/ clauses att(u1) & ... & att(un) & testunif((u1...un), (Gu1...fail...Gun)) -> bad
    disappears because ui can be either a message or fail, and in both cases
    testunif((x1...xn), (...fail...)) is false: if ui is a message, unification
    always fails; if ui is fail, unification always succeeds, independently
    of the value of secrets. *)

let rules_for_red pi_state phase f red_rules =
  List.iter (fun red_rule ->
    let res_pred = Param.get_pred (Attacker(phase, snd f.f_type)) in
    let (hyp, concl, side_c) = Terms.copy_red red_rule in
    add_rule (List.map (att_fact phase) hyp)
      (att_fact phase concl)
      side_c
      (Apply(f, res_pred));
    if Param.is_noninterf pi_state then
      begin
      (* The definition of destructors by rules
                   g(M11...M1n) -> M1
         otherwise g(M21...M2n) -> M2
         otherwise g(M31...M3n) -> M3
         etc
         allows verifying that the same rule applies for any value of the secret
         by just testunif((x1...xn),(M11...M1n)),
                 testunif((x1...xn),(M21...M2n)),
                 testunif((x1...xn),(M31...M3n)), etc. *)
        assert (!Terms.current_bound_vars == []);
        let hyp' = List.map (Terms.generalize_vars_not_in []) hyp in
        Terms.cleanup();

        let thyp = List.map Terms.get_term_type hyp in
        let tuple_fun = Terms.get_tuple_fun thyp in
        let vlist = List.map (Terms.new_var_def_term ~may_fail:true) thyp in
        add_rule
          ((testunif_fact (FunApp(tuple_fun, vlist)) (FunApp(tuple_fun, hyp')))
           :: List.map (att_fact phase) vlist)
          (Pred(bad_pred, []))
          Terms.true_constraints
          (TestApply(f, res_pred))
      end) red_rules

let transl_attacker pi_state my_types phase =
   (* The attacker can apply all functions *)
  List.iter (Terms.clauses_for_function (rules_for_red pi_state phase)) pi_state.pi_funs;
  Hashtbl.iter (fun _ -> Terms.clauses_for_function (rules_for_red pi_state phase)) Terms.tuple_table;

  List.iter (fun t ->
    let att_pred = Param.get_pred (Attacker(phase,t)) in
    let mess_pred = Param.get_pred (Mess(phase,t)) in

    (* The attacker has any message sent on a channel he has *)
    let v = Terms.new_var_def_term t in
    let vc = Terms.new_var_def_term Param.channel_type in
    add_rule [Pred(mess_pred, [vc; v]); att_fact phase vc]
          (Pred(att_pred, [v])) Terms.true_constraints (Rl(att_pred,mess_pred));

    if (!Param.active_attacker) then
      begin
      (* The attacker can send any message he has on any channel he has *)
        let v = Terms.new_var_def_term t in
        let vc = Terms.new_var_def_term Param.channel_type in
        add_rule [att_fact phase vc; Pred(att_pred, [v])]
          (Pred(mess_pred, [vc; v])) Terms.true_constraints (Rs(att_pred, mess_pred))
      end) my_types;


  if Param.is_noninterf pi_state then
    begin
      let att_pred = Param.get_pred (Attacker(phase,Param.channel_type)) in
      let input_pred = Param.get_pred (InputP(phase)) in
      let output_pred = Param.get_pred (OutputP(phase)) in

      (* The attacker can do communications *)
      let vc = Terms.new_var_def_term Param.channel_type in
      add_rule [Pred(att_pred, [vc])] (Pred(input_pred, [vc])) Terms.true_constraints (Ri(att_pred, input_pred));
      let vc = Terms.new_var_def_term Param.channel_type in
      add_rule [Pred(att_pred, [vc])] (Pred(output_pred, [vc])) Terms.true_constraints (Ro(att_pred, output_pred));

      (* Check communications do not reveal secrets *)
      let vc = Terms.new_var_def_term Param.channel_type in
      let vc2 = Terms.new_var_def_term Param.channel_type in
      add_rule [Pred(input_pred, [vc]);
                 Pred(output_pred, [vc2]);
                 testunif_fact vc vc2]
        (Pred(bad_pred, [])) Terms.true_constraints (TestComm(input_pred, output_pred))

    end


(* Weak secrets *)

let weaksecretcst =
  Param.memo_type (fun t ->
      { f_name = Fixed "@weaksecretcst";
        f_type = [], t;
        f_private = true;
        f_options = 0;
        f_cat = Eq [];
        f_initial_cat = Eq []
    })

let att_guess_fact t1 t2 =
  Pred(Param.get_pred (AttackerGuess(Terms.get_term_type t1)), [t1;t2])

(* [rules_for_red_guess] does not need the rewrite rules f(...fail...) -> fail
   for categories Eq and Tuple in [red_rules]. Indeed, clauses
   that come from these rewrite rules are useless:
       1/ if we use twice the same of these rewrite rules, we get
       att(u1,u1') & ... & att(fail_ti, fail_ti) & ... & att(un,un') -> att(fail, fail)
       which is subsumed by att(fail, fail)
       2/ if we use two distinct such rewrite rules, we get
       att(u1,u1') & ... & att(fail_ti, ui') & ... & att(uj, fail_tj) & ... & att(un,un') -> att(fail, fail)
       which is subsumed by att(fail, fail)
       3/ if we use one such rewrite rule and another rewrite rule, we get
       att(u1,M1) & ... & att(fail_ti, Mi) & ... & att(un, Mn) -> att(fail, M')
       which is subsumed by att(fail_ti, x) -> bad (recall that bad subsumes all conclusions)
       Mi are messages, they are not fail nor may-fail variables. *)

let rules_for_red_guess f red_rules =
  List.iter (fun red1 ->
    List.iter (fun red2 ->
      let (hyp1, concl1, side_c1) = Terms.copy_red red1 in
      let (hyp2, concl2, side_c2) = Terms.copy_red red2 in
      add_rule (List.map2 att_guess_fact hyp1 hyp2)
        (att_guess_fact concl1 concl2)
        (Terms.wedge_constraints side_c1 side_c2)
        (Apply(f, Param.get_pred (AttackerGuess(snd f.f_type))))
        ) red_rules
      ) red_rules


let weak_secret_clauses pi_state my_types w =
  add_rule [] (att_guess_fact (FunApp(w, [])) (FunApp(weaksecretcst (snd w.f_type), []))) Terms.true_constraints WeakSecr;

  (* rules_for_function_guess for each function, including tuples *)
  List.iter (Terms.clauses_for_function rules_for_red_guess) pi_state.pi_funs;
  Hashtbl.iter (fun _ -> Terms.clauses_for_function rules_for_red_guess) Terms.tuple_table;

  List.map (fun t ->
    let att_guess = Param.get_pred (AttackerGuess(t)) in

    let x = Terms.new_var_def_term t
    and fail = Terms.get_fail_term t in
    add_rule [Pred(att_guess, [x; fail])] (Pred(Param.bad_pred, [])) Terms.true_constraints (Rfail(att_guess));
    add_rule [Pred(att_guess, [fail; x])] (Pred(Param.bad_pred, [])) Terms.true_constraints (Rfail(att_guess));

    let v = Terms.new_var_def_term t in
    let hyp = [att_fact pi_state.pi_max_used_phase v] in
    let concl = Pred(att_guess, [v; v]) in
    let r = (t, Rule(!nrule, PhaseChange, hyp, concl, Terms.true_constraints)) in
    add_rule hyp concl Terms.true_constraints PhaseChange;

    let v1 = Terms.new_var_def_term t in
    let v2 = Terms.new_var_def_term t in
    let v3 = Terms.new_var_def_term t in
    add_rule [Pred(att_guess, [v1; v2]); Pred(att_guess, [v1; v3])]
      (Pred(Param.bad_pred, [])) (Terms.constraints_of_neq v2 v3) (TestEq(att_guess));

    let v1 = Terms.new_var_def_term t in
    let v2 = Terms.new_var_def_term t in
    let v3 = Terms.new_var_def_term t in
    add_rule [Pred(att_guess, [v2; v1]); Pred(att_guess, [v3; v1])]
      (Pred(Param.bad_pred, [])) (Terms.constraints_of_neq v2 v3) (TestEq(att_guess));

    (* adjust the selection function *)
    let v1 = Terms.new_var_def t in
    let v2 = Terms.new_var_def t in
    add_no_unif (att_guess, [FVar v1; FVar v2])
      (Selfun.never_select_weight+10) [Hypothesis];

    r) my_types


(* Handle key_compromise *)

let comp_output_rule prev_input out_fact =
  assert (!Terms.current_bound_vars == []);
  add_rule (List.map Terms.copy_fact2 prev_input)
    (Terms.copy_fact2 out_fact) Terms.true_constraints LblComp;
  Terms.cleanup()

let comp_fact t =
  Pred(Param.get_pred (Compromise(Terms.get_term_type t)), [t])

let rec comp_transl_process = function
   Nil -> ()
 | NamedProcess(_, _, p) -> comp_transl_process p
 | Par(p,q) -> comp_transl_process p;
               comp_transl_process q
 | Repl (p,_) ->
     comp_transl_process p
 | Restr(n,_,p,_) ->
     begin
       match n.f_cat with
         Name { prev_inputs_meaning = l } ->
           let rec build_params ml tl =
             match (ml, tl) with
               [],[] -> [],[]
             | (m::l),(ty::tyl) ->
                 let (name_params, prev_input) = build_params l tyl in
                 begin
                   match m with
                     MCompSid ->
                       (compromised_session :: name_params, prev_input)
                   | _ ->
                       let v = Var (Terms.new_var ~orig:false (Reduction_helper.meaning_name m) ty) in
                       (v :: name_params, (comp_fact v) :: prev_input)
                 end
             | _ -> Parsing_helper.internal_error "bad length in comp_transl_process"
           in
           let (name_params, prev_input) = build_params l (fst n.f_type) in
           comp_output_rule prev_input
             (comp_fact (FunApp(n, name_params)));
           if List.exists (fun x -> x == compromised_session) name_params then
             comp_output_rule prev_input
               (att_fact 0 (FunApp(n, name_params)))
       | _ -> internal_error "name expected in comp_transl_process"
     end;
     comp_transl_process p
 | Test(t1,p,q,_) ->
     comp_transl_process p;
     comp_transl_process q
 | Input(tc,pat,p,_) ->
     comp_transl_process p
 | Output(tc,t,p,_) ->
     comp_transl_process p
 | Let(pat,t,p,p',_) ->
     comp_transl_process p;
     comp_transl_process p'
 | LetFilter(_,_,p,q,_) ->
     comp_transl_process p;
     comp_transl_process q
 | Event (l,_,p,_) ->
     comp_transl_process p (* TO DO *)
 | Insert (_,p,_) ->
     comp_transl_process p
 | Get (_,_,p,q,_) ->
     comp_transl_process p;
     comp_transl_process q
 | Phase _ ->
     user_error "Phases are incompatible with key compromise.\nKey compromise is itself already a phase scenario"
 | Barrier _ | AnnBarrier _ ->
     internal_error "Barriers should not appear here (4)"

let comp_rules_for_function f =
   match f.f_cat with
     Eq _ | Tuple ->
       let vars = Terms.var_gen (fst f.f_type) in
       add_rule (List.map comp_fact vars)
         (comp_fact (FunApp(f,vars))) Terms.true_constraints
         (Apply(f, Param.get_pred (Compromise(snd f.f_type))))
   | _ -> ()

(* Not declarations *)

let get_not pi_state =
  let not_set = ref [] in
  let add_not f =
    not_set := f ::(!not_set)
  in
  List.iter (function
      QFact(p,_,l) ->
        (* We remove not declarations that contain choice. *)
        if not (List.exists Terms.has_choice l)
        then
          begin
            (* For attacker: not declarations, the not declaration is also
               valid in previous phases, because of the implication
               attacker_p(i):x => attacker_p(i+1):x.
               A similar point holds for table. *)
            begin
              match p.p_info with
                [Attacker(i,t)] ->
                  for j = 0 to i-1 do
                    let att_j = Param.get_pred (Attacker(j,t)) in
                    add_not(Pred(att_j,l))
                  done
              | [Table(i)] ->
                  for j = 0 to i-1 do
                    let table_j = Param.get_pred (Table(j)) in
                    add_not(Pred(table_j,l))
                  done
              | _ -> ()
            end;
            add_not(Pred(p,l))
          end
    | _ -> Parsing_helper.user_error "The only allowed facts in \"not\" declarations are attacker, mess, table, and user-defined predicates."
          ) (pi_state.pi_get_not pi_state);
  !not_set

(* clauses given in the input file and elimtrue declarations *)

let get_elimtrue_initial_clauses pi_state =
  List.iter (fun (hyp1, concl1, constra1, tag1) ->
    TermsEq.close_rule_destr_eq (fun (hyp, concl, constra) ->
      add_rule hyp concl constra tag1) (hyp1, concl1, constra1))
    pi_state.pi_input_clauses;
  let elimtrue_set = ref [] in
  let add_elimtrue f =
    elimtrue_set := f ::(!elimtrue_set)
  in
  List.iter (fun fact ->
    TermsEq.close_rule_destr_eq (fun (hyp, concl, constra) ->
      (* The elimtrue optimization is ignored when the constraint is
         not empty, which may happen if the fact contains destructors
         with side conditions *)
      if Terms.is_true_constraints constra then add_elimtrue (!nrule, concl);
      add_rule hyp concl constra LblClause) ([], fact, Terms.true_constraints))
    pi_state.pi_elimtrue;
  (!elimtrue_set, !red_rules)

(* Compute predicates that queries try to prove *)

(* [add p accu] adds the predicate [p] to [accu] if it is not already present *)
let add p accu =
  if List.memq p accu then accu else p::accu

let add_pred_prove_and_events_event (accu_pred,accu_ev) = function
  | QSEvent(_,_,_,FunApp(ev,_)) | QSEvent2(FunApp(ev,_),_) -> (accu_pred,add ev accu_ev)
  | QSEvent _ | QSEvent2 _ -> internal_error "[pitransl.ml >> add_pred_prove_and_events_for_lemmas_event] Events predicate should have an event symbol."
  | QNeq _ | QEq _ | QGeq _ | QIsNat _ -> (accu_pred,accu_ev)
  | QFact(p,_,_) ->
      match p.p_info with
      | [Attacker(n,t)] -> (add p accu_pred,accu_ev)
      | [Table(n)] -> (add p accu_pred,accu_ev)
      (* AttackerBin, AttackerGuess, TableBin cannot occur since we
	 translate a monoprocess *)
      | _ ->
	  if p.p_prop land Param.pred_BLOCKING == 0 then
	    (add p accu_pred,accu_ev)
	  else
	    (* Blocking predicates do not need to be added,
	       since we cannot resolve on them anyway. *)
	    (accu_pred,accu_ev)

let rec add_pred_prove_and_events_realquery accu = function
  | Before(_, concl) -> add_pred_prove_and_events_concl accu concl

and add_pred_prove_and_events_concl accu = function
  | QTrue | QFalse -> accu
  | QEvent e -> add_pred_prove_and_events_event accu e
  | NestedQuery(Before(hyp,concl)) ->
      let accu' = List.fold_left add_pred_prove_and_events_event accu hyp in
      add_pred_prove_and_events_concl accu' concl
  | QAnd(c1,c2) | QOr(c1,c2) ->
      add_pred_prove_and_events_concl (add_pred_prove_and_events_concl accu c1) c2

let add_pred_prove_and_events_query accu = function
  | PutBegin _ -> accu
  | RealQuery(q,_) ->
      add_pred_prove_and_events_realquery accu q
  | QSecret _ ->
      Parsing_helper.internal_error "QSecret should have been encoded"

let get_pred_prove_and_events ql =
  List.fold_left add_pred_prove_and_events_query ([],[]) ql

(* Global translation *)

let reset() =
  terms_to_add_in_name_params := [];
  nrule := 0;
  red_rules := [];
  no_gen_var := [];
  no_unif_set := [];
  current_precise_actions := []


let transl pi_state =
  (* Reset the record of which occurrence are precise (needed for reconstruction) *)
  Reduction_helper.reset_occ_precise_event ();
  reset();
  let ({ proc = p }, query) = Param.get_process_query pi_state in
  Reduction_helper.reset_name_args p;
  let non_interference = Param.is_noninterf pi_state in
  let my_types = if Param.get_ignore_types() then [Param.any_type] else pi_state.pi_types in
  let (elimtrue_set, clauses_to_initialize_selfun) =
    get_elimtrue_initial_clauses pi_state
  in
  (* We will use clauses_to_initialize_selfun to initialize
     the selection function.
     In particular, when there is a predicate
       member:x,y -> member:x,cons(z,y)
     we would like nounif member:*x,y
     It is important to initialize this very early, so that
     the simplification of the initial rules is performed with
     the good selection function. *)

  for i = 0 to pi_state.pi_max_used_phase do
    transl_attacker pi_state my_types i;
    List.iter (fun t ->
      (* The attacker has fail *)
      add_rule [] (att_fact i (Terms.get_fail_term t)) Terms.true_constraints Init;

      let att_i = Param.get_pred (Attacker(i,t)) in
      let v = Terms.new_var_def t in
      add_no_unif (att_i, [FVar v]) Selfun.never_select_weight [Hypothesis];
      if i > 0 then
        (* It is enough to transmit only messages from one phase to the next
           because the attacker already has fail in all phases. *)
        let w = Terms.new_var_def_term t in
        let att_im1 = Param.get_pred (Attacker(i-1,t)) in
        add_rule [Pred(att_im1, [w])] (Pred(att_i, [w])) Terms.true_constraints PhaseChange
          ) my_types;
    if i > 0 then
      let tbl_i = Param.get_pred (Table(i)) in
      let tbl_im1 = Param.get_pred (Table(i-1)) in
      let w = Terms.new_var_def_term Param.table_type in
      add_rule [Pred(tbl_im1, [w])] (Pred(tbl_i, [w])) Terms.true_constraints TblPhaseChange
  done;

   (* Knowing the free names and creating new names is necessary only in phase 0.
      The subsequent phases will get them by attacker_i(x) -> attacker_{i+1}(x) *)

   (* The attacker has the public free names.
      The non-interference queries have their private flag set. *)
  List.iter (fun ch ->
    if not ch.f_private then
      add_rule [] (att_fact 0 (FunApp(ch, []))) Terms.true_constraints Init) pi_state.pi_freenames;

  List.iter (fun t ->
    (* Clauses for equality *)
    let v = Terms.new_var_def_term t in
    add_rule [] (Pred(Param.get_pred (Equal(t)), [v;v])) Terms.true_constraints LblEq;

    (* The attacker can create new names *)
    let att_pred0 = Param.get_pred (Attacker(0, t)) in
    let v = Terms.new_var_def_term Param.sid_type in
    let new_name_fun = Terms.new_name_fun t in
    (* Fix now how the name [new_name_fun] is displayed, to avoid different
       displays in different clauses/derivations *)
    ignore (Display.string_of_fsymb new_name_fun);
    if non_interference then
      add_rule [att_fact 0 v] (att_fact 0 (FunApp(new_name_fun, [v])))
        Terms.true_constraints (Rn att_pred0)
    else
      add_rule [] (att_fact 0 (FunApp(new_name_fun, [v])))
        Terms.true_constraints (Rn att_pred0);

    if non_interference then
      begin
      (* Rules that derive bad from attacker are necessary only in the last phase.
         Previous phases will get them by attacker_i(x) -> attacker_{i+1}(x) *)

        let att_pred = Param.get_pred (Attacker(pi_state.pi_max_used_phase, t)) in

      (* The attacker can do all equality tests on data he has *)
        let v = Terms.new_var_def_term t in
        let vc = Terms.new_var_def_term t in
        add_rule [Pred(att_pred, [vc]); Pred(att_pred, [v]); testunif_fact vc v]
          (Pred(bad_pred, [])) Terms.true_constraints (TestEq(att_pred));

      end
        ) my_types;


  let att_rule_num =
    (* Weak secrets *)
    match query with
    | WeakSecret w -> weak_secret_clauses pi_state my_types w
    | _ -> []
  in

  (* Remove subsumed clauses and tautologies among attacker clauses,
     to avoid displaying many useless clauses. *)

  if !Param.remove_subsumed_clauses_before_display then
    begin
      let tmp_rules = ref [] in
      (* Store in tmp_rules the rules after removing subsumed rules and tautologies *)
      List.iter (function (hyp, concl, _, _) as rule ->
        (* eliminate tautologies *)
        if List.exists (Terms.equal_facts concl) hyp then () else
        (* eliminate subsumed clauses *)
        if List.exists (fun r -> Rules.implies r rule) (!tmp_rules) then () else
          tmp_rules := rule :: (List.filter (fun r -> not (Rules.implies rule r)) (!tmp_rules))
        ) (!red_rules);
      (* Renumber the rules *)
      red_rules := [];
      nrule := 0;
      List.iter (function
          (hyp', concl', Rule(_, tags, hyp, concl, constra), constra') ->
            red_rules := (hyp', concl', Rule(!nrule, tags, hyp, concl, constra), constra') :: (!red_rules);
            incr nrule
        | _ -> Parsing_helper.internal_error "All clauses should have history Rule(...) at this point"
             ) (!tmp_rules)
    end;

  List.iter (fun ch ->
    match ch.f_cat with
      Name r -> r.prev_inputs <- Some (FunApp(ch, []))
    | _ -> internal_error "should be a name 1")
    pi_state.pi_freenames;
  transl_process
    { tr_pi_state = pi_state;
      hypothesis = []; constra = Terms.true_constraints; unif = []; last_step_unif = [];
      last_step_constra = Terms.true_constraints; neg_success_conditions = ref None;
      name_params = []; repl_count = 0; current_session_id = None;
      is_below_begin = false; cur_phase = 0;
      input_pred = Param.get_pred (InputP(0));
      output_pred = Param.get_pred (OutputP(0));
      hyp_tags = [];
    } p;
  List.iter (fun ch ->
    match ch.f_cat with
      Name r -> r.prev_inputs <- None
    | _ -> internal_error "should be a name 2")
    pi_state.pi_freenames;

  if !Param.key_compromise > 0 then
    begin
      List.iter (fun t ->
        let v = Terms.new_var_def t in
        add_no_unif (Param.get_pred (Compromise(t)), [FVar v]) Selfun.never_select_weight [Hypothesis]
          ) my_types;
      comp_transl_process p;
      List.iter (fun ch ->
        if not ch.f_private then
          add_rule [] (comp_fact (FunApp(ch, []))) Terms.true_constraints Init) pi_state.pi_freenames;
      List.iter comp_rules_for_function pi_state.pi_funs;
      Hashtbl.iter (fun _ -> comp_rules_for_function) Terms.tuple_table
    end;

  List.iter (function ((_,fl) as f,n,for_hyp) ->
    (* We remove nounif that contains choice. *)
    if not (List.exists Terms.has_choice_format fl)
    then
      begin
        if !Param.verbose_term
        then
          begin
            Display.Text.print_string "Declared: nounif ";
            Display.auto_cleanup_display (fun () -> Display.Text.display_fact_format f);
            print_string ("/" ^ (string_of_int (Selfun.weight_of_user_weight n)));
            Display.Text.newline ();
          end;
        add_no_unif f n for_hyp
      end
  ) (pi_state.pi_get_nounif pi_state);

  let solver_kind =
    match query with
      WeakSecret _ ->
        Solve_WeakSecret(att_rule_num, pi_state.pi_max_used_phase)
    | NonInterfQuery secret_vars_with_sets ->
        Solve_Noninterf(secret_vars_with_sets)
    | CorrespQuery _ | CorrespQEnc _ ->
        Solve_Standard
    | _ -> Parsing_helper.internal_error "unsupported query in pitransl"
  in

  let (pred_prove,events_in_queries) =
    match query with
    | WeakSecret _ | NonInterfQuery _ -> ([],[])
    | CorrespQuery(ql,_) -> get_pred_prove_and_events ql
    | CorrespQEnc(qql,_) -> get_pred_prove_and_events (List.map snd qql)
    | _ -> Parsing_helper.internal_error "unsupported query in pitransl"
  in

  let pi_state' =
    { pi_state with
      pi_terms_to_add_in_name_params = Set (!terms_to_add_in_name_params);
      pi_precise_actions = !current_precise_actions
    }
  in
  let horn_state =
    { h_clauses = List.rev (!red_rules);
      h_equations = pi_state.pi_equations;
      h_close_with_equations = false;
      h_not = get_not pi_state;
      h_elimtrue = elimtrue_set;
      h_equiv = pi_state.pi_equivalence_clauses;
      h_nounif = !no_unif_set;
      h_clauses_to_initialize_selfun = clauses_to_initialize_selfun;
      h_solver_kind = solver_kind;
      h_lemmas = [];
      h_pred_prove = pred_prove;
      h_event_in_queries = events_in_queries
	(* lemma assumptions and assumptions of queries proved by induction
	   added in Lemma.transl_lemmas *)
    }
  in
  reset();
  horn_state, pi_state'
