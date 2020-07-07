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

let for_equivalence = ref true

(* Information computed by [transl], to add to the [pi_state] *)

let terms_to_add_in_name_params = ref []
let min_choice_phase = ref max_int

(* Variables local to this module, used to store elements of the t_horn_state we are going to return *)

(** Indicate the number of rules created *)
let nrule = ref 0

(** List of the rules created *)
let red_rules = ref ([] : reduction list)

let no_unif_set = ref ([] : (fact_format * int * nounif_op) list)

let current_precise_actions = ref ([] : funsymb list)

let add_in_precise_actions ev =
  if List.memq ev !current_precise_actions
  then ()
  else current_precise_actions := ev :: !current_precise_actions

let add_no_unif f n for_hyp =
  no_unif_set := (f,n,for_hyp) ::(!no_unif_set)

(*********************************************
          Function For Rules
**********************************************)

let mergelr = function
    Pred(p,[t1;t2]) as x ->
      begin
	match p.p_info with
	  | [AttackerBin(i,t)] ->
	      if i >= (!min_choice_phase) then x else
	      let att1_i = Param.get_pred (Attacker(i,t)) in
	      Terms.unify t1 t2;
	      Pred(att1_i, [t1])
	  | [TableBin(i)] ->
	      if i >= (!min_choice_phase) then x else
	      let tbl1_i = Param.get_pred (Table(i)) in
	      Terms.unify t1 t2;
	      Pred(tbl1_i, [t1])
	  | [InputPBin(i)] ->
	      if i >= (!min_choice_phase) then x else
	      let input1_i = Param.get_pred (InputP(i)) in
	      Terms.unify t1 t2;
	      Pred(input1_i, [t1])
	  | [OutputPBin(i)] ->
	      if i >= (!min_choice_phase) then x else
	      let output1_i = Param.get_pred (OutputP(i)) in
	      Terms.unify t1 t2;
	      Pred(output1_i, [t1])
	  | _ -> x
      end
  | Pred(p,[t1;t2;t3;t4]) as x ->
      begin
	match p.p_info with
	  | [MessBin(i,t)] ->
	      if i >= (!min_choice_phase) then x else
	      let mess1_i = Param.get_pred (Mess(i,t)) in
	      Terms.unify t1 t3;
	      Terms.unify t2 t4;
	      Pred(mess1_i, [t1;t2])
	  | _ -> x
      end
  | x -> x

let rec nb_rule_total = ref 0

let add_rule hyp concl constra tags =
  if !min_choice_phase > 0 then
    begin
      assert (!Terms.current_bound_vars == []);
      try
        let hyp' = List.map mergelr hyp in
        let concl' = mergelr concl in
        let hyp'' = List.map Terms.copy_fact2 hyp' in
        let concl'' = Terms.copy_fact2 concl' in
        let constra'' = Terms.copy_constra2 constra in
        let tags'' =
          match tags with
            ProcessRule(hsl, nl) -> ProcessRule(hsl, List.map Terms.copy_term2 nl)
          | x -> x
        in
        Terms.cleanup();

        begin
          try
            TermsEq.simplify_constraints (fun constra1 ->
              red_rules := (hyp'',concl'',Rule (!nrule, tags'', hyp'', concl'', constra1),constra1) :: !red_rules;
              incr nrule
            ) (fun constra1 ->
              let hyp1 = List.map Terms.copy_fact4 hyp'' in
              let concl1 = Terms.copy_fact4 concl'' in
              let tags1 =
                match tags'' with
                  ProcessRule(hsl, nl) -> ProcessRule(hsl, List.map Terms.copy_term4 nl)
                | x -> x
              in
              red_rules := (hyp1,concl1,Rule (!nrule, tags1, hyp1, concl1, constra1),constra1) :: !red_rules;
              incr nrule
            ) (concl''::hyp'') constra''
          with TermsEq.FalseConstraint -> ()
        end
      with Terms.Unify ->  Terms.cleanup ()
    end
  else
    try
      TermsEq.simplify_constraints (fun constra1 ->
        red_rules := (hyp,concl,Rule (!nrule, tags, hyp, concl, constra1),constra1) :: !red_rules;
        incr nrule
      ) (fun constra1 ->
        let hyp1 = List.map Terms.copy_fact4 hyp in
        let concl1 = Terms.copy_fact4 concl in
        let tags1 =
          match tags with
            ProcessRule(hsl, nl) -> ProcessRule(hsl, List.map Terms.copy_term4 nl)
          | x -> x
        in
        red_rules := (hyp1,concl1,Rule (!nrule, tags1, hyp1, concl1, constra1),constra1) :: !red_rules;
        incr nrule
      ) (concl::hyp) constra
    with TermsEq.FalseConstraint -> ()

(*********************************************
           Preliminary functions
**********************************************)

type transl_state =
  { tr_pi_state : t_pi_state; (* [pi_state] received as input *)

    hypothesis : fact list; (* Current hypotheses of the rule *)
    constra : constraints; (* Current constraints of the rule *)

    name_params : name_param_info list; (* List of parameters of names *)
    name_params_types : typet list;
    repl_count : int; (* Counter for replication *)

    input_pred : predicate;
    output_pred : predicate;
    cur_phase : int; (* Current phase *)

    hyp_tags : hypspec list
  }

let display_transl_state cur_state =
   Printf.printf "\n--- Display current state ---\n";
   Printf.printf "\nHypothesis:\n";
   Display.Text.display_list (Display.Text.WithLinks.fact) " ; " cur_state.hypothesis;
   Printf.printf "\nConstraint:\n";
   Display.Text.WithLinks.constraints cur_state.constra

(* Tools *)

let get_type_from_pattern = function
  | PatVar(v) -> v.btype
  | PatTuple(f,_) -> snd f.f_type
  | PatEqual(t) -> Terms.get_term_type t

(* Creation of fact of attacker', mess' and table. *)

let att_fact phase t1 t2 =
  Pred(Param.get_pred (AttackerBin(phase, Terms.get_term_type t1)), [t1; t2])

let mess_fact phase tc1 tm1 tc2 tm2 =
  Pred(Param.get_pred (MessBin(phase, Terms.get_term_type tm1)), [tc1;tm1;tc2;tm2])

let table_fact phase t1 t2 =
  Pred(Param.get_pred (TableBin(phase)), [t1;t2])

(* Outputing a rule *)

let output_rule cur_state out_fact =
  Terms.auto_cleanup (fun _ ->
    (* Apply the unification *)
    let hyp = List.map Terms.copy_fact2 cur_state.hypothesis in
    let concl = Terms.copy_fact2 out_fact in
    let constra = Terms.copy_constra2 cur_state.constra in
    let name_params = List.map Terms.copy_term2 (Reduction_helper.extract_name_params_noneed cur_state.name_params) in
    Terms.cleanup();

    add_rule hyp concl constra (ProcessRule(cur_state.hyp_tags, name_params))
  )


(* Decide when to optimize mess(c,M) into attacker(M) *)

let optimize_mess cur_state tc =
  !Param.active_attacker &&
  (match tc with
  | FunApp({ f_cat = Name _; f_private = false },_) -> true
  | _ -> false) &&
  ((not (!Param.allow_private_comm_on_public_free_names)) ||
   (not (Reduction_helper.prove_att_phase cur_state.tr_pi_state cur_state.cur_phase)))

(*********************************************
               Translate Terms
**********************************************)

(* [transl_term : (transl_state -> Types.terms -> Types.terms -> unit) -> transl_state -> Types.term -> unit
[transl_term f cur t] represent the translation of [t] in the current state [cur]. The two patterns that [f]
accepts as argument reprensent the result of the evalution
on open term on the left part and right part of [t].

Invariant : All variables should be linked with two closed terms when applied on the translation (due to closed processes)
*)
let rec transl_term next_f cur_state term = match term with
  | Var v ->
      begin
        match  v.link with
          | TLink (FunApp(_,[t1;t2])) -> next_f cur_state t1 t2
          | _ -> internal_error "unexpected link in translate_term (1)"
      end
  | FunApp(f,args) ->
      let transl_red red_rules =
      	transl_term_list (fun cur_state1 term_list1 term_list2 ->
      	  if cur_state.cur_phase < !min_choice_phase then
      	    List.iter (fun red_rule ->
      	      let (left_list1, right1, side_c1) = Terms.auto_cleanup (fun _ -> Terms.copy_red red_rule) in
      	      let (left_list2, right2, side_c2) = Terms.auto_cleanup (fun _ -> Terms.copy_red red_rule) in

      	      Terms.auto_cleanup (fun _ ->
		try
		  List.iter2 Terms.unify term_list1 left_list1;
		  List.iter2 Terms.unify term_list2 left_list2;
      	          let cur_state2 =
      	          { cur_state1 with
	            constra = Terms.wedge_constraints side_c1 (Terms.wedge_constraints side_c2 cur_state1.constra)
		  } in

		  TermsEq.check_constraints cur_state2.constra;
      	          next_f cur_state2 right1 right2
                with Terms.Unify | TermsEq.FalseConstraint -> ()
	      )
	    ) red_rules
	  else
	    List.iter (fun red_rule1 ->
	      List.iter (fun red_rule2 ->
	        (* Fresh rewrite rules *)
	        let (left_list1, right1, side_c1) = Terms.auto_cleanup (fun _ -> Terms.copy_red red_rule1) in
	        let (left_list2, right2, side_c2) = Terms.auto_cleanup (fun _ -> Terms.copy_red red_rule2) in

	        Terms.auto_cleanup (fun _ ->
		  try
		    List.iter2 Terms.unify term_list1 left_list1;
		    List.iter2 Terms.unify term_list2 left_list2;
	            let cur_state2 =
	            { cur_state1 with
	              constra = Terms.wedge_constraints side_c1 (Terms.wedge_constraints side_c2 cur_state1.constra)
		    } in

		    TermsEq.check_constraints cur_state2.constra;
	            next_f cur_state2 right1 right2
		  with Terms.Unify | TermsEq.FalseConstraint-> ()
	        )
	      ) red_rules
	    ) red_rules
	) cur_state args
      in

      match f.f_cat with
      	| Name n ->
      	    (* Parameters of names are now equals on the left and right side *)
      	    begin
      	      match n.prev_inputs with
      	        | Some (name_term) -> next_f cur_state name_term name_term
      	        | _ -> internal_error "unexpected prev_inputs in transl_term"
      	    end
      	| Tuple | Eq _ | Red _ ->
      	    transl_red (Terms.red_rules_fun f)
	| Choice ->
	    begin
	      match args with
	        | [t1;t2] ->
		  transl_term (fun cur_state1 t11 t12 ->
		    transl_term (fun cur_state2 t21 t22 ->
		      next_f cur_state2 t11 t22
		    ) cur_state1 t2
		  ) cur_state t1
		| _ -> Parsing_helper.internal_error "Choice should have two arguments"
	    end
        | BiProj side ->
            begin match args with
              | [t] ->
                  transl_term (fun cur_state1 t1 t2 ->
                    let t = match side with Left -> t1 | Right -> t2 in
                      next_f cur_state1 t t
                  ) cur_state t
              | _ -> assert false
            end
	| Failure -> next_f cur_state (FunApp(f,[]))  (FunApp(f,[]))

	| _ ->
	    Parsing_helper.internal_error "function symbols of these categories should not appear in input terms (pitranslweak)"

(* next_f takes a state and two lists of patterns as parameter *)
and transl_term_list next_f cur_state = function
    [] -> next_f cur_state [] []
  | (a::l) ->
      transl_term (fun cur_state1 p1 p2 ->
	transl_term_list (fun cur_state2 patlist1 patlist2 ->
	  next_f cur_state2 (p1::patlist1) (p2::patlist2)) cur_state1 l) cur_state a

let transl_term_incl_destructor next_f cur_state occ term =
  let may_have_several_patterns = Reduction_helper.transl_check_several_patterns terms_to_add_in_name_params occ term in
  transl_term (fun cur_state1 term1 term2 ->
    if may_have_several_patterns
    then
      let type_t = Terms.get_term_type term1 in
      next_f { cur_state1 with
          name_params = (MUnknown, FunApp(Param.choice_fun type_t,[term1;term2]), Always)::cur_state1.name_params;
          name_params_types = type_t (* this type may not be accurate when types are ignored
					(a type conversion function may have been removed); we
					don't use it since it is not associated to a variable *)
                                     :: cur_state1.name_params_types
        } term1 term2
    else
      next_f cur_state1 term1 term2
  ) cur_state term

let transl_term_list_incl_destructor next_f cur_state occ tl =
  let may_have_several_patterns = List.exists (Reduction_helper.transl_check_several_patterns terms_to_add_in_name_params occ) tl in
  transl_term_list (fun cur_state1 tl_left tl_right ->
    if may_have_several_patterns
    then
      let added_name_params =
        List.map2 (fun t_left t_right ->
          let ty = Terms.get_term_type t_left in
          (MUnknown, FunApp(Param.choice_fun ty,[t_left;t_right]), Always)
        ) tl_left tl_right
      in
      next_f { cur_state1 with
          name_params = added_name_params @ cur_state1.name_params;
          name_params_types = (List.map Terms.get_term_type tl_left) @ cur_state1.name_params_types
        } tl_left tl_right
    else next_f cur_state1 tl_left tl_right
  ) cur_state tl

(*********************************************
              Translate Facts
**********************************************)

let transl_fact next_f cur_state occ = function
  | Pred(p,args) ->
      transl_term_list_incl_destructor (fun cur_state1 args_left args_right ->
        next_f cur_state1 (Pred(p,args_left)) (Pred(p,args_right))
      ) cur_state occ args

(*********************************************
              Translate Patterns
**********************************************)

let rec transl_pat next_f cur_state pattern =
  match pattern with
  | PatVar b ->
      let x_left = Var (Terms.copy_var b)
      and x_right = Var (Terms.copy_var b) in
      b.link <- TLink (FunApp(Param.choice_fun b.btype, [x_left; x_right]));
      next_f cur_state (Var b) [b];
      b.link <- NoLink
  | PatTuple(fsymb,pat_list) ->
      transl_pat_list (fun cur_state2 term_list binder_list ->
        next_f cur_state2 (FunApp(fsymb,term_list)) binder_list
      ) cur_state pat_list
  | PatEqual t -> next_f cur_state t []

and transl_pat_list next_f cur_state = function
  | [] -> next_f cur_state [] []
  | pat::q ->
      transl_pat (fun cur_state2 term binders2 ->
        transl_pat_list (fun cur_state3 term_list binders3  ->
          next_f cur_state3 (term::term_list) (binders2@binders3)
        ) cur_state2 q
      ) cur_state pat

(*********************************************
        Equation of success or failure
**********************************************)

exception Failure_Unify

(* Unify term t with a message variable.
   Raises Unify in case t is fail. *)

let unify_var t =
  let x = Terms.new_var_def_term (Terms.get_term_type t) in
  Terms.unify t x

(* Unify term t with fail *)

let unify_fail t =
  let fail = Terms.get_fail_term (Terms.get_term_type t) in
  Terms.unify fail t

let transl_both_side_succeed nextf cur_state list_left list_right  =
  Terms.auto_cleanup (fun _ ->
    try
      List.iter unify_var list_left;
      List.iter unify_var list_right;
      nextf cur_state
    with Terms.Unify -> ()
  )

let transl_both_side_fail nextf cur_state list_left list_right  =
  List.iter (fun t_left ->
    List.iter (fun t_right ->
      Terms.auto_cleanup (fun _ ->
        try
          unify_fail t_left;
          unify_fail t_right;
          nextf cur_state
        with Terms.Unify -> ()
            )
      ) list_right;
  ) list_left


let transl_one_side_fails nextf cur_state list_failure list_success  =
  List.iter (fun t ->
    Terms.auto_cleanup (fun _ ->
      try
	List.iter unify_var list_success;
      	unify_fail t;
	nextf cur_state
      with Terms.Unify -> ()
	  )
  ) list_failure

(**********************************************************
        Generation of pattern with universal variables
***********************************************************)

let generate_pattern_with_uni_var binders_list term_pat_left term_pat_right =
  let var_pat_l,var_pat_r =
    List.split (
      List.map (fun b ->
        match b.link with
          | TLink(FunApp(_,[Var(x1);Var(x2)])) -> (x1,x2)
          | _ -> internal_error "unexpected link in translate_term (2)"
      ) binders_list
    ) in

  (* TO DO this code may cause internal errors in the presence of patterns
     let (b, =g(b)) = .... when b gets unified with a term that is not a variable.
     However, such patterns are forbidden, so this is not a problem. *)

  let new_var_pat_l = List.map (fun v ->
    match Terms.follow_link (fun b -> Var b) (Var v) with
      |Var v' -> v'
      |_ -> internal_error "unexpected term in translate_process (3)") var_pat_l

  and new_var_pat_r = List.map (fun v ->
    match Terms.follow_link (fun b -> Var b) (Var v) with
      |Var v' -> v'
      |_ -> internal_error "unexpected term in translate_process (4)") var_pat_r in

  let new_term_pat_left = Terms.follow_link (fun b -> Var b) term_pat_left
  and new_term_pat_right = Terms.follow_link (fun b -> Var b) term_pat_right in

  let gen_pat_l = Terms.auto_cleanup (fun _ -> Terms.generalize_vars_in new_var_pat_l new_term_pat_left)
  and gen_pat_r = Terms.auto_cleanup (fun _ -> Terms.generalize_vars_in new_var_pat_r new_term_pat_right) in

  gen_pat_l,gen_pat_r

(*********************************************
              Translate Process
**********************************************)

let get_occurrence_name_for_precise cur_state occ =
  let name_params = cur_state.name_params in
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


let rec transl_process cur_state process =

  (* DEBUG mode *)

  (*Printf.printf "\n\n**********************\n\n";
  Display.Text.display_process_occ "" process;
  display_transl_state cur_state;
  flush_all ();*)

  match process with
  | Nil -> ()
  | Par(proc1,proc2) ->
      transl_process cur_state proc1;
      transl_process cur_state proc2
  | Repl(proc,occ) ->
      (* Always introduce session identifiers ! *)
      let var = Terms.new_var ~orig:false "@sid" Param.sid_type in
      let sid_meaning = MSid (cur_state.repl_count + 1) in
      let cur_state' =
        {
          cur_state with
          repl_count = cur_state.repl_count + 1;
          name_params = (sid_meaning, Var var, Always)::cur_state.name_params;
          name_params_types = Param.sid_type ::cur_state.name_params_types;
          hyp_tags = (ReplTag(occ, Reduction_helper.count_name_params cur_state.name_params)) :: cur_state.hyp_tags
        } in
      transl_process cur_state' proc
  | Restr(name,(args,env),proc,occ) ->
      begin
        match name.f_cat with
          | Name r ->
              let need_list = Reduction_helper.get_need_vars cur_state.tr_pi_state name in
              let include_info = Reduction_helper.prepare_include_info env args need_list in
              let npm = Reduction_helper.extract_name_params_meaning name include_info cur_state.name_params in
              let np = Reduction_helper.extract_name_params name include_info cur_state.name_params in
              let name_prev_type = Reduction_helper.extract_name_params_types name include_info cur_state.name_params cur_state.name_params_types in
              if Terms.eq_lists (fst name.f_type) Param.tmp_type
              then
                begin
                  name.f_type <- name_prev_type, snd name.f_type;
                  r.prev_inputs_meaning <- npm
                end
              else if Param.get_ignore_types() then
                begin
                  (* When we ignore types, the types of the arguments may vary,
                     only the number of arguments is preserved. *)
                  if List.length (fst name.f_type) != List.length name_prev_type then
                    internal_error ("Name " ^ (Display.string_of_fsymb name) ^ " has bad arity")
                end
              else
                begin
                  if not (Terms.eq_lists (fst name.f_type) name_prev_type) then
                    internal_error ("Name " ^ (Display.string_of_fsymb name) ^ " has bad type")
                end;
              if List.length r.prev_inputs_meaning <> List.length np
              then internal_error "prev_inputs_meaning and np should have the same size";

              r.prev_inputs <- Some (FunApp(name, np));
              transl_process cur_state proc;
              r.prev_inputs <- None

          | _ -> internal_error "A restriction should have a name as parameter"
      end
  | Test(term1,proc_then,proc_else,occ) ->
      (* This case is equivalent to :
         Let z = equals(condition,True) in proc_then else proc_else *)

      if proc_else == Nil then
        (* We optimize the case q == Nil.
           In this case, the adversary cannot distinguish the situation
           in which t fails from the situation in which t is false. *)
        transl_term_incl_destructor (fun cur_state1 term1_left term1_right ->
            (* Branch THEN (both sides are true) *)
            Terms.auto_cleanup (fun _ ->
              try
                Terms.unify term1_left Terms.true_term;
                Terms.unify term1_right Terms.true_term;
                transl_process { cur_state1 with
                                 hyp_tags = (TestTag occ)::cur_state1.hyp_tags
                               } proc_then;
              with Terms.Unify -> ()
            );

            if !for_equivalence
            then
              begin
                (* BAD (Left is true / Right is false) *)
                Terms.auto_cleanup (fun _ ->
                  try
                    Terms.unify term1_left Terms.true_term;
                    unify_var term1_right;
                    output_rule { cur_state1 with
                                  constra = { cur_state1.constra with neq = [term1_right,Terms.true_term]::cur_state1.constra.neq };
                                  hyp_tags = (TestUnifTag2 occ)::cur_state1.hyp_tags
                                } (Pred(Param.bad_pred, []));
                  with Terms.Unify -> ()
                );

                (* BAD (Left is true / Right fails) *)
                Terms.auto_cleanup (fun _ ->
                  try
                    Terms.unify term1_left Terms.true_term;
                    unify_fail term1_right;
                    output_rule { cur_state1 with
                                  hyp_tags = (TestUnifTag2 occ)::cur_state1.hyp_tags
                                } (Pred(Param.bad_pred, []));
                  with Terms.Unify -> ()
                );

                (* BAD (Left is false / Right is true) *)
                Terms.auto_cleanup (fun _ ->
                  try
                    Terms.unify term1_right Terms.true_term;
                    unify_var term1_left;
                    output_rule { cur_state1 with
                                  constra = { cur_state1.constra with neq = [term1_left,Terms.true_term]::cur_state1.constra.neq };
                                  hyp_tags = (TestUnifTag2 occ)::cur_state1.hyp_tags
                                } (Pred(Param.bad_pred, []));
                  with Terms.Unify -> ()
                );

                (* BAD (Left fails / Right is true) *)
                Terms.auto_cleanup (fun _ ->
                  try
                    Terms.unify term1_right Terms.true_term;
                    unify_fail term1_left;
                    output_rule { cur_state1 with
                                  hyp_tags = (TestUnifTag2 occ)::cur_state1.hyp_tags
                                } (Pred(Param.bad_pred, []));
                  with Terms.Unify -> ()
                )
              end
        ) cur_state (OTest(occ)) term1
      else
        transl_term_incl_destructor (fun cur_state1 term1_left term1_right ->
          (* Case both sides succeed *)
          transl_both_side_succeed (fun cur_state2 ->
            (* Branch THEN *)
            Terms.auto_cleanup (fun _ ->
              try
                Terms.unify term1_left Terms.true_term;
                Terms.unify term1_right Terms.true_term;
                transl_process { cur_state2 with
                                 hyp_tags = (TestTag occ)::cur_state2.hyp_tags
                               } proc_then;
              with Terms.Unify -> ()
            );

            (* Branch ELSE *)
            transl_process { cur_state2 with
              constra = { cur_state2.constra with neq = [term1_left,Terms.true_term]::[term1_right,Terms.true_term]::cur_state2.constra.neq };
              hyp_tags = (TestTag occ)::cur_state2.hyp_tags
            } proc_else;

            if !for_equivalence
            then
              begin
                (* BAD (Left ok / Right ko) *)
                Terms.auto_cleanup (fun _ ->
                  try
                    Terms.unify term1_left Terms.true_term;
                    output_rule { cur_state2 with
                                  constra = { cur_state2.constra with neq = [term1_right,Terms.true_term]::cur_state2.constra.neq };
                                  hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                                } (Pred(Param.bad_pred, []));
                  with Terms.Unify -> ()
                );

                (* BAD (Left ko / Right ok) *)
                Terms.auto_cleanup (fun _ ->
                  try
                    Terms.unify term1_right Terms.true_term;
                    output_rule { cur_state2 with
                                  constra = { cur_state2.constra with neq = [term1_left,Terms.true_term]::cur_state2.constra.neq };
                                  hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                                } (Pred(Param.bad_pred, []));
                  with Terms.Unify -> ()
                )
              end
          ) cur_state1 [term1_left] [term1_right];

          if !for_equivalence
          then
            begin
              (* Case left side succeed and right side fail *)
              transl_one_side_fails (fun cur_state2 ->
                (* BAD *)
                output_rule { cur_state2 with
                  hyp_tags = TestUnifTag2(occ)::cur_state2.hyp_tags
                } (Pred(Param.bad_pred, []));
              ) cur_state1 [term1_right] [term1_left];

              (* Case right side succeed and left side fail *)
              transl_one_side_fails (fun cur_state2 ->
                (* BAD *)
                output_rule { cur_state2 with
                  hyp_tags = TestUnifTag2(occ)::cur_state2.hyp_tags
                } (Pred(Param.bad_pred, []));
              ) cur_state1 [term1_left] [term1_right]
            end
        ) cur_state (OTest(occ)) term1
  | Let(pat,term,proc_then,proc_else, occ) ->

      transl_term_incl_destructor (fun cur_state1 term_left term_right ->
        transl_pat (fun cur_state2 term_pattern binders_list ->
          transl_term (fun cur_state3 term_pat_left term_pat_right ->
            (* Generate the pattern with universal_variable *)
            let gen_pat_l, gen_pat_r = generate_pattern_with_uni_var binders_list term_pat_left term_pat_right in

            (* Case both sides succeed *)
            transl_both_side_succeed (fun cur_state4 ->
              (* Branch THEN *)
              Terms.auto_cleanup (fun _ ->
                try
                  Terms.unify term_left term_pat_left;
                  Terms.unify term_right term_pat_right;
                  transl_process { cur_state4 with
                    name_params = (List.rev_map
                        (fun b -> (MVar(b, None), (match b.link with
                           | TLink t -> t
                           | _ ->internal_error "unexpected link in translate_term (4)"), IfQueryNeedsIt)
                            ) binders_list) @ cur_state4.name_params;
                    name_params_types = (List.rev_map (fun b -> b.btype) binders_list)@cur_state4.name_params_types;
                    hyp_tags = (LetTag occ)::cur_state4.hyp_tags
                  } proc_then;
                with Terms.Unify -> ()
              );

              (* Branch ELSE *)
              transl_process { cur_state4 with
                constra = { cur_state4.constra with neq = [gen_pat_l,term_left]::[gen_pat_r,term_right]::cur_state4.constra.neq };
                hyp_tags = (LetTag occ)::cur_state4.hyp_tags
              } proc_else;

              if !for_equivalence
              then
                begin
                  (* BAD (Left ok / Right ko) *)
                  Terms.auto_cleanup (fun _ ->
                    try
                      Terms.unify term_left term_pat_left;
                      output_rule { cur_state4 with
                        constra = { cur_state4.constra with neq = [gen_pat_r,term_right]::cur_state4.constra.neq };
                        hyp_tags = TestUnifTag2(occ)::cur_state4.hyp_tags
                      } (Pred(Param.bad_pred, []))
                    with Terms.Unify -> ()
                  );

                  (* BAD (Left ko / Right ok) *)
                  Terms.auto_cleanup (fun _ ->
                    try
                      Terms.unify term_right term_pat_right;
                      output_rule { cur_state4 with
                        constra = { cur_state4.constra with neq = [gen_pat_l,term_left]::cur_state4.constra.neq };
                        hyp_tags = TestUnifTag2(occ)::cur_state4.hyp_tags
                      } (Pred(Param.bad_pred, []));
                    with Terms.Unify -> ()
                  )
                end
            ) cur_state3 [term_pat_left;term_left] [term_pat_right;term_right];

            (* Case both sides fail *)
            transl_both_side_fail (fun cur_state4 ->
              transl_process { cur_state4 with
                hyp_tags = (LetTag occ)::cur_state4.hyp_tags
              } proc_else
            ) cur_state3 [term_pat_left;term_left] [term_pat_right;term_right];

            (* Case left side succeed and right side fail *)
            transl_one_side_fails (fun cur_state4 ->
              (* Branch ELSE *)
              transl_process { cur_state4 with
                constra = { cur_state4.constra with neq = [gen_pat_l,term_left]::cur_state4.constra.neq };
                hyp_tags = (LetTag occ)::cur_state4.hyp_tags
              } proc_else;

              if !for_equivalence
              then
                (* BAD (Left ok) *)
                Terms.auto_cleanup (fun _ ->
                  try
                    Terms.unify term_left term_pat_left;
                    output_rule { cur_state4 with
                      hyp_tags = TestUnifTag2(occ)::cur_state4.hyp_tags
                    } (Pred(Param.bad_pred, []))
                  with Terms.Unify -> ()
                )
            ) cur_state3 [term_pat_right;term_right] [term_pat_left;term_left];

            (* Case right side succeed and left side fail *)
            transl_one_side_fails (fun cur_state4 ->
              (* Branch ELSE *)
              transl_process { cur_state4 with
                constra = { cur_state4.constra with neq = [gen_pat_r,term_right]::cur_state4.constra.neq };
                hyp_tags = (LetTag occ)::cur_state4.hyp_tags
              } proc_else;

              if !for_equivalence
              then
                (* BAD (Left ko) *)
                Terms.auto_cleanup (fun _ ->
                  try
                    Terms.unify term_right term_pat_right;
                    output_rule { cur_state4 with
                      hyp_tags = TestUnifTag2(occ)::cur_state4.hyp_tags
                    } (Pred(Param.bad_pred, []))
                  with Terms.Unify -> ()
                )
            ) cur_state3 [term_pat_left;term_left] [term_pat_right;term_right]
          ) cur_state2 term_pattern
        ) cur_state1 pat
      ) cur_state (OLet(occ)) term
  | LetFilter(_,_,_,_,_) -> user_error "Predicates are currently incompatible with proofs of equivalences."
  | Input(tc,pat,proc,occ) ->
      if optimize_mess cur_state tc then
        begin
            transl_pat (fun cur_state1 term_pattern binders ->
              transl_term (fun cur_state2 term_pat_left term_pat_right ->
                (* Generate the basic pattern variables *)
                let x_right = Terms.new_var_def_term (Terms.get_term_type term_pat_right)
                and x_left = Terms.new_var_def_term (Terms.get_term_type term_pat_left) in

                (* Generate the pattern with universal_variable *)
                let gen_pat_l, gen_pat_r = generate_pattern_with_uni_var binders term_pat_left term_pat_right in

                (* Case both sides succeed *)
                transl_both_side_succeed (fun cur_state3 ->

                  let (hypothesis,hyp_tags) =
                    let fact1 = att_fact cur_state.cur_phase term_pat_left term_pat_right in
                    let tag1 = InputTag occ in
                    if occ.precise || !Param.precise_actions
                    then
                      begin
                        let occ_name = get_occurrence_name_for_precise cur_state3 occ in
                        let precise_info = Action (Terms.get_term_type term_pat_left) in
                        let ev = Param.get_precise_event precise_info in
                        Reduction_helper.add_precise_info_occ occ precise_info;
                        add_in_precise_actions ev;
                        (fact1::Pred(Param.begin2_pred,[FunApp(ev,[occ_name;term_pat_left]);FunApp(ev,[occ_name;term_pat_right])])::cur_state3.hypothesis,
                        tag1  :: PreciseTag(occ) ::cur_state3.hyp_tags
                        )
                      end
                    else
                      (fact1::cur_state3.hypothesis, tag1::cur_state3.hyp_tags)
                  in

                  (* Pattern satisfied in both sides *)
                  transl_process { cur_state3 with
                    name_params = (List.rev_map
                      (fun b -> (MVar(b,None), (match b.link with
                         | TLink t -> t
                         | _ ->internal_error "unexpected link in translate_term (3)"), Always)
                          ) binders) @ cur_state3.name_params;
                    name_params_types = (List.rev_map (fun b -> b.btype) binders)@cur_state3.name_params_types;
                    hypothesis = hypothesis;
                    hyp_tags = hyp_tags
                  } proc;

                  if !for_equivalence
                  then
                    begin
                      (* Pattern satisfied only on left side *)
                      output_rule { cur_state3 with
                        constra = { cur_state3.constra with neq = [gen_pat_r,x_right]::cur_state3.constra.neq };
                        hypothesis = (att_fact cur_state3.cur_phase term_pat_left x_right) :: cur_state3.hypothesis;
                        hyp_tags = TestUnifTag2(occ)::(InputTag occ)::cur_state3.hyp_tags
                      } (Pred(Param.bad_pred, []));

                      (* Pattern satisfied only on right side *)
                      output_rule { cur_state3 with
                        constra = { cur_state3.constra with neq = [gen_pat_l,x_left]::cur_state3.constra.neq };
                        hypothesis = (att_fact cur_state3.cur_phase x_left term_pat_right) :: cur_state3.hypothesis;
                        hyp_tags = TestUnifTag2(occ)::(InputTag occ)::cur_state3.hyp_tags
                      } (Pred(Param.bad_pred, []))
                    end
                ) cur_state2 [term_pat_left] [term_pat_right];

                if !for_equivalence
                then
                  begin
                    (* Case left side succeed and right side fail *)
                    transl_one_side_fails (fun cur_state3 ->
                      output_rule { cur_state3 with
                        hypothesis = (att_fact cur_state3.cur_phase term_pat_left x_right) :: cur_state3.hypothesis;
                        hyp_tags = (TestUnifTag2 occ)::(InputTag occ)::cur_state3.hyp_tags
                      } (Pred(Param.bad_pred, []))
                    ) cur_state2 [term_pat_right] [term_pat_left];

                    (* Case right side succeed and left side fail *)
                    transl_one_side_fails (fun cur_state3 ->
                      output_rule { cur_state3 with
                        hypothesis = (att_fact cur_state3.cur_phase x_left term_pat_right) :: cur_state3.hypothesis;
                        hyp_tags = (TestUnifTag2 occ)::(InputTag occ)::cur_state3.hyp_tags
                      } (Pred(Param.bad_pred, []))
                    ) cur_state2 [term_pat_left] [term_pat_right]
                  end
              ) cur_state1 term_pattern
            ) cur_state pat
        end
      else
        begin

          transl_term_incl_destructor (fun cur_state1 channel_left channel_right ->
            (* Case both channel succeed *)
            transl_both_side_succeed (fun cur_state2 ->
              transl_pat (fun cur_state3 term_pattern binders ->
                transl_term (fun cur_state4 term_pat_left term_pat_right ->
                  (* Generate the basic pattern variables *)
                  let x_right = Terms.new_var_def_term (Terms.get_term_type term_pat_right)
                  and x_left = Terms.new_var_def_term (Terms.get_term_type term_pat_left) in

                  (* Generate the pattern with universal_variable *)
                  let gen_pat_l, gen_pat_r = generate_pattern_with_uni_var binders term_pat_left term_pat_right in

                  (* Case where both pattern succeed *)

                  transl_both_side_succeed (fun cur_state5 ->
                    let cur_state6 = { cur_state5 with
                      name_params = (List.rev_map
                        (fun b -> (MVar(b, None), (match b.link with
                           | TLink t -> t
                           | _ ->internal_error "unexpected link in translate_term (4)"), Always)
                            ) binders) @ cur_state5.name_params;
                      name_params_types = (List.rev_map (fun b -> b.btype) binders)@cur_state5.name_params_types;
                    } in

                    let (hypothesis,hyp_tags) =
                      let fact1 = mess_fact cur_state.cur_phase channel_left term_pat_left channel_right term_pat_right in
                      let tag1 = InputTag occ in
                      if occ.precise || !Param.precise_actions
                      then
                        begin
                          let occ_name = get_occurrence_name_for_precise cur_state5 occ in
                          let precise_info = Action (Terms.get_term_type term_pat_left) in
                          let ev = Param.get_precise_event precise_info in
                          Reduction_helper.add_precise_info_occ occ precise_info;
                          add_in_precise_actions ev;
                          (fact1::Pred(Param.begin2_pred,[FunApp(ev,[occ_name;term_pat_left]);FunApp(ev,[occ_name;term_pat_right])])::cur_state6.hypothesis,
                          tag1  :: PreciseTag(occ) :: cur_state6.hyp_tags
                          )
                        end
                      else
                        (fact1::cur_state6.hypothesis, tag1::cur_state6.hyp_tags)
                    in

                    (* Pattern satisfied in both sides *)
                    transl_process { cur_state6 with
                      hypothesis = hypothesis;
                      hyp_tags = hyp_tags
                    } proc;

                    if !for_equivalence
                    then
                      begin
                        output_rule { cur_state6 with
                          hyp_tags = (InputPTag occ) :: cur_state6.hyp_tags
                        } (Pred(cur_state6.input_pred, [channel_left; channel_right]));

                        (* Pattern satisfied only on left side *)
                        output_rule { cur_state5 with
                          constra = { cur_state5.constra with neq = [gen_pat_r,x_right]::cur_state5.constra.neq };
                          hypothesis = (mess_fact cur_state.cur_phase channel_left term_pat_left channel_right x_right)::cur_state5.hypothesis;
                          hyp_tags = TestUnifTag2(occ)::(InputTag occ)::cur_state5.hyp_tags
                        } (Pred(Param.bad_pred, []));

                        (* Pattern satisfied only on right side *)
                        output_rule { cur_state5 with
                          constra = { cur_state5.constra with neq = [gen_pat_l,x_left]::cur_state5.constra.neq };
                          hypothesis = (mess_fact cur_state.cur_phase channel_left x_left channel_right term_pat_right)::cur_state5.hypothesis;
                          hyp_tags = TestUnifTag2(occ)::(InputTag occ)::cur_state5.hyp_tags
                        } (Pred(Param.bad_pred, []))
                      end

                  ) cur_state4  [term_pat_left] [term_pat_right];

                  if !for_equivalence
                  then
                    begin
                      (*  Case with left pattern succeed but right fail *)

                      transl_one_side_fails (fun cur_state5 ->
                        output_rule { cur_state5 with
                          hypothesis = (mess_fact cur_state.cur_phase channel_left term_pat_left channel_right x_right)::cur_state5.hypothesis;
                          hyp_tags = TestUnifTag2(occ)::(InputTag occ)::cur_state5.hyp_tags
                        } (Pred(Param.bad_pred, []))
                      ) cur_state4 [term_pat_right] [term_pat_left];

                      (*  Case with right pattern succeed but left fail *)

                      transl_one_side_fails (fun cur_state5 ->
                        output_rule { cur_state5 with
                          hypothesis = (mess_fact cur_state.cur_phase channel_left x_left channel_right term_pat_right)::cur_state5.hypothesis;
                          hyp_tags = TestUnifTag2(occ)::(InputTag occ)::cur_state5.hyp_tags
                        } (Pred(Param.bad_pred, []))
                      ) cur_state4 [term_pat_left] [term_pat_right]
                    end
                ) cur_state3 term_pattern
              ) cur_state2 pat
            ) cur_state1 [channel_left] [channel_right];

            if !for_equivalence
            then
              begin
                (* Case left channel succeed and right channel fail *)
                transl_one_side_fails (fun cur_state2 ->
                  output_rule { cur_state2 with
                    hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                  } (Pred(Param.bad_pred, []))
                ) cur_state1 [channel_right] [channel_left];

                (* Case right side succeed and left side fail *)
                transl_one_side_fails (fun cur_state2 ->
                  output_rule { cur_state2 with
                    hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                  } (Pred(Param.bad_pred, []))
                ) cur_state1 [channel_left] [channel_right]
              end
          ) cur_state (OInChannel(occ)) tc
        end
  | Output(term_ch, term, proc, occ) ->
      if optimize_mess cur_state term_ch then
        begin
             transl_term (fun cur_state1 term_left term_right ->
                (* Case both sides succeed *)
                transl_both_side_succeed (fun cur_state2 ->
                  transl_process { cur_state2 with
                      hyp_tags = (OutputTag occ)::cur_state2.hyp_tags
                    } proc;

                  output_rule { cur_state2 with
                      hyp_tags = (OutputTag occ)::cur_state2.hyp_tags
                    } (att_fact cur_state2.cur_phase term_left term_right)
                ) cur_state1 [term_left] [term_right];

                if !for_equivalence
                then
                  begin
                    (* Case left side succeed and right side fail *)
                    transl_one_side_fails (fun cur_state2 ->
                      output_rule { cur_state2 with
                        hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                      } (Pred(Param.bad_pred, []))
                    ) cur_state1 [term_right] [term_left];

                    (* Case right side succeed and left side fail *)
                    transl_one_side_fails (fun cur_state2 ->
                      output_rule { cur_state2 with
                        hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                      } (Pred(Param.bad_pred, []))
                    ) cur_state1 [term_left] [term_right]
                  end
               ) cur_state term
        end
      else
        begin
              transl_term (fun cur_state1 channel_left channel_right ->
                transl_term (fun cur_state2 term_left term_right ->
                  (* Case both sides succeed *)
                  transl_both_side_succeed (fun cur_state3 ->
                    transl_process { cur_state3 with
                        hyp_tags = (OutputTag occ)::cur_state3.hyp_tags
                      } proc;

                    if !for_equivalence
                    then
                      output_rule { cur_state3 with
                          hyp_tags = (OutputPTag occ) :: cur_state3.hyp_tags
                        } (Pred(cur_state3.output_pred, [channel_left; channel_right]));

                    output_rule { cur_state3 with
                        hyp_tags = (OutputTag occ)::cur_state3.hyp_tags
                      } (mess_fact cur_state3.cur_phase channel_left term_left channel_right term_right)
                  ) cur_state2 [channel_left;term_left] [channel_right;term_right];

                  if !for_equivalence
                  then
                    begin
                      (* Case left side succeed and right side fail *)
                      transl_one_side_fails (fun cur_state3 ->
                        output_rule { cur_state3 with
                          hyp_tags = (TestUnifTag2 occ)::cur_state3.hyp_tags
                        } (Pred(Param.bad_pred, []))
                      ) cur_state2 [channel_right;term_right] [channel_left;term_left];

                      (* Case right side succeed and left side fail *)
                      transl_one_side_fails (fun cur_state3 ->
                        output_rule { cur_state3 with
                          hyp_tags = (TestUnifTag2 occ)::cur_state3.hyp_tags
                        } (Pred(Param.bad_pred, []))
                      ) cur_state2 [channel_left;term_left] [channel_right;term_right]
                    end
                ) cur_state1 term
              ) cur_state term_ch
        end
  | Event(FunApp(f,_) as t,_,p,occ) ->
      let fstatus = Pievent.get_event_status cur_state.tr_pi_state f in

      (* Even if the event does nothing, the term t is evaluated *)
      transl_term (fun cur_state1 term_left term_right ->
        (* Case both sides succeed *)
        begin match fstatus.begin_status with
          | No ->
              transl_both_side_succeed (fun cur_state2 ->
                if not !for_equivalence
                then
                  begin match fstatus.end_status with
                    | No -> ()
                    | NonInj ->
                        output_rule { cur_state2 with
                          hyp_tags = BeginEvent(occ) :: cur_state2.hyp_tags
                        } (Pred(Param.end2_pred, [term_left;term_right]));
                    | Inj -> Parsing_helper.internal_error "[pitranslweak.ml >> transl_process] Status of event should not be injective for equivalence queries."
                  end;
                transl_process { cur_state2 with hyp_tags = (BeginEvent(occ)) :: cur_state2.hyp_tags } p
              ) cur_state1 [term_left] [term_right];
          | NonInj ->
              transl_both_side_succeed (fun cur_state2 ->
                if not !for_equivalence
                then
                  begin match fstatus.end_status with
                    | No -> ()
                    | NonInj ->
                        output_rule { cur_state2 with
                          hyp_tags = BeginEvent(occ) :: cur_state2.hyp_tags
                        } (Pred(Param.end2_pred, [term_left;term_right]));
                    | Inj -> Parsing_helper.internal_error "[pitranslweak.ml >> transl_process] Status of event should not be injective for equivalence queries."

                  end;

                let cur_state3 =
                  { cur_state2 with
                    hypothesis = Pred(Param.begin2_pred,[term_left;term_right]) :: cur_state2.hypothesis;
                    hyp_tags = BeginFact :: (BeginEvent(occ)) :: cur_state2.hyp_tags
                  }
                in
                transl_process cur_state3 p
              ) cur_state1 [term_left] [term_right];
          | Inj -> Parsing_helper.internal_error "[pitranslweak.ml >> transl_process] Status of event should not be injective for equivalence queries."
        end;

        if !for_equivalence
        then
          begin
            (* Case left side succeeds and right side fails *)
            transl_one_side_fails (fun cur_state2 ->
              output_rule { cur_state2 with
                hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                } (Pred(Param.bad_pred, []))
            ) cur_state1 [term_right] [term_left];

            (* Case right side succeeds and left side fails *)
            transl_one_side_fails (fun cur_state2 ->
              output_rule { cur_state2 with
                hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                } (Pred(Param.bad_pred, []))
            ) cur_state1 [term_left] [term_right]
          end
      ) cur_state t
  | Event(_,_,_,_) -> user_error ("Events should be function applications")
  | Insert(term,proc,occ) ->
      transl_term (fun cur_state1 term_left term_right ->
        (* Case both sides succeed *)
        transl_both_side_succeed (fun cur_state2 ->
          output_rule { cur_state2 with
            hyp_tags = (InsertTag occ) :: cur_state2.hyp_tags
          } (table_fact cur_state2.cur_phase term_left term_right);

          transl_process { cur_state2 with
            hyp_tags = (InsertTag occ) :: cur_state2.hyp_tags
          } proc;
        ) cur_state1 [term_left] [term_right];

        if !for_equivalence
        then
          begin
            (* Case left side succeeds and right side fails *)
            transl_one_side_fails (fun cur_state2 ->
              output_rule { cur_state2 with
                hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                } (Pred(Param.bad_pred, []))
            ) cur_state1 [term_right] [term_left];

            (* Case right side succeeds and left side fails *)
            transl_one_side_fails (fun cur_state2 ->
              output_rule { cur_state2 with
                hyp_tags = (TestUnifTag2 occ)::cur_state2.hyp_tags
                } (Pred(Param.bad_pred, []))
            ) cur_state1 [term_left] [term_right]
          end
      ) cur_state term
  | Get(pat,term,proc,proc_else,occ) ->
      transl_pat (fun cur_state1 term_pattern binders ->
        transl_term (fun cur_state2 term_pat_left term_pat_right ->

          let x_right = Terms.new_var_def_term (Terms.get_term_type term_pat_right)
          and x_left = Terms.new_var_def_term (Terms.get_term_type term_pat_right) in

          (* Generate the pattern with universal_variable *)
          let gen_pat_l, gen_pat_r = generate_pattern_with_uni_var binders term_pat_left term_pat_right in

          transl_term (fun cur_state3 term_left term_right ->

            (* Case both sides succeed *)
            transl_both_side_succeed (fun cur_state4 ->
              (* Success *)
              Terms.auto_cleanup (fun _ ->
                try
                  Terms.unify term_left Terms.true_term;
                  Terms.unify term_right Terms.true_term;

                  let (hypothesis,hyp_tags) =
                    let fact1 = table_fact cur_state4.cur_phase term_pat_left term_pat_right in
                    let tag1 = GetTag(occ) in
                    if occ.precise || !Param.precise_actions
                    then
                      begin
                        let occ_name = get_occurrence_name_for_precise cur_state4 occ in
                        let precise_info = Action (Terms.get_term_type term_pat_left) in
                        let ev = Param.get_precise_event precise_info in
                        Reduction_helper.add_precise_info_occ occ precise_info;
                        add_in_precise_actions ev;
                        (fact1::Pred(Param.begin2_pred,[FunApp(ev,[occ_name;term_pat_left]);FunApp(ev,[occ_name;term_pat_right])])::cur_state4.hypothesis,
                        tag1  :: PreciseTag(occ) :: cur_state4.hyp_tags
                        )
                      end
                    else
                    (fact1::cur_state4.hypothesis, tag1::cur_state4.hyp_tags)
                  in

                  transl_process { cur_state4 with
                    name_params = (List.rev_map
                      (fun b -> (MVar(b,None), (match b.link with
                         | TLink t -> t
                         | _ ->internal_error "unexpected link in translate_term (6)"), Always)
                          ) binders) @ cur_state4.name_params;
                    name_params_types = (List.rev_map (fun b -> b.btype) binders)@cur_state4.name_params_types;
                    hypothesis = hypothesis;
                    hyp_tags = hyp_tags;
                  } proc;
                with Terms.Unify -> ()
              );

              if !for_equivalence
              then
                begin
                  (* BAD (Left ok / Right ko) *)
                  Terms.auto_cleanup (fun _ ->
                    try
                      Terms.unify term_left Terms.true_term;
                      output_rule { cur_state4 with
                        hypothesis = (table_fact cur_state4.cur_phase term_pat_left term_pat_right) :: cur_state4.hypothesis;
                        constra = { cur_state4.constra with neq = [term_right,Terms.true_term]::cur_state4.constra.neq };
                        hyp_tags = TestUnifTag2(occ)::(GetTag occ)::cur_state4.hyp_tags
                      } (Pred(Param.bad_pred, []));
                    with Terms.Unify -> ()
                  );

                  Terms.auto_cleanup (fun _ ->
                    try
                      Terms.unify term_left Terms.true_term;
                      output_rule { cur_state4 with
                        hypothesis = (table_fact cur_state4.cur_phase term_pat_left x_right) :: cur_state4.hypothesis;
                        constra = { cur_state4.constra with neq = [x_right,gen_pat_r]::cur_state4.constra.neq };
                        hyp_tags = TestUnifTag2(occ)::(GetTag(occ))::cur_state4.hyp_tags
                      } (Pred(Param.bad_pred, []));
                    with Terms.Unify -> ()
                  );

                  (* BAD (Left ko / Right ok) *)
                  Terms.auto_cleanup (fun _ ->
                    try
                      Terms.unify term_right Terms.true_term;
                      output_rule { cur_state4 with
                        hypothesis = (table_fact cur_state4.cur_phase term_pat_left term_pat_right) :: cur_state4.hypothesis;
                        constra = { cur_state4.constra with neq = [term_left,Terms.true_term]::cur_state4.constra.neq };
                        hyp_tags = TestUnifTag2(occ)::(GetTag(occ))::cur_state4.hyp_tags
                      } (Pred(Param.bad_pred, []));
                    with Terms.Unify -> ()
                  );

                  Terms.auto_cleanup (fun _ ->
                    try
                      Terms.unify term_right Terms.true_term;
                      output_rule { cur_state4 with
                        hypothesis = (table_fact cur_state4.cur_phase x_left term_pat_right) :: cur_state4.hypothesis;
                        constra = { cur_state4.constra with neq = [x_left,gen_pat_l]::cur_state4.constra.neq };
                        hyp_tags = TestUnifTag2(occ)::(GetTag(occ))::cur_state4.hyp_tags
                      } (Pred(Param.bad_pred, []))
                    with Terms.Unify -> ()
                  )
                end
            ) cur_state3 [term_pat_left;term_left] [term_pat_right;term_right];

            if !for_equivalence
            then
              begin
                (* Case left side succeed and right side fail *)
                transl_one_side_fails (fun cur_state4 ->
                  (* BAD *)
                  Terms.auto_cleanup (fun _ ->
                    try
                      Terms.unify term_left Terms.true_term;
                      output_rule { cur_state4 with
                        hypothesis = (table_fact cur_state4.cur_phase term_pat_left x_right) :: cur_state4.hypothesis;
                        hyp_tags = TestUnifTag2(occ)::(GetTag(occ))::cur_state4.hyp_tags
                      } (Pred(Param.bad_pred, []))
                    with Terms.Unify -> ()
                  )
                ) cur_state3 [term_pat_right;term_right] [term_pat_left;term_left];

                (* Case right side succeed and left side fail *)
                transl_one_side_fails (fun cur_state4 ->
                  (* BAD *)
                  Terms.auto_cleanup (fun _ ->
                    try
                      Terms.unify term_right Terms.true_term;
                      output_rule { cur_state4 with
                        hypothesis = (table_fact cur_state4.cur_phase x_left term_pat_right) :: cur_state4.hypothesis;
                        hyp_tags = TestUnifTag2(occ)::(GetTag(occ))::cur_state4.hyp_tags
                      } (Pred(Param.bad_pred, []))
                    with Terms.Unify -> ()
                  )
                ) cur_state3 [term_pat_left;term_left] [term_pat_right;term_right]
              end

          ) cur_state2 term
       ) cur_state1 term_pattern
     ) cur_state pat;
     transl_process { cur_state with hyp_tags = GetTagElse(occ) :: cur_state.hyp_tags } proc_else
  | Phase(n,proc,_) ->
      transl_process { cur_state with
                      input_pred = Param.get_pred (InputPBin(n));
                      output_pred = Param.get_pred (OutputPBin(n));
                      cur_phase = n } proc
  | NamedProcess(_,_,p) ->
      transl_process cur_state p
  | Barrier _ | AnnBarrier _ ->
      internal_error "Barriers should not appear here (7)"

(***********************************
	The attacker clauses
************************************)


(* Clauses corresponding to an application of a function

   [rules_Rf_for_red] does not need the rewrite rules f(...fail...) -> fail
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

let rules_Rf_for_red phase f_symb red_rules =
  let result_predicate = Param.get_pred (AttackerBin(phase, snd f_symb.f_type)) in
  if phase < !min_choice_phase then
    (* Optimize generation when no choice in the current phase *)
    List.iter (fun red_rule ->
      let (hyp1, concl1, side_c1) = Terms.copy_red red_rule in

      add_rule (List.map (fun t1 -> att_fact phase t1 t1) hyp1)
      	(att_fact phase concl1 concl1)
      	side_c1
      	(Apply(f_symb, result_predicate))
        ) red_rules
  else
    List.iter (fun red_rule1 ->
      List.iter (fun red_rule2 ->
        let (hyp1, concl1, side_c1) = Terms.copy_red red_rule1
        and (hyp2, concl2, side_c2) = Terms.copy_red red_rule2 in

        add_rule (List.map2 (fun t1 t2 -> att_fact phase t1 t2) hyp1 hyp2)
      	  (att_fact phase concl1 concl2)
      	  (Terms.wedge_constraints side_c1 side_c2)
      	  (Apply(f_symb, result_predicate))
      	  ) red_rules
      	) red_rules

let transl_attacker pi_state my_types phase =

  (* The attacker can apply all functions, including tuples *)
  List.iter (Terms.clauses_for_function (rules_Rf_for_red phase)) pi_state.pi_funs;
  Hashtbl.iter (fun _ -> Terms.clauses_for_function (rules_Rf_for_red phase)) Terms.tuple_table;

  List.iter (fun t ->
    let att_pred = Param.get_pred (AttackerBin(phase,t)) in
    let mess_pred = Param.get_pred (MessBin(phase,t)) in

    (* The attacker has any message sent on a channel he has (Rule Rl)*)
    let v1 = Terms.new_var_def_term t in
    let vc1 = Terms.new_var_def_term Param.channel_type in
    let v2 = Terms.new_var_def_term t in
    let vc2 = Terms.new_var_def_term Param.channel_type in
    add_rule [Pred(mess_pred, [vc1; v1; vc2; v2]); att_fact phase vc1 vc2]
      (Pred(att_pred, [v1; v2])) Terms.true_constraints (Rl(att_pred, mess_pred));

    if (!Param.active_attacker) then
      begin
        (* The attacker can send any message he has on any channel he has (Rule Rs) *)
      	let v1 = Terms.new_var_def_term t in
      	let vc1 = Terms.new_var_def_term Param.channel_type in
      	let v2 = Terms.new_var_def_term t in
      	let vc2 = Terms.new_var_def_term Param.channel_type in
      	add_rule [att_fact phase vc1 vc2; Pred(att_pred, [v1; v2])]
          (Pred(mess_pred, [vc1; v1; vc2; v2])) Terms.true_constraints (Rs(att_pred, mess_pred))
      end;

    (* Clauses for equality *)
    let v = Terms.new_var_def_term t in
    add_rule [] (Pred(Param.get_pred (Equal(t)), [v;v])) Terms.true_constraints LblEq;

    (* Check for destructor failure (Rfailure) *)

    if phase >= !min_choice_phase
    then
      begin
        let x = Terms.new_var_def_term t
        and fail = Terms.get_fail_term t in

        add_rule [Pred(att_pred, [x; fail])] (Pred(Param.bad_pred, [])) Terms.true_constraints (Rfail(att_pred));
        add_rule [Pred(att_pred, [fail; x])] (Pred(Param.bad_pred, [])) Terms.true_constraints (Rfail(att_pred))
      end;

    ) my_types;

  if phase >= !min_choice_phase && !for_equivalence then
    begin
      let att_pred = Param.get_pred (AttackerBin(phase,Param.channel_type)) in
      let input_pred = Param.get_pred (InputPBin(phase)) in
      let output_pred = Param.get_pred (OutputPBin(phase)) in

      (* The attacker can do communications (Rule Ri and Ro)*)
      let vc1 = Terms.new_var_def_term Param.channel_type in
      let vc2 = Terms.new_var_def_term Param.channel_type in
      add_rule [Pred(att_pred, [vc1; vc2])] (Pred(input_pred, [vc1;vc2])) Terms.true_constraints (Ri(att_pred, input_pred));
      let vc1 = Terms.new_var_def_term Param.channel_type in
      let vc2 = Terms.new_var_def_term Param.channel_type in
      add_rule [Pred(att_pred, [vc1; vc2])] (Pred(output_pred, [vc1; vc2])) Terms.true_constraints (Ro(att_pred, output_pred));

      (* Check communications do not reveal secrets (Rule Rcom and Rcom')*)
      let vc = Terms.new_var_def_term Param.channel_type in
      let vc1 = Terms.new_var_def_term Param.channel_type in
      let vc2 = Terms.new_var_def_term Param.channel_type in
      add_rule [Pred(input_pred, [vc; vc1]);
      		 Pred(output_pred, [vc; vc2])]
      	 (Pred(Param.bad_pred, [])) (Terms.constraints_of_neq vc1 vc2)
      	 (TestComm(input_pred, output_pred));

      let vc = Terms.new_var_def_term Param.channel_type in
      let vc1 = Terms.new_var_def_term Param.channel_type in
      let vc2 = Terms.new_var_def_term Param.channel_type in
      add_rule [Pred(input_pred, [vc1; vc]);
      		 Pred(output_pred, [vc2; vc])]
      	(Pred(Param.bad_pred, [])) (Terms.constraints_of_neq vc1 vc2)
      	(TestComm(input_pred, output_pred))

     end

(* Convert terms (possibly with choice) to one term or to
   a pair of terms.
   You need to cleanup links after calling convert_to_1 and
   convert_to_2. *)

let rec convert_to_2 = function
    Var x ->
      begin
	match x.link with
	  TLink (FunApp(_,[t1;t2])) -> (t1,t2)
	| NoLink -> (Var x, Var x)
	| _ -> assert false
      end
  | FunApp(f, [t1;t2]) when f.f_cat == Choice ->
      let (t1',_) = convert_to_2 t1 in
      let (_,t2') = convert_to_2 t2 in
      (t1', t2')
  | FunApp(f, l) ->
      match f.f_cat with
	Name { prev_inputs_meaning = pim } ->
	  let l' = List.map2 (fun t m ->
	    match m with
	      MSid _ | MCompSid | MAttSid ->
		begin
		try
		  convert_to_1 t
		with Terms.Unify ->
		  user_error "In not declarations, session identifiers should be variables."
		end
	    | _ ->
	        (* The arguments of names are always choice, except for session identifiers *)
		let (t1,t2) = convert_to_2 t in
		FunApp(Param.choice_fun (Terms.get_term_type t1), [t1;t2])
	      ) l pim
	  in
	  (FunApp(f, l'), FunApp(f, l'))
      |	_ ->
	  let (l1, l2) = List.split (List.map convert_to_2 l) in
	  (FunApp(f, l1), FunApp(f, l2))

(* convert_to_1 raises Terms.Unify when there is a choice
   that cannot be unified into one term. *)

and convert_to_1 t =
  let (t1, t2) = convert_to_2 t in
  Terms.unify t1 t2;
  t1

let convert_to_2 t =
  let (t1, t2) = convert_to_2 t in
  (Terms.copy_term2 t1, Terms.copy_term2 t2)

let convert_to_1 t =
  Terms.copy_term2 (convert_to_1 t)

(* Convert formats (possibly with choice) to one format or to
   a pair of formats.
   Since nounif cannot be used for a phase earlier than the
   one mentioned in the nounif declaration, it is not essential
   that we can convert a nounif made with choice into a single format.
   Moreover, we do not have a unification for formats ready,
   so we prefer forbidding choice when a single format is needed.
 *)

let rec convertformat_to_1 = function
    FVar x -> FVar x
  | FAny x -> FAny x
  | FFunApp(f, [t1;t2]) when f.f_cat == Choice ->
      Parsing_helper.user_error "choice not allowed in nounif declarations for phases in which choice is not used in the process"
  | FFunApp(f, l) ->
      match f.f_cat with
        Name { prev_inputs_meaning = pim } ->
          (* The arguments of names are always choice, except for
             session identifiers *)
          let l' = List.map2 (fun t m ->
            match m with
              MSid _ | MCompSid | MAttSid ->
                convertformat_to_1 t
            | _ ->
                let t' = convertformat_to_1 t in
                FFunApp(Param.choice_fun (Terms.get_format_type t'), [t';t'])
                ) l pim
          in
          FFunApp(f, l')
      | _ ->
          FFunApp(f, List.map convertformat_to_1 l)

let rec convertformat_to_2 = function
    FVar x -> (FVar x, FVar x)
  | FAny x -> (FAny x, FAny x)
  | FFunApp(f, [t1;t2]) when f.f_cat == Choice ->
      let (t1',_) = convertformat_to_2 t1 in
      let (_,t2') = convertformat_to_2 t2 in
      (t1', t2')
  | FFunApp(f, l) ->
      match f.f_cat with
        Name { prev_inputs_meaning = pim } ->
          (* The arguments of names are always choice, except for
             session identifiers *)
          let l' = List.map2 (fun t m ->
            match m with
              MSid _ | MCompSid | MAttSid ->
                begin
                  match t with
                    FVar x -> assert (x.btype == Param.sid_type); FVar x
                  | FAny x -> assert (x.btype == Param.sid_type); FAny x
                  | _ -> Parsing_helper.user_error "In nounif declarations, session identifiers should be variables."
                end
            | _ ->
                let (t1,t2) = convertformat_to_2 t in
                FFunApp(Param.choice_fun (Terms.get_format_type t1), [t1;t2])
                ) l pim
          in
          (FFunApp(f, l'), FFunApp(f, l'))
      | _ ->
          let (l1, l2) = List.split (List.map convertformat_to_2 l) in
          (FFunApp(f, l1), FFunApp(f, l2))

(* Take into account "not fact" declarations (secrecy assumptions) *)

let get_not pi_state =
  let not_set = ref [] in
  let add_not f =
    not_set := f ::(!not_set)
  in
   List.iter (function
       QFact({ p_info = [Attacker(i,ty)] },_,[t]) ->
      	 (* For attacker: not declarations, the not declaration is also
	    valid in previous phases, because of the implication
	      attacker_p(i):x => attacker_p(i+1):x
	    Furthermore, we have to translate unary to binary not declarations *)
	 for j = 0 to i do
	   if j < !min_choice_phase then
	     (* Phase coded by unary predicate, since it does not use choice *)
	     let att_j = Param.get_pred (Attacker(j,ty)) in
	     try
	       add_not(Pred(att_j,[Terms.auto_cleanup (fun () -> convert_to_1 t)]))
	     with Terms.Unify -> ()
	   else
	     (* Phase coded by binary predicate *)
	     let att2_j = Param.get_pred (AttackerBin(j,ty)) in
	     let (t',t'') = Terms.auto_cleanup (fun () -> convert_to_2 t) in
	     add_not(Pred(att2_j,[t';t'']))
	 done
     | QFact({ p_info = [Mess(i,ty)] } as p,_,[t1;t2]) ->
	 (* translate unary to binary not declarations *)
	 if i < !min_choice_phase then
	   (* Phase coded by unary predicate, since it does not use choice *)
	   try
	     let t1', t2' = Terms.auto_cleanup (fun () ->
	       convert_to_1 t1, convert_to_1 t2)
	     in
	     add_not(Pred(p, [t1'; t2']))
	   with Terms.Unify -> ()
	 else
	   (* Phase coded by binary predicate *)
	   let mess2_i = Param.get_pred (MessBin(i,ty)) in
	   let (t1', t1''), (t2', t2'') = Terms.auto_cleanup (fun () ->
	     convert_to_2 t1, convert_to_2 t2)
	   in
	   add_not(Pred(mess2_i,[t1';t2';t1'';t2'']))
     | QFact({ p_info = [Table(i)] },_,[t]) ->
      	 (* For "table" not declarations, the not declaration is also
	    valid in previous phases, because of the implication
	      table_p(i):x => table_p(i+1):x
	    Furthermore, we have to translate unary to binary not declarations *)
	 for j = 0 to i do
	   if j < !min_choice_phase then
	     (* Phase coded by unary predicate, since it does not use choice *)
	     let table_j = Param.get_pred (Table(j)) in
	     try
	       add_not(Pred(table_j,[Terms.auto_cleanup (fun () -> convert_to_1 t)]))
	     with Terms.Unify -> ()
	   else
	     (* Phase coded by binary predicate *)
	     let table2_j = Param.get_pred (TableBin(j)) in
	     let (t',t'') = Terms.auto_cleanup (fun () -> convert_to_2 t) in
	     add_not(Pred(table2_j,[t';t'']))
	 done
     | _ -> Parsing_helper.user_error "The only allowed facts in \"not\" declarations are attacker, mess, and table predicates (for process equivalences, user-defined predicates are forbidden)."
	   ) (pi_state.pi_get_not pi_state);
  !not_set

(* Compute predicates that queries try to prove *)

(* [add p accu] adds the predicate [p] to [accu] if it is not already present *)
let add p accu =
  if List.memq p accu then accu else p::accu

let add_events_event accu = function
  | QSEvent(_,_,_,FunApp(ev,_)) | QSEvent2(FunApp(ev,_),_) -> add ev accu
  | QSEvent _ | QSEvent2 _ -> internal_error "[pitranslweak.ml >> add_pred_prove_and_events_for_lemmas_event] Events predicate should have an event symbol."
  | QNeq _ | QEq _ | QGeq _ | QIsNat _ | QFact _ -> accu

let rec add_events_realquery accu = function
  | Before(_, concl) -> add_events_concl accu concl

and add_events_concl accu = function
  | QTrue | QFalse -> accu
  | QEvent e -> add_events_event accu e
  | NestedQuery(Before(hyp,concl)) ->
      let accu' = List.fold_left add_events_event accu hyp in
      add_events_concl accu' concl
  | QAnd(c1,c2) | QOr(c1,c2) ->
      add_events_concl (add_events_concl accu c1) c2

let add_events_query accu = function
  | RealQuery(q,_) -> add_events_realquery accu q
  | _ -> Parsing_helper.internal_error "[pitranslweak.ml >> add_events_query] Unexpected query for lemmas."

let get_events ql =
  List.fold_left add_events_query [] ql

(* Global translation *)

let reset() =
  terms_to_add_in_name_params := [];
  min_choice_phase := max_int;
  nrule := 0;
  red_rules := [];
  no_unif_set := [];
  for_equivalence := true;
  current_precise_actions := []

let transl pi_state =
  (* Reset the record of which occurrence are precise (needed for reconstruction) *)
  Reduction_helper.reset_occ_precise_event ();
  reset ();
  let p =
    match pi_state.pi_process_query with
      SingleProcessSingleQuery(p, (ChoiceQuery | ChoiceQEnc _)) -> p.proc
    | SingleProcessSingleQuery(p, (CorrespQEnc _ | CorrespQuery _)) ->
        (* Case when we try to prove lemmas on biprocesses. *)
        for_equivalence := false;
        p.proc
    | _ -> Parsing_helper.internal_error "query not supported by pitranslweak"
  in
  Reduction_helper.reset_name_args p;
  let my_types = if Param.get_ignore_types() then [Param.any_type] else pi_state.pi_types in
  min_choice_phase :=
     begin
       match pi_state.pi_min_choice_phase with
       | Set min_phase -> min_phase
       | Unset -> Parsing_helper.internal_error "Pitranslweak.transl: pi_min_choice_phase should be set"
     end;

  for i = 0 to pi_state.pi_max_used_phase do

    transl_attacker pi_state my_types i;

    List.iter (fun t ->
      (* The attacker has the fail constants *)
      let fail_term = Terms.get_fail_term t in
      add_rule [] (att_fact i fail_term fail_term) Terms.true_constraints Init;

      let att_i = Param.get_pred (AttackerBin(i,t)) in
      if i < !min_choice_phase then
        begin
      	  (* Phase coded by unary predicates *)
      	  let v = Terms.new_var_def t in
      	  let att_i = Param.get_pred (Attacker(i,t)) in
      	  add_no_unif (att_i, [FVar v]) Selfun.never_select_weight [Hypothesis]
      	end
      else
      	begin
      	  (* Phase coded by binary predicates *)
      	  let v1 = Terms.new_var_def t in
      	  let v2 = Terms.new_var_def t in
      	  add_no_unif (att_i, [FVar v1; FVar v2]) Selfun.never_select_weight [Hypothesis]
      	end;

      if i > 0 then
      	(* It is enough to transmit only messages from one phase to the next,
      	   because the attacker already has (fail, fail) in all phases
      	   and the cases (fail, x) and (x, fail) immediately lead
      	   to bad in all cases. *)
      	let w1 = Terms.new_var_def_term t in
      	let w2 = Terms.new_var_def_term t in
      	let att_im1 = Param.get_pred (AttackerBin(i-1,t)) in
      	add_rule [Pred(att_im1, [w1; w2])] (Pred(att_i, [w1; w2])) Terms.true_constraints PhaseChange
    ) my_types;

    if i > 0 then
      let w1 = Terms.new_var_def_term Param.table_type in
      let w2 = Terms.new_var_def_term Param.table_type in
      let tbl_i = Param.get_pred (TableBin(i)) in
      let tbl_im1 = Param.get_pred (TableBin(i-1)) in
      add_rule [Pred(tbl_im1, [w1; w2])] (Pred(tbl_i, [w1; w2])) Terms.true_constraints TblPhaseChange
  done;


  (* Knowing the free names and creating new names is necessary only in phase 0.
     The subsequent phases will get them by attacker'_i(x,y) -> attacker'_{i+1}(x,y) *)

  (* The attacker has the public free names *)
  List.iter (fun ch ->
    if not ch.f_private then
      add_rule [] (att_fact 0 (FunApp(ch, [])) (FunApp(ch, []))) Terms.true_constraints Init) pi_state.pi_freenames;

  List.iter (fun t ->
    (* The attacker can create new names *)
    let v1 = Terms.new_var_def_term Param.sid_type in
    let new_name_fun = Terms.new_name_fun t in
    (* Fix now how the name [new_name_fun] is displayed, to avoid different
       displays in different clauses/derivations *)
    ignore (Display.string_of_fsymb new_name_fun);
    add_rule [] (att_fact 0 (FunApp(new_name_fun, [v1])) (FunApp(new_name_fun, [v1])))
      Terms.true_constraints (Rn (Param.get_pred (AttackerBin(0, t))));

    (* Rules that derive bad are necessary only in the last phase.
       Previous phases will get them by attacker'_i(x,y) -> attacker'_{i+1}(x,y) *)

    let att_pred = Param.get_pred (AttackerBin(pi_state.pi_max_used_phase, t)) in

    (* The attacker can perform equality tests *)
    let v1 = Terms.new_var_def_term t in
    let v2 = Terms.new_var_def_term t in
    let v3 = Terms.new_var_def_term t in
    add_rule [Pred(att_pred, [v1; v2]); Pred(att_pred, [v1; v3])]
    (Pred(Param.bad_pred, [])) (Terms.constraints_of_neq v2 v3) (TestEq(att_pred));

    let v1 = Terms.new_var_def_term t in
    let v2 = Terms.new_var_def_term t in
    let v3 = Terms.new_var_def_term t in
    add_rule [Pred(att_pred, [v2; v1]); Pred(att_pred, [v3; v1])]
    (Pred(Param.bad_pred, [])) (Terms.constraints_of_neq v2 v3) (TestEq(att_pred))
  ) my_types;

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
       | Name r -> r.prev_inputs <- Some (FunApp(ch, []))
       | _ -> internal_error "should be a name 1"
   ) pi_state.pi_freenames;

   (* Translate the process into clauses *)

   Terms.auto_cleanup (fun _ -> transl_process
     { tr_pi_state = pi_state;
       hypothesis = []; constra = Terms.true_constraints;
       name_params = [];  name_params_types = [];
       repl_count = 0;
       input_pred = Param.get_pred (InputPBin(0));
       output_pred = Param.get_pred (OutputPBin(0));
       cur_phase = 0;
       hyp_tags = []
     } p;
   );

   List.iter (fun ch -> match ch.f_cat with
     Name r -> r.prev_inputs <- None
   | _ -> internal_error "should be a name 2")
    pi_state.pi_freenames;

  (* Take into account "nounif" declarations *)

  List.iter (function (f,n,opts) ->
    let fact_format =
      (* translate unary to binary nounif declarations *)
      match f with
        | ({ p_info = [Attacker(i,ty)] } as pred, [t]) ->
            if i < !min_choice_phase then
              (* Phase coded by unary predicate, since it does not use choice *)
              pred, [convertformat_to_1 t]
            else
              (* Phase coded by binary predicate *)
              let att2_i = Param.get_pred (AttackerBin(i,ty)) in
              let (t', t'') = convertformat_to_2 t in
              att2_i, [t';t'']
        | ({ p_info = [Mess(i,ty)] } as pred, [t1;t2]) ->
            if i < !min_choice_phase then
              (* Phase coded by unary predicate, since it does not use choice *)
              pred, [convertformat_to_1 t1; convertformat_to_1 t2]
            else
              (* Phase coded by binary predicate *)
              let mess2_i = Param.get_pred (MessBin(i,ty)) in
              let (t1', t1'') = convertformat_to_2 t1 in
              let (t2', t2'') = convertformat_to_2 t2 in
              mess2_i,[t1';t2';t1'';t2'']
        | ({ p_info = [Table(i)] } as pred, [t]) ->
            if i < !min_choice_phase then
              (* Phase coded by unary predicate, since it does not use choice *)
              pred, [convertformat_to_1 t]
            else
              (* Phase coded by binary predicate *)
              let table2_i = Param.get_pred (TableBin(i)) in
              let (t', t'') = convertformat_to_2 t in
              table2_i, [t';t'']
        | _ -> Parsing_helper.user_error "The only allowed facts in \"nounif\" declarations are attacker, mess, and table predicates (for process equivalences, user-defined predicates are forbidden)."
    in
    if !Param.verbose_term
    then
      begin
        Display.Text.print_string "Declared: nounif ";
        Display.auto_cleanup_display (fun () -> Display.Text.display_fact_format fact_format);
        print_string ("/" ^ (string_of_int (Selfun.weight_of_user_weight n)));
        Display.Text.newline ();
      end;
    add_no_unif fact_format n opts
  ) (pi_state.pi_get_nounif pi_state);

  let events_in_queries = match pi_state.pi_process_query with
    | SingleProcessSingleQuery(_, (ChoiceQuery | ChoiceQEnc _)) -> []
    | SingleProcessSingleQuery(_, CorrespQEnc(qql,_)) -> get_events (List.map snd qql)
    | SingleProcessSingleQuery(_, CorrespQuery(ql,_)) -> get_events ql
    | _ -> Parsing_helper.internal_error "query not supported by pitranslweak"
  in

  let pi_state' =
    { pi_state with
      pi_terms_to_add_in_name_params = Set(!terms_to_add_in_name_params);
      pi_precise_actions = !current_precise_actions
    }
  in
  let horn_state =
    { h_clauses = List.rev (!red_rules);
      h_equations = pi_state.pi_equations;
      h_close_with_equations = false;
      h_not = get_not pi_state;
      h_elimtrue = [];
      h_equiv = pi_state.pi_equivalence_clauses;
      h_nounif = !no_unif_set;
      h_clauses_to_initialize_selfun = [];
      h_solver_kind = Solve_Equivalence;
      h_lemmas = [];
      h_pred_prove = [];
	(* The only queries that we can prove are lemmas, and
           their conclusions can contain only events, blocking predicates,
           and constraints, so nothing needs to be added for those in
           h_pred_prove.
           Lemma assumptions and assumptions of queries proved by induction
	   added in Lemma.transl_lemmas *)
     h_event_in_queries = events_in_queries
    }
  in
  reset();
  horn_state, pi_state'
