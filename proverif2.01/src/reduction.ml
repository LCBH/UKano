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
(* Trace reconstruction
   This version of the trace reconstruction does not exploit the
   order of nodes in the derivation tree.
   *)

(* I use evaluated terms in the "comment" field, when
   the step succeeds, except for "if", because it would display
   "if true" or "if false". In case of failure of the step,
   I use non-evaluated terms, precisely because the evaluation
   often fails. *)

open Types
open Pitypes
open Terms
open Reduction_helper
open Evaluation_helper

let made_forward_step = ref false
let failed_traces = ref 0

let debug_find_io_rule = ref false
let debug_backtracking = ref false
let debug_print s = ()
   (* print_string s; Display.Text.newline() *)

(* This exception is raise when the derivation prevents executing
   a step *)
exception DerivBlocks

(* This exception is used in reduction_nobacktrack
   It is raised after a bunch of reductions to
   to get the final state after these reductions,
   while preventing backtracking on these reductions.*)
exception Reduced of term reduc_state

(* [Terms.auto_cleanup f] runs [f()], removing all links
   created by [f()], whether [f] terminates normally or
   with an exception

   [auto_cleanup_red] is a variant of this function that
   treats the exception [Reduced] specially. Indeed, in most
   cases, when an exception is raised, it is because we
   backtrack, so the links we have set must be removed,
   since we undo the reductions.
   However, the exception [Reduced] is different: for this
   exception, we want to get the final state, so the links
   must be kept.
*)

let auto_cleanup_red f =
  let tmp_bound_vars = !current_bound_vars in
  current_bound_vars := [];
  try
    let r = f () in
    List.iter (fun v -> v.link <- NoLink) (!current_bound_vars);
    current_bound_vars := tmp_bound_vars;
    r
  with
    Reduced s ->
      (* Do not delete the links when the exception [Reduced] is raised.
	 Keep them in [current_bound_vars] so that they are deleted later if needed *)
      current_bound_vars := List.rev_append tmp_bound_vars (!current_bound_vars);
      raise (Reduced s)
  | x ->
    List.iter (fun v -> v.link <- NoLink) (!current_bound_vars);
    current_bound_vars := tmp_bound_vars;
    raise x


(* Set when we should take the else branch of Get but we cannot
   because an element has already been inserted so that the in branch
   is taken. In this case, we try delaying the inserts. *)
let has_backtrack_get = ref false

exception No_result
(* We use the exception Unify for local failure *)

let equal_io_rule (n1, h1, hs1, np1, f1) (n2, h2, hs2, np2, f2) =
  (n1 == n2) &&
    (List.length h1 == List.length h2) &&
    (List.for_all2 Termslinks.equal_facts_with_links h1 h2) &&
    (List.length hs1 == List.length hs2) &&
    (List.for_all2 (=) hs1 hs2) &&
    (List.length np1 == List.length np2) &&
    (List.for_all2 Termslinks.equal_terms_with_links np1 np2) &&
    (Termslinks.equal_facts_with_links f1 f2)

(* Detect various goals *)

let is_table_goal cur_phase t = function
    Pred({p_info = [Table(i)]},[tbl_elem]) ->
      cur_phase <= i &&
      equal_terms_modulo tbl_elem t
       (* If the term tbl_elem is in the table
	  in phase prev_state.current_phase, it will still be in the table in any
	  later phase. *)
  | _ -> false

let is_mess_goal cur_phase tc t = function
    Pred({p_info = [Mess(n,_)]},[tcg;tg]) ->
      (n == cur_phase) &&
      (equal_terms_modulo tg t) &&
      (equal_terms_modulo tcg tc)
      (* SUCCESS! when true *)
  | _ -> false

(* Display clauses *)

let display_rule (n, sons, hsl, nl, concl) =
  print_string ("Rule " ^ (string_of_int n) ^ ": ");
  display_tag hsl nl;
  print_string "  ";
  Display.Text.display_rule (List.map copy_fact2 sons, copy_fact2 concl, Empty concl, Terms.true_constraints);
  Display.Text.newline()

(* Display the trace *)

let noninterftest_to_string = function
    ProcessTest _ -> " process performs a test that may give the attacker some information on the secret"
  | InputProcessTest _ -> "The success or failure of the pattern-matching in the input may give the attacker some information on the secret."
  | ApplyTest _ -> "This gives the attacker some information on the secret."
  | NIFailTest _ -> Parsing_helper.internal_error "Unexpected FailTest for noninterf"
  | CommTest _ -> "The success or failure of the communication may give the attacker some information on the secret."
  | NIEqTest _ -> "This gives the attacker some information on the secret."


let display_trace final_state =
  match !Param.trace_display with
    Param.NoDisplay -> ()
  | Param.ShortDisplay ->
    if !Param.html_output then
      Display.Html.display_labeled_trace final_state
    else
      begin
	if !Param.display_init_state then
	  begin
	    print_string "A more detailed output of the traces is available with\n";
	    if !Param.typed_frontend then
	      print_string "  set traceDisplay = long.\n"
            else
	      print_string "  param traceDisplay = long.\n";
	    Display.Text.newline()
	  end;
	Display.Text.display_labeled_trace final_state
      end
  | Param.LongDisplay ->
    if !Param.html_output then
      begin
	ignore (Display.Html.display_reduc_state Display.term_to_term true final_state);
      end
    else
      begin
        ignore (Display.Text.display_reduc_state Display.term_to_term true final_state) ;
      end
(* Find a clause *)

let find_io_rule next_f hypspeclist hyplist name_params1 var_list io_rules =
  let name_params = extract_name_params_noneed name_params1 in
  let l = List.length hypspeclist in
  let lnp = List.length name_params in
  let lh = List.length hyplist in
  (* Useful for debugging *)
  if !debug_find_io_rule then
    begin
      auto_cleanup (fun () ->
	print_string "Looking for ";
	display_tag hypspeclist name_params;
	print_string "  ";
	Display.Text.display_list Display.Text.WithLinks.fact " & " hyplist;
	Display.Text.newline())
    end;
  let found_terms = ref [] in
  let rec find_io_rule_aux = function
  [] -> raise Unify
    | ((n, sons, hypspeclist2, name_params2, _)::io_rules) ->
      let l2 = List.length hypspeclist2 in
      let lnp2 = List.length name_params2 in
      let lh2 = List.length sons in
      if (l2 < l) || (lnp2 < lnp) || (lh2 < lh)
        || (not (hypspeclist = skip (l2-l) hypspeclist2)) then
	find_io_rule_aux io_rules
      else
        begin
	  let sons3 = skip (lh2-lh) sons in
	  try
	    let name_params' = skip (lnp2-lnp) name_params2 in
	    if not (Param.get_ignore_types()) &&
	      (List.exists2 (fun t1 t2 -> Terms.get_term_type t1 != Terms.get_term_type t2) name_params name_params') then
	      raise Unify;
	    auto_cleanup_red (fun () ->
	      match_modulo_list (fun () ->
	        match_equiv_list (fun () ->
                  let new_found = List.map copy_closed_remove_syntactic var_list in
	          if List.exists (fun old_found ->
	            List.for_all2 equal_terms_modulo old_found new_found) (!found_terms) then
	            raise Unify;
	          found_terms := new_found :: (!found_terms);
		  if !debug_find_io_rule then
		    begin
		      auto_cleanup (fun () ->
			print_string "Found ";
			Display.Text.display_list Display.Text.WithLinks.term ", " new_found;
			Display.Text.newline())
		    end;
	          next_f new_found) sons3 hyplist
              ) name_params name_params'
	    )
          with Unify -> find_io_rule_aux io_rules
        end
  in
  find_io_rule_aux io_rules


let term_evaluation_name_params occ t name_params =
  let may_have_several_types = reduction_check_several_patterns occ in
  let t' = term_evaluation_fail t in
  if may_have_several_types then
    (t', (MUnknown,t',Always) :: name_params)
  else
    (t', name_params)

(* [included_fact_lists fl1 f2l] is true when
   the list [fl1] is included in [fl2]. *)
let included_fact_lists fl1 fl2 =
  List.for_all (fun f1 ->
    List.exists (fun f2 ->
      Termslinks.equal_facts_with_links f1 f2
	) fl2
      ) fl1

(* [add_assumed_false l1 l2] returns the list [l2]
   with [l1] added. Each element of [l1] and [l2] is
   a list of facts [f1; ...; fn] representing
   [not(f1 && ... && fn)]. The function removes elements
   that are implied by other elements. *)
let rec add_assumed_false l1 l2 =
  match l1 with
    [] -> l2
  | fl1::r1 ->
      (* [l2] is [l2] with element [fl1] added,
	 but useless elements removed. *)
      let l2' =
	if List.exists (fun fl2 ->
	  included_fact_lists fl2 fl1) l2
	then
	  (* If a list included in [fl1] is already present,
             [fl1] is useless *)
	  l2
	else
	  (* Otherwise, we add [fl1], but remove useless elements
             from [l2], that is, those that contain [fl1] *)
	  fl1::(List.filter (fun fl2 ->
	    not (included_fact_lists fl1 fl2)) l2)
      in
      add_assumed_false r1 l2'

let update_corresp_goals_with_injectivity goal_list =
  List.map (function Pred(p,_) as pred_goal ->
    if p == Param.end_pred || p == Param.end_pred_inj
    then EventGoal(rev_name_subst_fact pred_goal,None)
    else Fact(rev_name_subst_fact pred_goal, None, false)
  ) goal_list

(*
  Terms come with a recipe that explains how to compute them.
  Recipes may contain variables (especially in prepared_attacker_rules)
  which are later instantiated by putting links in these variables.
  Copies of the recipes are not made immediately after creating the links,
  so these links remain when the trace progresses; they are removed
  in case of backtrack (by auto_cleanup_red).
  Not making too many copies is important for speed in complex
  examples such as ffgg.
  Copies of recipes are made before adding a term to public,
  so that recipes in public do not contain links.
  They are also made before using a term in an input.
*)

let rec get_copy_sid = function
  | [] -> []
  | (MSid _, sid, Always)::q -> sid::(get_copy_sid q)
  | _::q -> get_copy_sid q

(* Occurence name *)

let get_occurrence_name_for_precise occ name_params =
  let (np,npm) =
    List.fold_right (fun (m,t,_) (acc_np,acc_npm) -> match m with
      | MSid _ -> (t::acc_np,m::acc_npm)
      | _ -> (acc_np,acc_npm)
    ) name_params ([],[])
  in
  let n = Reduction_helper.get_occ_name occ in
  match n.f_cat with
    | Name r ->
        let n' = FunApp(n,np) in
        FunApp(add_name_for_pat n',[])
    | _ -> Parsing_helper.internal_error "[reduction.ml >> get_occurrence_name_for_precise] Unexpected case."

(* Do reductions that do not involve interactions
   f takes as input
   - a boolean indicating whether the attacker knowledge has changed
   - the new state

   When the goal is reached, do_red_nointeract returns the final state.
   Otherwise, raises an exception No_result.
*)

let rec do_red_nointeract f prev_state n =
  let (proc, name_params, occs, facts, cache_info) =
    List.nth prev_state.subprocess n in
  let new_goal_opt =
    match prev_state.goal with
      NonInterfGoal(ProcessTest((TestUnifTag occ_goal)::occs_goal, name_params_goal, loc)) ->
      (* Note: when a clause concludes bad_pred and is a ProcessRule, then its first tag
         is TestUnifTag *)
        begin
	  match proc with
	    Test(_,_,_,occ) | Let(_,_,_,_,occ) | Input(_,_,_,occ) | Output(_,_,_,occ)
	  | LetFilter(_,_,_,_,occ) | Event(_,_,_,occ) | Insert(_,_,occ) | Get(_,_,_,_,occ) ->
	    let l = List.length name_params in
	    let lg = List.length name_params_goal in
	    if (occ == occ_goal) &&
	      (occs = occs_goal) &&
	      (l <= lg) &&
	      (List.for_all2 equal_terms_modulo (extract_name_params_noneed name_params) (skip (lg-l) name_params_goal))
	    then
	      Some(NonInterfGoal(ProcessTest((TestUnifTag occ_goal)::occs_goal, name_params_goal, Some (n, List.nth prev_state.subprocess n))))
	    else
	      None
	  | _ -> None
        end
    | _ -> None
  in
  match new_goal_opt with
    Some new_goal -> (* SUCCESS! *) { prev_state with goal = new_goal }
  | None ->
    match proc with
      Nil -> debug_print "Doing Nil";
        made_forward_step := true;
        f false (do_rnil prev_state n)
    | Par(p,q) ->
      debug_print "Doing Par";
      made_forward_step := true;
      do_red_nointeract (fun new_att_know cur_state2 ->
        do_red_nointeract (fun new_att_know2 cur_state3 ->
          f (new_att_know || new_att_know2) cur_state3)
          cur_state2 n
      ) { prev_state with
	subprocess = add_at n (p, name_params, occs, facts, Nothing)
	  (replace_at n (q, name_params, occs, facts, Nothing)
             prev_state.subprocess);
        comment = RPar(n);
        previous_state = Some prev_state } (n+1)
    | Restr(na,(args,env),p,occ) ->
      debug_print "Doing Restr";
      made_forward_step := true;
      let need_list = get_need_vars (!Param.current_state) na in
      let include_info = prepare_include_info env args need_list in
      let nt = FunApp(na, extract_name_params na include_info name_params) in
      let n' = FunApp(add_name_for_pat nt,[]) in
      let p' = process_subst p na n' in
      begin
	do_red_nointeract f { prev_state with
	  subprocess = replace_at n (p', name_params, occs, facts, Nothing) prev_state.subprocess;
          comment = RRestr(n, na, n');
          previous_state = Some prev_state } n
      end
    | Let(pat,t,p,q,occ) ->
      debug_print "Doing Let";
      made_forward_step := true;
      let new_occs = (LetTag occ) :: occs in
      begin
        try
          auto_cleanup_red (fun () ->
            let (t', name_params') = term_evaluation_name_params (OLet(occ)) t name_params in
            match_pattern pat t';
            let p' = copy_process p in
            let name_params'' = update_name_params IfQueryNeedsIt name_params' pat in
            do_red_nointeract f { prev_state with
	      subprocess = replace_at n (p', name_params'', new_occs, facts, Nothing) prev_state.subprocess;
              comment = RLet_In(n, pat, t');
              previous_state = Some prev_state } n
	  )
        with Unify ->
          do_red_nointeract f { prev_state with
	    subprocess = replace_at n (q, name_params, new_occs, facts, Nothing) prev_state.subprocess;
            comment = RLet_Else(n, pat, t);
            previous_state = Some prev_state } n
      end
    | Test(t,p,q,occ) ->
      debug_print "Doing Test";
      made_forward_step := true;
      begin
	try
          auto_cleanup_red (fun () ->
	    let new_occs = (TestTag occ) :: occs in
            let (t', name_params') = term_evaluation_name_params (OTest(occ)) t name_params in
            if equal_terms_modulo t' Terms.true_term then
	      do_red_nointeract f
		{ prev_state with
	          subprocess = replace_at n (p, name_params', new_occs, facts, Nothing) prev_state.subprocess;
                  comment = RTest_Then(n, t);
                  previous_state = Some prev_state } n
            else
              do_red_nointeract f
		{ prev_state with
	          subprocess = replace_at n (q, name_params', new_occs, facts, Nothing) prev_state.subprocess;
                  comment = RTest_Else(n, t);
                  previous_state = Some prev_state } n
	  )
        with Unify ->
	  f false { prev_state with
	    subprocess = remove_at n prev_state.subprocess;
            comment = RTest_Remove(n, t, DestrFails);
            previous_state = Some prev_state }
      end
    | Output(tc,t,p,occ) ->
      begin
      let new_goal_opt =
	if cache_info != Nothing then
	  None (* Was already tested and failed before; will still fail if tested again *)
	else
	  match prev_state.goal with
	  | NonInterfGoal(CommTest(tin,tout,loc)) ->
	    if equal_terms_modulo_eval tc tout then
	      begin
	        (match is_in_public prev_state.public tin with
                  Some (recipe) ->
		    Some(NonInterfGoal(CommTest(tin,tout,Some (LocAttacker recipe, LocProcess(n, List.nth prev_state.subprocess n)))))
	        | None -> (* find a process that does some input on tin *)
		  try
		    let (n',p') =
		      findi (function
		    (Input(tc,_,_,_),_,_,_,_) -> equal_terms_modulo_eval tc tin
		      | _ -> false
		      ) prev_state.subprocess
		    in
		    Some(NonInterfGoal(CommTest(tin,tout,Some (LocProcess(n',p'), LocProcess(n, List.nth prev_state.subprocess n)))))
                  with Not_found ->
		    None)
	      end
	    else None
	  | _ -> None
      in
      match new_goal_opt with
	Some new_goal -> { prev_state with goal = new_goal }
      | None ->
	  debug_print "Doing Output";
          (* For passive attackers, do red I/O only,
	     but still evaluate the arguments of the output *)
	  if not (!Param.active_attacker) then
	    match cache_info with
	      InputInfo _ | GetInfo _ -> Parsing_helper.internal_error "Should not have input/get info for an output!"
	    | OutputInfo _ -> f false prev_state (* Arguments already evaluated *)
	    | Nothing ->
	      try
	        auto_cleanup_red (fun () ->
        	  let tc' = term_evaluation_fail tc in
                  let tclist = decompose_term_rev (new_var ~orig:false "Useless" (Terms.get_term_type t), tc') in
		  let t' = term_evaluation_fail t in
		  f false { prev_state with
                    subprocess = replace_at n (Output(tc',t',p,occ), name_params, occs, facts,
					       (OutputInfo(tclist, prev_state.public)))
                      prev_state.subprocess }
		)
              with Unify ->
	        f false { prev_state with
                  subprocess = remove_at n prev_state.subprocess;
                  comment = ROutput_Remove(n, tc, t, DestrFails);
                  previous_state = Some prev_state }
	  else
            (* For active attackers, one can output on public channels *)
	    begin
	      let new_occs = (OutputTag occ) :: occs in
	      match cache_info with
	        InputInfo _ | GetInfo _ -> Parsing_helper.internal_error "Should not have input/get info for an output!"
	      | OutputInfo(tclist, oldpub) ->
	        let tclist' = update_term_list oldpub prev_state.public tclist in
                if tclist' = [] then
	          begin
                    made_forward_step := true;
		    let (new_recipe, prev_state') = add_public prev_state t in
		    do_red_nointeract (if prev_state.public == prev_state'.public then f else
		        (fun mod_public cur_state -> f true cur_state))
               	      { prev_state' with
                        subprocess = replace_at n (p, name_params, new_occs, facts, Nothing) prev_state.subprocess;
                        comment = ROutput_Success(n, tc, new_recipe, t);
		        previous_state = Some prev_state } n
		  end
	        else
		  f false { prev_state with
                    subprocess = replace_at n (proc, name_params, occs, facts,
					       (OutputInfo(tclist', prev_state.public)))
                      prev_state.subprocess }
	      | Nothing ->
	        try
		  auto_cleanup_red (fun () ->
		    let tc' = term_evaluation_fail tc in
		    let tclist = decompose_term_rev (new_var ~orig:false "Useless" (get_term_type tc'), tc') in
		    let tclist' = remove_first_in_public prev_state.public tclist in
		    let t' = term_evaluation_fail t in
		    if tclist' = [] then
		      begin
                        made_forward_step := true;
		        let (new_recipe, prev_state') = add_public prev_state t' in
		        do_red_nointeract (if prev_state.public == prev_state'.public then f else
		            (fun mod_public cur_state -> f true cur_state))
			  { prev_state' with
                            subprocess = replace_at n (p, name_params, new_occs, facts, Nothing) prev_state.subprocess;
			    comment = ROutput_Success(n, tc', new_recipe, t');
			    previous_state = Some prev_state } n
		      end
		    else
		      f false { prev_state with
                        subprocess = replace_at n (Output(tc',t',p,occ), name_params, occs, facts,
						   (OutputInfo(tclist', prev_state.public)))
                          prev_state.subprocess }
		  )
                with Unify ->
	          f false { prev_state with
                    subprocess = remove_at n prev_state.subprocess;
                    comment = ROutput_Remove(n, tc, t, DestrFails);
                    previous_state = Some prev_state }
	    end
      end
    | Event(FunApp(fs,l) as t,(env_args, env),p,occ) ->
      debug_print "Doing Event";
      made_forward_step := true;
      let fstatus = Pievent.get_event_status (!Param.current_state) fs in
      let do_end prev_state name_params' new_occs new_facts t =
        let n_subprocess = replace_at n (p, name_params', new_occs, new_facts, Nothing) prev_state.subprocess in
        let sid_list = get_copy_sid name_params' in

        let (new_goal, event_in_goal, success) =
          update_corresp_goal prev_state.goal (Some (occ,List.rev sid_list))
            (function
                | Pred(pr,[t']) -> pr == Param.end_pred && equal_terms_modulo_eval t t'
                | Pred(pr,[occ_n';t']) ->
		    pr == Param.end_pred_inj && equal_terms_modulo_eval t t' &&
		    ((* When the event appears with t = t' and pr = Param.end_pred_inj,
			it must have injective end status, so [get_occ_name]
			has been called at this occurrence in pitransl.ml,
			and in particular, [prev_inputs_meaning] is correctly set. *)
                    let occ_n = get_occ_name occ in
		    let include_info = prepare_include_info env env_args [] in
		    let nt = FunApp(occ_n,extract_name_params occ_n include_info name_params') in
		    let n' = FunApp(add_name_for_pat nt,[]) in
		    equal_terms_modulo_eval n' occ_n')
                | _ -> false)
        in
        let new_state =
          { prev_state with
            subprocess = n_subprocess;
            comment = REvent_Success(n,t,event_in_goal);
            events = t::prev_state.events;
            goal = new_goal;
            previous_state = Some prev_state }
        in
        if success then
          new_state
        else
          do_red_nointeract f new_state n
      in
      begin
        try
          match fstatus.begin_status with
            No ->
              (* Check that the argument of the event can be evaluated but otherwise ignore it *)
              let t' = term_evaluation_fail t in
              let new_occs = (BeginEvent (occ)) :: occs in
              do_end prev_state name_params new_occs facts t'
          | NonInj ->
              auto_cleanup_red (fun () ->
                let (t', name_params') = term_evaluation_name_params (OEvent(occ)) t name_params in
                let new_occs' = (BeginEvent (occ)) :: occs in
                let new_occs = BeginFact :: new_occs' in
                let new_facts = (Pred(Param.begin_pred,[t'])) :: facts in
                find_io_rule (fun _ ->
                  do_end prev_state name_params' new_occs new_facts t'
                ) new_occs' facts name_params' [] prev_state.io_rule
              )
          | Inj ->
              auto_cleanup_red (fun () ->
                let occ_n = get_occ_name occ in
                let include_info = prepare_include_info env env_args [] in
                let nt = FunApp(occ_n,extract_name_params occ_n include_info name_params) in
                let n' = FunApp(add_name_for_pat nt,[]) in
                let (t', name_params') = term_evaluation_name_params (OEvent(occ)) t name_params in
                let new_occs' = (BeginEvent (occ)) :: occs in
                let new_occs = BeginFact :: new_occs' in
                let new_facts = (Pred(Param.begin_pred_inj,[t';n'])) :: facts in
		try
                  find_io_rule (fun _ ->
                    do_end prev_state name_params' new_occs new_facts t'
                      ) new_occs' facts name_params' [] prev_state.io_rule
		with Unify -> raise DerivBlocks
              )
        with Unify ->
          f false { prev_state with
              subprocess = remove_at n prev_state.subprocess;
              comment = REvent_Remove(n, t, DestrFails);
              previous_state = Some prev_state }
	| DerivBlocks ->
          f false { prev_state with
              subprocess = remove_at n prev_state.subprocess;
              comment = REvent_Remove(n, t, Blocks);
              previous_state = Some prev_state }
      end
    | LetFilter(bl, Pred(pr,l), p, q, occ) ->
      debug_print "Doing LetFilter";
      made_forward_step := true;
      let letfilter_succeeds = ref false in
      begin
        try
          let vars_types = List.map (fun v -> v.btype) bl in
          let vars_bl = List.map (fun b -> Var b) bl in
          auto_cleanup_red (fun () ->
            let (l', name_params') = term_evaluation_letfilter (OLetFilter(occ)) l
              ((List.map2 (fun v v' -> (MVar(v, None), v', Always)) bl vars_bl) @ name_params)
            in
            let fact' = Pred(pr,l') in
            let (new_occs,new_facts) = match vars_types with
              | [vtype] when Reduction_helper.exists_specific_precise_events_of_occ occ (Action vtype) ->
                  let occ_n = get_occurrence_name_for_precise occ name_params' in
                  let ev_precise = Param.get_precise_event (Action vtype) in
                  (LetFilterTag occ) :: (PreciseTag(occ)) :: occs, [Pred(pr,l'); (Pred(Param.begin_pred,[FunApp(ev_precise,[occ_n;List.hd vars_bl])]))]
              | _ when Reduction_helper.exists_specific_precise_events_of_occ occ (Action Param.bitstring_type) ->
                  let occ_n = get_occurrence_name_for_precise occ name_params' in
                  let f_tuple = Terms.get_tuple_fun vars_types in
                  let ev_precise = Param.get_precise_event (Action Param.bitstring_type) in
                  (LetFilterTag occ) :: (PreciseTag(occ)) :: occs, [Pred(pr,l'); (Pred(Param.begin_pred,[FunApp(ev_precise,[occ_n;FunApp(f_tuple,vars_bl)])]))]
              | _ -> (LetFilterTag occ) :: occs, [Pred(pr,l')]
            in
            try
              find_io_rule (fun terms_bl ->
                let new_facts' = (List.map TermsEq.copy_remove_syntactic_fact new_facts) @ facts in
                List.iter2 (fun b term_b ->
                  Terms.link b (TLink term_b)) bl terms_bl;
                let name_params'' = List.map
                  (function (m,t,always) -> (m,copy_closed_remove_syntactic t,always)) name_params'
                in
                let p' = auto_cleanup (fun () -> copy_process p) in
                letfilter_succeeds := true;
                    (* Allow choosing a different result for letfilter when search fails *)
                try
                  do_red_nointeract f { prev_state with
                    subprocess = replace_at n (p', name_params'', LetFilterFact :: new_occs, new_facts', Nothing) prev_state.subprocess;
                    comment = RLetFilter_In(n, bl, terms_bl, Pred(pr,l));
                    previous_state = Some prev_state } n
                with No_result -> raise Unify
              ) new_occs (new_facts @ facts) name_params' vars_bl prev_state.io_rule
            with Unify ->
              if !letfilter_succeeds then raise No_result else
                  (* it should be ok to query the fact with names instead of patterns?
                     Note: there may be an overapproximation here. For instance, when the depth of terms is limited, Rules.query_goal_std may answer that the fact is derivable when in fact it is not. It just leads to considering that LetFilter blocks, so it remains sound. *)
              let letfilterclauses = auto_cleanup (fun () -> Rules.query_goal_std [] fact') in

              (* When the predicate is for natural number, we only have to check if the clauses exist. *)
              let false_required_for_else_branch =
                List.map (fun { rule = (hyp, _, _, _); _ } ->
                  (* [filtered_hyp] contains a list of blocking facts [f1; ...; fn].
                     Assuming [not (f1 && ... && fn)], the clause [(hyp, _, _, _)]
                     cannot be applied to derive [fact']. *)
                  let filtered_hyp =
                    List.filter (function
                        Pred(p,l) when p.p_prop land Param.pred_BLOCKING != 0 ->
                          (* When [Pred(p,l)] unifies with an element of [prev_state.hyp_not_matched],
                             I assumed that [Pred(p,l)] was true, so I cannot assume that it is
                             false as well. *)
                          List.for_all (function (_, Pred(p',l')) when p == p' ->
                            begin
                            try
                              Terms.auto_cleanup (fun () ->
                                TermsEq.unify_modulo_list (fun () -> false) l l')
                            with Unify -> true
                            end
                            | _ -> true
                            ) prev_state.hyp_not_matched
                      | _ -> false) hyp
                  in
                  (* when [filtered_hyp == []], [fact'] may be derivable from the clauses,
                     since I cannot prove or assume that the hypothesis of the clause is false =>
                     LetFilter may succeed but not allowed by the derivation tree =>
                     consider that LetFilter blocks *)
                  if filtered_hyp == [] then raise DerivBlocks;
                  filtered_hyp
                  ) letfilterclauses
              in
              do_red_nointeract f { prev_state with
                subprocess = replace_at n (q, name_params, new_occs, facts, Nothing) prev_state.subprocess;
                comment = RLetFilter_Else(n, bl, Pred(pr,l));
                assumed_false = add_assumed_false false_required_for_else_branch prev_state.assumed_false;
                previous_state = Some prev_state } n
          )
        with Unify ->
          f false { prev_state with
            subprocess = remove_at n prev_state.subprocess;
            comment = RLetFilter_Remove(n, bl, Pred(pr,l), DestrFails);
            previous_state = Some prev_state }
        | DerivBlocks ->
          f false { prev_state with
            subprocess = remove_at n prev_state.subprocess;
            comment = RLetFilter_Remove(n, bl, Pred(pr,l), Blocks);
            previous_state = Some prev_state }

      end
    | Repl(p,occ) ->
      debug_print "Doing Repl";
      made_forward_step := true;
      let sid = new_var ~orig:false "sid" Param.sid_type in
      let new_occs = (ReplTag (occ,count_name_params name_params))::occs in
      let copy_number = ref 0 in
      let new_state = ref { prev_state with
	subprocess = remove_at n prev_state.subprocess;
        comment = RRepl(n,0);
        previous_state = Some prev_state }
      in
      begin
        try
          auto_cleanup (fun () ->
            find_io_rule (function
          [sid_pat] ->
	            (* TO DO this assumes no key compromise
	               (which is coherent with the current usage of this module)
	               With key compromise, we may need two session ids. *)
            let p' = auto_cleanup (fun () -> copy_process p) in
            incr copy_number;
            new_state := { !new_state with
              subprocess =
	        if Param.is_noninterf (!Param.current_state) then
		  (* With non-interference, we need to add the session id in facts *)
		  add_at n (p', (MSid 0,sid_pat,Always)::name_params, new_occs, (Pred(Param.get_pred (Attacker(!new_state.current_phase, Param.sid_type)), [sid_pat]))::facts, Nothing) !new_state.subprocess
		else
		  add_at n (p', (MSid 0,sid_pat,Always)::name_params, new_occs, facts, Nothing) !new_state.subprocess;
            };
            raise Unify
            | _ -> Parsing_helper.internal_error "Repl case, reduction.ml"
	    ) new_occs facts ((MSid 0,Var sid,Always)::name_params) [Var sid] prev_state.io_rule
          )
        with Unify ->
          let rec do_red_copies b ncopies state =
            if ncopies < 0 then
              f b state
            else
              do_red_nointeract (fun b' s -> do_red_copies (b||b') (ncopies-1) s) state (n+ncopies)
	  in
	  do_red_copies false ((!copy_number)-1)
            { !new_state with
              comment = RRepl(n,!copy_number)
            }
      end
    | Input(tc,_,_,_) ->
      begin
	match prev_state.goal with
	| NonInterfGoal(CommTest(tin,tout,loc)) ->
	  if equal_terms_modulo_eval tc tin then
            begin
              (match is_in_public prev_state.public tout with
              | Some (recipe) ->
		begin
                  let new_goal = NonInterfGoal(CommTest(tin,tout,Some (LocProcess(n, List.nth prev_state.subprocess n), LocAttacker (recipe)))) in
		  { prev_state with goal = new_goal }
		end
              | None ->
		try
		  let (n',p') =
		    findi (function
		  (Output(tc,_,_,_),_,_,_,_) -> equal_terms_modulo_eval tc tout
		    | _ -> false
		    ) prev_state.subprocess
		  in
		  let new_goal = NonInterfGoal(CommTest(tin,tout,Some (LocProcess(n, List.nth prev_state.subprocess n), LocProcess(n',p')))) in
		  { prev_state with goal = new_goal }
		with Not_found ->
		  f false prev_state)
	    end
	  else f false prev_state
	| _ -> f false prev_state
      end
    | Insert(t,p,occ) ->
      debug_print "Doing Insert";
      let new_occs = (InsertTag occ) :: occs in
      let new_element_inserted = ref false in
      begin
	try
	  auto_cleanup_red (fun () ->
	    let t' = term_evaluation_fail t in
	    let already_in = List.exists (equal_terms_modulo t') prev_state.tables in
	    new_element_inserted := not already_in;
	    made_forward_step := true;
	    let (new_goal, insert_in_goal, success) =
	      update_corresp_goal prev_state.goal None
		(is_table_goal prev_state.current_phase t')
	    in
	    let new_state =
	      { prev_state with
                subprocess = replace_at n (p, name_params, new_occs, facts, Nothing) prev_state.subprocess;
	        tables = if already_in then prev_state.tables else t' :: prev_state.tables;
		comment = RInsert_Success(n, t', insert_in_goal);
                goal = new_goal;
		previous_state = Some prev_state }
	    in
	    if success then
	      new_state
	    else
	      do_red_nointeract f new_state n
	  )
        with Unify ->
	  f false { prev_state with
            subprocess = remove_at n prev_state.subprocess;
            comment = RInsert_Remove(n, t, DestrFails);
            previous_state = Some prev_state }
	| No_result ->
	     (* The attack reconstruction failed after doing the insert.
	        Try not doing it, in case that allows executing the else branch of a Get. *)
	  if (!has_backtrack_get) && (!new_element_inserted) then
	    f false prev_state
	  else
	    raise No_result
      end
    | NamedProcess(name,l,p) ->
      debug_print "Doing NamedProcess";
      do_red_nointeract f { prev_state with
        subprocess = replace_at n (p, name_params, occs, facts, Nothing) prev_state.subprocess;
        comment = RNamedProcess(n, name, l);
        previous_state = Some prev_state } n
    | _ -> f false prev_state

(* Test success when the knowledge of the attacker has changed *)

let test_success cur_state' =
  try
    match cur_state'.goal with
      CorrespGoal(l) ->
	let new_goal =
	  CorrespGoal (List.map (fun goal ->
	    match goal with
	      Fact(Pred({p_info = [Attacker(i,_)]},[t]) as fact, _, false) when cur_state'.current_phase <= i ->
                (* compute the new recipe_lst
                   if t is known by the attacker in phase cur_state'.current_phase,
		   it will still be known in phase i *)
		(match is_in_public cur_state'.public t with
		| Some recipe -> Fact(fact, Some [recipe], true)
		| _ -> goal)
	    | Fact(Pred({p_info = [Mess(i,_)]},[tc;t]) as fact, _, false) when cur_state'.current_phase <= i ->
                (* compute the new recipe_lst
		   if tc and t are known by the attacker in phase cur_state'.current_phase,
		   they will still be known in phase i,
		   so the attacker will be able to send t on tc in phase i *)
		(match is_in_public cur_state'.public t, is_in_public cur_state'.public tc with
		| Some recipe1, Some recipe2 -> Fact(fact, Some [recipe1; recipe2], true)
		| _ -> goal)
	    | _ -> goal
		  ) l)
	in
	(is_success_corresp_goal new_goal,
	 {cur_state' with goal = new_goal})

    | WeakSecrGoal(l,t,w1,w2) ->
        (* compute the new recipe_lst *)
      let lopt = is_in_public_list cur_state'.public (List.map (fun (x,y,z) -> x) l) in
      (match lopt with
      | Some l' ->
          let l'' = List.map2 (fun (x,y,z) recipe -> (x,y,Some recipe)) l l' in
	  let new_goal = WeakSecrGoal(l'',t,w1,w2) in
          (true, {cur_state' with goal = new_goal})
      | None -> (false, cur_state'))

    | NonInterfGoal(NIEqTest((t1, _),(t2, _))) ->
      (match is_in_public cur_state'.public t1, is_in_public cur_state'.public t2 with
      | Some recipe1, Some recipe2 ->
	  let new_goal = NonInterfGoal(NIEqTest((t1, Some recipe1),(t2, Some recipe2))) in
          (true, {cur_state' with goal = new_goal})
      | _ -> (false, cur_state'))

    | NonInterfGoal(ApplyTest(f, l)) ->
      let lopt = is_in_public_list cur_state'.public (List.map (fun (x, y) -> x) l) in
      (match lopt with
      | Some l' ->
          let l'' = List.map2 (fun (x, y) recipe -> (x, Some recipe)) l l' in
	  let new_goal = NonInterfGoal(ApplyTest(f, l'')) in
          (true, {cur_state' with goal = new_goal})
      | None -> (false, cur_state'))

    | NonInterfGoal(CommTest(tin,tout,loc)) ->
      let rin =
        match is_in_public cur_state'.public tin with
          Some (recipe) -> Some (LocAttacker recipe)
        | None ->
      	  try
	    let (n,p) =
	      findi (function
	    (Input(tc,_,_,_),_,_,_,_) -> equal_terms_modulo_eval tc tin
	      | _ -> false
	      ) cur_state'.subprocess
            in
	    Some (LocProcess(n,p))
	  with Not_found ->
            None
      in
      let rout =
	match is_in_public cur_state'.public tout with
          Some (recipe) -> Some (LocAttacker (recipe))
        | None ->
	  try
	    let (n,p) =
	      findi (function
	    (Output(tc,_,_,_),_,_,_,_) -> equal_terms_modulo_eval tc tout
	      | _ -> false
	      ) cur_state'.subprocess
	    in
	    Some (LocProcess(n,p))
          with Not_found ->
	    None
      in
      (match rin,rout with
        Some lin, Some lout ->
	  let new_goal =  NonInterfGoal(CommTest(tin,tout,Some(lin,lout))) in
          (true, {cur_state' with goal = new_goal})
      | _ -> (false, cur_state'))

    | _ -> false, cur_state'
  with Unify ->
    false, cur_state'

(* let test_success = Profile.f1 "test_success" test_success *)

let end_if_success next_f cur_state =
  let (success, cur_state') = test_success cur_state in
  if success then cur_state' else next_f cur_state'

(* Normalize the state after a reduction *)

let rec find_possible_outputs f cur_state n seen_list = function
[] -> f cur_state
  | (Output(tc,t,p,out_occ) as proc, name_params, occs, facts, cache_info)::rest_subprocess when (!Param.active_attacker) ->
    let tclist' =
      match cache_info with
	InputInfo _ | GetInfo _ -> Parsing_helper.internal_error "Should not have input/get info for an output!"
      | OutputInfo(tclist, oldpub) ->
	update_term_list oldpub cur_state.public tclist
      | Nothing ->
	let tclist = decompose_term_rev ((new_var ~orig:false "Useless" (Terms.get_term_type tc)), tc) in
	remove_first_in_public cur_state.public tclist
    in
    let seen_list' = (proc, name_params, occs, facts, OutputInfo(tclist', cur_state.public)) :: seen_list in
    if tclist' = [] then
      do_red_nointeract (fun change_pub cur_state2 ->
        if change_pub then
          end_if_success (find_possible_outputs_rec f) cur_state2
        else
          find_possible_outputs f cur_state2 0 [] cur_state2.subprocess
      ) { cur_state with subprocess = List.rev_append seen_list' rest_subprocess } n
    else
      find_possible_outputs f cur_state (n+1) seen_list' rest_subprocess
  | sub_proc::rest_subprocess -> find_possible_outputs f cur_state (n+1) (sub_proc::seen_list) rest_subprocess

and find_possible_outputs_rec f cur_state3 =
  find_possible_outputs f cur_state3 0 [] cur_state3.subprocess

(*      When the process number n has been changed *)

let normal_state f change_pub cur_state n =
  do_red_nointeract (fun change_pub2 cur_state2 ->
    if change_pub || change_pub2 then
      end_if_success (find_possible_outputs_rec f) cur_state2
    else f cur_state2
  ) cur_state n

(*      When two processes have been changed, numbers n1 and n2 *)

let normal_state2 f change_pub cur_state n1 n2 =
  let n1',n2' = if n1 < n2 then n1,n2 else n2,n1 in
  do_red_nointeract (fun change_pub2 cur_state2 ->
    do_red_nointeract (fun change_pub3 cur_state3 ->
      if change_pub || change_pub2 || change_pub3 then
        end_if_success (find_possible_outputs_rec f) cur_state3
      else f cur_state3
    ) cur_state2 n1'
  ) cur_state n2'

(*      When all processes have been changed *)

let normal_state_all f change_pub cur_state =
  let rec do_red_all change_pub2 cur_state2 n =
    if n < 0 then
      if change_pub2 then
	end_if_success (find_possible_outputs_rec f) cur_state2
      else
	f cur_state2
    else
      do_red_nointeract (fun change_pub3 cur_state3 ->
	do_red_all (change_pub2 || change_pub3) cur_state3 (n-1)
      ) cur_state2 n
  in
  do_red_all change_pub cur_state (List.length cur_state.subprocess - 1)

(* Initial attacker knowledge *)

let rec public_build l =
  match l with
  | [] -> []
  | h::l' ->
    if not h.f_private then
      let t = (FunApp(h,[])) in
      (t, t)::(public_build l')
    else
      public_build l'

(* Initialize the rule lists *)

let rec init_rule state tree =
  match tree.desc with
    FHAny | FEmpty | FRemovedWithMaxHyp ->
      begin
        let generate_state () =
          let fact = rev_name_subst_fact tree.thefact in
          if List.exists (fun (_, fact') -> Terms.equal_facts fact fact') state.hyp_not_matched then
            (* Do not add [fact] in [state.hyp_not_matched] if it is already present *)
            state
          else
            { state with
              hyp_not_matched = (None, fact)::state.hyp_not_matched }
        in
        match tree.thefact with
        | Pred(p,_) when p == Param.begin_pred || p == Param.begin_pred_inj -> state
        | Pred(p, [t]) when p.p_prop land Param.pred_ATTACKER != 0 ->
        (* Note that the predicate "comp" is not pred_ATTACKER and
           could be handled similarly, but anyway it does not
           appear here since key compromise is incompatible with
           attack reconstruction. *)
          begin
            let t' = rev_name_subst t in
            match t' with
              FunApp({ f_cat = Name _; f_private = false },[]) ->
                { state with public = (t', t') :: state.public }
            | _ ->
            (* Public contains terms, not patterns
               -> translate the pattern into a term.
               If the translation fails because a name is not in the table, we have to stop. *)
              if (not (is_in_public state.public t' = None)) then
                state
              else
              (* I introduce a variable for the recipe here,
                 and use it when displaying hyp_not_matched.
                 Note: it is important that the term t' is never a tuple.
                 Otherwise, it would be decomposed later, and the link
                 between the recipe in public and the one in hyp_not_matched
                 would be lost. *)
                let recipe = Var (new_var ~orig:false "~M" (Terms.get_term_type t')) in
                { state with
                  public = (recipe, t') :: state.public;
                  hyp_not_matched = (Some recipe, Pred(p,[t']))::state.hyp_not_matched }
          end
        | _ -> generate_state ()

      end
  | FRemovedWithProof _ -> state
  | FRule (n, tags, constra, sons,_,_) ->
    let rec init_sons_rule state1 = function
      | [] ->
	begin
	  match tags with
	    ProcessRule (hsl,nl) ->
	      let new_io_rule = (n, List.map (fun t -> rev_name_subst_fact t.thefact) sons,
			         hsl, rev_name_subst_list nl, rev_name_subst_fact tree.thefact)
	      in
	      { state1 with io_rule = new_io_rule::state1.io_rule }
          (*
            if not (List.exists (equal_io_rule new_io_rule) state1.io_rule) then
            { state1 with io_rule = new_io_rule::state1.io_rule }
            else
            state1
          *)
	  |	Apply (f, {p_info = [AttackerGuess(_)]}) ->
	    (* Clauses attacker_guess_pred will be handled when looking for the goal *)
	    state1
          | Apply (f,_) when f.f_cat != Tuple ->
	    begin
	      let (p,c) =
		match tree.thefact with
		  Pred(p,[t]) -> (p,rev_name_subst t)
		| _ -> Parsing_helper.internal_error "unexpected Apply clause"
              in
	      let h = List.map (function
	      { thefact = Pred(_,[t]) } -> (new_var ~orig:false "~X" (get_term_type t), rev_name_subst t)
	        |	_ -> Parsing_helper.internal_error "unexpected Apply clause") sons
              in
              let h' = decompose_list_rev h in
	      (* recipe_concl is the recipe used to compute the conclusion from the hypotheses *)
              let recipe_concl = FunApp(f, (List.map (fun (x, y) -> Var x) h)) in
	      {state1 with prepared_attacker_rule = (p, h', (recipe_concl, c))::state1.prepared_attacker_rule};

	    end
          | Rn _ ->
            begin
	      match tree.thefact with
                Pred(p, [t]) ->
                  let t' = rev_name_subst t in
                  { state1 with prepared_attacker_rule = (p, [], (t', t'))::state1.prepared_attacker_rule }
              | _ ->
		Parsing_helper.internal_error "Rule Rn should conclude p(name)"
	    end
	  | _ -> state1
	end
      | h::t ->
        let state1' = init_rule state1 h in
	init_sons_rule state1' t
    in
    init_sons_rule state sons
  | FEquation son -> init_rule state son


(* Handle reductions i/o and in *)

(* Perform an input on a public channel (Res In) *)

let success_input cur_state n new_occs name_params' mess_term output_loc =
  match cur_state.goal with
    NonInterfGoal(InputProcessTest((TestUnifTag occ_goal)::occs_goal, name_params_goal, mess_term_goal, loc)) ->
    (* Note: when a clause concludes bad_pred and is a ProcessRule, then its first tag
       is TestUnifTag *)
      begin
        match new_occs with
	  InputTag occ :: _ ->
	    let l = List.length name_params' in
	    let lg = List.length name_params_goal in
	    if (occ == occ_goal) &&
	      (new_occs = occs_goal) &&
	      (l <= lg) &&
	      (equal_terms_modulo mess_term mess_term_goal) &&
	      (List.for_all2 equal_terms_modulo (extract_name_params_noneed name_params') (skip (lg-l) name_params_goal)) then
	      begin
	        let new_loc = Some (n, List.nth cur_state.subprocess n, output_loc) in
		Some (NonInterfGoal(InputProcessTest((TestUnifTag occ_goal)::occs_goal, name_params_goal, mess_term_goal, new_loc)))
	      end
	    else None
        | _ -> None
      end
  | _ -> None


let do_res_in cur_state seen_list rest_subprocess n current_cache_list name_params' new_occs facts tc pat p tc' (mess_term: term) public_status next_f =
      (* The real list of processes is (List.rev_append seen_list (InputProcess :: rest_subprocess)) *)
  let (recipe, mess_list, oldpub) =
    match public_status with
      Some (recipe,m,o) -> (recipe,m,o)
    | None ->
      let new_recipe = new_var ~orig:false "~M" (get_term_type mess_term) in
      (Var new_recipe, decompose_term_rev (new_recipe, mess_term), [])
  in
  (* Remove the elements of mess_list' that are already in cur_state.public *)
  let mess_list' = update_term_list oldpub cur_state.public mess_list in
  let recipe' = Terms.copy_term4 recipe in
  (* When mess_list' is not empty, its first element is not in cur_state.public
     Remember that point to avoid testing again that part of public *)
  current_cache_list := (mess_term, Some (recipe', mess_list', cur_state.public)) :: (!current_cache_list);
  debug_print "Input on public channel (message found)";
  if mess_list' != [] then raise Unify; (* The message is not public *)
  debug_print "Ok, the message is public";
  try
    made_forward_step := true;
    let new_goal_opt = success_input cur_state n new_occs name_params' mess_term (LocAttacker recipe') in
    match new_goal_opt with
      Some new_goal -> (* SUCCESS! *) { cur_state with goal = new_goal }
    | None ->
      auto_cleanup_red (fun () ->
        match_pattern pat mess_term;
        let name_params'' = update_name_params Always name_params' pat in
        let p' = auto_cleanup (fun () -> copy_process p) in
        let fact' = Pred(Param.get_pred(Mess(cur_state.current_phase, get_term_type mess_term)), [tc'; mess_term]) in
	let new_facts =
          match new_occs with
          | (InputTag _)::(PreciseTag(occ))::_ ->
              let occ_n = get_occurrence_name_for_precise occ name_params' in
              let ev_precise = Param.get_precise_event (Action (get_term_type mess_term)) in
	      fact' :: Pred(Param.begin_pred,[FunApp(ev_precise,[occ_n;mess_term])]) :: facts
          | (InputTag _) :: _ ->
	      fact' :: facts
          | _ -> Parsing_helper.internal_error "[reduction.ml >> do_res_in] First element of new_occs should be an input tag."
        in
        normal_state next_f false
          { cur_state with
            subprocess = List.rev_append seen_list ((p', name_params'', new_occs, new_facts, Nothing) :: rest_subprocess);
            comment = RInput_Success(n, tc', pat, recipe', mess_term);
            previous_state = Some cur_state } n

      )
  with No_result ->
        (* Inputting the message mess_term on this input will always fail,
           even in the following of the trace *)
        current_cache_list := List.tl (!current_cache_list);
        raise Unify


let optional_eavesdrop state public_channel mess_term =
  if public_channel then
     (* The adversary is passive and the channel is public;
        the adversary eavesdrops the message [mess_term] sent by RIO / RIO_PatRemove *)
     let (new_recipe, state') = add_public state mess_term in
    (Some new_recipe, state')
  else
    (None, state)

(* Perform a (Red I/O) reduction between an input and an asynchronous output *)

let do_async_res_io cur_state seen_list rest_subprocess n current_cache_list name_params' new_occs facts tc pat p tc' mess_term public_channel next_f =
  (* The real list of processes is (List.rev_append seen_list (InputProcess :: rest_subprocess))
     It differs from cur_state.subprocess only by the cache of input processes, so when
     looking for an output process, we can use cur_state.subprocess instead. *)
  current_cache_list := (mess_term, None) :: (!current_cache_list);
  (* Find the corresponding asynchronous output *)
  let rec find_asynchronous_output noutput = function
      [] -> raise Unify (* not found *)
    | ((Output(tc2, t2, Nil,out_occ), name_params2,occs2, facts2, cache_info2)::_) when
        (equal_terms_modulo tc2 tc') && (equal_terms_modulo t2 mess_term) ->
      noutput
    | _::rest_subprocess2 -> find_asynchronous_output (noutput+1) rest_subprocess2
  in
  let noutput = find_asynchronous_output 0 cur_state.subprocess in
  begin
    try
      made_forward_step := true;
      let new_goal_opt = success_input cur_state n new_occs name_params' mess_term
          (LocProcess(noutput, List.nth cur_state.subprocess noutput))
      in
      match new_goal_opt with
        Some new_goal -> (* SUCCESS! *) { cur_state with goal = new_goal }
      | None ->
        try
          auto_cleanup_red (fun () ->
            match_pattern pat mess_term;
            let name_params'' = update_name_params Always name_params' pat in
            let p' = auto_cleanup (fun () -> copy_process p) in
            let fact' = Pred(Param.get_pred(Mess(cur_state.current_phase, get_term_type mess_term)), [tc'; mess_term]) in
            let new_facts = match new_occs with
              | (InputTag _)::(PreciseTag(occ))::_ ->
                  let occ_n = get_occurrence_name_for_precise occ name_params' in
                  let ev_precise = Param.get_precise_event (Action (get_term_type mess_term)) in
                  [fact';Pred(Param.begin_pred,[FunApp(ev_precise,[occ_n;mess_term])])]
              | (InputTag _) :: _ -> [fact']
              | _ -> Parsing_helper.internal_error "[reduction.ml >> do_async_res_io] First element of new_occs should be an input tag."
            in
              (* Do RIO *)
            let (_, name_params2,occs2, facts2, _) = List.nth cur_state.subprocess noutput in
            let (new_goal, comm_in_goal, attack_found) =
              update_corresp_goal cur_state.goal None
		(is_mess_goal cur_state.current_phase tc' mess_term)
            in
            (* When the adversary is passive and the channel is public,
               the adversary eavesdrops the message sent by RIO *)
	    let (opt_recipe, cur_state1) = optional_eavesdrop cur_state public_channel mess_term in
            let cur_state2 =
              { cur_state1
                with
                  subprocess = replace_at noutput (Nil, name_params2,occs2, facts2, Nothing)
                    (List.rev_append seen_list ((p', name_params'', new_occs, new_facts @ facts, Nothing) :: rest_subprocess));
                  comment = RIO(n, tc', pat, noutput, tc', opt_recipe, mess_term, comm_in_goal);
                  goal = new_goal;
                  previous_state = Some cur_state }
            in
              (* Then do RNil on the Nil process that follows the output *)
            let cur_state' = do_rnil cur_state2 noutput in
            let ninput = if n > noutput then n-1 else n in
            if attack_found then
                (* SUCCESS! *)
              cur_state'
            else
              normal_state next_f (cur_state'.public != cur_state.public) cur_state' ninput
          )
        with Unify ->
          (* The pattern does not match *)
          let noutput' = if n>noutput then noutput else noutput-1 in
          (* Do RIO_PatRemove *)
          let (_, name_params2,occs2, facts2, _) = List.nth cur_state.subprocess noutput in
          let (new_goal, comm_in_goal, attack_found) =
            update_corresp_goal cur_state.goal None
	      (is_mess_goal cur_state.current_phase tc' mess_term)
          in
          (* When the adversary is passive and the channel is public,
             the adversary eavesdrops the message sent by RIO_PatRemove *)
	  let (opt_recipe, cur_state1) = optional_eavesdrop cur_state public_channel mess_term in
          let cur_state2 =
            { cur_state1 with
                subprocess = replace_at noutput' (Nil, name_params2,occs2, facts2, Nothing) (List.rev_append seen_list rest_subprocess);
                comment = RIO_PatRemove(n, tc', pat, noutput, tc', opt_recipe, mess_term, comm_in_goal, true);
                goal = new_goal;
                previous_state = Some cur_state }
          in
          (* Then do RNil on the Nil process that follows the output *)
          let cur_state'' = do_rnil cur_state2 noutput' in
          if attack_found then
            (* SUCCESS! *)
            cur_state''
          else
            next_f cur_state''
    with No_result ->
      current_cache_list := List.tl (!current_cache_list);
      raise Unify
  end


(* Perform a (Res I/O) reduction with a synchronous output *)

let do_sync_res_io cur_state seen_list rest_subprocess n name_params' new_occs facts tc pat p tc' public_channel next_f   =
  (* The real list of processes is (List.rev_append seen_list (InputProcess :: rest_subprocess))
     It differs from cur_state.subprocess only by the cache of input processes, so when
     looking for an output process, we can use cur_state.subprocess instead. *)
  let rec find_synchronous_output noutput = function
    | [] -> raise Unify (* Not found *)
    | (Output(tc2,t2,p2,out_occ),name_params2,occs2, facts2, cache_info2)::rest_subprocess2 ->
      begin
        try
          if not (equal_terms_modulo tc2 tc') then
            raise Unify;
          let (new_goal, comm_in_goal, attack_found) =
            update_corresp_goal cur_state.goal None
	      (is_mess_goal cur_state.current_phase tc' t2)
          in
          (* When p2 is Nil and the Horn clause derivation does not justify the
             input, the output is useless (because it does not allow to execute
             more instructions), except in two situations:
               - when the attacker is passive and the channel is public;
                 in this case, it allows the attacker to obtain the message
                 (public_channel is true in this case)
               - when the communication itself is what makes the attack succeed,
                 that is, the goal is that communication.
                 (comm_in_goal is true in this case) *)
          if not ((p2 != Nil) || public_channel || comm_in_goal) then
            raise Unify;
          made_forward_step := true;
          let new_goal_opt = success_input cur_state n new_occs name_params' t2
              (LocProcess(noutput, List.nth cur_state.subprocess noutput))
          in
          match new_goal_opt with
            Some new_goal -> (* SUCCESS! *) { cur_state with goal = new_goal }
          | None ->
            (* The i/o reduction is possible, compute the reduced state *)
          let fact = Pred(Param.get_pred(Mess(cur_state.current_phase, get_term_type t2)), [tc'; t2]) in
          let new_facts = match new_occs with
            | (InputTag _)::(PreciseTag(occ))::_ ->
                let occ_n = get_occurrence_name_for_precise occ name_params' in
                let ev_precise = Param.get_precise_event (Action (get_term_type t2)) in
                [fact;Pred(Param.begin_pred,[FunApp(ev_precise,[occ_n;t2])])]
            | (InputTag _) :: _ -> [fact]
            | _ -> Parsing_helper.internal_error "[reduction.ml >> do_sync_res_io] First element of new_occs should be an input tag."
          in
          try
            auto_cleanup_red (fun () ->
              match_pattern pat t2;
              let name_params'' = update_name_params Always name_params' pat in
              let p' = auto_cleanup (fun () -> copy_process p) in
              (* When the adversary is passive and the channel is public,
                 the adversary eavesdrops the message sent by RIO *)
	      let (opt_recipe, cur_state1) = optional_eavesdrop cur_state public_channel t2 in
              let cur_state2 =
                  { cur_state1 with
                    subprocess = replace_at noutput (p2, name_params2, (OutputTag out_occ)::occs2, facts2, Nothing)
                            (List.rev_append seen_list ((p', name_params'', new_occs, new_facts @ facts, Nothing) :: rest_subprocess));

                    comment = RIO(n, tc', pat, noutput, tc2, opt_recipe, t2, comm_in_goal);
                    goal = new_goal;
                    previous_state = Some cur_state }
              in
              if attack_found then
                cur_state2
              else
                normal_state2 next_f (cur_state2.public != cur_state.public) cur_state2 noutput n
                  )
          with Unify -> (* The pattern does not match *)
            let noutput' = if n > noutput then noutput else noutput-1 in
            (* When the adversary is passive and the channel is public,
               the adversary eavesdrops the message sent by RIO_PatRemove *)
	    let (opt_recipe, cur_state1) = optional_eavesdrop cur_state public_channel t2 in
            let cur_state' =
                { cur_state1 with
                  subprocess = replace_at noutput' (p2, name_params2, occs2, facts2, Nothing)
                          (List.rev_append seen_list rest_subprocess);
                  comment = RIO_PatRemove(n, tc', pat, noutput, tc2, opt_recipe, t2, comm_in_goal, true);
                  goal = new_goal;
                  previous_state = Some cur_state }
            in
            if attack_found then
              (* SUCCESS! *)
              cur_state'
            else
              normal_state next_f (cur_state'.public != cur_state.public) cur_state' noutput'
        with Unify | No_result ->
          find_synchronous_output (noutput+1) rest_subprocess2
      end
    | _::rest_subprocess2 -> find_synchronous_output (noutput+1) rest_subprocess2
  in
  find_synchronous_output 0 cur_state.subprocess

(* Perform a get (Res Get) *)

let rec find_term stop_l t l =
  if l == stop_l then false else
    match l with
      [] -> false
    | (a::r) ->
      if equal_terms_modulo t a then true else find_term stop_l t r

let do_res_get cur_state seen_list rest_subprocess n current_cache_list name_params' new_occs facts pat t p mess_term old_tables next_f =
  (* The real list of processes is (List.rev_append seen_list (GetProcess :: rest_subprocess)) *)
  current_cache_list := mess_term :: (!current_cache_list);
  debug_print "Get";
  if not (find_term old_tables mess_term cur_state.tables) then raise Unify; (* The entry is not found *)
  debug_print "Ok, the entry is present";
  try
    made_forward_step := true;
    auto_cleanup_red (fun () ->
      match_pattern pat mess_term;
      let name_params'' = update_name_params Always name_params' pat in
      let t' = term_evaluation_fail t in
      if equal_terms_modulo t' true_term then
          (* we check that t evaluates to true *)
        let p' = auto_cleanup (fun () -> copy_process p) in
        let fact' = Pred(Param.get_pred(Table(cur_state.current_phase)), [mess_term]) in
        let new_facts = match new_occs with
          | (GetTag _)::(PreciseTag(occ))::_ ->
              let occ_n = get_occurrence_name_for_precise occ name_params' in
              let ev_precise = Param.get_precise_event (Action Param.table_type) in
              [fact';Pred(Param.begin_pred,[FunApp(ev_precise,[occ_n;mess_term])])]
          | (GetTag _) :: _ -> [fact']
          | _ -> Parsing_helper.internal_error "[reduction.ml >> do_res_get] First element of new_occs should be a Get tag."
        in
        normal_state next_f false
          { cur_state with
            subprocess = List.rev_append seen_list ((p', name_params'', new_occs, new_facts @ facts, Nothing) :: rest_subprocess);
            comment = RGet_In(n, pat, t, mess_term);
            previous_state = Some cur_state } n
      else
        raise Unify
    )
  with No_result ->
    (* Using the entry mess_term on this input will always fail,
       even in the following of the trace *)
    current_cache_list := List.tl (!current_cache_list);
    raise Unify

(* Dispatch between (Res In), asynchronous (Res I/O), and synchronous (Res I/O), and (Res Get)
   May also execute (Insert) in case an insert has been delayed because it prevented executing the
   else branch of Get. *)

exception Backtrack_get
(* This exception is used only when I should take the
   else of Get and I cannot because an element that
   makes Get succeed already occurs. *)

let rec find_in_out next_f cur_state n seen_list = function
  | [] -> raise No_result
  | ((Input(tc,pat,p,occ) as proc ,name_params,occs, facts, cache_info)::rest_subprocess) ->
    debug_print ("Trying Input on process " ^ (string_of_int n));
    begin
      match cache_info with
        OutputInfo _ | GetInfo _ -> Parsing_helper.internal_error "Should not have output/get info for an input!"
      | InputInfo(tc_list, oldpub, tc', name_params', new_occs, l) ->
        let tc_list' = update_term_list oldpub cur_state.public tc_list in
        if (!Param.active_attacker) && (tc_list' = []) then
          begin
            (* The channel is public and the attacker is active, try (Res In) *)
            debug_print "Input on public channel (cached)";
            let current_cache_list = ref [] in
            let rec do_l = function
              |        [] ->
              let seen_list' = (proc ,name_params,occs, facts,
                                InputInfo(tc_list', cur_state.public, tc', name_params', new_occs, !current_cache_list)) :: seen_list in
              find_in_out next_f cur_state (n+1) seen_list' rest_subprocess
              | (mess_term, public_status)::l ->
                try
                  do_res_in cur_state seen_list rest_subprocess n current_cache_list name_params' new_occs facts tc pat p tc' mess_term public_status next_f
                with Unify ->
                  do_l l
            in
            do_l l
          end
        else
          begin
            (* The channel is private or the attacker is passive, try (Res I/O) *)
            debug_print "Input on private channel (cached); trying asynchronous output";
            let current_cache_list = ref [] in
            let public_channel = (not (!Param.active_attacker)) && (tc_list' = []) in
            let rec do_l = function
              |        [] ->
              let seen_list' = (proc ,name_params,occs, facts,
                                InputInfo(tc_list', cur_state.public, tc', name_params', new_occs, !current_cache_list)) :: seen_list in
              begin
                debug_print "Input on private channel (cached); trying synchronous output";
                try
                  do_sync_res_io cur_state seen_list rest_subprocess n name_params' new_occs facts tc pat p tc' public_channel next_f
                with Unify | No_result ->
                  find_in_out next_f cur_state (n+1) seen_list' rest_subprocess
              end
              | (mess_term,_)::l ->
                try
                  do_async_res_io cur_state seen_list rest_subprocess n current_cache_list name_params' new_occs facts tc pat p tc' mess_term public_channel next_f
                with Unify ->
                  do_l l
            in
            do_l l
          end
      | Nothing ->
        let seen_list' = ref ((proc, name_params, occs, facts, cache_info) :: seen_list) in
        try
          auto_cleanup_red (fun () ->
            let (tc', name_params') = term_evaluation_name_params (OInChannel(occ)) tc name_params in
            let m = Reduction_helper.new_var_pat1 pat in
            let fact = Pred(Param.get_pred(Mess(cur_state.current_phase, m.btype)), [tc'; Var m]) in
            let (new_occs,new_facts) =
              if Reduction_helper.exists_specific_precise_events_of_occ occ (Action m.btype)
              then
                let occ_n = get_occurrence_name_for_precise occ name_params' in
                let ev_precise = Param.get_precise_event (Action m.btype) in
                ((InputTag occ) :: (PreciseTag(occ)) :: occs, [fact;Pred(Param.begin_pred,[FunApp(ev_precise,[occ_n;Var m])])])
              else ((InputTag occ) :: occs, [fact])
            in

            let new_recipe = new_var ~orig:false "Useless" (get_term_type tc') in
            let tc_list = decompose_term_rev (new_recipe, tc') in
            let tc_list' = remove_first_in_public cur_state.public tc_list in
            if (!Param.active_attacker) && (tc_list' = []) then
              begin
                  (* Input on a public channel, and the attacker is active: apply (Res In)  *)
                debug_print "Input on public channel";
                let current_cache_list = ref [] in
                try
                  find_io_rule (function
                    | [mess_term] ->
                        do_res_in cur_state seen_list rest_subprocess n current_cache_list name_params' new_occs facts tc pat p tc' mess_term None next_f
                    | _ -> Parsing_helper.internal_error "input case; reduction.ml"
                  ) new_occs (new_facts @ facts) name_params' [Var m] cur_state.io_rule
                with Unify ->
                  seen_list' := (proc, name_params, occs, facts,
                                 InputInfo([], [], tc', name_params', new_occs, !current_cache_list)) :: seen_list;
                  raise Unify
              end
            else
              begin
                  (* Input on a private channel or the attacker is passive: apply (Res I/O)
                     First try an asynchronous output, with a corresponding clause in the tree *)
                debug_print "Input on private channel; trying asynchronous output";
                let current_cache_list = ref [] in
                let public_channel = (not (!Param.active_attacker)) && (tc_list' = []) in
                try
                  find_io_rule (function
                    | [mess_term] ->
                        do_async_res_io cur_state seen_list rest_subprocess n current_cache_list name_params' new_occs facts tc pat p tc' mess_term public_channel next_f
                    | _ -> Parsing_helper.internal_error "input case; reduction.ml"
                  ) new_occs (new_facts @ facts) name_params' [Var m] cur_state.io_rule
                with Unify ->
                  seen_list' := (proc, name_params,occs, facts,
                                 InputInfo(tc_list', cur_state.public, tc', name_params', new_occs, !current_cache_list)) :: seen_list;
                    (* Try a synchronous output *)
                  debug_print "Input on private channel; trying synchronous output";
                  do_sync_res_io cur_state seen_list rest_subprocess n name_params' new_occs facts tc pat p tc' public_channel next_f
              end
          )
        with Unify | No_result ->
          find_in_out next_f cur_state (n+1) (!seen_list') rest_subprocess
    end
  | ((Get(pat,t,p,p_else, occ) as proc ,name_params,occs, facts, cache_info)::rest_subprocess) ->
    (* TO DO optimize the case with else branch *)
    debug_print ("Trying Get on process " ^ (string_of_int n));
    begin
      match cache_info with
        OutputInfo _ | InputInfo _ -> Parsing_helper.internal_error "Should not have input/output info for a get!"
      | GetInfo(old_tables, l) ->
          let new_occs =
	    if Reduction_helper.exists_specific_precise_events_of_occ occ (Action Param.table_type)
            then
	      (GetTag occ) :: (PreciseTag(occ)) :: occs
	    else
	      (GetTag occ) :: occs
	  in
          let current_cache_list = ref [] in
          let rec do_l = function
            | [] ->
		let seen_list' = (proc ,name_params,occs, facts,
				  GetInfo(cur_state.tables, !current_cache_list)) :: seen_list in
		find_in_out next_f cur_state (n+1) seen_list' rest_subprocess
            | mess_term::l ->
		try
		  do_res_get cur_state seen_list rest_subprocess n current_cache_list name_params new_occs facts pat t p mess_term old_tables next_f
		with Unify ->
		  do_l l
        in
        do_l l
      | Nothing ->
        let seen_list' = ref ((proc, name_params, occs, facts, cache_info) :: seen_list) in
        try
          auto_cleanup_red (fun () ->
            let m = Reduction_helper.new_var_pat1 pat in
            let fact = Pred(Param.get_pred(Table(cur_state.current_phase)), [Var m]) in
            let (new_occs,new_facts) =
              if Reduction_helper.exists_specific_precise_events_of_occ occ (Action Param.table_type)
              then
                let occ_n = get_occurrence_name_for_precise occ name_params in
                let ev_precise = Param.get_precise_event (Action m.btype) in
                ((GetTag occ) :: (PreciseTag(occ)) :: occs, [fact;Pred(Param.begin_pred,[FunApp(ev_precise,[occ_n;Var m])])])
              else ((GetTag occ) :: occs, [fact])
            in

            let current_cache_list = ref [] in
            try
              find_io_rule (function
            [mess_term] ->
              do_res_get cur_state seen_list rest_subprocess n current_cache_list name_params new_occs facts pat t p mess_term [] next_f
              | _ -> Parsing_helper.internal_error "get case; reduction.ml"
              ) new_occs (new_facts @ facts) name_params [Var m] cur_state.io_rule
            with Unify ->
              if p_else != Nil then
                  (* See if we should take the else branch if present *)
                begin
                  try
                    let new_occs = (GetTagElse occ) :: occs in
                    find_io_rule (function
                  [] ->
                            (* We should take the else branch, since a clause uses that branch *)
                    debug_print "Get: else branch should be taken";
                    if List.exists (fun mess_term ->
                      try
                        auto_cleanup (fun () ->
                                      (* we check that the pattern pat matches and t evaluates to true *)
                          match_pattern pat mess_term;
                          let t' = term_evaluation_fail t in
                          equal_terms_modulo t' true_term)
                      with Unify -> false) cur_state.tables
                    then
                      begin
                        debug_print "Get: an element of the table matches, cannot take the else branch, backtracking";
                                (* The Get process is blocked forever: the else branch should be taken,
                                   but the table contains an element that prevents it. Since elements
                                   are only added to tables, this situation will not change.
                                   So I backtrack. *)
                        has_backtrack_get := true;
                        raise Backtrack_get
                      end
                    else
                      begin
                        debug_print "Get: taking the else branch";
                        normal_state next_f false
                          { cur_state with
                            subprocess = List.rev_append seen_list ((p_else, name_params, new_occs, facts, Nothing) :: rest_subprocess);
                                    (*pat*)
                            comment = RGet_Else(n, pat, t);
                            previous_state = Some cur_state } n
                      end
                    | _ -> Parsing_helper.internal_error "get else case; reduction_bipro.ml"
                    ) new_occs facts name_params [] cur_state.io_rule
                  with Unify ->
                    seen_list' := (proc, name_params, occs, facts,
                                   GetInfo(cur_state.tables, !current_cache_list)) :: seen_list;
                    raise Unify
                end
              else
                begin
                  seen_list' := (proc, name_params, occs, facts,
                                 GetInfo(cur_state.tables, !current_cache_list)) :: seen_list;
                  raise Unify
                end
          )
        with Unify | No_result ->
          find_in_out next_f cur_state (n+1) (!seen_list') rest_subprocess
        | Backtrack_get -> raise No_result
    end
  | ((Insert(t,p,occ), name_params, occs, facts, cache_info) as sub_proc)::rest_subprocess ->
    debug_print "Doing Insert";
    begin
      let new_occs = (InsertTag occ) :: occs in
      let new_element_inserted = ref false in
      try
	auto_cleanup_red (fun () ->
	  let t' = term_evaluation_fail t in
          let already_in = List.exists (equal_terms_modulo t') cur_state.tables in
	  new_element_inserted := not already_in;
	  (* This test will probably never succeed, because in
	     case it would succeed, it would have been detected earlier
	     in the [Insert] case of [do_red_nointeract] *)
          let (new_goal, insert_in_goal, success) =
	    update_corresp_goal cur_state.goal None
	      (is_table_goal cur_state.current_phase t')
          in
	  let new_state =
	    { cur_state with
	      subprocess = List.rev_append seen_list ((p, name_params, new_occs, facts, Nothing) :: rest_subprocess);
	      tables = if already_in then cur_state.tables else t'::cur_state.tables;
              comment = RInsert_Success(n, t', insert_in_goal);
	      goal = new_goal;
              previous_state = Some cur_state }
	  in
	  if success then
	    new_state
	  else
	    normal_state next_f false new_state n
	)
      with Unify ->
	Parsing_helper.internal_error "Insert: Unify/FailOneSideOnly should have been detected on the first try of that insert"
      | No_result ->
	   (* The attack reconstruction failed after doing the insert.
	      Try not doing it, in case that allows executing the else branch of a Get. *)
	if (!has_backtrack_get) && (!new_element_inserted) then
	  find_in_out next_f cur_state (n+1) (sub_proc :: seen_list) rest_subprocess
	else
	  raise No_result
    end
  | sub_proc::rest_subprocess ->
    find_in_out next_f cur_state (n+1) (sub_proc :: seen_list) rest_subprocess

(* Handle phases *)

(* [extract_phase n processes] modifies the processes for a [phase n] transition:
   removes processes with no phase prefix or a phase prefix less than [n];
   removes the phase prefix [phase n], leaving the rest of the process;
   leaves processes with phase prefix greater than [n] unchanged. *)

let rec extract_phase n = function
  | [] -> []
  | (Phase(n',p,occ),name_params,occs, facts, cache_info)::r ->
    let r' = extract_phase n r in
    if n = n' then (p,name_params,occs, facts, Nothing)::r' else
      if n<n' then (Phase(n',p,occ),name_params,occs, facts, Nothing)::r' else r'
  | _::r -> extract_phase n r

(* [find_phase current_phase None processes] returns either
   [None] when no process in [processes] starts with a phase, or
   [Some n] when a process in [processes] starts with phase [n] and this is the lowest such phase.
   It is an error if a process in [processes] starts with a phase less or equal to [current_phase]. *)

let rec find_phase current_phase found_phase = function
    [] -> found_phase
  | (Phase(n,p,_),name_params,occs, facts, cache_info)::rest_subprocess ->
      if n <= current_phase then
	Parsing_helper.user_error "Phases should be in increasing order.";
      let found_phase' =
	match found_phase with
	  None -> Some n
	| Some n_found -> if n_found <= n then found_phase else Some n
      in
      find_phase current_phase found_phase' rest_subprocess
  | _::rest_subprocess ->
      find_phase current_phase found_phase rest_subprocess

let do_phase next_f cur_state =
  match find_phase cur_state.current_phase None cur_state.subprocess with
    None ->
      if !made_forward_step then
	begin
	  incr failed_traces;
	  made_forward_step := false
	end;
      (* Useful for debugging *)
      if !debug_backtracking then
	begin
	  ignore (Display.Text.display_reduc_state Display.term_to_term true cur_state);
	  print_string "Blocked. Backtracking...\n"
	end
      else
	debug_print "Backtracking";
      raise No_result
  | Some n ->
      debug_print "Doing Phase";
      made_forward_step := true;
      (* Reclose public, since new function symbols may become applicable *)
      let cur_state' = close_public_phase_change cur_state n in
      (* Do transition to phase n *)
      let cur_state'' =
	{ cur_state' with
	  subprocess = extract_phase n cur_state'.subprocess;
	  previous_state = Some cur_state;
	  current_phase = n;
	  comment = RPhase(n) }
      in
      normal_state_all next_f false cur_state''

(* Put all reductions together *)

let reduction_step next_f state =
  try
    find_in_out next_f state 0 [] state.subprocess
  with No_result ->
    do_phase next_f state

let rec reduction_backtrack state =
  reduction_step reduction_backtrack state

let rec reduction_nobacktrack state =
  try
    reduction_step (fun state' -> raise (Reduced state')) state
  with Reduced one_red_state ->
    display_trace one_red_state;
    Param.display_init_state := false;
    reduction_nobacktrack { one_red_state with previous_state = None }

let reduction state =
  if !Param.trace_backtracking then
    reduction_backtrack state
  else
    reduction_nobacktrack state

(* Build the goal for weak secrets *)

let rec analyze_weak_secr_tree_rec accu weaksecrets tree =
  match tree.desc with
    FRule(_, lbl, _, hyp,_,_) ->
      begin
        match lbl with
	  Apply(f,{ p_info = [AttackerGuess _]}) ->
	    FunApp(f,
	           List.map (analyze_weak_secr_tree_rec accu weaksecrets) hyp)
        | WeakSecr ->
	  begin
	    match tree.thefact with
	      Pred({ p_info = [AttackerGuess _]}, [t1;t2]) ->
	        weaksecrets := Some (rev_name_subst t1,rev_name_subst t2);
	        rev_name_subst t2
	    |	_ -> Parsing_helper.internal_error "Unexpected WeakSecr clause in the derivation for weaksecret"
	  end
        | PhaseChange ->
	  begin
	    match tree.thefact with
	      Pred({ p_info = [AttackerGuess _] }, [t1;t2]) ->
	        let v = new_var ~orig:false "v" (get_term_type t1) in
	        let t1' = rev_name_subst t1 in
	        accu := (t1', v, None) :: (!accu);
	        Var v
	    |	_ -> Parsing_helper.internal_error "Unexpected WeakSecr clause in the derivation for weaksecret"
	  end
        | _ -> Parsing_helper.internal_error "Unexpected clause in derivation for weaksecret"
      end
  | FEquation t -> analyze_weak_secr_tree_rec accu weaksecrets t
  | FRemovedWithProof t -> analyze_weak_secr_tree_rec accu weaksecrets t
  | FHAny | FEmpty | FRemovedWithMaxHyp -> Parsing_helper.internal_error "Unexpected derivation for weaksecret"


let analyze_weak_secret_tree accu weaksecrets tree =
  match tree.desc with
    FRule(_, lbl, _, hyp,_,_) ->
      begin
        let l = List.map (analyze_weak_secr_tree_rec accu weaksecrets) hyp in
        match lbl, l with
	  Rfail({ p_info = [AttackerGuess _] }), [t] ->
	    FailTest(t)
        | TestEq({ p_info = [AttackerGuess _] } ), [t1;t2] ->
	  EqTest(t1,t2)
        | _ -> Parsing_helper.internal_error "Unexpected clause concluding the derivation for weaksecret"
      end
  | _ -> Parsing_helper.internal_error "Unexpected derivation for weaksecret"


(* Build the goal for non-interference *)

let analyze_non_interf_tree tree =
  match tree.desc with
    FRule(_, lbl, _, hyp,_,_) ->
      begin
        match lbl, hyp with
	| ProcessRule(hyp_tags, name_params), hyp ->
	    begin
	      match hyp_tags with
	        TestUnifTag occ :: InputTag occ' :: _ when occ == occ' ->
	    (* Pattern-matching test in an input *)
	          let mess_term =
	            match hyp with
		      _ (* testunif fact *) :: { thefact = Pred(_, [t]) } (* att fact *) :: _ -> rev_name_subst t
	            | _ (* testunif fact *) :: { thefact = Pred(_, [_;t]) } (* mess fact *) :: _ -> rev_name_subst t
	            | _ -> Parsing_helper.internal_error "Unexpected derivation for noninterf: input with fact other than att/mess"
	          in
	          InputProcessTest(hyp_tags, rev_name_subst_list name_params, mess_term, None)
	      |	_ ->
	        ProcessTest(hyp_tags, rev_name_subst_list name_params, None)
	    end
        | TestApply(f, p), _(*testunif fact*)::hyp ->
	  ApplyTest(f, List.map (function
	      { thefact = Pred(_, [t]) } -> (rev_name_subst t, None)
	    | _ -> Parsing_helper.internal_error "Unexpected derivation for noninterf")
		      hyp)
        | TestComm(pi,po), [{thefact = Pred(_,[tin])}; {thefact = Pred(_,[tout])}; _(* testunif fact *)] ->
	    CommTest(rev_name_subst tin, rev_name_subst tout, None)
        | TestEq(p), [{thefact = Pred(_,[t1])};{thefact = Pred(_,[t2])};_(* testunif fact *)] ->
	    NIEqTest((rev_name_subst t1, None), (rev_name_subst t2, None))
        | _ -> Parsing_helper.internal_error "Unexpected clause concluding the derivation for noninterf"
      end
  | _ -> Parsing_helper.internal_error "Unexpected derivation for noninterf"

(* For injectivity *)


(* Copy the history

   let rec copy_tree { desc = d; thefact = f} =
   { desc = copy_tree_desc d; thefact = copy_fact2 f }

   and copy_tree_desc = function
   FHAny -> FHAny
   | FEmpty -> FEmpty
   | FRemovedWithProof t -> FRemovedWithProof t
   | FRule(n, descr, constra, l) -> FRule(n, copy_descr descr, List.map copy_constra2 constra, List.map copy_tree l)
   | FEquation(t) -> FEquation(copy_tree t)

   and copy_descr = function
   ProcessRule(hypspec,name_params) ->
   ProcessRule(hypspec, List.map copy_term2 name_params)
   | x -> x
*)

let new_sid() =
  Terms.create_name ~orig:false "sid" ([], Param.sid_type) false

let add_sid (v,f) l =
  if not (List.exists (fun (v',f') -> f == f') (!l)) then l := (v,f) :: (!l)

let rec get_sid = function
Var ({ link = TLink (FunApp(sid,[])) } as v) ->
  (v, sid)
  | Var { link = TLink t } -> get_sid t
  | t ->
    Display.Text.display_term t;
    begin
      match t with
	Var v ->
	  begin
	    print_string " Var ";
	    match v.link with
	      NoLink -> print_string " NoLink "
	    | TLink _ -> print_string " TLink "
	    | VLink _ -> print_string " VLink "
	    | TLink2 _ -> print_string " TLink2 "
	    | _ -> print_string " other link "
	  end
      |	FunApp _ -> print_string " FunApp "
    end;
    Parsing_helper.internal_error "Constant session ids should be function applications with no arguments stored as links of variables"

let rec has_sid_term sid = function
  | Var { link = TLink t } -> has_sid_term sid t
  | Var _ -> false
  | FunApp(f,l) ->
    (f == sid) || (List.exists (has_sid_term sid) l)

let find_sid_fact end_sid no_dup_begin_sids = function
  | Pred(p,[_;occ]) when p == Param.begin_pred_inj ->
      if not (has_sid_term end_sid occ)
      then
        begin match occ with
          | FunApp({ f_cat = Name info; _},args) ->
              List.iter2 (fun t -> function
                | MSid _ -> add_sid (get_sid t) no_dup_begin_sids
                | _ -> ()
              ) args info.prev_inputs_meaning
          | _ -> Parsing_helper.internal_error "[reduction.ml >> find_sid_fact] Expecting a name."
        end
  | _ -> ()

let rec find_sid_tree end_sid all_sids no_dup_begin_sids t =
  find_sid_fact end_sid no_dup_begin_sids t.thefact;
  match t.desc with
    FHAny | FEmpty -> ()
  | FRemovedWithProof _ | FRemovedWithMaxHyp -> ()
  | FEquation t -> find_sid_tree end_sid all_sids no_dup_begin_sids t
  | FRule(_,tags,constra,tl,_,_) ->
    List.iter (find_sid_tree end_sid all_sids no_dup_begin_sids) tl;
    match tags with
      ProcessRule (hsl,nl) ->
      (* find session ids in nl by looking for corresponding elements of hsl:
	 if hsl contains ReplTag(_,count_params), then the count_params-th element of nlrev is a session id. *)
        let nlrev = List.rev nl in
        List.iter (function
      ReplTag(_,count_params) -> add_sid (get_sid (List.nth nlrev count_params)) all_sids
	| _ -> ()) hsl
    |	_ -> ()


(* For injectivity: [check_query_falsified q final_state] checks
   that the trace [final_state] really falsifies the query [q] *)

(* The event_table contains the list of events executed in the trace.
   Each event is accompanied with the list of occurrences in the query
   in which it has already been used. This is useful for injective
   events: they cannot be used twice at the same occurrence in the query.
   Initially, this list is empty. *)

let rec build_event_table state =
  List.rev_map (fun t -> (t, [])) state.events

let rec extract_premises restwork = function
  | [] -> restwork ([],[],Terms.true_constraints,[],[])
  | (a::l) ->
      extract_premises (fun (ev', facts', constra', eq_left', eq_right') ->
        match a with
          | (QSEvent _) as ev -> restwork (ev :: ev', facts', constra', eq_left', eq_right')
              (* It is important not to copy ev = QSEvent _, because
                 we use its physical address to represent the occurrence
                in the query *)
          | QFact(p,_,l) -> restwork (ev', Pred(p,l)::facts', constra', eq_left', eq_right')
          | _ -> Parsing_helper.internal_error "[reduction.ml >> extract_premises] Bad premise in nested query"
      ) l

let rec extract_conclusion_query restwork = function
  | QTrue -> restwork ([],[],Terms.true_constraints,[],[])
  | QFalse -> raise Unify
  | QEvent((QSEvent _) as ev) ->
      (* It is important not to copy ev = QSEvent _, because
         we use its physical address to represent the occurrence
        in the query *)
      restwork ([ev],[],Terms.true_constraints,[],[])
  | QEvent(QFact(p,_,l)) -> restwork ([],[Pred(p,l)],Terms.true_constraints,[],[])
  | QEvent (QNeq (t1,t2)) -> restwork ([], [], Terms.constraints_of_neq t1 t2, [], [])
  | QEvent (QGeq (t1,t2)) -> restwork ([], [], Terms.constraints_of_geq t1 t2, [], [])
  | QEvent (QIsNat t) -> restwork ([],[],Terms.constraints_of_is_nat t,[],[])
  | QEvent (QEq (t1,t2)) -> restwork ([], [], Terms.true_constraints, [t1], [t2])
  | QEvent (QSEvent2 _) -> Parsing_helper.internal_error "[reduction.ml >> extract_conclusion_query] QSEvent2 should only occur in query for biprocesses."
  | NestedQuery(Before(evl,_)) -> extract_premises restwork evl
  | QAnd(concl1,concl2) ->
      extract_conclusion_query (fun (ev1, facts1, constra1, eq_left1, eq_right1) ->
        extract_conclusion_query (fun (ev2, facts2, constra2, eq_left2, eq_right2) ->
          restwork (ev1@ev2, facts1@facts2, Terms.wedge_constraints constra1 constra2, eq_left1@eq_left2, eq_right1@eq_right2)
        ) concl2
      ) concl1
  | QOr(concl1,concl2) ->
      try
        extract_conclusion_query restwork concl1
      with Unify ->
        extract_conclusion_query restwork concl2

(* [find_in_event_table restwork ev0 seen_event_table event_table]
   looks for an instance of [ev0] in [event_table].
   When found, calls [restwork event_table'] with an updated event table
   that takes into account when injective events are already used.
   When not found, raises [Unify].
   [seen_event_table] is the part of the event table that has already
   been scanned (initially empty). *)

let rec find_in_event_table restwork steps_l ev0 seen_event_table = function
    [] -> raise Unify
  | (ev, usage_list)::rest ->
      let (inj,param) =
        match ev0 with
          QSEvent(inj,_,_,param) -> (inj,param)
        | _ -> Parsing_helper.internal_error "event expected in Reduction.find_in_event_table"
      in
      try
        begin match inj with
          | None ->
              TermsEq.unify_modulo (fun () ->
                restwork (List.rev_append seen_event_table ((ev,usage_list)::rest))
              ) param ev
          | Some k ->
              (* For injective events, do not allow using the same event
                 to be associated with different steps of the query's premisse
                 for the same injective index. *)
              if List.exists (fun (k',steps_l') -> k = k' && steps_l <> steps_l') usage_list
              then raise Unify;

              let usage_list' =
                if List.mem (k,steps_l) usage_list
                then usage_list
                else (k,steps_l)::usage_list
              in

              TermsEq.unify_modulo (fun () ->
                restwork (List.rev_append seen_event_table ((ev,usage_list')::rest))
              ) param ev
        end
      with Unify ->
        find_in_event_table restwork steps_l ev0 ((ev,usage_list)::seen_event_table) rest

let rec find_event_list restwork steps_l event_table = function
    [] -> restwork event_table
  | ev::evlist ->
      find_in_event_table (fun event_table' ->
        find_event_list restwork steps_l event_table' evlist
      ) steps_l ev [] event_table

let bad_fact = Pred(Param.bad_pred, [])

let check_conclusion_query restwork event_table steps_l concl_q =
  extract_conclusion_query (fun (evlist, facts, constra, eq_left, eq_right) ->
    find_event_list (fun event_table' ->
      TermsEq.unify_modulo_list (fun () ->
          (* I filter out blocking predicates.
             I will never be able to prove that they are false,
             so I consider them as possibly true.

             I also filter out attacker, mess, and table.
             Indeed, there would be a problem with these predicates,
             because the Horn clause derivation considers
             that the attacker facts attacker(a_i[])
             where a_i is a fresh name are not derivable, but in fact they are!
             So I restrict myself to non-blocking user-defined predicates.
             The definition of these predicates only depends on clauses
             given by the user, and is correctly handled by resolution.

             TO DO Another solution would be to generate clauses for the particular trace, including
             clauses for user-defined predicates, attacker clauses,
             clauses saying that the attacker has the terms in public (in the right phase...),
             clauses saying that actual messages are sent on channels.
	     For mess and table, I should rather look at all messages sent /
	     table insertions in the trace.

             I approximate in that a query may be considered true when
             it is in fact false. This approximation is fine:
             ProVerif will consider that the found trace does not falsify
             the query and will answer "cannot be proved". *)
        let facts =
          List.filter (function
              Pred(p,_) ->
                (* Exclude blocking predicates *)
                (p.p_prop land Param.pred_BLOCKING == 0) &&
                (match p.p_info with
                  [Attacker _|Mess _|Table _] ->
                    false
                | _ -> (* User-defined predicate. Indeed, only attacker, mess, table
                          and user-defined predicates are allowed in queries.
                          Since we exclude attacker, mess, and table above,
                          only user-defined predicates remain *)
                    true)) facts
        in
        TermsEq.close_constraints_eq_synt (fun constra' ->
          if facts = [] then
            begin
	      let constra'' = TermsEq.remove_syntactic_constra constra' in
	      begin
                try
                  TermsEq.check_constraints constra''
                with TermsEq.FalseConstraint -> raise Unify
		end;
                (* The current hypothesis has been satisfied *)
	      restwork event_table'
            end
          else
            Terms.auto_cleanup (fun () ->
	      let facts = List.map (fun f -> Terms.copy_fact2 (TermsEq.remove_syntactic_fact f)) facts in
	      let constra = Terms.copy_constra2 (TermsEq.remove_syntactic_constra constra') in
              (* check the facts and constraints by resolution *)
	      let r0 = { rule = (facts, bad_fact, Rule(-1, LblNone, facts, bad_fact, constra), constra); order_data = None } in
	      if (Rules.solving_request_rule [] [] r0) != [] then
                (* The facts and constra may be derivable.
                   There may be an overapproximation here, but that's fine *)
                restwork event_table'
	      else
                (* The facts and constra are for sure not satisfiable,
                   so this disjunct of the query is false with the current choices *)
                raise Unify
		  )
	      ) constra
      ) eq_left eq_right
    ) steps_l event_table evlist
  ) concl_q

exception FalseQuery

let all_events_to_check concl_q_accu concl_q evl event_table =

  let ev_term_l =
    List.map (function
      | QSEvent(Some _,_,_,ev) -> ev
      | _ -> Parsing_helper.internal_error "[reduction.ml >> all_events] All events should be injective."
    ) evl
  in

  let rec search_event restwork i ev0 = function
    | [] -> ()
    | (ev,_)::ev_tbl ->
        begin
          try
            TermsEq.unify_modulo (fun () ->
              restwork i
            ) ev ev0;
          with Unify -> ()
        end;
        search_event restwork (i+1) ev0 ev_tbl

  and search_event_list i_list ev_list event_table = match ev_list with
    | [] ->
        (* Found matching premises. Copy the conclusion of the conclusion of the query
           in the accumulator *)
        let concl_q' =
          Terms.auto_cleanup (fun () ->
            Terms.copy_conclusion_query2 concl_q
          )
        in
        concl_q_accu := (List.rev i_list,concl_q') :: !concl_q_accu
    | ev0::q ->
        search_event (fun i ->
          search_event_list (i::i_list) q event_table
        ) 0 ev0 event_table
  in

  search_event_list [] ev_term_l event_table

let rec check_all_conclusion_query restwork event_table = function
  | [] -> restwork event_table
  | (steps_l,concl_q)::rest_concl ->
      check_conclusion_query (fun event_table1 ->
        check_all_conclusion_query restwork event_table1 rest_concl
      ) event_table steps_l concl_q

let is_fresh_name f =
  match f.f_cat with
  | Name _ -> not (List.memq f (!Param.current_state).pi_freenames)
  | _ -> false

let rec has_name_t = function
  | FunApp(f,l) -> (is_fresh_name f) || (List.exists has_name_t l)
  | Var _ -> false

let has_name_f = function
  | Pred(p,[t;_]) when p = Param.begin_pred_inj -> has_name_t t
  | Pred(_,l) -> List.exists has_name_t l

let has_name_e = function
    QSEvent(_,_,_,t) -> has_name_t t
  | QSEvent2 _ -> Parsing_helper.internal_error "[reduction.ml >> has_name_e] QSEvent2 should only occur in query for biprocesses."
  | QIsNat t -> has_name_t t
  | QFact(_,_,l) -> List.exists has_name_t l
  | QNeq(t1,t2)
  | QEq(t1,t2)
  | QGeq(t1,t2) -> (has_name_t t1) || (has_name_t t2)

let rec has_name_c = function
  | QEvent ev -> has_name_e ev
  | NestedQuery(Before(evl,_)) -> List.exists has_name_e evl
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) -> has_name_c concl1 || has_name_c concl2
  | _ -> false

let has_name_q (Before(el,concl_q)) = List.exists has_name_e el || has_name_c concl_q

let is_non_inj_neq = function
    QSEvent(Some _,_,_,_) -> false
  | QNeq _ -> Parsing_helper.internal_error "inequalities should not occur in left-hand side of ==> in queries"
  | _ -> true

let is_non_inj_neq_fact = function
    QSEvent(Some _,_,_,_) | QNeq _ | QFact _ -> false
  | _ -> true

let rec is_simple_conclusion_query = function
  | NestedQuery _ -> false
  | QEvent e -> is_non_inj_neq_fact e
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) -> is_simple_conclusion_query concl1 && is_simple_conclusion_query concl2
  | _ -> true

let is_simple_query (Before(el,l)) =
  (List.for_all is_non_inj_neq el) && is_simple_conclusion_query l

let rec check_query_falsified_rec restwork event_table concl_q evl goall =
  match (evl, goall) with
    [], [] ->
      (* The query does not contain any injective event. *)
      let concl_q' =
        Terms.auto_cleanup (fun () ->
          Terms.copy_conclusion_query2 concl_q
        )
      in
      check_conclusion_query restwork event_table [] concl_q'
  | QSEvent(Some _,_,_,_)::_, _ ->
      (* The injective events always appear first before ==> in the query.
         Since we reversed the lists of elements before ==> and of goals,
         they always appears last here. *)
      let concl_q_accu = ref [] in
      all_events_to_check concl_q_accu concl_q evl event_table;

      check_all_conclusion_query restwork event_table !concl_q_accu
  | ev::rest_evl, (Fact(goal,_,_) | EventGoal(goal,_))::rest_goall ->
      let (l,l') =
        match ev, goal with
          QFact(p,_,l), Pred(p',l') when p == p' -> l,l'
        | QSEvent(None,_,_,t), Pred(pr,[t']) when pr == Param.end_pred -> [t],[t']
        | QSEvent(None,_,_,t), Pred(pr,[_;t']) when pr == Param.end_pred_inj -> [t],[t']
        | _ ->
            print_string "Query: "; Display.Text.display_event ev; print_newline();
            print_string "Goal: "; Display.Text.display_fact goal; print_newline();
            Parsing_helper.internal_error "The goal of the trace does not match the query (1)"
      in
      begin
        try
          TermsEq.unify_modulo_list (fun () ->
            try
              check_query_falsified_rec restwork event_table concl_q rest_evl rest_goall
            with Unify -> raise FalseQuery
          ) l l'
        with
          | Unify ->
              print_string "Query: "; Display.Text.WithLinks.term_list l; print_newline();
              print_string "Goal: "; Display.Text.WithLinks.term_list l'; print_newline();
              Parsing_helper.internal_error "The goal of the trace does not match the query (2)"
          | FalseQuery -> raise Unify
      end
  | _ ->
      Parsing_helper.internal_error "The goal of the trace does not match the query (3)"

let check_query_falsified q id_goals final_state =
  (* Include in [event_table] the executed events *)
  let event_table = build_event_table final_state in
  if has_name_q q then
    begin
      if is_simple_query q then
	begin
	  Display.Def.print_line "The previous trace falsifies the query, because the query is\nsimple and the trace corresponds to the derivation.";
	  true
	end
      else
	begin
	  Display.Def.print_line "I cannot confirm that the previous trace falsifies the query,\nbecause the query contains fresh names.";
	  false
	end
    end
  else
    (*
    List.iter (fun (t,_) ->
      print_string "Event found "; Display.Text.display_term t; print_newline()) event_table;
    *)
    let Before(evl, hyp) = q in
    match final_state.goal with
      CorrespGoal(goall) ->
        begin
          let goall' = retrieve_goals_from_id id_goals goall in
          let size_evl = List.length evl in
          if List.length goall' = 2 * size_evl
          then
            (* The trace corresponds to a clause for injectivity *)
            let (goall1, goall2) = split_list size_evl goall' in
            let rev_evl = List.rev evl in
            let rev_goall1 = List.rev goall1 in
            let rev_goall2 = List.rev goall2 in

            try
              check_query_falsified_rec (fun event_table1 ->
                check_query_falsified_rec (fun _ ->
                  (* The trace may not falsify the query *)
                  Display.Def.print_line "I could not confirm that the previous trace falsifies the query.";
                  false
                ) event_table1 hyp rev_evl rev_goall2
              ) event_table hyp rev_evl rev_goall1
            with Unify -> true
          else
            (* The trace corresponds to a standard clause *)
            try
              check_query_falsified_rec (fun _ ->
                (* The trace may not falsify the query *)
                Display.Def.print_line "I could not confirm that the previous trace falsifies the query.";
                false
              ) event_table hyp (List.rev evl) (List.rev goall')
            with Unify -> true
        end
    | _ ->
        Parsing_helper.internal_error "The goal of the trace does not match the query (4)"

(* Main trace reconstruction function *)

let build_trace state =
  if !debug_find_io_rule then
    begin
      auto_cleanup (fun () ->
	Display.Text.print_line "Available rules:";
	List.iter display_rule state.io_rule)
    end;
  (* We start a new trace: empty the event table *)
  let final_state = normal_state reduction true state 0 in
  display_trace final_state;
  if !Param.html_output then
    Display.Html.display_goal Display.term_to_term noninterftest_to_string final_state true
  else
    Display.Text.display_goal Display.term_to_term noninterftest_to_string final_state true;
  (final_state, (final_state.hyp_not_matched = []) && (final_state.assumed_false = []))

let is_inj = function
    Some (Before(QSEvent(Some _,_,_,_)::_,_)) -> true
      (* The injective event, if any, always appears first before ==> in the query *)
  | _ -> false

let do_reduction opt_query axioms tree =
  (*  Profile.start();  *)
  made_forward_step := true;
  failed_traces := 0;
  let freenames = (!Param.current_state).pi_freenames in
  let public_init = public_build freenames in
  public_free := List.map snd public_init;
  Param.display_init_state := true;
  init_name_mapping freenames;
  let inj_mode = is_inj opt_query in
  let links = ref [] in

  try
    Reduction_helper.instantiate_natural_predicates (fun () ->
      if not inj_mode then
        close_tree tree
      else
        close_tree_collect_links links tree;
      (* At this point, all variables in tree are linked with TLink n where n
         is a fresh public name that do not contain any parameter. *)

      (* The variable links is used to restore the links destroyed by
         rev_name_subst, only when inj_mode is true, so we avoid computing
         it when inj_mode is false *)
      let ({ proc = main_process }, query) = Param.get_process_query (!Param.current_state) in
      let (goal, id_goals) =
        match query with
        | WeakSecret _ ->
           begin
             let accu = ref [] in
             let weaksecrets = ref None in
             let compute_term = analyze_weak_secret_tree accu weaksecrets tree in
             match !weaksecrets with
             | None ->
                Parsing_helper.internal_error "weak secret clause should appear"
             | Some (w1,w2) ->
                WeakSecrGoal(!accu, compute_term, w1, w2),[]
           end
        | NonInterfQuery _ ->
           NonInterfGoal(analyze_non_interf_tree tree),[]
        | CorrespQuery _ | CorrespQEnc _ ->
            let (goal_list,id_goals) = get_corresp_goals tree in
            let goal_list' = update_corresp_goals_with_injectivity goal_list in
            CorrespGoal(goal_list'),id_goals
              (* Name insides the goals are replaced by fresh private names without any parameter.
                 Note that [rev_name_subst_fact f] are closed (no variables).
                 Variables of the goals were linked with TLink2 meaning that variables of the tree may have both TLink and TLink2 at that point. *)
        | _ ->
           Parsing_helper.internal_error "Unexpected query in reduction.ml"
      in
      let init_state =
        { goal = goal;
          subprocess = [(main_process, [],[],[],Nothing)];
          public = public_init;
          pub_vars = List.map fst public_init;
          tables = [];
          io_rule = [];
          prepared_attacker_rule = [];
          previous_state = None;
          hyp_not_matched = [];
          assumed_false = [];
          current_phase = 0;
          comment = RInit;
          events = [];
          barriers = []
        }
      in
      let res =
        Display.auto_cleanup_display (fun () ->
          try
            if !Param.html_output then
              begin
                let qs = string_of_int (!Param.derivation_number) in
                Display.LangHtml.openfile ((!Param.html_dir) ^ "/trace" ^ qs ^ ".html") ("ProVerif: trace for query " ^ qs);
                Display.Html.print_string "<H1>Trace</H1>\n";
              end;
            let state = init_rule init_state tree in
            (* Close initially the set public *)
            let state = close_public_initial state in
            (* print_string ((string_of_int (List.length state.io_rule)) ^ " io rules");
               print_newline(); *)
            let (final_state, r) = build_trace state in
            let dot_err = Reduction_helper.create_pdf_trace Display.term_to_term noninterftest_to_string "" final_state in
            if !Param.html_output then
              begin
                Display.LangHtml.close();
                let qs = string_of_int (!Param.derivation_number) in
                Display.Html.print_string ("<A HREF=\"trace" ^ qs ^ ".html\">Trace</A><br>\n");
                if (not !Param.command_line_graph_set) && (!Param.trace_backtracking && (dot_err = 0))  then
                  Display.Html.print_string ("<A HREF=\"trace" ^ qs ^ ".pdf\">Trace graph</A><br>\n")
              end;

            let result = r &&
              (match opt_query with
                Some q ->
                  (* When the query is present, verify that the trace really falsifies the query *)
                  check_query_falsified q id_goals final_state
              | None -> true)
            in
            if result
            then
              (* Check the validity of the trace w.r.t. axioms *)
              Lemma.check_axioms final_state axioms;
            result
          with No_result ->
            if not (!Param.trace_backtracking) then
              Display.Def.print_line "Blocked!";

            if !Param.html_output then
              begin
                Display.LangHtml.close();
                if not (!Param.trace_backtracking) then
                  begin
                    let qs = string_of_int (!Param.derivation_number) in
                    Display.Html.print_string ("<A HREF=\"trace" ^ qs ^ ".html\">Unfinished trace</A><br>\n")
                  end;
                Display.Html.print_line "Could not find a trace corresponding to this derivation."
              end;
            Display.Text.print_line "Could not find a trace corresponding to this derivation.";
            false
        )
      in
      (*  print_endline ("Failed " ^ (string_of_int (!failed_traces)) ^ " traces."); *)
      (*  Profile.stop(); *)
      res
    ) tree
  with TermsEq.FalseConstraint -> false

let do_reduction recheck opt_query lemmas tree =
  let res =
    Display.auto_cleanup_display (fun () ->
      History.unify_derivation (fun tree ->
        Display.auto_cleanup_display (fun () ->
          do_reduction opt_query lemmas tree
        )
      ) recheck tree
    )
  in
  cleanup ();
  res
