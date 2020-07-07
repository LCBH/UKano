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

let never_select_weight = -10000
let match_concl_weight = -7000
let default_add_no_unif_weight = -5000
let default_user_no_unif_weight = -6000
let dummy_weight = -4000

let no_unif_set = ref ([] : (fact_format * int) list)
let no_unif_concl_set = ref ([] : (fact_format * int) list)

(* [no_unif_induction] represents the list of nounif declared with
   the option [ignoreOnce] *)
let no_unif_induction = ref ([] : fact_format list)

(* [no_unif_induction_saturation] represents the list of nounif declared with
   the option [InductionSat] *)
let no_unif_induction_saturation = ref ([] : (fact_format * binder list) list)
let inst_constraints = ref false
let modify_nounif = ref true
let apply_induction = ref true

let weight_of_user_weight n =
  if n >= 0 then default_user_no_unif_weight else
    if n <= never_select_weight then never_select_weight+1 else
      n

let initialize v_no_unif_set solver_kind =

  no_unif_set := [];
  no_unif_concl_set := [];
  no_unif_induction := [];
  no_unif_induction_saturation := [];

  List.iter (fun (f,n,opt) ->
    let n = weight_of_user_weight n in

    List.iter (function
      | Hypothesis -> no_unif_set := (f,n) :: !no_unif_set
      | Conclusion -> no_unif_concl_set := (f,n) :: !no_unif_concl_set
      | InductionVerif -> no_unif_induction := f :: !no_unif_induction
      | InductionSat vl -> no_unif_induction_saturation := (f,vl) :: !no_unif_induction_saturation
    ) opt;

    if !Param.nounif_ignore_once = Param.NIO_All && not (List.exists (fun op -> op = InductionVerif) opt)
    then no_unif_induction := f :: !no_unif_induction
  ) v_no_unif_set;

  match solver_kind with
    Solve_Equivalence
  | Solve_WeakSecret _ ->
     inst_constraints := true
  | _ ->
     inst_constraints := false

let rec has_same_format_term t1 t2 =
   match (t1,t2) with
   | (FunApp(f1,l1), FFunApp(f2,l2)) ->
        (f1 == f2) && (List.for_all2 has_same_format_term l1 l2)
   | (Var _, FVar v2) | (_, FAny v2) ->
       begin
	 match v2.link with
	   NoLink ->
	     begin
	       if v2.unfailing then
		 begin
		   Terms.link v2 (TLink t1);
		   true
		 end
	       else
		 (* v2 is a message variable; the matching works only if t1 is a message *)
		 match t1 with
		   Var v' when v'.unfailing -> false
		 | FunApp(f,[]) when f.f_cat = Failure -> false
		 | _ -> Terms.link v2 (TLink t1); true
	     end
	 | TLink t1' -> Terms.equal_terms t1 t1'
	 | _ -> Parsing_helper.internal_error "unexpected link in has_same_format_term"
       end
   | (_,_) -> false

let has_same_format (c1, p1) (c2, p2) =
  (c1 == c2) && (auto_cleanup (fun () -> List.for_all2 has_same_format_term p1 p2))

let rec find_same_format f = function
    [] -> 0
  | ((a,n)::l) -> if has_same_format f a then n else find_same_format f l

(* Function dealing with induction nounif *)

let rec has_same_format_induction nextf (c1,p1) (c2,p2,vl2) =
  if (c1 == c2)
  then
    let vl' =
      auto_cleanup (fun () ->
        if List.for_all2 has_same_format_term p1 p2
        then
          List.map (fun v2 -> match v2.link with
            | TLink (Var v2') -> v2'
            | _ -> Parsing_helper.internal_error "[selfun.ml >> has_same_format_induction] Inductive variable can only be matched with other variables"
          ) vl2
        else raise Not_found
      )
    in
    nextf vl'
  else raise Not_found

(* [find_inductive_variable_to_remove nextf rule] tries to find two facts in the
   hypotheses of [rule] that match the same nounif declared with the option
   [inductionOn]. When it is the case, by definition of the nounif, it extracts
   the two lists of variables in the hypotheses of [rule] corresponding to the
   nounif declaration, say v11,...,v1n and v21,...,v2n, and checks whether
     1) v11 >= v21 && v12 >= v22 && ... && v1n >= v2n
     2) or, v11 <= v21 && v12 <= v22 && ... && v1n <= v2n
   is implied by the constraints in [rule].
   In case 1: the function applies [nextf] to the list v21,...,v2n
   In case 2: the function applies [nextf] to the list v11,...,v1n
   Otherwise it raises Not_found. *)
let find_inductive_variable_to_remove nextf (hyp,_,_,constra) =

  if !no_unif_induction_saturation = []
  then raise Not_found;

  let rec find_unif_induction nextf hyp = function
    | [] -> raise Not_found
    | ((p,args),vl)::q ->
        try
          has_same_format_induction (fun vl' ->
            nextf vl' (p,args,vl)
          ) hyp (p,args,vl)
        with Not_found -> find_unif_induction nextf hyp q
  in

  let rec find_inductive_variable_hyp nextf v1 format = function
    | [] -> raise Not_found
    | Pred(p2,args2)::q2 ->
        try
          has_same_format_induction nextf (p2,args2) format
        with Not_found -> find_inductive_variable_hyp nextf v1 format q2
  in

  let rec find_inductive_variable_hyp_list nextf = function
    | [] -> raise Not_found
    | Pred(p1,args1)::q1 ->
        try
          find_unif_induction (fun vl1 format ->
            find_inductive_variable_hyp (fun vl2 ->
              let binders = ref vl1 in
              List.iter (fun v2 -> if not (List.memq v2 !binders) then binders := v2 :: !binders ) vl2;

              (* We have two variables that satisfy the same format.
                 We now check whether the constraints imply v1 >= v2 or v2 >= v1 *)
              try
                let constra' = { neq = []; is_nat = []; is_not_nat = []; geq = List.map2 (fun v1 v2 -> (Var v1,0,Var v2)) vl1 vl2} in
                TermsEq.implies_constraints_keepvars_binders !binders constra constra';
                nextf vl2
              with NoMatch ->
                try
                  let constra' = { neq = []; is_nat = []; is_not_nat = []; geq = List.map2 (fun v1 v2 -> (Var v2,0,Var v1)) vl1 vl2} in
                  TermsEq.implies_constraints_keepvars_binders !binders constra constra';
                  nextf vl1
                with NoMatch -> raise Not_found
            ) vl1 format q1
          ) (p1,args1) !no_unif_induction_saturation
        with Not_found -> find_inductive_variable_hyp_list nextf q1
  in

  find_inductive_variable_hyp_list nextf hyp

(* [induction_required ()] returns [true] if and only if some nounif have been
   declared with the option [ignoreOnce]. *)
let induction_required () = !no_unif_induction != []

(* The i-th element of [induc_auth] indicates whether we can apply a resolution on
  the i-th hypothesis of the clause despite the declaration of a nounif. Note that
  such application can only occur if the matching nounif has been declared with the
  option [ignoreOnce].

  [selection_induction hyp induc_auth] checks whether one hypothesis of hyp can be
  matched with a nounif declared with option [ignoreOnce] and the application
  is authorized by [induc_auth]. When it is the case, the function returns the position [i]
  of the hypothesis in [hyp] as well as an updated authorization list in which the
  authorization for the [i]th hypothesis has been revoked. Typically, this new
  authorization list will be used after the resolution on the [i]th hypothesis
  to enforce that such resolution is applied only once per hypothesis.

  When no hypothesis is authorized, the function returns -1 and [induc_auth].
*)
let selection_induction hyp induc_auth =

  let rec explore_hyp n passed_induc hyp induc_auth = match hyp,induc_auth with
    | [], [] -> (-1,List.rev passed_induc)
    | [], _
    | _, [] -> Parsing_helper.internal_error "[selfun.ml >> selection_induction] The hypotheses and induction authorisation should have the same length."
    | Pred(p,args) :: q_hyp, (ord,b) :: q_auth ->
        if b && List.exists (has_same_format (p,args)) !no_unif_induction
        then
          (* A format has been matched *)
          let induc_auth' = List.rev_append passed_induc ((ord,false)::q_auth) in
          (n,induc_auth')
        else
          (* No format has been matched *)
          explore_hyp (n+1) ((ord,b)::passed_induc) q_hyp q_auth
  in

  explore_hyp 0 [] hyp induc_auth

(* Remark: format_equal could be a bit less strict. When a variable
   is marked at least once "FVar", it has the same meaning as if it
   is always marked "FVar". *)

let rec format_equal t1 t2 =
   match (t1,t2) with
   | (FFunApp(f1,l1), FFunApp(f2,l2)) ->
        (f1 == f2) && (List.for_all2 format_equal l1 l2)
   | (FVar v1, FVar v2) | (FAny v1, FAny v2) ->
       begin
	 (v1.unfailing == v2.unfailing) &&
	 (match v2.link with
	   NoLink -> Terms.link v2 (VLink v1); true
	 | VLink v1' -> v1 == v1'
	 | _ -> Parsing_helper.internal_error "unexpected link in format_equal")
       end
   | (_,_) -> false

let format_equal_fact (c1, p1) ((c2, p2),_) =
  (c1 == c2) && (auto_cleanup (fun () -> List.for_all2 format_equal p1 p2))

let rec compute_match_format t1 t2 =
   match (t1,t2) with
   | (Var v1), (Var v2) -> FAny v1
   | (Var v1), _ -> FVar v1
   | (FunApp (f1,l1')), (FunApp (f2,l2')) ->
       if f1 != f2 then
	 internal_error "terms do not match 3";
       FFunApp(f1,List.map2 compute_match_format l1' l2')
   | _,_ -> internal_error "terms do not match 4"

let compute_match_format_fact f1 f2 = match (f1,f2) with
  Pred(c1, p1), Pred(c2, p2) ->
    if c1 != c2 then
      internal_error "facts do not match";
    (c1, List.map2 compute_match_format p1 p2)

(* selection_fun rule returns -1 if no fact is selected in rule, and
   the index of the selected hypothesis otherwise  (0 corresponds to
   the first hypothesis)
*)

(* Standard, equivalent to the old version without selection function *)

let term_warning ((hyp, concl, _, _) as rule) =
  if (!Param.max_depth) < 0 then
    begin
      if (!Param.should_stop_term) || (!Param.verbose_term) then
	begin
	  print_string "The following rule unifies with itself\n";
	  Display.Text.display_rule_indep rule;
	  print_string "The completion process will probably not terminate\n"
	end;
      if !Param.should_stop_term then
	begin
	  print_string "You have several solutions to guarantee termination:\n";
	  print_string " - limit the depth of terms with param maxDepth = <depth>.\n";
	  print_string " - add one of the unifying facts of this rule to the set\n";
	  print_string "   of facts on which unification is forbidden, with nounif <fact>.\n";
	  print_string " - add a rule that is more general than all rules generated by the\n";
	  print_string "   unifications of the above rule. (Maybe you have already done that, and I\n";
	  print_string "   did not detect it. If so, ignore this message by pressing [return].)\n";
	  print_string "Press [return] to continue, [ctrl-c] to stop\n";
	  Param.should_stop_term := false;
	  ignore(read_line())
	end
    end

let selection_fun_nounifset ((hyp, concl, _, _) as rule) =
  let rec sel (nold, wold) n = function
      [] ->
        if (nold >= 0) && (matchafactstrict concl (List.nth hyp nold)) && (!modify_nounif) then
	  term_warning(rule);
        nold
    | (f::l) when is_unselectable f ->
	  (* Guarantee that p(x) is never selected when we decompose data
	     constructors on p, except that we can select the conclusion when
	     all hypotheses and the conclusion are of the form p(x) for
	     such p. This is important for the soundness of
	     the decomposition of data constructors. *)
        sel (nold, wold) (n+1) l
    | (Pred(p,lp) as h::l) ->
	let wnew = find_same_format (p,lp) (!no_unif_set) in
	if wnew < 0 then
	  if wnew > wold
 	  then sel (n,wnew) (n+1) l
          else sel (nold, wold) (n+1) l
	else
	  begin
	    if (matchafactstrict concl h) && (!modify_nounif) then term_warning(rule);
	    n
	  end
  in
  if is_unselectable concl then
    (* The conclusion is never selected if an hypothesis can be *)
    sel (-1, never_select_weight) 0 hyp
  else
    (* The conclusion can be selected if we don't find better in
       the hypothesis *)
    match concl with
      | Pred(p,args) ->
          let w = find_same_format (p,args) !no_unif_concl_set in
          if w < 0
          then sel (-1, w) 0 hyp
          else sel (-1, -1) 0 hyp



(* Very good for skeme, but slightly slower for some other protocols *)

let selection_fun_nounifset_maxsize ((hyp, concl, _, _) as rule) =
  let rec sel (nold, wold) n = function
      [] ->
	if (nold >= 0) && (matchafactstrict concl (List.nth hyp nold)) && (!modify_nounif) then
	  term_warning(rule);
	nold
    | (f::l) when is_unselectable f ->
	  (* Guarantee that p(x) is never selected when we decompose data
	     constructors on p, except that we can select the conclusion when
	     all hypotheses and the conclusion are of the form p(x) for
	     such p. This is important for the soundness of
	     the decomposition of data constructors. *)
        sel (nold, wold) (n+1) l
    | (Pred(p,lp) as h::l) ->
	let wtmp = find_same_format (p,lp) (!no_unif_set) in
        let wnew =
	  if wtmp < 0
	  then wtmp
	  else fact_size h
	in
        if wnew > wold
	then sel (n,wnew) (n+1) l
        else sel (nold, wold) (n+1) l
  in
  if is_unselectable concl then
    (* The conclusion is never selected if an hypothesis can be *)
    sel (-1, never_select_weight) 0 hyp
  else
    (* The conclusion can be selected if we don't find better in
       the hypothesis *)
    match concl with
      | Pred(p,args) ->
          let w = find_same_format (p,args) !no_unif_concl_set in
          if w < 0
          then sel (-1, w) 0 hyp
          else sel (-1, -1) 0 hyp

(* Very good for termination - even if it does not solve all cases, of course *)

let selection_fun_weight ((hyp, concl, _, _) as rule) =
  let rec sel (nold, wold) n = function
      [] ->
	if (nold = -1) && (!modify_nounif) then (* conclusion selected *)
	  begin
	    List.iter (function h ->
	      if matchafactstrict concl h then
		begin
		  let format = compute_match_format_fact h concl in
		  if not (List.exists (format_equal_fact format) (!no_unif_set)) then
		    begin
		      no_unif_set := (format, default_add_no_unif_weight) :: !no_unif_set;
		      if !Param.nounif_ignore_once <> Param.NIO_None
		      then no_unif_induction := format :: !no_unif_induction;
		      if !Param.verbose_term then
			begin
			  print_string "nounif ";
			  Display.Text.display_fact_format format;
			  print_string ("/" ^ (string_of_int default_add_no_unif_weight));
			  Display.Text.newline()
			end
		    end
		end) hyp
	  end;
        if (!Param.verbose_term) && (((wold < 0) && (nold >= 0)) (* || (wold < -1) *) ) && (!modify_nounif) then
	  begin
	    print_string "Termination warning: ";
	    Display.Text.display_rule_indep rule;
	    print_string ("Selecting " ^ (string_of_int nold));
	    Display.Text.newline()
	  end;
        nold
    | (f::l) when is_unselectable f ->
	  (* Guarantee that p(x) is never selected when we decompose data
	     constructors on p. This is important for the soundness of
	     the decomposition of data constructors. *)
        sel (nold, wold) (n+1) l
    | (Pred(p,lp) as h::l) ->
	let wnew =
	  if matchafactstrict concl h then match_concl_weight else
	  let wtmp = find_same_format (p,lp) (!no_unif_set) in
	  if wtmp < 0 then wtmp else
	  if !Param.select_fun == Param.TermMaxsize then fact_size h else 0
	in
        if wnew > wold
	then sel (n,wnew) (n+1) l
        else sel (nold, wold) (n+1) l
  in
  let wconcl =
    if is_unselectable concl then
      (* The conclusion is never selected if an hypothesis can be *)
      never_select_weight
    else
      match concl with
	Pred(p, []) when p == Param.dummy_pred -> dummy_weight
      |	Pred(p,args) ->
          (* The conclusion can be selected if we don't find better in
	     the hypothesis *)
	  if List.exists (fun h -> matchafactstrict h concl) hyp
          then match_concl_weight
          else
            let w = find_same_format (p,args) !no_unif_concl_set in
            if w < 0
            then w
            else -1
  in
  sel (-1, wconcl) 0 hyp

(* Avoid creating cycles when instantiating in inst_constra:
   renames all variables to unused ones. *)
let rec false_copy = function
    Var v -> Terms.new_var_def_term v.btype
  | FunApp(f,l) -> FunApp(f, List.map false_copy l)

let inst_constra = function
  | (Var v,t) ->
      if v.link = NoLink then
	Terms.link v (TLink (false_copy t))
  | _ -> ()



let selection_fun ((hyp,concl,hist,constra) as rule) =
  let r =
   match !Param.select_fun with
     Param.NounifsetMaxsize -> selection_fun_nounifset_maxsize rule
   | Param.Term | Param.TermMaxsize -> selection_fun_weight rule
   | Param.Nounifset -> selection_fun_nounifset rule
  in
  let r =
    (* For proofs of equivalences (!inst_constraints = true),
       if the conclusion is selected (r = -1) and it is unselectable,
       that is, it is of the form such as bad: or attacker:x,x',
       then we try to find a better selection by selecting an hypothesis
       attacker:x,x' in which x (or x') occurs in an inequality x <> M. *)
    if (r = -1) && (!inst_constraints) && (is_unselectable concl) then
      begin
	List.iter (List.iter inst_constra) constra.neq;
	let rule2 = (List.map copy_fact2 hyp, copy_fact2 concl, hist, copy_constra2 constra) in
	Terms.cleanup();
	match !Param.select_fun with
	  Param.NounifsetMaxsize -> selection_fun_nounifset_maxsize rule2
	| Param.Term | Param.TermMaxsize -> selection_fun_weight rule2
	| Param.Nounifset -> selection_fun_nounifset rule2
      end
    else r
  in
  let r =
    if r = -1 then Noninterf.selfun rule else r
  in
  if r = -1 then Weaksecr.selfun rule else r

let selection_fun_nostatechange rule =
  modify_nounif := false;
  let r = selection_fun rule in
  modify_nounif := true;
  r

let guess_no_unif rulequeue =
  (* If no "nounif" instruction is given, first guess them by "selection_fun_weight" *)
  if (!no_unif_set = []) || (!Param.select_fun == Param.Term)
      || (!Param.select_fun == Param.TermMaxsize) then
    Pvqueue.iter rulequeue (fun r -> ignore (selection_fun_weight r))
