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
open Pitypes
open Terms
open Parsing_helper

let has_equations = ref false

let hasEquations() =
  !has_equations

let non_syntactic f =
  match f.f_cat with
  | Syntactic f' -> f'
  | _ -> f


(******** Close clauses modulo the equational theory ******
 close_rule_eq is used for clauses entered by the user in Horn-clause
 front-ends,
 close_fact_eq is used for closing the goals

 We assume here that terms do not contain destructor function symbols. *)

let rec close_list_eq close_elt restwork = function
  | [] -> restwork []
  | elt::q ->
      close_elt (fun elt' ->
        close_list_eq close_elt (fun q' ->
          restwork (elt'::q')
        ) q
      ) elt

let rec close_term_eq restwork = function
    Var x ->
      begin
        match x.link with
          TLink t -> close_term_eq restwork t
        (* TO DO should I always recursively close links modulo equations? *)
        | NoLink -> restwork (Var x)
        | _ -> internal_error "unexpected link in close_term_eq"
      end

  | FunApp(f,l) ->
      close_list_eq close_term_eq (fun l' ->
        restwork (FunApp(f,l'));
        match f.f_cat with
        | Eq eqlist ->
            List.iter (fun (lhd,rhs) ->
              Terms.auto_cleanup (fun () ->
                let (leq', req',_) = copy_red (lhd,rhs,true_constraints) in
                try
                  List.iter2 unify l' leq';
                  restwork req'
                with Unify -> ()
                    )
            ) eqlist
         | _ -> ()
      ) l

let close_term_list_eq = close_list_eq close_term_eq

let close_geq_eq restwork (t1,n,t2) =
  close_term_eq (fun t1' ->
    close_term_eq (fun t2' ->
      restwork (t1',n,t2')
    ) t2
  ) t1

let close_constra_eq restwork c =
  (* Disequalities and predicates is_not_nat are not closed modulo the equational theory. *)
  close_term_list_eq (fun is_nat ->
    close_list_eq close_geq_eq (fun geq ->
      restwork { c with is_nat = is_nat; geq = geq }
    ) c.geq
  ) c.is_nat

let close_fact_eq restwork = function
    Pred(p,l) ->
      close_term_list_eq (fun l' -> restwork (Pred(p,l'))) l

let rec close_fact_list_eq = close_list_eq close_fact_eq

let close_rule_eq restwork (hyp,concl,hist,constra) =
  close_fact_list_eq (fun hyp' ->
    close_fact_eq (fun concl' ->
      close_constra_eq (fun constra' ->
        let tmp_bound = !current_bound_vars in
        current_bound_vars := [];

        let hyp'' = List.map copy_fact2 hyp' in
        let concl'' = copy_fact2 concl' in
        let constra'' = copy_constra2 constra' in

        let histref = ref hist in

        (* Generate history w.r.t. hypotheses *)
        let rank = ref 0 in
        List.iter2 (fun hyp1 hyp1' ->
          if not (equal_facts hyp1 hyp1')
          then histref := HEquation(!rank, copy_fact2 hyp1, copy_fact2 hyp1', !histref);
          incr rank
        ) hyp hyp';

        let r = (hyp'', concl'',
                 (if equal_facts concl concl' then
                   (!histref)
                 else
                   HEquation(-1, concl'', copy_fact2 concl, !histref)),
                 constra'') in
        cleanup();
        restwork r;
        current_bound_vars := tmp_bound
      ) constra
    ) concl
  ) hyp

let close_rule_hyp_eq restwork (hyp,concl,hist,constra) =
  close_fact_list_eq (fun hyp' ->
    close_constra_eq (fun constra' ->
      let tmp_bound = !current_bound_vars in
      current_bound_vars := [];

      let hyp'' = List.map copy_fact2 hyp' in
      let constra'' = copy_constra2 constra' in

      let histref = ref hist in

      (* Generate history w.r.t. hypotheses *)
      let rank = ref 0 in
      List.iter2 (fun hyp1 hyp1' ->
        if not (equal_facts hyp1 hyp1') then
          histref := HEquation(!rank, copy_fact2 hyp1, copy_fact2 hyp1', !histref);
        incr rank) hyp hyp';

      let r = (hyp'', copy_fact2 concl, !histref, constra'') in
      cleanup();
      restwork r;
      current_bound_vars := tmp_bound
    ) constra
  ) hyp

let close_term_eq restwork t =
  if hasEquations() then close_term_eq restwork t else restwork t

let close_term_list_eq restwork t =
  if hasEquations() then close_term_list_eq restwork t else restwork t

let close_fact_eq restwork t =
  if hasEquations() then close_fact_eq restwork t else restwork t

let close_fact_list_eq restwork t =
  if hasEquations() then close_fact_list_eq restwork t else restwork t

let close_rule_eq restwork t =
  if hasEquations() then close_rule_eq restwork t else restwork t

(***** Close clauses by rewrite rules of constructors and destructors. *****
   Used for clauses that define predicates (for LetFilter).

   The variable accu_constra collects side-conditions of
   destructors. *)

let rec close_list_destr_eq close_elt accu_constra restwork = function
  | [] -> restwork accu_constra []
  | elt::q ->
      close_elt accu_constra (fun accu_constra1 elt' ->
        close_list_destr_eq close_elt accu_constra1 (fun accu_constra2 q' ->
          restwork accu_constra2 (elt'::q')
        ) q
      ) elt

let rec close_term_destr_eq accu_constra restwork = function
    Var x ->
      begin
        match x.link with
          TLink t ->
          (* TO DO should I always recursively close links modulo equations? *)
            close_term_eq (fun t' -> restwork accu_constra t') t
        | NoLink -> restwork accu_constra (Var x)
        | _ -> internal_error "unexpected link in close_term_destr_eq"
      end
  | FunApp(f,l) ->
      close_list_destr_eq close_term_destr_eq accu_constra (fun accu_constra' l' ->
        let eqlist = Terms.red_rules_fun f in

        List.iter (fun red ->
          Terms.auto_cleanup (fun () ->
            let (leq', req', side_c') = copy_red red in

            try
              List.iter2 unify l' leq';
              restwork (wedge_constraints side_c' accu_constra') req'
            with Unify -> ()
                )
            ) eqlist
        ) l

let close_fact_destr_eq accu_constra restwork = function
    Pred(p,l) ->
      close_list_destr_eq close_term_destr_eq accu_constra
        (fun accu_constra' l' ->
          Terms.auto_cleanup (fun () ->
            try
            (* Check that the arguments of the predicate do not fail,
               by unifying them with a message variable (which cannot be fail) *)
              List.iter (fun t -> unify t (Terms.new_var_def_term (Terms.get_term_type t))) l';
              restwork accu_constra' (Pred(p,l'))
            with Unify -> ()
                )
            ) l

let close_term_no_fail_destr_eq accu_constra restwork t =
  close_term_destr_eq accu_constra (fun accu_constra' t' ->
    Terms.auto_cleanup (fun () ->
      try
        (* Check that the term does not fail, by unifying them with a
           message variable (which cannot be fail) *)
        unify t' (Terms.new_var_def_term (Terms.get_term_type t'));
        restwork accu_constra t
      with Unify -> ()
    )
  ) t

let close_pair_term_no_fail_destr_eq accu_constra restwork (t1,t2) =
  close_term_no_fail_destr_eq accu_constra (fun accu_constra1 t1' ->
    close_term_no_fail_destr_eq accu_constra1 (fun accu_constra2 t2' ->
      restwork accu_constra2 (t1',t2')
    ) t2
  ) t1

let close_geq_no_fail_destr_eq accu_constra restwork (t1,n,t2) =
  close_pair_term_no_fail_destr_eq accu_constra (fun accu_constra' (t1',t2') ->
    restwork accu_constra' (t1',n,t2')
  ) (t1,t2)

let close_constra_destr_eq accu_constra restwork c =
  close_list_destr_eq (close_list_destr_eq close_pair_term_no_fail_destr_eq) accu_constra (fun accu_constra1 neq ->
    close_list_destr_eq close_term_destr_eq accu_constra1 (fun accu_constra2 is_nat ->
      close_list_destr_eq close_term_destr_eq accu_constra2 (fun accu_constra3 is_not_nat ->
        close_list_destr_eq close_geq_no_fail_destr_eq accu_constra3 (fun accu_constra4 geq ->
          restwork accu_constra4 { neq = neq; is_nat = is_nat; is_not_nat = is_not_nat; geq = geq }
        ) c.geq
      ) c.is_not_nat
    ) c.is_nat
  ) c.neq

let close_rule_destr_eq restwork (hyp,concl,constra) =
  close_list_destr_eq close_fact_destr_eq true_constraints (fun accu_constra hyp' ->
    close_fact_destr_eq accu_constra (fun accu_constra' concl' ->
      close_constra_destr_eq accu_constra' (fun accu_constra'' constra' ->
        let tmp_bound = !current_bound_vars in
        current_bound_vars := [];
        let r = (List.map copy_fact2 hyp', copy_fact2 concl', copy_constra2 (wedge_constraints accu_constra'' constra')) in
        cleanup();
        restwork r;
        current_bound_vars := tmp_bound
      ) constra
    ) concl
  ) hyp

(********* Transform equations into rewrite rules *********)

(* Copy an equation *)

let copy_eq (leq, req) =
  assert (!current_bound_vars == []);
  let eq' = (copy_term2 leq, copy_term2 req) in
  cleanup();
  eq'

(* Swap sides of an equation *)

let swap_eq (leq, req) = (req, leq)

(* Complete the equations, to obtain all terms equal to one term
   Store the result in the information associated with each constructor *)

let rewrite_system = ref []
let order = ref []

let rec normal_form = function
    Var v -> Var v
  | FunApp(f,l) ->
      let t' = FunApp(f, List.map normal_form l) in
      let rec find_red = function
        [] -> t'
      | ((leq,req)::redl) ->
         try
           if not (Terms.equal_types (Terms.get_term_type leq) (Terms.get_term_type t')) then
      raise NoMatch;
           Terms.match_terms leq t';
           let r = copy_term3 req in
           Terms.cleanup();
           normal_form r
         with NoMatch ->
           Terms.cleanup();
           find_red redl
      in
      find_red (!rewrite_system)

let rec joinable_critical_pairs build_context (leq1, req1) (leq2, req2) =
  match leq2 with
    Var v -> true
  | FunApp(f,l) ->
      ((not (Terms.equal_types (Terms.get_term_type leq1) (Terms.get_term_type leq2))) ||
       (try
         Terms.unify leq1 leq2;
         let req1' = copy_term2 (build_context req1) in
         let req2' = copy_term2 req2 in
         Terms.cleanup();
         let r = Terms.equal_terms (normal_form req1') (normal_form req2') in
         (*if not r then
           begin
             print_string "Non-joinable critical pair:";
             display_eq (leq1,req1);
             print_string " and ";
             display_eq (leq2,req2);
             print_string ". We should have ";
             display_eq (req1',req2');
             print_string "\n"
           end;*)
         r
       with Unify ->
         Terms.cleanup();
         true
      ))
        &&
      (
       let seen = ref [] in
       let to_see = ref l in
       List.for_all (fun x ->
	 to_see := List.tl (!to_see);
	 let cur_seen = !seen in
	 let cur_to_see = !to_see in
	 let r = joinable_critical_pairs (fun y -> build_context (
	   FunApp(f, List.rev_append cur_seen (y :: cur_to_see))))
	     (leq1, req1) (x, req2) in
	 seen := x :: (!seen);
	 r) l
      )


let rec check_confluent new_rule = function
  [] -> true
| (a::l) ->
    (joinable_critical_pairs (fun x -> x) a new_rule) &&
    (joinable_critical_pairs (fun x -> x) new_rule a) &&
    (check_confluent new_rule l)


let eq_queue = Pvqueue.new_queue()
let eq_base = ref []
let eq_count = ref 0

let rec build_rules_eq leq req f get_rule = function
   FunApp(f2,l) as t ->
      if f2 == f then
      begin
	assert (!current_bound_vars == []);
        try
          unify t leq;
          get_rule req
        with Unify ->
          cleanup()
      end;
      build_rules_eq_list leq req f (fun concl_list -> get_rule (FunApp(f2,concl_list))) l
  | Var _ -> ()

and build_rules_eq_list leq req f get_rule = function
    [] -> ()
  | (a::l) ->
      build_rules_eq leq req f (fun concl -> get_rule (concl::l)) a;
      build_rules_eq_list leq req f (fun concl_list -> get_rule (a::concl_list)) l

let rec implies_eq (leq1, req1) (leq2, req2) =
  assert (!current_bound_vars == []);
  try
    if not (Terms.equal_types (Terms.get_term_type leq1) (Terms.get_term_type leq2)) then
      raise NoMatch;
    Terms.match_terms leq1 leq2;
    Terms.match_terms req1 req2;
    cleanup();
    true
  with NoMatch ->
    cleanup();
    (* Try to match the equation inside a context *)
    match leq2, req2 with
      (FunApp(fl, ll), FunApp(fr, lr)) when fl == fr ->
	List.exists2 (fun leq2 req2 ->
	  implies_eq (leq1, req1) (leq2, req2)) ll lr
    | _ -> false

let add_eq (leq, req) =
  (* reduce to normal form *)
  let leq =
    match leq with
      FunApp(f,l) -> FunApp(f, List.map normal_form l)
    | _ -> leq in
  let req = normal_form req in
  let new_eq = (leq, req) in
  (* check not a trivial equation *)
  if equal_terms leq req then () else
  (* check not x = y *)
  match (leq, req) with
    Var x, Var y when x != y ->
      user_error "The equational theory equates all terms.\nThis trivial case is not supported by the verifier."
  | _ ->
  (* check not subsumed *)
  let test_impl = fun eq -> implies_eq eq new_eq in
  if (List.exists test_impl (!eq_base)) ||
     (Pvqueue.exists eq_queue test_impl) then () else
  begin
    let test_impl = fun eq -> not(implies_eq new_eq eq) in
    eq_base := List.filter test_impl (!eq_base);
    Pvqueue.filter eq_queue test_impl;
    Pvqueue.add eq_queue new_eq
  end

(* Combine leq2 -> req2 followed by leq1 -> req1
   when req2 unifies with C[leq1] *)

let combine_eq_eq1 (leq1, req1) (leq2, req2) =
  match leq1 with
    Var _ -> ()
  | FunApp(f,_) ->
      build_rules_eq leq1 req1 f (fun new_term ->
        let eq3 = (copy_term2 leq2, copy_term2 new_term) in
        cleanup();
        add_eq eq3) req2

(* Combine leq2 -> req2 followed by leq1 -> req1
   when leq1 unifies with C[req2] *)

let combine_eq_eq2 (leq1, req1) (leq2, req2) =
  match req2 with
    Var _ -> ()
  | FunApp(f,_) ->
      build_rules_eq req2 leq2 f (fun new_term ->
        let eq3 = (copy_term2 new_term, copy_term2 req1) in
        cleanup();
        add_eq eq3) leq1

(* Close the equational theory *)

let rec complete_eq bothdir =
  match Pvqueue.get eq_queue with
    None -> !eq_base
  | Some eq ->
      eq_base := eq :: (!eq_base);
      let eq' = copy_eq eq in
      List.iter (fun eq2 ->
	combine_eq_eq1 eq' eq2;
	combine_eq_eq1 eq2 eq';
	if bothdir then
	  begin
	    combine_eq_eq2 eq' eq2;
	    combine_eq_eq2 eq2 eq';
	    if (!rewrite_system) != [] then (* Useful only for non-proved algo. *)
	      begin
		let eqs' = swap_eq eq' in
		let eqs2 = swap_eq eq2 in
		(* Swap eq' *)
		combine_eq_eq1 eqs' eq2;
		combine_eq_eq1 eq2 eqs';
		combine_eq_eq2 eqs' eq2;
		combine_eq_eq2 eq2 eqs';
		(* Swap eq2 *)
		combine_eq_eq1 eq' eqs2;
		combine_eq_eq1 eqs2 eq';
		combine_eq_eq2 eq' eqs2;
		combine_eq_eq2 eqs2 eq';
		(* Swap eq' and eq2 *)
		combine_eq_eq1 eqs' eqs2;
		combine_eq_eq1 eqs2 eqs';
		combine_eq_eq2 eqs' eqs2;
		combine_eq_eq2 eqs2 eqs';
	      end (* End useful only for non-proved algo. *)
	  end) (!eq_base);
      if !Param.verbose_rules then
	begin
          Display.Text.display_eq eq;
	  Display.Text.newline()
	end
      else
         begin
           incr eq_count;
	   if (!eq_count) mod 200 = 0 then
	     begin
	       print_string ((string_of_int (!eq_count)) ^
			     " equations inserted. The rule base contains " ^
			     (string_of_int (List.length (!eq_base))) ^
			     " equations. " ^
			     (string_of_int (Pvqueue.length eq_queue)) ^
			     " equations in the queue.");
	       Display.Text.newline()
	     end
	 end;
       complete_eq bothdir

(* Check subterm *)

let rec check_subterm t1 t2 =
  (equal_terms t1 t2) || (check_strict_subterm t1 t2)

and check_strict_subterm t1 t2 =
  match t1 with
    FunApp(_,l) -> List.exists (fun t -> check_subterm t t2) l
  | _ -> false

(* Find the rewrite system S *)

let add_rewrite ((leq, req) as r) =
  (* check that all variables on the right-hand side also occur in the
     left-hand side *)
  let var_right = ref [] in
  Terms.get_vars var_right req;
  if List.for_all (fun v -> Terms.occurs_var v leq) (!var_right) then
    begin
      (* check that the resulting system is confluent *)
      rewrite_system := r :: (!rewrite_system);
      if not (check_confluent r (!rewrite_system)) then
	begin
	  rewrite_system := List.tl (!rewrite_system);
	  false
	end
      else
	true
    end
  else
    false

let rec check_no_path f f' =
  (f != f') &&
  (List.for_all (fun (f2,f2') ->
    if f == f2 then check_no_path f2' f' else true) (!order))


let find_rewrite_system eq =
  let (leq, req) = copy_eq eq in
  if check_strict_subterm req leq then
    ignore (add_rewrite (leq, req))
  else
    match leq with
      FunApp(f,l) ->
	let rec find_fun_symb accu = function
	    Var _ -> accu
	  | FunApp(f2,l2) ->
	      let accu' = if List.memq f2 accu then accu else f2::accu in
	      List.fold_left find_fun_symb accu' l2
	in
	let new_symbols = find_fun_symb [] req in
	if List.for_all (fun f2 -> check_no_path f2 f) new_symbols then
	  if add_rewrite (leq, req) then
	    order := (List.map (fun f2 -> (f,f2)) new_symbols) @ (!order)
    | Var _ -> ()


(* Lexicographic path ordering *)

let rec add_order = function
    (FunApp(f1,l1), (FunApp(f2,l2) as t2)) when f1 == f2 ->
      List.iter (fun t1 -> add_order (t1,t2)) l1;
      List.iter2 (fun t1 t2 -> add_order  (t1,t2)) l1 l2
  | (FunApp(f1,l1), t2) when occurs_f f1 t2 ->
      (*
      Useful for finding a good ordering for Delaune-ex3.prv, but then
      the generation of the rewrite rules corresponding to the equations
      does not terminate anyway, so it's not that useful.
      begin
	match t2 with
	  FunApp(f2,_) ->
	    if check_no_path f2 f1 then
	      order := (f1,f2) :: (!order)
	| _ -> ()
      end; *)
      List.iter (fun t1 -> add_order (t1,t2)) l1
  | (FunApp(f1,l1), t2) ->
      let rec find_fun_symb accu = function
	  Var _ -> accu
	| FunApp(f2,l2) ->
	    let accu' = if List.memq f2 accu then accu else f2::accu in
	    List.fold_left find_fun_symb accu' l2
      in
      let new_symbols = find_fun_symb [] t2 in
      if List.for_all (fun f2 -> check_no_path f2 f1) new_symbols then
	order := (List.map (fun f2 -> (f1,f2)) new_symbols) @ (!order)
  | _ -> ()

let rec get_symbols_t accu = function
    FunApp(f,l) ->
      if not (List.memq f (!accu)) then
	accu := f :: (!accu);
      List.iter (get_symbols_t accu) l
  | Var _ -> ()

let get_symbols accu equations =
  List.iter (fun (t1,t2) ->
    get_symbols_t accu t1;
    get_symbols_t accu t2) equations

let rec convert_to_symbols symbols = function
    [] -> []
  | ((s,ext)::l) ->
      try
	let f = List.find (fun f -> Terms.get_fsymb_basename f = s) symbols in
	f::(convert_to_symbols symbols l)
      with Not_found ->
	convert_to_symbols symbols l

let rec convert_to_pairs ext = function
    [] | [_] -> []
  | a::((b::l) as l') ->
      if List.memq a l' then
	Parsing_helper.input_error ("Ordering of function symbols contain a duplicate element " ^ (Terms.get_fsymb_basename a) ^ ".\n") ext;
      (a,b)::(convert_to_pairs ext l')

let order_from_string (s,ext0) equations =
  let symbols = ref [] in
  List.iter (fun (eq, _) -> get_symbols symbols eq) equations;
  let lexbuf = Lexing.from_string s in
  Parsing_helper.set_start lexbuf ext0;
  let order =
    try
      Pitparser.order Pitlexer.token lexbuf
    with Parsing.Parse_error ->
      Parsing_helper.input_error "Syntax error in ordering"
	(Parsing_helper.extent lexbuf)
  in
  let order = convert_to_symbols (!symbols) order in
  convert_to_pairs ext0 order

let rec greater_lpo t1 t2 = match (t1,t2) with
  (Var v1, _) -> false
| (t1, Var v2) -> occurs_var v2 t1
| (FunApp(f1,l1), FunApp(f2,l2)) ->
    (List.exists (fun t1' -> equal_terms t1' t2 || greater_lpo t1' t2) l1) ||
    ((f1 != f2) && (not (check_no_path f1 f2)) &&
     (List.for_all (greater_lpo t1) l2)) ||
    ((f1 == f2) && (greater_lpo_lex l1 l2))

and greater_lpo_lex l1 l2 = match (l1,l2) with
  ([], []) -> false
| (t1::l1',t2::l2') ->
    (greater_lpo t1 t2) ||
    ((equal_terms t1 t2) && (greater_lpo_lex l1' l2'))
| _ -> Parsing_helper.internal_error "Different length in greater_lpo_lex"

(* Build block of equations disjoint from others *)

let rec get_fun_symb flist = function
    Var v -> ()
  | FunApp(f,l) ->
      if not (List.mem f (!flist)) then flist := f :: (!flist);
      List.iter (get_fun_symb flist) l

let rec unionlist l1 = function
    [] -> l1
  | (a::l) ->
      if List.memq a l1 then
	unionlist l1 l
      else
	a::(unionlist l1 l)

let disjoint_list l1 l2 =
  List.for_all (fun x1 -> not (List.memq x1 l2)) l1

let buildblocks eqlists =
  (* Group the blocks of equations into two sets:
     no_info_block: all equations with no specific information
     other_blocks: the groups of equations with specific information *)
  let no_info_block = ref [] in
  let other_blocks = ref [] in
  List.iter (fun (eqlist, eqinfo) ->
    if eqinfo = EqNoInfo then
      no_info_block := eqlist @ (!no_info_block)
    else
      let flist = ref [] in
      List.iter (fun (eq1,eq2) ->
	get_fun_symb flist eq1;
	get_fun_symb flist eq2) eqlist;
      other_blocks := (!flist, eqlist, eqinfo) :: (!other_blocks)
						    ) eqlists;
  (* Split no_info_block into groups of equations with disjoint
     function symbols *)
  let blocks = ref [] in
  List.iter (fun eq ->
    let flist = ref [] in
    get_fun_symb flist (fst eq);
    get_fun_symb flist (snd eq);
    let tmpblocks = !blocks in
    let cur_block = ref ((!flist),[eq]) in
    blocks := [];
    List.iter (fun (bfunsymb, beq) ->
      if List.exists (fun f1 -> List.memq f1 (!flist)) bfunsymb then
	(* Block has common function symbol with cur_block
           -> merge them *)
	cur_block := (unionlist bfunsymb (fst (!cur_block)),
		      beq @ (snd (!cur_block)))
      else
	(* Block has no common function symbol with cur_block
           -> leave it as it is *)
	blocks := (bfunsymb, beq) :: (!blocks)
      ) tmpblocks;
    blocks := (!cur_block) :: (!blocks);
    ) (!no_info_block);
  (* Check that the other groups of equations (!other_blocks)
     use pairwise disjoint sets of function symbols *)
  List.iter (fun (f1,l1,_) ->
    List.iter (fun (f2,l2) ->
      if not (disjoint_list f1 f2) then
	begin
	  print_string "Error: the following sets of equations";
	  Display.Text.display_item_list Display.Text.display_eq l1;
	  print_string "and";
	  Display.Text.display_item_list Display.Text.display_eq l2;
	  print_string "use common function symbols.\n";
	  Parsing_helper.user_error "Blocks of equations marked [convergent] or [linear] should use function symbols disjoint from equations not marked [convergent] or [linear]."
	end
	  ) (!blocks)
      ) (!other_blocks);
  let rec check_disj = function
      [] -> ()
    | (f1,l1,_)::l ->
	List.iter (fun (f2,l2,_) ->
	  if not (disjoint_list f1 f2) then
	    begin
	      print_string "Error: the following sets of equations";
	      Display.Text.display_item_list Display.Text.display_eq l1;
	      print_string "and";
	      Display.Text.display_item_list Display.Text.display_eq l2;
	      print_string "use common function symbols.\n";
	      Parsing_helper.user_error "Blocks of equations marked [convergent] or [linear] should use function symbols disjoint from each other."
	    end
	      ) l;
	check_disj l
  in
  check_disj (!other_blocks);
  (* Return the blocks of equations, with associated eqinfo *)
  (List.map (fun (_,eqlist) -> (eqlist, EqNoInfo)) (!blocks))
    @ (List.map (fun (_,eqlist,eqinfo) -> (eqlist,eqinfo)) (!other_blocks))

(* Check block convergent *)

exception Nontermination of equation
exception Nonconfluent of equation * equation

let check_term block =
  (* Check termination *)
  List.iter (fun ((leq, req) as eq) -> if not (greater_lpo leq req) then
    raise (Nontermination eq)) block

let check_confluent block =
  (* Check confluence *)
  rewrite_system := block;
  List.iter (fun r1 ->
    let r1 = copy_eq r1 in
    List.iter (fun r2 ->
      if not (joinable_critical_pairs (fun x -> x) r1 r2) then
	begin
	  rewrite_system := [];
	  raise (Nonconfluent(r1,r2))
	end) block
	) block;
  rewrite_system := []

let check_convergent block =
  check_term block;
  check_confluent block

(* Check block linear *)

let rec is_linear_term vlist = function
    Var v ->
      if List.memq v (!vlist) then false else
      begin
	vlist := v :: (!vlist);
	true
      end
  | FunApp(_,l) ->
      List.for_all (is_linear_term vlist) l

let is_linear block =
  List.for_all (fun (leq, req) ->
    (is_linear_term (ref []) leq) && (is_linear_term (ref []) req)) block


(* Transforms equations into "equational destructors" *)

let record_eqs_internal equations_list =
  if !Param.eqtreatment = Param.ConvLin then
  begin
    (*print_string "Building order...";
    Display.Text.newline();*)
    begin
       match !Param.symb_order with
	 None ->
	   List.iter (fun (l, _) -> List.iter add_order l) equations_list
       | Some sext ->
	   order := order_from_string sext equations_list
    end;
    (*print_string "Order:\n";
    List.iter (fun (f1,f2) -> print_string (f1.f_name ^ " > " ^ f2.f_name ^ "\n")) (!order);
    print_string "Building blocks...";
    Display.Text.newline();*)
    let blocks = buildblocks equations_list in
    (*print_string "Separating convergent/linear...";
    Display.Text.newline();*)
    let convergent_part = ref [] in
    let linear_part = ref [] in
    List.iter (fun (block,eqinfo) ->
      match eqinfo with
	EqNoInfo ->
	  begin
	  try
	    check_convergent block;
            convergent_part := block @ (!convergent_part)
	  with
	    (Nontermination _ | Nonconfluent _) as e ->
	      if is_linear block then
		linear_part := block @ (!linear_part)
	      else
		begin
		  print_string "Error: Cannot handle the following equations:";
		  Display.Text.display_item_list Display.Text.display_eq block;
		  print_string "This block of equations is not linear and could not be proved convergent.\n";
		  begin
		    match e with
		      Nontermination eq ->
			print_string "(I could not prove that\n";
			Display.Text.display_eq eq;
			print_string "\nis decreasing in a lexicographic path ordering.\nIf you know that your equations are convergent, you can bypass the\ntermination check by declaring your equations by:\n  equation (your convergent equations) [convergent].)\n"
		    | Nonconfluent(eq1,eq2) ->
			print_string "(The system is not confluent because of a critical pair between\n";
			Display.Text.display_eq eq1;
			print_string "\nand\n";
			Display.Text.display_eq eq2;
			print_string ".)\n"
		    | _ -> Parsing_helper.internal_error "TermsEq: added to avoid warning for non-exhaustive pattern-matching"
		  end;
		  Parsing_helper.user_error "These equations cannot be handled."
		end
        end
      | EqLinear ->
	  if is_linear block then
	    linear_part := block @ (!linear_part)
	  else
	    begin
	      print_string "Error: Cannot handle the following equations:";
	      Display.Text.display_item_list Display.Text.display_eq block;
	      print_string "This block of equations is declared linear but it is not.\n";
	      Parsing_helper.user_error "These equations cannot be handled."
	    end
      |	EqConvergent ->
	  begin
	    try
	      check_term block
	    with Nontermination _ ->
	      print_string "Warning: the following equations";
	      Display.Text.display_item_list Display.Text.display_eq block;
	      print_string "are declared convergent. I could not prove termination.\n";
	      print_string "I assume that they really terminate.\n";
	      print_string "Expect problems (such as ProVerif going into a loop) if they do not!\n";
	      flush stdout
	  end;
	  begin
	    try
	      check_confluent block
	    with Nonconfluent(eq1,eq2) ->
	      print_string "Error: Cannot handle the following equations:";
	      Display.Text.display_item_list Display.Text.display_eq block;
	      print_string "This block of equations is declared convergent but it is not\n";
	      print_string "confluent because of a critical pair between\n";
	      Display.Text.display_eq eq1;
	      print_string "\nand\n";
	      Display.Text.display_eq eq2;
	      print_string ".)\n";
	      Parsing_helper.user_error "These equations cannot be handled."
	  end;
          convergent_part := block @ (!convergent_part)
	) blocks;

    if !Param.html_output then
      begin
        Display.Html.print_string "<H2>Linear part</H2>\n";
        Display.Html.print_string "Initial equations:";
        Display.Html.display_item_list Display.Html.display_eq (!linear_part)
      end
    else if !Param.verbose_eq then
      begin
        Display.Text.print_string "Linear part:";
        Display.Text.display_item_list Display.Text.display_eq (!linear_part)
      end;
    List.iter (fun eq ->
       add_eq eq;
       add_eq (swap_eq eq)) (!linear_part);
    print_string "Completing equations...";
    Display.Text.newline();
    let resulting_equations_linear = complete_eq true in
    eq_base := [];
    if !Param.html_output then
      begin
        Display.Html.print_string "Completed equations:";
        Display.Html.display_item_list Display.Html.display_eq resulting_equations_linear
      end
    else if !Param.verbose_eq then
      begin
        Display.Text.print_string "Completed equations:";
        Display.Text.display_item_list Display.Text.display_eq resulting_equations_linear
      end;

    if !Param.html_output then
      begin
        Display.Html.print_string "<H2>Convergent part</H2>\n";
        Display.Html.print_string "Initial equations:";
	Display.Html.display_item_list Display.Html.display_eq (!convergent_part)
      end
    else if !Param.verbose_eq then
      begin
        Display.Text.print_string "Convergent part:";
	Display.Text.display_item_list Display.Text.display_eq (!convergent_part)
      end;
    rewrite_system := !convergent_part;
    List.iter add_eq (!convergent_part);
    print_string "Completing equations...";
    Display.Text.newline();
    let resulting_equations_convergent = complete_eq false in
    if !Param.html_output then
      begin
        Display.Html.print_string "Completed equations:";
        Display.Html.display_item_list Display.Html.display_eq resulting_equations_convergent
      end
    else if !Param.verbose_eq then
      begin
        Display.Text.print_string "Completed equations:";
            Display.Text.display_item_list Display.Text.display_eq resulting_equations_convergent
      end;

    let resulting_equations = resulting_equations_linear @ resulting_equations_convergent in
    (* record the equations in each constructor *)
    List.iter (function
      (FunApp(f, l), req) as eq ->
        begin
	  let var_list_rhs = ref [] in
	  Terms.get_vars var_list_rhs req;
	  if not (List.for_all (fun v -> List.exists (Terms.occurs_var v) l) (!var_list_rhs)) then
	    begin
	      print_string "Error in equation: ";
	      Display.Text.display_eq eq;
	      print_newline();
	      Parsing_helper.user_error "All variables of the right-hand side of an equation\nshould also occur in the left-hand side."
	    end;

          match f.f_cat with
            Eq leq -> f.f_cat <- Eq ((l, req) :: leq)
          | _ -> user_error "Does not support equations on non-constructors"
        end
    | _ -> ()) resulting_equations

  end
  else
  begin
    (* Old, non-proved treatment of equations.
       Kept just in case it is useful...
       Just ignore the convergent/linear information. *)
     let eq_list = ref [] in
     List.iter (fun (eqlist,_) ->
       eq_list := eqlist @ (!eq_list)) equations_list;
    List.iter find_rewrite_system (!eq_list);
    if !Param.verbose_eq then
      begin
        print_string "Rewriting system:";
        Display.Text.display_item_list Display.Text.display_eq (!rewrite_system)
      end;

    List.iter (fun eq -> add_eq eq;
                         add_eq (swap_eq eq)) (!eq_list);
    print_string "Completing equations...";
    Display.Text.newline();
    let resulting_equations = complete_eq true in
    (* record the equations in each constructor *)
    if !Param.verbose_eq then
      begin
	print_string "Completed equations:";
	Display.Text.display_item_list Display.Text.display_eq resulting_equations
      end;
    List.iter (function
      (FunApp(f, l), req) as eq ->
        begin
	  let var_list_rhs = ref [] in
	  Terms.get_vars var_list_rhs req;
	  if not (List.for_all (fun v -> List.exists (Terms.occurs_var v) l) (!var_list_rhs)) then
	    begin
	      print_string "Equation: ";
	      Display.Text.display_eq eq;
	      print_newline();
	      Parsing_helper.user_error "All variables of the right-hand side of an equation\nshould also occur in the left-hand side."
	    end;

          match f.f_cat with
            Eq leq -> f.f_cat <- Eq ((l, req) :: leq)
          | _ -> user_error "Does not support equations on non-constructors"
        end
    | _ -> ()) resulting_equations

   end


(****** Unification modulo the equational theory ******)

(* Equivalent of copy_term, but replaces function symbols with
   syntactic ones *)

let syntactic_table = Hashtbl.create 7

let get_syntactic f =
  try
    Hashtbl.find syntactic_table f
  with Not_found ->
    let f' = { f_name = (* "sy_" ^ *)
                 begin
                   match f.f_name with
                   | Fixed _ -> f.f_name
                   | Renamable _ -> Parsing_helper.internal_error "get_syntactic only for fixed functions"
                 end;
               f_type = f.f_type;
               f_cat = Syntactic f;
               f_initial_cat = Syntactic f;
               f_private = f.f_private;
               f_options = f.f_options } in
    Hashtbl.add syntactic_table f f';
    f'

let rec put_syntactic = function
  | FunApp(f,l) -> FunApp(get_syntactic f, List.map put_syntactic l)
  | Var v ->
      match v.link with
      |	NoLink ->
          let r = Terms.copy_var v in
          link v (VLink r);
          Var r
      | VLink l -> Var l
      | _ -> internal_error "Unexpected link in put_syntactic"

(* Equivalent of copy_term2, but replaces syntactic function symbols
   with their non-syntactic equivalents *)

let rec copy_remove_syntactic = function
  | FunApp(f,l) -> FunApp(non_syntactic f, List.map copy_remove_syntactic l)
  | Var v ->
      match v.link with
	NoLink ->
	  let r = copy_var v in
	  link v (VLink r);
          Var r
      | TLink l -> copy_remove_syntactic l
      | VLink r -> Var r
      | _ -> internal_error "unexpected link in copy_remove_syntactic"

let copy_remove_syntactic_fact = function
    Pred(chann, t) -> Pred(chann, List.map copy_remove_syntactic t)

let copy_remove_syntactic_occurrence = function
  | None -> None
  | Some t -> Some (copy_remove_syntactic t)

let copy_remove_syntactic_event = function
  | QSEvent(inj,ord_fun,occ,t) -> QSEvent(inj,ord_fun,copy_remove_syntactic_occurrence occ,copy_remove_syntactic t)
  | QSEvent2(t1,t2) -> QSEvent2(copy_remove_syntactic t1, copy_remove_syntactic t2)
  | QFact(p,ord_fun,args) -> QFact(p,ord_fun,List.map copy_remove_syntactic args)
  | QNeq(t1,t2) -> QNeq(copy_remove_syntactic t1, copy_remove_syntactic t2)
  | QEq(t1,t2) -> QEq(copy_remove_syntactic t1, copy_remove_syntactic t2)
  | QGeq(t1,t2) -> QGeq(copy_remove_syntactic t1, copy_remove_syntactic t2)
  | QIsNat(t) -> QIsNat(copy_remove_syntactic t)

let rec copy_remove_syntactic_conclusion_query = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QEvent ev -> QEvent (copy_remove_syntactic_event ev)
  | NestedQuery q -> NestedQuery (copy_remove_syntactic_realquery q)
  | QAnd(concl1,concl2) -> QAnd(copy_remove_syntactic_conclusion_query concl1,copy_remove_syntactic_conclusion_query concl2)
  | QOr(concl1,concl2) -> QOr(copy_remove_syntactic_conclusion_query concl1,copy_remove_syntactic_conclusion_query concl2)

and copy_remove_syntactic_realquery = function
  | Before(evl,concl) -> Before(List.map copy_remove_syntactic_event evl, copy_remove_syntactic_conclusion_query concl)

(* Remove syntactic function symbols without copying *)

let rec remove_syntactic_term = function
 | FunApp(f,l) -> FunApp(non_syntactic f, List.map remove_syntactic_term l)
 | Var v -> match v.link with
      NoLink -> Var v
    | TLink l -> remove_syntactic_term l
    | _ -> internal_error "unexpected link in remove_syntactic_term"

let remove_syntactic_fact = function
    Pred(chann, t) -> Pred(chann, List.map remove_syntactic_term t)

let rec remove_syntactic_constra c = Terms.map_constraints remove_syntactic_term c

let remove_syntactic_rule (hyp,concl,hist,constra) =
  List.map remove_syntactic_fact hyp,
  remove_syntactic_fact concl,
  hist,
  remove_syntactic_constra constra

(* Collect variables that are not defined yet *)

let rec collect_unset_vars accu = function
    FunApp(f,l) -> List.iter (collect_unset_vars accu) l
  | Var v ->
      match v.link with
	NoLink ->
	  if not (List.memq v (!accu)) then
	    accu := v :: (!accu)
      | TLink t -> collect_unset_vars accu t
      | _ -> internal_error "unexpected link in collect_unset_vars"

(* Unification modulo itself *)

let f_has_no_eq f =
  match f.f_cat with
    Eq [] -> true
  | Eq _ -> false
  | _ -> true

exception NoBacktrack of binder list ref

let rec close_term_eq_synt restwork = function
  | (Var x) as t ->
    begin
      match x.link with
        | TLink t -> close_term_eq_synt restwork t
        | NoLink -> restwork t
        | _ -> internal_error "unexpected link in close_term_eq_synt"
    end
  | (FunApp(f,l) as t) when f_has_no_eq f ->
      (* Distinguishing this case explicitly helps avoiding a
         stack overflow: the stack does not grow in this case
         because we make a tail call. *)
      restwork t
  | (FunApp(f,l) as t) ->
      try
        auto_cleanup (fun () -> restwork t)
      with Unify ->
        match f.f_cat with
        | Eq eqlist ->
            let rec reweqlist = function
              | (leq, req) :: lrew ->
                  let leq', req'  = auto_cleanup (fun () ->
                    List.map put_syntactic leq,
                    put_syntactic req)
                  in
                  begin
                    try
                      auto_cleanup (fun () ->
                        unify_modulo_list (fun () -> restwork req')  l leq')
                    with Unify ->
                      (* Try another rewriting when Unify is raised *)
                      reweqlist lrew
                  end
              | [] -> raise Unify
            in
            reweqlist eqlist
        | _ -> Parsing_helper.internal_error "close_term_eq_synt: cases other than Eq should have been treated before"

and unify_modulo restwork t1 t2 =
  close_term_eq_synt (fun t1 ->
    close_term_eq_synt (fun t2 ->
      match (t1,t2) with
      | (Var v, Var v') when v == v' -> restwork ()
      | (Var v, _) ->
          begin
            match v.link with
            | NoLink ->
                begin
                  match t2 with
                  | Var {link = TLink t2'} -> unify_modulo restwork t1 t2'
                  | Var v' when v.unfailing ->
                      link v (TLink t2);
                      restwork ()
                  | Var v' when v'.unfailing ->
                      link v' (TLink t1);
                      restwork ()
                  | FunApp (f_symb,_) when (non_syntactic f_symb).f_cat = Failure && v.unfailing = false -> raise Unify
                  | _ ->
                      occur_check v t2;
                           link v (TLink t2);
                           restwork ()
                end
            | TLink t1' -> unify_modulo restwork t1' t2
            | _ -> internal_error "Unexpected link in unify 1"
          end
      | (FunApp(f,_), Var v) ->
          begin
            match v.link with
            | NoLink ->
                if v.unfailing = false && (non_syntactic f).f_cat = Failure
                then raise Unify
                else
                  begin
                    occur_check v t1;
                    link v (TLink t1);
                    restwork ()
                  end
            | TLink t2' -> unify_modulo restwork t1 t2'
            | _ -> internal_error "Unexpected link in unify 2"
          end
      | (FunApp(f1, l1), FunApp(f2,l2)) ->
            if (non_syntactic f1) != (non_syntactic f2) then raise Unify;
            unify_modulo_list restwork l1 l2
    ) t2
  ) t1

and unify_modulo_list_internal restwork l1 l2 =
  match (l1, l2) with
  | [], [] -> restwork ()
  | (a1::l1'), (a2::l2') ->
      begin
        let unset_vars = ref [] in
        collect_unset_vars unset_vars a1;
        collect_unset_vars unset_vars a2;
        try
          unify_modulo (fun () ->
            if not (List.exists (fun v -> v.link != NoLink) (!unset_vars))  then
              (* No variable of a1, a2 defined by unification modulo.
                 In this case, we do not need to backtrack on the choices made
                 in unify_modulo (...) a1 a2 when a subsequent unification fails. *)
              raise (NoBacktrack unset_vars)
            else
              unify_modulo_list_internal restwork l1' l2'
          ) a1 a2;
        with NoBacktrack unset_vars' when unset_vars == unset_vars' ->
          unify_modulo_list_internal restwork l1' l2'
      end
  | _ -> internal_error "Lists should have same length in unify_modulo_list"

(* Optimized version of unification modulo: try to decompose
   the root symbols as much as possible when they do not use an
   equational theory. *)

and unify_modulo_list restwork l1 l2 =
  let unif_to_do_left = ref [] in
  let unif_to_do_right = ref [] in
  let rec add_unif_term t1 t2 =
    match t1, t2 with
      FunApp(f1, l1), FunApp(f2,l2) when f_has_no_eq f1 && f_has_no_eq f2 ->
  	if (non_syntactic f1) != (non_syntactic f2) then raise Unify;
	List.iter2 add_unif_term l1 l2
    | Var v, Var v' when v == v' -> ()
    | (Var v, _) ->
	  begin
	    match v.link with
	    | NoLink ->
		begin
		  match t2 with
		  | Var {link = TLink t2'} -> add_unif_term t1 t2'
		  | Var v' when v.unfailing ->
		      link v (TLink t2)
		  | Var v' when v'.unfailing ->
		      link v' (TLink t1)
		  | FunApp (f_symb,_) when (non_syntactic f_symb).f_cat = Failure && v.unfailing = false -> raise Unify
		  | _ ->
		      try
			occur_check v t2;
             		link v (TLink t2)
		      with Unify ->
			(* When the occur check fails, it might succeed
			   after rewriting the terms, so try that *)
			unif_to_do_left := t1 :: (!unif_to_do_left);
			unif_to_do_right := t2 :: (!unif_to_do_right)
		end
	    | TLink t1' ->
                add_unif_term t1' t2
	    | _ -> internal_error "Unexpected link in unify_modulo_list (optimized) 1"
	  end
      | (FunApp(f,_), Var v) ->
	  begin
	    match v.link with
	    | NoLink ->
		if v.unfailing = false && (non_syntactic f).f_cat = Failure
		then raise Unify
		else
		  begin
		    try
		      occur_check v t1;
		      link v (TLink t1)
		    with Unify ->
		      (* When the occur check fails, it might succeed
			 after rewriting the terms, so try that *)
		      unif_to_do_left := t1 :: (!unif_to_do_left);
		      unif_to_do_right := t2 :: (!unif_to_do_right)
		  end
	    | TLink t2' -> add_unif_term t1 t2'
	    | _ -> internal_error "Unexpected link in unify_modulo_list (optimized) 2"
	  end
      | _ ->
	  unif_to_do_left := t1 :: (!unif_to_do_left);
	  unif_to_do_right := t2 :: (!unif_to_do_right)
  in
  auto_cleanup (fun () ->
    List.iter2 add_unif_term l1 l2;
    unify_modulo_list_internal restwork (!unif_to_do_left) (!unif_to_do_right))

let unify_modulo restwork t1 t2 =
  unify_modulo_list restwork [t1] [t2]

let close_geq_eq_synt restwork (t1,n,t2) =
  close_term_eq_synt (fun t1' ->
    close_term_eq_synt (fun t2' ->
      restwork (t1',n,t2')
    ) t2
  ) t1

let close_constraints_eq_synt restwork c =
  close_list_eq close_term_eq_synt (fun is_nat ->
    close_list_eq close_geq_eq_synt (fun geq ->
      restwork { c with is_nat = is_nat; geq = geq }
    ) c.geq
  ) c.is_nat

(* Unification of environments, modulo an equational theory *)

let rec get_list l1 l2 =
  match (l1,l2) with
  | [],[] -> []
  | ((v1,t1)::l1'),((v2,t2)::l2') ->
      let l' = get_list l1' l2' in
      (* Unification of environments ignores variables that do not match.
	 When needed, the result of the unification should be an
	 environment that contains only the common variables *)
      if v1 == v2 then t1 :: l' else l'
  | _ -> internal_error "Lists should have same length in get_list"

(****************************************************************
***  Treatment of constraints
****************************************************************)

(* Implication between constraints. Use this after simplification
   to get the best possible precision. *)

let assoc_gen_with_term = ref []

let rec implies_list_terms nextf l_t1 l_t2 = match (l_t1,l_t2) with
  | [], [] -> nextf ()
  | ((FunApp(f1,[]))::l1, t2::l2) when f1.f_cat = General_var ->
    begin
      try
        let t = List.assq f1 (!assoc_gen_with_term) in
        if not (equal_terms t t2) then raise NoMatch;

        implies_list_terms nextf l1 l2

      with Not_found ->
        assoc_gen_with_term := (f1, t2) :: (!assoc_gen_with_term);
        try
          let r = implies_list_terms nextf l1 l2 in
          assoc_gen_with_term := List.tl (!assoc_gen_with_term);
          r
        with NoMatch ->
          assoc_gen_with_term := List.tl (!assoc_gen_with_term);
          raise NoMatch
    end

  | ((Var v1)::l1), ((Var v2)::l2) when v1 == v2 ->
      implies_list_terms nextf l1 l2
  | ((FunApp (f1,l1'))::l1, (FunApp (f2,l2'))::l2) ->
      if f1 != f2 then raise NoMatch;
      implies_list_terms nextf (l1' @ l1) (l2' @ l2)
  | _,_ -> raise NoMatch

let implies_simple_constraint nextf (t1,t1') (t2, t2') =
  implies_list_terms nextf [t1;t1'] [t2;t2']

let rec search_for_implied_constraint_in nextf sc1 = function
    [] -> raise NoMatch
  | (sc2::sc_l2) ->
        try
          implies_simple_constraint nextf sc1 sc2
        with NoMatch ->
          search_for_implied_constraint_in nextf sc1 sc_l2

let implies_constraint sc_list1 sc_list2 =
  let rec sub_implies_constraint sc_list1 sc_list2 () =
    match sc_list1 with
    | [] -> ()
    | sc1::sc_l1 -> search_for_implied_constraint_in (sub_implies_constraint sc_l1 sc_list2) sc1 sc_list2
  in
  try
    sub_implies_constraint sc_list1 sc_list2 ();
    true
  with NoMatch ->
    false

(* Simplification of constraints *)

(* Remark: for the way the subsumption test is implemented,
   it is important that all variables that occur in constraints
   also occur in the rest of the rule.
   Indeed, only the variables that occur in the rest of the rule
   are bound during the subsumption test. Other variables
   are always considered to be different, yielding the non-detection
   of subsumption

   When there is no universally quantified variable and no equational
   theory, we can simply remove all inequalities that contain variables
   not in the rest of the rule.
   However, "for all x, x <> y" is wrong even when y does not
   occur elsewhere. Similarly, "x <> decrypt(encrypt(x,y),y)" is wrong
   with the equation "decrypt(encrypt(x,y),y) = x".
   In this case, we can replace these variables with _new_
   constants.
   In the long run, the best solution might be to consider
   inequalities as an ordinary blocking predicate (and to remove
   constraints completely).
 *)

exception TrueConstraint
exception FalseConstraint

(** [elim_var_if_possible has_gen_var keep_vars accu_nat_vars nat_vars v] checks if [v] occurs
    in the list of variables [keep_vars].
    If not and it is not a natural number variable, then it adds a [Tlink]
    into [v] with an "any_val" symbol, so that [v] will be replaced
    with "any_val".
    If not and it is a natural number variable, then it adds [v]
    to [accu_nat_vars].
    [nat_vars] contains the list of natural number variables. *)
let elim_var_if_possible has_gen_var keep_vars accu_nat_vars nat_vars v =
  if not (List.memq v keep_vars) then
  begin
    if List.memq v nat_vars
    then
      begin
        if not (List.memq v !accu_nat_vars)
        then accu_nat_vars := v :: !accu_nat_vars
      end
    else
      if (not has_gen_var) && (not (hasEquations()))
      then raise TrueConstraint
      else
        begin
          match v.link with
          | NoLink ->
              Terms.link v (TLink (FunApp(
                { f_name = Renamable (Terms.new_id ~orig:false "any_val");
                  f_type = [], v.btype;
                  f_cat = Eq []; (* Should not be a name to avoid bad interaction with any_name_fsymb *)
                  f_initial_cat = Eq []; (* Should not be a name to avoid bad interaction with any_name_fsymb *)
                  f_private = true;
                  f_options = 0 }, [])))
          | TLink _ -> ()
          | _ -> Parsing_helper.internal_error "unexpected link in elim_var_if_possible"
        end
  end

let rec check_vars_occurs has_gen_var keep_vars accu_nat_vars nat_vars = function
  | FunApp(_,l) -> List.iter (check_vars_occurs has_gen_var keep_vars accu_nat_vars nat_vars) l
  | Var v -> elim_var_if_possible has_gen_var keep_vars accu_nat_vars nat_vars v

let rec has_gen_var = function
    Var v -> false
  | FunApp(f,[]) when f.f_cat = General_var -> true
  | FunApp(_,l) -> List.exists has_gen_var l

(** [elim_var_notelsewhere] expects contraints with a variable on the left part
    of the disequation *)
let elim_var_notelsewhere has_gen_var keep_vars accu_nat_vars nat_vars = function
  | Var v1, Var v2 ->
      assert(v1 != v2);
      elim_var_if_possible has_gen_var keep_vars accu_nat_vars nat_vars v1;
      elim_var_if_possible has_gen_var keep_vars accu_nat_vars nat_vars v2
      (* constraints Neq(x,t), where x does not appear in the keep_vars and t is not a variable, are true
         Note that, if t was a universally quantified variable, it would have been removed by swap.
      *)
  | Var v, t ->
      elim_var_if_possible false keep_vars accu_nat_vars nat_vars v;
      check_vars_occurs has_gen_var keep_vars accu_nat_vars nat_vars t
  | c ->
      Display.Text.display_constra [c];
      Parsing_helper.internal_error "unexpected constraint in simplify_simple_constraint: t <> t', t not variable"

(*************************************************
*** Simplification of natural number predicates **)

type status_nat =
  | IsNat
  | CanBeNat of binder
  | NeverNat

(* [get_status_natural_number] and [can_be_natural_number] do not take into
   account the equational theory. *)
let rec get_status_natural_number nat_vars = function
  | Var { link = TLink t; _ } -> get_status_natural_number nat_vars t
  | Var v ->
      if equal_types v.btype Param.nat_type
      then
        if List.memq v nat_vars || not (Param.get_ignore_types())
        then IsNat
        else CanBeNat v
      else NeverNat
  | FunApp(f,[t]) when (non_syntactic f) == Terms.succ_fun -> get_status_natural_number nat_vars t
  | FunApp(f,[]) when (non_syntactic f) == Terms.zero_cst -> IsNat
  | _ -> NeverNat

let rec can_be_natural_number = function
  | Var { link = TLink t; _ } -> can_be_natural_number t
  | Var v -> equal_types v.btype Param.nat_type
  | FunApp(f,[t]) when (non_syntactic f) == Terms.succ_fun -> can_be_natural_number t
  | FunApp(f,[]) when (non_syntactic f) == Terms.zero_cst -> true
  | _ -> false

let rec elim_var_in_is_not_nat accu_vars accu_keep_nat_vars keep_vars nat_vars = function
  | Var { link = TLink t ; _ } ->
      (* In such a case, [t] is in fact a name any_val. *)
      t
  | Var ({ link = NoLink ; _ } as v) ->
      if List.memq v keep_vars
      then
        begin
          if not (List.memq v !accu_vars)
          then accu_vars := v :: !accu_vars;
          Var v
        end
      else
        if List.memq v nat_vars
        then
          begin
            if not (List.memq v !accu_vars)
            then accu_vars := v :: !accu_vars;
            if not (List.memq v !accu_keep_nat_vars)
            then accu_keep_nat_vars := v :: !accu_keep_nat_vars;
            Var v
          end
        else
          begin
            let t =
              FunApp(
                { f_name = Renamable (Terms.new_id ~orig:false "any_val");
                  f_type = [], v.btype;
                  f_cat = Eq []; (* Should not be a name to avoid bad interaction with any_name_fsymb *)
                  f_initial_cat = Eq []; (* Should not be a name to avoid bad interaction with any_name_fsymb *)
                  f_private = true;
                  f_options = 0 }, [])
            in
            Terms.link v (TLink t);
            t
          end

  | Var _ -> Parsing_helper.internal_error "[termsEq.ml >> elim_var_in_is_not_nat] Unexpected link."
  | FunApp(f,args) -> FunApp(f,List.map (elim_var_in_is_not_nat accu_vars accu_keep_nat_vars keep_vars nat_vars) args)

let rec check_is_nat accu_vars = function
  | Var v ->
      if not (equal_types v.btype Param.nat_type)
      then raise FalseConstraint;

      if not (List.memq v !accu_vars)
      then accu_vars := v :: !accu_vars
  | FunApp(f,[t]) when f == Terms.succ_fun -> check_is_nat accu_vars t
  | FunApp(f,[]) when f == Terms.zero_cst -> ()
  | _ -> raise FalseConstraint

let rec check_and_decompose accu_vars = function
  | Var v ->
      if not (equal_types v.btype Param.nat_type)
      then raise FalseConstraint;

      if not (List.memq v !accu_vars)
      then accu_vars := v :: !accu_vars;

      (Var v,0)
  | FunApp(f,[t]) when f == Terms.succ_fun ->
      let (t',n) = check_and_decompose accu_vars t in
      (t',n+1)
  | FunApp(f,[]) as t when f == Terms.zero_cst -> (t,0)
  | _ -> raise FalseConstraint

let rec simplify_geq accu_vars (t1,n,t2) =
  let (t1',n1) = check_and_decompose accu_vars t1 in
  let (t2',n2) = check_and_decompose accu_vars t2 in

  (t1',(n1 + n - n2), t2')

(* The reference [accu_keep_vars] accumulates the natural variables in the predicates
   is_not_nat *)
let rec simplify_is_not_nat accu_keep_vars nat_vars = function
  | [] -> []
  | t :: q ->
      let t1 = normal_form t in

      let accu_vars = ref [] in
      let accu_keep_nat_vars = ref [] in
      let t2 = elim_var_in_is_not_nat accu_vars accu_keep_nat_vars !accu_keep_vars nat_vars t1 in
      Terms.cleanup ();

      let can_be_nat = ref false in
      try
        close_term_eq_synt (fun t3 -> match get_status_natural_number nat_vars t3 with
          | IsNat ->
              (* When t1 is for sure a natural number, we check that the variables of [t] have not been
                instantiated. In such a case, we know that [t] is for sur a natural number. *)
              if List.for_all (function { link = NoLink; _} -> true | _ -> false) !accu_vars
              then raise FalseConstraint;
              can_be_nat := true;
              raise Unify
          | CanBeNat _ ->
              can_be_nat := true;
              raise Unify
          | NeverNat -> raise Unify
        ) t2
        (* The function never returns and always raises Unify. *)
      with Unify ->
        if !can_be_nat
        then
          begin
            accu_keep_vars := !accu_keep_nat_vars @ !accu_keep_vars;
            t::(simplify_is_not_nat accu_keep_vars nat_vars q)
          end
        else simplify_is_not_nat accu_keep_vars nat_vars q

let check_is_not_nat nat_vars t =
  let accu_vars = ref [] in
  get_vars accu_vars t;
  try
    close_term_eq_synt (fun t1 -> match get_status_natural_number nat_vars t1 with
      | IsNat ->
          (* When t1 is for sure a natural number, we check that the variables of [t] have not been
            instantiated. In such a case, we know that [t] is for sur a natural number. *)
          if List.for_all (function { link = NoLink; _} -> true | _ -> false) !accu_vars
          then raise FalseConstraint;
          raise Unify
      | CanBeNat _ | NeverNat -> raise Unify
    ) t
    (* The function never returns and always raises Unify. *)
  with Unify -> ()

module HashType =
  struct
    type t = term
    let equal = Terms.equal_terms
    let hash = Hashtbl.hash
  end

module HashTerm = Hashtbl.Make(HashType)

let vertices = HashTerm.create 10

type infInt = N of int | Infinity

(*** Simplifying inequalities after BellmanFord ***)

(* [get_sons i distance assoc vars_to_remove (number_vertices - 1)]
   returns the list of [(j,n,active)] where
   [(term associated to node i) <= (term associated to node j) + n],
   [active] is a boolean ref initially set to true.

   [assoc.(i) = t] means that the term associated to node [i] is [t].
   These terms [t] are always variables or 0, because the constructor
   succ is simplified out, 0 is a valid natural number and all other
   constructors are not natural numbers.
   [distance.(i).(j) = k] means that
   (term associated to node i) <= (term associated to node j) + k.
   [vars_to_remove] are the variables that we remove because we
   showed that they are equal to another variable. *)

let rec get_sons i distance assoc keep_vars = function
  | -1 -> []
  | j when i = j || j = 0 || not (List.exists (fun x -> Terms.equal_terms assoc.(j) (Var x)) keep_vars) ->
        get_sons i distance assoc keep_vars (j-1)
  | j ->
      match distance.(i).(j) with
        | N n -> (j,n,ref true)::(get_sons i distance assoc keep_vars (j-1))
        | Infinity -> get_sons i distance assoc keep_vars (j-1)

let compare_sons (_,n1,_) (_,n2,_) = compare n1 n2

let display_edge_set edge assoc number_vertices =
  for i = 0 to number_vertices - 1 do
    print_string "Term ";
    Display.Text.display_term assoc.(i);
    print_string ": ";
    Display.Text.display_list (fun (j,k,active) ->
      print_string "(";
      Display.Text.display_term assoc.(j);
      Printf.printf ",%d,%b)" k !active
    ) "; " edge.(i);
    print_string "\n"
  done

(* [remove_son (i1,n1) sons] applied to the sons [sons] of
   a node [k] removes the inequality
   [(term associated to node k) <= (term associated to node i1) + n1]
   because it is already known from other inequalities.

   Note that by Bellman-Ford algorithm, if
   [(term associated to node k) <= (term associated to node i1) + n1]
   can be inferred from other inequalities, we will never have
   [(i1, n2)] with [n2 > n1] as a son of [k].
*)
let rec remove_son (i1,n1) = function
  | [] -> ()
  | (_,n2,_)::_ when n1 < n2 -> ()
  | (i2,n2,active)::q when n1 = n2 ->
      if i2 = i1
      then active := false
      else remove_son (i1,n1) q
  | (i2,_,_)::q when i2 = i1 -> ()
  | _::q -> remove_son (i1,n1) q

let rec update_hist_and_remove_edge j k edge_set = function
  | [] -> []
  | (i,n)::hist_q ->
      let n' = n + k in
      remove_son (j,n') edge_set.(i);
      (i,n')::(update_hist_and_remove_edge j k edge_set hist_q)

let rearrange_inequalities distance assoc number_vertices keep_vars =
  (* Initialize the set of edges *)
  let edge_set = Array.make number_vertices [] in
  for i = 0 to number_vertices - 1 do
    if i = 0 || List.exists (fun x -> Terms.equal_terms assoc.(i) (Var x)) keep_vars
    then edge_set.(i) <- List.sort compare_sons (get_sons i distance assoc keep_vars (number_vertices - 1) )
    else edge_set.(i) <- []
  done;

  let rec explore hist x =
    if List.exists (fun (j,_) -> x = j) hist
    then ()
    else
      let rec explore_sons = function
        | [] -> ()
        | (_,_,active)::q when not !active -> explore_sons q
        | (y,k,_)::q ->
            let hist' = update_hist_and_remove_edge y k edge_set hist in
            explore ((x,k)::hist') y;
            explore_sons q
      in
      explore_sons edge_set.(x)
  in

  let rec full_explore = function
    | -1 -> ()
    | x ->
        explore [] x;
        full_explore (x-1)
  in

  full_explore (number_vertices-1);

  let relations = ref [] in

  for x = 0 to number_vertices - 1 do
    List.iter (fun (y,k,active) ->
      if !active
      then
        let tx = assoc.(x)
        and ty = assoc.(y) in

        if (x = 0 && k >= 0)
        then ()
        else relations := (ty,k,tx) :: !relations
    ) edge_set.(x)
  done;

  !relations

(*** Algorithme BellmanFord ***)

(* We assume here that edges is a list of tuple (i,j,k) representing inequalities,
   meaning (term associated to node i) <= (term associated to node j) + k *)
let algo_BellmanFord_core number_vertices edges =
  (* We generate the matrix that will contain the final result.
    In the end, distance.(i).(j) = k means that
    (term associated to node i) <= (term associated to node j) + k.
  *)
 let distance = Array.make_matrix number_vertices number_vertices Infinity in

 (* Apply the algorithm *)
 for i = 0 to number_vertices - 1 do
   distance.(i).(i) <- N 0;
   let modification = ref true in
   let j = ref 1 in

   while !j < number_vertices && !modification do
     modification := false;
     List.iter (fun (k1,k2,w) (* k1 <= k2 + w *) ->
       match distance.(i).(k1), distance.(i).(k2) with
         | N n, Infinity -> distance.(i).(k2) <- N (n + w); modification := true
         | N n1, N n2 when n1 + w < n2 -> distance.(i).(k2) <- N (n1 + w); modification := true
         | _, _ -> ()
     ) edges;
     incr j
   done;

   (* We check there are no negative weight cycles
      (a negative weight cycle means that the inequalities
      are unsatisfiable). *)
   List.iter (fun (k1,k2,w) ->
     match distance.(i).(k1), distance.(i).(k2) with
       | N n1, N n2 ->
         if n1 + w < n2
         then raise FalseConstraint
       | N _, Infinity -> Parsing_helper.internal_error "[piauth.ml >> algo_BellmanFord] Unexpected case"
       | _, _ -> ()
   ) edges
 done;

 distance

let algo_BellmanFord restwork rel_list =
  (* We clean the hash table containing the vertices. *)
  HashTerm.clear vertices;

  (* We add the node for "zero" *)
  let number_vertices = ref 1 in
  HashTerm.add vertices Terms.zero_term 0;

  let add_vertice t =
    try
      HashTerm.find vertices t
    with Not_found ->
      HashTerm.add vertices t !number_vertices;
      incr number_vertices;
      !number_vertices - 1
  in

  (* We transform the relation list into edge (and we add the vertices in the hash table).
     Each node is associated to a term.
     We have an edge from node k2 to k1 with label i when
     (term associated to k2) <= (term associated to k1) + i. *)
  let edges =
    List.map (fun (t1,n,t2) ->
      let k1 = add_vertice t1 in
      let k2 = add_vertice t2 in
      (k2,k1,n)
    ) rel_list
  in

  (* We add additional egdes representing that x >= 0 for all x. *)
  let rec standard_rel acc = function
    | 0 -> acc
    | i -> standard_rel ((0,i,0)::acc) (i-1)
  in

  let final_edges = standard_rel edges (!number_vertices-1) in

  let distance = algo_BellmanFord_core !number_vertices final_edges in

  (* [assoc.(i) = t] means that the term associated to node [i] is [t]. *)
  let assoc = Array.make !number_vertices Terms.zero_term in
  HashTerm.iter (fun t i -> assoc.(i) <- t) vertices;

  restwork assoc !number_vertices distance

let get_equalities restwork rel_list =
  algo_BellmanFord (fun assoc number_vertices distance ->
    let eq_left = ref []
    and eq_right = ref [] in

    for i = 0 to number_vertices - 1 do
      for j = i + 1 to number_vertices - 1 do
        match distance.(i).(j), distance.(j).(i) with
          | N n_i, N n_j when n_i + n_j = 0 ->
              if n_i >= 0 then
                begin
                  eq_left := assoc.(i) :: !eq_left;
                  eq_right := (Terms.sum_nat_term assoc.(j) n_i) :: !eq_right
                end
              else
                begin
                eq_left := assoc.(j) :: !eq_left;
                eq_right := (Terms.sum_nat_term assoc.(i) n_j) :: !eq_right
                end
          | _ , _ -> ()
      done
    done;

    restwork !eq_left !eq_right assoc number_vertices distance
  ) rel_list

let get_edges number_vertices distance =

  let geq = ref [] in

  let get_rel i j = match distance.(i).(j) with
    | N n -> geq := (i,j,n) :: !geq
    | _ -> ()
  in

  for i = 0 to number_vertices - 1 do
    for j = i + 1 to number_vertices - 1 do
      get_rel i j;
      get_rel j i
    done
  done;

  !geq

(*** Remove disequalities on natural numbers ***)

let can_never_be_natural_number_diseq t =
  (* In this function, we replace the general variables by normal variables and see if
     [t] can never become a natural number. *)
  try
    close_term_eq_synt (fun t1 ->
      if not (can_be_natural_number t1)
      then raise Unify
    ) (Terms.replace_f_var (ref []) t);
    false
  with Unify -> true

(*** Update [keepvars] after unification
     Returns a boolean [is_instantiated]
     and the new value of [keepvars] ***)

let update_keepvars keep_vars =
  let is_instantiated = ref false in
  let keep_ref = ref [] in
  let new_terms = ref [] in

  List.iter (fun v -> match v.link with
    | NoLink -> keep_ref := v :: !keep_ref
    | TLink t ->
        new_terms := t :: !new_terms;
        is_instantiated := true
    | _ -> Parsing_helper.internal_error "[termsEq.ml >> update_keepvars] Unexpected link."
  ) keep_vars;

  List.iter (Termslinks.get_vars keep_ref) !new_terms;

  (!is_instantiated,!keep_ref)

type status_term =
  | General of int * funsymb (* General(n,f): the term is f + n where f is a general variable *)
  | Nat of int (* Nat(n): the term is the natural number n *)
  | NatVar of binder * int (* NatVar(v,n): the term is v + n where v is a variable that contains a natural number *)
  | NeverNat2 (* the term is never a natural number *)
  | Unknown

let rec get_term_status nat_vars depth = function
  | Var v ->
      if (not v.unfailing) && equal_types v.btype Param.nat_type && (List.memq v nat_vars || not (Param.get_ignore_types()))
      then NatVar(v,depth)
      else Unknown
  | FunApp(f,[t]) when (non_syntactic f) == Terms.succ_fun -> get_term_status nat_vars (depth+1) t
  | FunApp(f,[]) when (non_syntactic f) == Terms.zero_cst -> Nat depth
  | FunApp({f_cat = General_var | General_mayfail_var; _} as f,_) -> General(depth,f)
  | t ->
      if can_never_be_natural_number_diseq t
      then NeverNat2
      else Unknown

(* The functions [remove_nat_diseq_neq_conj] and [remove_nat_diseq_neq_conj_exc] apply
   case analysis on the disequations that contains natural number variables.
   For instance, with a constraint i >= z && z >= j && i <> j, these functions
   will apply the next function
      - [f_next_geq] on i >= z && z >= j && i > j
      - [f_next_geq] on i >= z && z >= j && i < j
      - [f_next_inst] on i >= z && z >= j && i <> j
        with variables i and j linked, so that i = j
        The last case leads to a contradiction and is removed (the next function
        raises [FalseConstraint]).

    The function [remove_nat_diseq_neq_conj_exc] first executes the next function on
    the first case distinction and only executes the next function on the second case
    if the first one raised the exception FalseConstraint (similar to unify_modulo).

    The function [remove_nat_diseq_neq_conj] executes all the cases distinctions.
    We assume here that the next functions do not raises exceptions.
   *)
let remove_nat_diseq_neq_conj_exc f_next f_next_geq f_next_inst nat_vars neq =

  let rec explore_disj f_next f_next_geq f_next_inst = function
    | [] -> f_next false
    | (Var v1,t2)::q ->
        (* Since the disequations are simplified, we know that t1 is a variable *)
        if List.memq v1 nat_vars
        then
          let case_distinction n2 t2' =
            try
              (* First case: v1 > t2 + n2 *)
              f_next_geq (Var v1,(-n2-1),t2')
            with FalseConstraint ->
              try
                (* Second case: v1 < t2 + n2 *)
                f_next_geq (t2',(n2-1),Var v1)
              with FalseConstraint ->
                (* Last case v1 = t2 + n2 *)
                Terms.auto_cleanup (fun () ->
                  link v1 (TLink (Terms.sum_nat_term t2' n2));
                  f_next_inst ()
                )
          in

          let status2 = get_term_status nat_vars 0 t2 in
          match status2 with
            | Nat n2 ->
                (* Case of v1 <> n2 *)
                case_distinction n2 Terms.zero_term
            | NatVar(v2,n2) ->
                (* Case of v1 <> v2 + n2 *)
                case_distinction n2 (Var v2)
            | General(n2,f) ->
		(* Case v1 <> n2 + f for all f
		   -> we introduce the case v1 < n2, written 0+n2-1 >= v1
		   and the case v1 = n2 + n' for a fresh variable n'. *)
                begin
                  try
                    f_next_geq (Terms.zero_term,(n2-1),Var v1)
                  with FalseConstraint ->
                    Terms.auto_cleanup (fun () ->
                      let v' = Terms.new_var_def Param.nat_type in
                      let t = Terms.sum_nat_term (Var v') n2 in
                      Terms.link v1 (TLink t);
                      f_next_inst ()
                    )
                end
            | NeverNat2 -> f_next true
            | _ -> explore_disj f_next f_next_geq f_next_inst q
        else explore_disj f_next f_next_geq f_next_inst q
    | _ -> Parsing_helper.internal_error "[termsEq.ml >> remove_nat_diseq_neq_conj] Left term of a disequality should be a variable."
  in

  let rec explore_conj passed_conj = function
    | [] -> f_next passed_conj
    | disj::q ->
        explore_disj (fun b ->
          if b
          then
            (* In such a case, the disjunction is always true. *)
            explore_conj passed_conj q
          else explore_conj (disj::passed_conj) q
        ) (fun added_geq ->
          (* Case where we added an inequality and the disjunction is true
             provided that the inequality holds. *)
          f_next_geq (List.rev_append passed_conj q) added_geq
        ) (fun () ->
          (* Case where we added an equality *)
          f_next_inst (disj::(List.rev_append passed_conj q))
        ) disj
  in

  explore_conj [] neq


let remove_nat_diseq_neq_conj f_next f_next_geq f_next_inst nat_vars keep_vars neq =

  let rec explore_disj f_next f_next_geq f_next_inst = function
    | [] -> f_next false
    | (Var v1,t2)::q ->
        (* Since the disequations are simplified, we know that t1 is a variable *)
        if List.memq v1 nat_vars
        then
          let status2 = get_term_status nat_vars 0 t2 in
          match status2 with
            | Nat n2 ->
                (* Case of v1 <> n2 *)
                (* First case: v1 > n2 *)
                f_next_geq (Var v1,(-n2-1),Terms.zero_term);
                (* Second case: v1 < n2 *)
                f_next_geq (Terms.zero_term,(n2-1),Var v1);
                (* Last case v1 = n2 *)
                Terms.auto_cleanup (fun () ->
                  link v1 (TLink (Terms.generate_nat n2));
                  let (is_instantiated,keep_vars1) = update_keepvars keep_vars in
                  f_next_inst keep_vars1 is_instantiated
                )
            | NatVar(v2,n2) ->
                (* Case of v1 <> v2 + n2 *)
                (* First case: v1 > v2 + n2 *)
                f_next_geq (Var v1,(-n2-1),Var v2);
                (* Second case: v1 < v2 + n2 *)
                f_next_geq (Var v2,(n2-1),Var v1);
                (* Last case v1 = v2 + n2 *)
                Terms.auto_cleanup (fun () ->
                  Terms.link v1 (TLink (Terms.sum_nat_term (Var v2) n2));
                  let (is_instantiated,keep_vars1) = update_keepvars keep_vars in
                  f_next_inst keep_vars1 is_instantiated
                )
            | General(n2,f) ->
		(* Case of v1 <> n2 + f for all f *)
		(* First case: v1 < n2 *)
                f_next_geq (Terms.zero_term,(n2-1),Var v1);
		(* Second case: v1 = n2 + v' for a fresh variable v' *)
                Terms.auto_cleanup (fun () ->
                  let v' = Terms.new_var_def Param.nat_type in
                  let t = Terms.sum_nat_term (Var v') n2 in
                  Terms.link v1 (TLink t);
                  let (is_instantiated,keep_vars1) = update_keepvars keep_vars in
                  f_next_inst keep_vars1 is_instantiated
                )
            | NeverNat2 -> f_next true
            | _ -> explore_disj f_next f_next_geq f_next_inst q
        else explore_disj f_next f_next_geq f_next_inst q
    | _ -> Parsing_helper.internal_error "[termsEq.ml >> remove_nat_diseq_neq_conj] Left term of a disequality should be a variable."
  in

  let rec explore_conj passed_conj = function
    | [] -> f_next passed_conj
    | disj::q ->
        explore_disj (fun b ->
          if b
          then
            (* In such a case, the disjunction is always true. *)
            explore_conj passed_conj q
          else explore_conj (disj::passed_conj) q
        ) (fun added_geq ->
          (* Case where we added an inequality and the disjunction is true
             provided that the inequality holds. *)
          f_next_geq (List.rev_append passed_conj q) added_geq
        ) (fun keep_vars1 is_instantiated ->
          (* Case where we added an equality *)
          f_next_inst (disj::(List.rev_append passed_conj q)) keep_vars1 is_instantiated
        ) disj
  in

  explore_conj [] neq

(*********************************************************
        functions for formula simplification. This section
        include the functions :
                - unify_disequation
                - elim_universal_variable
**********************************************************)

(** Unify_disequations *)

let rev_assoc2 keep_vars assoc_gen_var v =
  match rev_assoc v (!assoc_gen_var) with
    Var _ ->
      if List.mem v keep_vars then
        Var v
      else
        let v' = new_gen_var v.btype false in
        assoc_gen_var := (v', v) :: (!assoc_gen_var);
        FunApp(v', [])
  | x -> x

(** [make_disequation_from_unify] create the list of simple constraint
        corresponding to $\bigvee_j x_j \neq \sigma_k x_j$*)
let rec make_disequation_from_unify keep_vars assoc_gen_with_var = function
  | [] -> []
  | (var::l) ->
      let l' = make_disequation_from_unify keep_vars assoc_gen_with_var l in
      match var.link with
        | NoLink -> l'
        | TLink _ -> (rev_assoc2 keep_vars assoc_gen_with_var var, follow_link (rev_assoc2 keep_vars assoc_gen_with_var) (Var var)) :: l'
        | _ -> internal_error "unexpected link in make_disequation_from_unify"

let rec close_disequation_eq restwork = function
  | [] -> restwork ()
  | (t1,t2)::l ->
      begin
        try
          unify_modulo (fun () ->
            close_disequation_eq restwork l;
            raise Unify) t1 t2
            (* In fact, always terminates by raising Unify; never returns; cleanup() *)
        with
          Unify -> cleanup ()
      end

let unify_disequation nextf accu constra =
  let assoc_gen_with_var = ref [] in (* Association list general var * var *)

  assert (!Terms.current_bound_vars == []);

  (* Get all classic variables *)

  let keep_vars = ref [] in
  List.iter (fun (t1,t2) -> get_vars keep_vars t1; get_vars keep_vars t2) constra;

  (* all general variable in [constra] are replaced by classic variables *)
  let constra' = List.map (fun (t1,t2) -> replace_f_var assoc_gen_with_var t1, replace_f_var assoc_gen_with_var t2) constra in

  let var_list = ref [] in
  List.iter (fun (t1,t2) -> get_vars var_list t1; get_vars var_list t2) constra';

  close_disequation_eq (fun () ->
    try
      let new_disequation = make_disequation_from_unify !keep_vars assoc_gen_with_var !var_list in
      cleanup ();
      accu := (nextf new_disequation) :: (!accu)
    with TrueConstraint -> cleanup ()
  ) constra';

  assert (!Terms.current_bound_vars == [])

(** Elim_universal_variables *)

(** This function must be applied after [unify_disequation]. Indeed we assume that for
        any v \neq t in [constra], v only occur once in [constra].*)
let elim_universal_variable constra =

  let rec look_for_general_var constra_done = function
    | [] -> List.rev constra_done
    | (FunApp(f,[]),_)::q when f.f_cat = General_mayfail_var -> look_for_general_var constra_done q
    | (v1, FunApp(f,[]))::q when f.f_cat = General_mayfail_var ->
        let rep (x,t) = x, replace_name f v1 t in
        let constra_done' = List.map rep constra_done
        and q' = List.map rep q in

        look_for_general_var constra_done' q'
    | (Var v,_)::q when v.unfailing -> Parsing_helper.internal_error "May-fail variables forbidden in inequalities (1)"
    | (_, Var v)::q when v.unfailing -> Parsing_helper.internal_error "May-fail variables forbidden in inequalities (2)"
      (* Given the previous cases, at this point, in Neq(t,t'), t and t' cannot
         fail: they cannot be General_mayfail_vars nor may-fail variables,
         and they cannot be the constant fail, because the unification of
         fail with the cases that remain (General_var, variable) fails. *)
    | (FunApp(f,[]),_)::q when f.f_cat = General_var -> look_for_general_var constra_done q
    | (Var(v) as v1,FunApp(f,[]))::q when f.f_cat = General_var ->
        let rep (x,t) = x, replace_name f v1 t in
        let constra_done' = List.map rep constra_done
        and q' = List.map rep q in

        look_for_general_var constra_done' q'
    | t::q -> look_for_general_var (t::constra_done) q
  in
  look_for_general_var [] constra

(*** Combining the simplification ***)

let copy_neq_list3 = List.map (fun (t1,t2) -> copy_term3 t1, copy_term3 t2)

let feed_new_constra accu_keep_vars nat_vars accu constra =
  (* TO DO do not keep "syntactic" terms after unification modulo?
   let constra = remove_syntactic_constra constra in *)
  try
    let constra_has_gen_var = List.exists (fun (_,t) -> has_gen_var t) constra in
    let accu_nat_vars = ref [] in
    List.iter (elim_var_notelsewhere constra_has_gen_var !accu_keep_vars accu_nat_vars nat_vars) constra;

    let constrasimp = copy_neq_list3 constra in
    Terms.cleanup();
    if constrasimp = [] then
      raise FalseConstraint
    else if List.exists (fun a'' -> implies_constraint a'' constrasimp) (!accu) then
      ()
    else
      begin
        accu_keep_vars := !accu_nat_vars @ !accu_keep_vars;
        accu := constrasimp :: (List.filter (fun a'' -> not (implies_constraint constrasimp a'')) (!accu))
      end
  with TrueConstraint ->
    Terms.cleanup()

let simplify_neq_conj accu_keep_vars nat_vars neq_conj =
  Terms.auto_cleanup (fun () ->
    let accu = ref [] in
    List.iter (unify_disequation elim_universal_variable accu) neq_conj;
    let accu' = ref [] in
    List.iter (feed_new_constra accu_keep_vars nat_vars accu') (!accu);
    !accu'
  )

let check_neq_conj neq_conj =
  Terms.auto_cleanup (fun () ->
    let accu = ref [] in
    List.iter (unify_disequation elim_universal_variable accu) neq_conj;
    List.iter (function [] -> raise FalseConstraint | _ -> ()) !accu
  )

(* Simplification function with NoMatch exception *)

let rec check_and_decompose2 = function
  | Var v ->
      if not (equal_types v.btype Param.nat_type)
      then raise NoMatch;

      (Var v,0)
  | FunApp(f,[t]) when f == Terms.succ_fun ->
      let (t',n) = check_and_decompose2 t in
      (t',n+1)
  | FunApp(f,[]) as t when f == Terms.zero_cst -> (t,0)
  | _ -> raise NoMatch

let rec simplify_geq2 (t1,n,t2) =
  let (t1',n1) = check_and_decompose2 t1 in
  let (t2',n2) = check_and_decompose2 t2 in

  (t1',(n1 + n - n2), t2')

let simplify_neq_conj2 neq_conj =
  Terms.auto_cleanup (fun () ->
    let accu = ref [] in
    List.iter (unify_disequation elim_universal_variable accu) neq_conj;
    List.iter (function [] -> raise NoMatch | _ -> ()) !accu;
    !accu
  )

(*** Main simplification function ***)

(* The function simplify_constraints_keepvars does not try to apply case distinction w.r.t.
   natural variables occuring in disequalities. Such case distinction is only
   applied on clauses during the saturation.
   Note however, that simplify_constraints_keepvars may instantiate some of the variables in
   keep_vars due to inequalities. *)

let simplify_constraints_keepvars f_next f_next_inst keep_vars c =
  let nat_vars = ref [] in

  (* Check the predicates is_nat *)
  List.iter (check_is_nat nat_vars) c.is_nat;

  (* Simplify the predicates geq: We only check that the terms are natural numbers.
     We do not check here is full satisfiability of the conjunction of inequalities. *)
  let geq1 = List.map (simplify_geq nat_vars) c.geq in

  (* Simplify the inequalities *)
  get_equalities (fun eq_left eq_right assoc number_vertices distance ->

    Terms.auto_cleanup (fun () ->
      List.iter2 Terms.unify eq_left eq_right;
      let (is_instantiated, keep_vars1) = update_keepvars keep_vars in

      (* Simplify the predicates is_not_nat. Moreover, we remove from keep_vars the
         variables that have been instantiated. *)
      let is_not_nat1 =
        if eq_left <> []
        then List.map copy_term4 c.is_not_nat
        else c.is_not_nat
      in

      let accu_keep_vars = ref keep_vars1 in

      let is_not_nat2 = Terms.auto_cleanup (fun () -> simplify_is_not_nat accu_keep_vars !nat_vars is_not_nat1) in

      (* At this point, [accu_keep_vars] contains the variables of [keep_vars] and the
         natural variables that still occur in is_not_nat2. *)

      let neq_conj1 =
        if eq_left <> []
        then List.map (List.map (fun (t1,t2) -> copy_term4 t1, copy_term4 t2)) c.neq
        else c.neq
      in

      let neq_conj2 = simplify_neq_conj accu_keep_vars !nat_vars neq_conj1 in

      let geq2 = rearrange_inequalities distance assoc number_vertices !accu_keep_vars in

      let is_nat2 =
        let geq_vars = ref [] in
        List.iter (fun (t1,_,t2) -> get_vars geq_vars t1; get_vars geq_vars t2) geq2;
        List.fold_left (fun acc v ->
          (* We only keep the variables that do not occur in the relations *)
          if (List.memq v !accu_keep_vars) && not (List.memq v !geq_vars)
          then (Var v) :: acc
          else acc
        ) [] !nat_vars
      in

      let constraints =
        {
          neq = neq_conj2;
          is_nat = is_nat2;
          is_not_nat = is_not_nat2;
          geq = geq2
        }
      in

      if is_instantiated
      then f_next_inst constraints
      else f_next constraints
    )
  ) geq1

let get_vars_facts l =
  let vars = ref [] in
  List.iter (Terms.get_vars_fact vars) l;
  !vars

let simplify_constraints f_next f_next_inst fact_list c =
  simplify_constraints_keepvars f_next f_next_inst (get_vars_facts fact_list) c

let rec simplify_after_inst f_next f_next_inst added_nat keep_vars constra =
  try
    let nat_vars = ref added_nat in
    List.iter (check_is_nat nat_vars) constra.is_nat;
    let geq1 = List.map (simplify_geq nat_vars) constra.geq in

    (* Change to have one function that does not gather keepvars *)
    let dummy_keep_vars = ref keep_vars in
    let neq1 = simplify_neq_conj dummy_keep_vars !nat_vars constra.neq in

    remove_nat_diseq_neq_conj (fun neq2 ->
      (* Case where nothing is changed *)
      try
	(* A bit of work is repeated here (check_is_nat, simplify_geq)
	   but it is not a real problem *)
        simplify_constraints_keepvars f_next f_next_inst keep_vars { constra with geq = geq1 ; neq = neq2 }
      with FalseConstraint -> ()
    ) (fun neq2 added_geq ->
      (* Case where we added an inequatity as hypothesis *)
      simplify_after_geq f_next f_next_inst added_nat !nat_vars keep_vars { constra with geq = added_geq::geq1; neq = neq2 }
    ) (fun neq2 keep_vars1 is_instantiated ->
      (* Case where a substitution has been applied *)
      let constra1 = Terms.copy_constra4 { constra with geq = geq1 ; neq = neq2 } in

      simplify_after_inst (if is_instantiated then f_next_inst else f_next)
	f_next_inst added_nat keep_vars1 constra1
    ) !nat_vars keep_vars neq1
  with FalseConstraint -> ()

and simplify_after_geq f_next f_next_inst nat_vars added_nat keep_vars constra =
  (* In this case, we first check that geq has a solution. *)
  try
    get_equalities (fun eq_left eq_right assoc number_vertices distance ->
      Terms.auto_cleanup (fun () ->
        List.iter2 Terms.unify eq_left eq_right;

        let (is_instantiated,keep_vars1,constra1) =
          if eq_left = []
          then false,keep_vars,constra
          else
            let (is_instantiated,keep_vars1) = update_keepvars keep_vars in
            is_instantiated, keep_vars1, Terms.copy_constra4 constra
        in

        simplify_after_inst (if is_instantiated then f_next_inst else f_next)
	  f_next_inst added_nat keep_vars1 constra1
      )
    ) constra.geq
  with FalseConstraint -> ()

let simplify_constraints_rule f_next f_next_inst (hypl,concl,hist,constra) =
  try
    if constra.geq = []
    then
      simplify_constraints_keepvars (fun constra' ->
        f_next (hypl,concl,hist,constra')
      ) (fun constra' ->
        let r' = copy_rule2 (hypl,concl,hist,constra') in
        Terms.auto_cleanup (fun () -> f_next_inst r')
      ) (get_vars_facts (concl::hypl)) constra
    else
      simplify_after_inst (fun constra' ->
	(* This copy is needed so that distinct clauses use distinct variables *)
        let r' = copy_rule2 (hypl,concl,hist,constra') in
        Terms.auto_cleanup (fun () -> f_next r')
      ) (fun constra' ->
        let r' = copy_rule2 (hypl,concl,hist,constra') in
        Terms.auto_cleanup (fun () -> f_next_inst r')
      ) [] (get_vars_facts (concl::hypl)) constra
  with FalseConstraint -> ()

(* Check that the current constraints are still satisfiable.
   Raise [FalseConstraint] when they are not.

   In the next function, [Terms.auto_cleanup] is useful because
   links may be stored in [Terms.current_bound_vars] when the function
   is called; these links must remain. *)

let rec check_after_inst f_next constra =
  let nat_vars = ref [] in
  List.iter (check_is_nat nat_vars) constra.is_nat;
  let geq1 = List.map (simplify_geq nat_vars) constra.geq in

  (* Simplify the disequalities *)
  let neq1 =
    Terms.auto_cleanup (fun () ->
      let accu = ref [] in
      List.iter (unify_disequation elim_universal_variable accu) constra.neq;
      List.iter (function [] -> raise FalseConstraint | _ -> ()) !accu;
      !accu
    )
  in

  remove_nat_diseq_neq_conj_exc (fun neq2 ->
    (* Case where nothing is changed *)
    f_next { constra with geq = geq1 ; neq = neq2 }
  ) (fun neq2 added_geq ->
    (* Case where we added an inequatity as hypothesis *)
    check_after_geq f_next !nat_vars { constra with geq = added_geq::geq1; neq = neq2 }
  ) (fun neq2 ->
    (* Case where a substitution has been applied *)
    let constra1 = Terms.copy_constra4 { constra with geq = geq1 ; neq = neq2 } in

    check_after_inst f_next constra1
  ) !nat_vars  neq1

and check_after_geq f_next nat_vars constra =
  (* In this case, we first check that geq as a solution. *)
  get_equalities (fun eq_left eq_right assoc number_vertices distance ->
    Terms.auto_cleanup (fun () ->
      List.iter2 Terms.unify eq_left eq_right;

      let constra1 =
        if eq_left = []
        then constra
        else Terms.copy_constra4 constra
      in

      check_after_inst f_next constra1
    )
  ) constra.geq

let check_constraints c =
  Terms.auto_cleanup (fun () ->
    let c1 = Terms.copy_constra2 c in
    Terms.cleanup ();

    check_after_inst (fun c2 ->
      (* Gather nat vars *)
      let nat_vars = ref [] in
      List.iter (check_is_nat nat_vars) c2.is_nat;
      let geq1 = List.map (simplify_geq nat_vars) c2.geq in

      (* Simplify the inequalities *)
      get_equalities (fun eq_left eq_right assoc number_vertices distance ->
        Terms.auto_cleanup (fun () ->
          List.iter2 Terms.unify eq_left eq_right;

          let (is_not_nat2, neq2) =
            if eq_left <> []
            then List.map copy_term4 c1.is_not_nat, List.map (List.map (fun (t1,t2) -> copy_term4 t1, copy_term4 t2)) c1.neq
            else c1.is_not_nat, c1.neq
          in

          (* Check the predicates is_not_nat  *)
          List.iter (check_is_not_nat !nat_vars) is_not_nat2;
          (* Check the disequalities *)
          check_neq_conj neq2
        )
      ) geq1
    ) c1
  )

(* Check closed constraints.
   This function is used to evaluate destructors in trace reconstruction.
   This function closed all constraints modulo the equational theory,
   because this is not done before. *)

let rec nat_of_closed_term = function
  | Var { link = TLink t } -> nat_of_closed_term t
  | FunApp(f,[t]) when (non_syntactic f) == Terms.succ_fun -> (nat_of_closed_term t) + 1
  | FunApp(f,[]) when (non_syntactic f) == Terms.zero_cst -> 0
  | _ -> raise Unify

let check_closed_is_nat t =
  try
    close_term_eq_synt (fun t' ->
      ignore (nat_of_closed_term t');
      true
    ) t
  with Unify -> false

let check_closed_neq_disj neq =
  let assoc_gen_with_var = ref [] in (* Association list general var * var *)
  (* all general variable in [constra] are replaced by classic variables *)
  let (left_terms, right_terms) = List.fold_left (fun (acc_l,acc_r) (t1,t2) -> (replace_f_var assoc_gen_with_var t1)::acc_l, (replace_f_var assoc_gen_with_var t2)::acc_r) ([],[]) neq in

  Terms.auto_cleanup (fun () ->
    try
      unify_modulo_list (fun () -> false) left_terms right_terms
    with Unify -> true)

let check_closed_geq (t1,n,t2) =
  try
    close_term_eq_synt (fun t1' ->
      let n1 = nat_of_closed_term t1' in
      close_term_eq_synt (fun t2' ->
        let n2 = nat_of_closed_term t2' in
        if n1 + n >= n2
        then true
        else raise Unify
      ) t2
    ) t1
  with Unify -> false

let check_closed_constraints c =
  List.for_all check_closed_is_nat c.is_nat &&
  List.for_all check_closed_geq c.geq &&
  List.for_all check_closed_neq_disj c.neq &&
  not (List.exists check_closed_is_nat c.is_not_nat)

(* Implication between constraints

1/ copy the constraints to instantiate variables according to
   the substitution computed by matching conclusion and hypotheses.
   This uses copy_constra3

2/ simplify the obtained constraint, by simplify_constra_list

3/ test the implication, by implies_constra
   raise NoMatch if it fails

Notice that variables may not be cleaned up when this function is called.
*)

let rec copy_term5 modified = function
  | Var { link = TLink t } ->
      (* We remove the syntactic symbols *)
      modified := true;
      remove_syntactic_term t
  | Var v -> Var v
  | FunApp(f,args) -> FunApp(f,List.map (copy_term5 modified) args)

let implies_is_not_nat constraints1 nat_vars t =
  try
    close_term_eq_synt (fun t1 ->
      let nat_vars' = match get_status_natural_number nat_vars t1 with
        | IsNat -> nat_vars
        | CanBeNat v -> v::nat_vars
        | NeverNat -> raise Unify
      in

      try
        List.iter (fun t' ->
          let modified = ref false in
          let t'' = copy_term5 modified t' in
          if !modified
          then check_is_not_nat nat_vars' t''
        ) constraints1.is_not_nat;

        List.iter (fun neq_disj ->
          let modified = ref false in
          let neq_disj' = List.map (fun (t1,t2) -> copy_term5 modified t1, copy_term5 modified t2) neq_disj in
          if !modified
          then check_neq_conj [neq_disj']
        ) constraints1.neq
      with FalseConstraint -> raise Unify
    ) t;
    raise NoMatch
  with Unify -> ()

let index_of_term assoc t =
  let index = ref 0 in
  try
    Array.iteri (fun i t' ->
      if Terms.equal_terms t t'
      then
        begin
          index := i;
          raise NoMatch
        end
    ) assoc;
    None
  with NoMatch -> Some !index

(* We assume here that both [constraints1] and [constraints2] are simplified.
    [geq1_data] is a function that returns [Some(distance,nb,assoc,edges)]
    when [constraints1] contains some inequalities and where [distance] is the matrix
    of minimum path associated to the inequalities of [constraints1]. [nb] is the
    number of vertices, [assoc] is the association table associating indices of the
    matrix [distance] with terms, [edges] is a function that returns the list of
    non-infinite edges in [distance]

    If [constraints1] does not contains inequalities then geq1_op = None.

    [geq1_data] and [edges] are functions that ensure that we only compute once
    the matrix [distance] and the edges of [distance]. *)
let implies_constraints nat_vars1 geq1_data constraints1 constraints2 =
  (* Retrieve nat variables and check implication of natural variables  *)
  let nat_vars2 = ref [] in
  List.iter (get_vars nat_vars2) constraints2.is_nat;
  List.iter (fun (t1,_,t2) -> get_vars nat_vars2 t1; get_vars nat_vars2 t2) constraints2.geq;

  if List.exists (fun v2 -> not (List.memq v2 !nat_vars1)) !nat_vars2
  then raise NoMatch;

  (* We now check the implication of is_not_nat predicates *)
  List.iter (implies_is_not_nat constraints1 !nat_vars1) constraints2.is_not_nat;

  (* We check the implication of disequalities *)
  if not
      (List.for_all (fun neq_disj2 ->
        List.exists (fun neq_disj1 -> implies_constraint neq_disj1 neq_disj2) constraints1.neq
          ) constraints2.neq) then raise NoMatch;

  (* We check the implication of inequalities *)
  match geq1_data () with
    | None ->
        (* In such case, [constraints1] does not contain an inequality.
          Hence, the implication holds only if [constraints2.geq] is always true. *)
        List.iter (fun (t1,n,t2) ->
          if not (Terms.equal_terms t2 Terms.zero_term) || n < 0
          then raise NoMatch
        ) constraints2.geq
    | Some(assoc,number_vertices,distance,edges) ->
        List.iter (fun (t1,n,t2) ->
          match index_of_term assoc t2 with
            | None ->
                (* Since t2 is not in the association table, then t2 is necessarily a variable
                   (0 is always part of assoc) and so implication is not possible. *)
                raise NoMatch
            | Some i2 ->
                match index_of_term assoc t1 with
                  | None ->
                      (* Since t2 is in the association table, but t1 is not then
                         the implication only holds when t2 <= n. This is only the case
                         when [constraints1.geq] enforces t2 <= k with k <= n, i.e.
                         distance.(i2).(0) <= n *)
                      begin match distance.(i2).(0) with
                        | N k -> if k > n then raise NoMatch
                        | Infinity -> raise NoMatch
                      end
                  | Some i1 ->
                      try
                        (* In such case, t1 and t2 are both already in the matrix, hence we can directly
                           add the edge (i1,i2,(-n-1)) to [edges ()] and check that there is no solution.
                           Recall that the edge (i1,i2,(-n-1)) means that t1 <= t2 - n - 1 which is the
                           negation of t1 + n >= t2 *)
                        ignore(algo_BellmanFord_core number_vertices ((i1,i2,(-n-1))::(edges ())));
                        raise NoMatch
                      with FalseConstraint -> ()
        ) constraints2.geq

exception Implied

let implies_constraints_copy f_copy keep_vars constraints1 constraints2 =
  (* We assume in this function that [constraints1] is already simplified
  so only [constraints2] needs to be simplified *)

  let nat_vars1 = ref [] in
  List.iter (get_vars nat_vars1) constraints1.is_nat;
  List.iter (fun (t1,_,t2) -> get_vars nat_vars1 t1; get_vars nat_vars1 t2) constraints1.geq;
  let constraints2' = f_copy constraints2 in

  (* We keep only the disequalities of [constraints2] that are not
     trivially implied by [constraints1] *)
  let neq2 = simplify_neq_conj2 constraints2'.neq in
  let neq2' =
    List.filter (fun neq_disj2 ->
      not (List.exists (fun neq_disj1 -> implies_constraint neq_disj1 neq_disj2) constraints1.neq)
    ) neq2
  in

  (* Same thing with inequalities *)
  let geq2 = List.map simplify_geq2 constraints2'.geq in
  let geq2' =
    List.filter (fun (t2,n2,t2') ->
      not (List.exists (fun (t1,n1,t1') ->
        Terms.equal_terms t1 t2 && Terms.equal_terms t1' t2' && n1 <= n2
      ) constraints1.geq)
    ) geq2
  in

  let constraints2'' = { constraints2' with geq = geq2'; neq = neq2' } in

  if not (is_true_constraints constraints2'')
  then
    let geq1_data_ref = ref None in
    let geq1_data () = match !geq1_data_ref with
      | Some data -> data
      | None ->
          if constraints1.geq = []
          then
            begin
              geq1_data_ref := Some None;
              None
            end
          else
            begin
              (* Since we assumed that [constraints1] is simplified, the following cannot fail. *)
              let data =
                algo_BellmanFord (fun assoc number_vertices distance ->
                  let geq1_edges_ref = ref None in
                  let geq1_edges () = match !geq1_edges_ref with
                    | None ->
                        let edges = get_edges number_vertices distance in
                        geq1_edges_ref := Some edges;
                        edges
                    | Some rel -> rel
                  in
                  Some(assoc,number_vertices,distance,geq1_edges)
                ) constraints1.geq
              in
              geq1_data_ref := Some data;
              data
            end
    in
    try
      simplify_after_inst (fun constraints2''' ->
        try
          implies_constraints nat_vars1 geq1_data constraints1 constraints2''';
          raise Implied
        with NoMatch -> ()
      ) (fun _ ->
        (* In such a case, [constraints2] forces an equality between some variables.
        Since we assumed that [constraints1] is already simplified, it does not
        enforce any equality. Therefore, we directly obtain that the implication
        does not hold. *)
        ()
      ) !nat_vars1 keep_vars constraints2'';

      raise NoMatch
    with Implied -> ()

let implies_constraints_keepvars_binders bl = implies_constraints_copy (fun c -> c) bl

let implies_constraints_keepvars rule = implies_constraints_copy (fun c -> c) (get_vars_facts rule)

let implies_constraints_keepvars3 rule = implies_constraints_copy Terms.copy_constra3 (get_vars_facts rule)

let implies_constraints_keepvars4 rule = implies_constraints_copy Terms.copy_constra4 (get_vars_facts rule)

(* [get_solution f_next constra] calls [f_next] after linking variables to
   a solution of the constraints [constra].
   Raises [FalseConstraint] when there is no solution. *)
let get_solution f_next constra =
  check_after_inst (fun constra1 ->
    (* Gather nat vars *)
    let nat_vars = ref [] in
    List.iter (check_is_nat nat_vars) constra1.is_nat;
    let geq1 = List.map (simplify_geq nat_vars) constra1.geq in

    algo_BellmanFord (fun assoc number_vertices distance ->
      Terms.auto_cleanup (fun () ->
        (* We know that the index 0 in distance corresponds to the constant zero. *)
        for i = 1 to number_vertices - 1 do
          match assoc.(i), distance.(0).(i) with
            | Var v, N w -> link v (TLink (generate_nat (-w)))
            | _ -> Parsing_helper.internal_error "[natural_number.ml >> get_solution] Should be a variable and the distance should not be infinite."
        done;

        List.iter (fun v -> match v.link with
          | NoLink -> link v (TLink zero_term)
          | _ -> ()
        ) !nat_vars;

        f_next ()
      )
    ) geq1
  ) constra

(* [gather_nat_vars constra] returns the list of natural number variables
   in [constra] *)

let rec gather_nat_vars_term accu_vars = function
  | Var v ->
      if (equal_types v.btype Param.nat_type) && not (List.memq v !accu_vars)
      then accu_vars := v :: !accu_vars
  | FunApp(f,[t]) when f == Terms.succ_fun -> gather_nat_vars_term accu_vars t
  | FunApp(f,[]) when f == Terms.zero_cst -> ()
  | _ -> ()

let gather_nat_vars constra =
  let nat_vars = ref [] in

  List.iter (gather_nat_vars_term nat_vars) constra.is_nat;
  List.iter (fun (t1,_,t2) -> gather_nat_vars_term nat_vars t1; gather_nat_vars_term nat_vars t2) constra.geq;

  !nat_vars

(***** Close destructor rewrite rules under equations ******)


(* Subsumption between rewrite rules with side conditions *)

let implies_rew (leq1, req1, side_c1) (leq2, req2, side_c2) =
  assert (!current_bound_vars == []);
  try
    List.iter2 Terms.match_terms leq1 leq2;
    Terms.match_terms req1 req2;
    (* test side_c2 => \sigma side_c1
       where \sigma is obtained by the above matching.*)
    let vars = ref [] in
    List.iter (Terms.get_vars vars) leq2;
    Terms.get_vars vars req2;
    implies_constraints_copy Terms.copy_constra3 !vars side_c2 side_c1;
    Terms.cleanup();
    true
  with NoMatch ->
    Terms.cleanup();
    false

(* Closure of destructors itself *)

let close_destr_eq f l =
  let results = ref [] in

  List.iter (fun (leq, req,side_c) ->
    close_term_list_eq (function
      | [] -> internal_error "should not be empty"
      | (req'::leq') ->
          close_constra_eq (fun side_c0 ->
            let curr_bound_vars = !current_bound_vars in
            current_bound_vars := [];

            let (leq1,req1, side_c1) =
              (List.map copy_term2 leq', copy_term2 req', copy_constra2 side_c0)
            in
            cleanup();

            (* Simplify the obtained constraints *)
            begin
              try
                let vars = ref [] in
                List.iter (Terms.get_vars vars) leq1;
                Terms.get_vars vars req1;
                let rew1 =
                  simplify_constraints_keepvars (fun side ->
                    leq1,req1,side
                  ) (fun side ->
                    List.map copy_term4 leq1, copy_term4 req1, side
                  ) !vars side_c1
                in

                (* Eliminate redundant rewrite rules *)
                if List.exists (fun rew2 ->
                  implies_rew rew2 rew1) (!results) then ()
                else
                  results := rew1 :: (List.filter (fun rew2 ->
                    not(implies_rew rew1 rew2)) (!results));
              with FalseConstraint -> ()
            end;
            current_bound_vars := curr_bound_vars
        ) side_c
    ) (req::leq)
  ) l;

  (* Check that all variables are bound in the LHS of the rewrite rule *)
  List.iter (fun (leq, req, side_c) ->
    let var_list_rhs = ref [] in
    Terms.get_vars var_list_rhs req;
    Terms.get_vars_constra var_list_rhs side_c;
    if not (List.for_all (fun v -> List.exists (Terms.occurs_var v) leq) (!var_list_rhs)) then
      begin
        print_string ("Error in the definition of destructor " ^ (Display.string_of_fsymb f) ^ " after taking into account equations:\nIncorrect rewrite rule: ");
        Display.Text.display_red f [leq, req, side_c];
        Parsing_helper.user_error "All variables of the right-hand side of a rewrite rule\nshould also occur in the left-hand side."
      end;
  ) !results;

  !results

(* Record equations *)

let record_eqs horn_state =
  has_equations := (horn_state.h_equations != []);
  if hasEquations() then
    begin
      if !Param.html_output then
        begin
          Display.LangHtml.openfile ((!Param.html_dir) ^ "/eq.html") "ProVerif: equations";
          Display.Html.print_string "<H1>Equations</H1>\n"
        end;
      record_eqs_internal horn_state.h_equations;
      if !Param.html_output then
        begin
      	  Display.LangHtml.close();
	  Display.Html.print_string "<A HREF=\"eq.html\">Equations</A><br>\n"
	end
    end

(* Record equations, also updating rewrite rules of destructors *)

let record_eqs_with_destr pi_state =
  has_equations := (pi_state.pi_equations != []);
  if hasEquations() then
    begin
      if !Param.html_output then
	begin
	  Display.LangHtml.openfile ((!Param.html_dir) ^ "/eq.html") "ProVerif: equations and destructors";
	  Display.Html.print_string "<H1>Equations</H1>\n"
	end;
      record_eqs_internal pi_state.pi_equations;

      if !Param.html_output then
	Display.Html.print_string "<H1>Completed destructors</H2>\n"
      else if !Param.verbose_destr then
	Display.Text.print_line "Completed destructors:";

      List.iter (fun f ->
	match f.f_cat with
	| Red red_rules ->
	    let red_rules' = close_destr_eq f red_rules in
	    if !Param.html_output then
	      (Display.Html.display_red f red_rules';Display.Html.print_string "<br>")
	    else if !Param.verbose_destr then
	      (Display.Text.display_red f red_rules';Display.Text.print_string "\n");
	    f.f_cat <- Red red_rules'
	| _ -> ()
	      ) pi_state.pi_funs;

      if !Param.html_output then
	begin
	  Display.LangHtml.close();
	  Display.Html.print_string "<A HREF=\"eq.html\">Equations & Destructors</A><br>\n"
	end
    end

(********* Simplifies a term using the equations ********)

exception Reduces

let simp_eq t =
  if not (!Param.simpeq_remove) then
    normal_form t
  else
    let rec find_red_term = function
	Var v -> ()
      | (FunApp(f,l)) as t ->
	  List.iter find_red_term l;
	  let rec find_red = function
              [] -> ()
	    | ((leq,req)::redl) ->
		try
		  if not (Terms.equal_types (Terms.get_term_type leq) (Terms.get_term_type t)) then
		    raise NoMatch;
		  Terms.match_terms leq t;
		  (*let r = copy_term3 req in*)
		  Terms.cleanup();
		  raise Reduces
		with NoMatch ->
		  Terms.cleanup();
		  find_red redl
	  in
	  find_red (!rewrite_system)
    in
    find_red_term t;
    t

(*
let simp_eq t =
  print_string "Simplifying ";
  Display.Text.display_term t;
  print_string " into ";
  let r = simp_eq t in
  Display.Text.display_term r;
  Display.Text.newline();
  r
*)
