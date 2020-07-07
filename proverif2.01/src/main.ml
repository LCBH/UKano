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
open Parsing_helper

type out_pos =
    Spass
  | Solve

type in_pos =
    Horn
  | HornType
  | SpassIn
  | Pi
  | PiType
  | Default

let gc = ref false

let out_kind = ref Solve

let in_kind = ref Default

let out_file = ref ""

let out_n = ref 0

let up_out = function
    "spass" -> Spass
  | "solve" -> Solve
  | _ -> Parsing_helper.user_error "-out should be followed by spass or solve"

let up_in = function
    "horn" -> Horn
  | "horntype" -> HornType
  | "spass" -> SpassIn
  | "pi" -> Pi
  | "pitype" -> PiType
  | _ -> Parsing_helper.user_error "-in should be followed by horn, horntype, spass, pi, or pitype"

let current_axioms = ref []
let current_lemmas = ref []

let group_summary = ref { sum_queries = []; sum_lemmas = []; sum_axioms = [] }
let full_summary = ref []

exception Is_determined of query_res

(* Store the obtained result and raise Is_determined
   if the result is determined (i.e. True or False).
   [group_summary] is assumed to contain a single query,
   whose result is initially set to [DontKnow].

   When the result is determined, it stores the obtained
   result in [group_summary] with the current lemmas and
   axioms from the last call to [prove_lemmas].
   Older lemmas and axioms are forgotten.

   Otherwise, when [always_store] is false, it just forgets
   the results (this is what happens when we simplify
   a process with choice: we keep only the results for the
   process given by the user, for simplicity);
   When [always_store] is true, it adds the current
   axioms and lemmas to [group_summary]. *)
let store_and_raise_determined always_store = function
  | [(True | False) as r, _] ->
      begin
	match (!group_summary).sum_queries with
	| [q,_] ->
	    group_summary :=
	       { sum_queries = [q,r];
		 sum_lemmas = !current_lemmas;
		 sum_axioms = !current_axioms }
	| _ -> assert false
      end;
      raise (Is_determined(r))
  | _ ->
      if always_store then
	group_summary :=
	   { !group_summary with
             sum_lemmas = (!current_lemmas) @ (!group_summary).sum_lemmas;
             sum_axioms = (!current_axioms) @ (!group_summary).sum_axioms }

let check_disequations l =
  if l <> [] then
    begin
      List.iter (fun (t1, t2) ->
        try
          Terms.auto_cleanup (fun () ->
            TermsEq.unify_modulo (fun () ->
              Display.Text.print_string "Disequation: ";
              Display.Text.display_term t1;
              Display.Text.print_string " <> ";
              Display.Text.display_term t2;
              Display.Text.newline();
              Parsing_helper.user_error "Invalid disequation: the terms unify"
                ) t1 t2)
        with Terms.Unify -> ()
            ) l;
      Display.Text.print_line "Note: all disequations are valid. (ProVerif otherwise ignores them.)"
    end

let set_need_vars_in_names pi_state =
  match pi_state.pi_need_vars_in_names with
    Computed _ -> pi_state
  | Function f ->
      let need_vars_in_names = f pi_state in
      { pi_state with
        pi_need_vars_in_names = Computed need_vars_in_names }

let transl_query pi_state =
  let aux = function
    | QueryToTranslate f -> f pi_state
    | x -> x
  in
  let process_query' =
    match pi_state.pi_process_query with
    | (Equivalence _) as pq -> pq
    | SingleProcess(p,ql) -> SingleProcess(p, List.map aux ql)
    | SingleProcessSingleQuery(p,q) -> SingleProcessSingleQuery(p, aux q)
  in
  { pi_state with
    pi_process_query = process_query' }

let transl_lemma pi_state =
  let aux = function
    | LemmaToTranslate f -> f pi_state
    | x -> x
  in
  { pi_state with
    pi_lemma = List.map (fun lemma -> aux lemma) pi_state.pi_lemma }

(* Remove lemmas and axioms with bound names for equivalences queries.
   They cause an error in Lemma.translate_to_bi_lemma. It may be possible
   to handle them by deeper changes, but this does not seem essential. *)

let remove_lemmas_with_bound_names pi_state =
  { pi_state with
      pi_lemma =
        List.filter (fun t_lem ->
          if Lemma.no_bound_name_t_lemmas t_lem
          then true
          else
            begin
              Parsing_helper.input_warning "Lemmas and axioms containing bound names are ignored for equivalence queries." Parsing_helper.dummy_ext;
              false
            end
        ) pi_state.pi_lemma
    }

let check_delayed_names pi_state =
  let aux = function
    | QueryToTranslate _ ->
        Parsing_helper.internal_error "Queries should have been translated before check_delayed_names"
    | CorrespQuery(ql,s_status) ->
        CorrespQuery(List.map Reduction_helper.check_delayed_names ql, s_status)
    | CorrespQEnc(qql,s_status) ->
        CorrespQEnc(List.map (fun (qorig, qencoded) ->
          (Reduction_helper.check_delayed_names qorig,
           Reduction_helper.check_delayed_names qencoded)) qql, s_status)
    | ChoiceQEnc q -> ChoiceQEnc(Reduction_helper.check_delayed_names q)
    | x -> x
  in

  let process_query' =
    match pi_state.pi_process_query with
    | (Equivalence _) as pq -> pq
    | SingleProcess(p,ql) -> SingleProcess(p, List.map aux ql)
    | SingleProcessSingleQuery(p,q) -> SingleProcessSingleQuery(p, aux q)
  in
  let t_lemmas_list' =
    List.map (function
      | LemmaToTranslate _ -> Parsing_helper.internal_error "Lemmas should have been translated before check_delayed_names"
      | Lemma lem_state ->
          let lemmas' =
            List.map (fun lem -> match lem.ql_original_query with
              | None -> { lem with ql_query = Reduction_helper.check_delayed_names lem.ql_query }
              | Some q -> { lem with ql_query = Reduction_helper.check_delayed_names lem.ql_query; ql_original_query = Some(Reduction_helper.check_delayed_names q) }
            ) lem_state.lemmas in
          Lemma { lem_state with lemmas = lemmas' }
    ) pi_state.pi_lemma
  in
  let original_axioms' = List.map Reduction_helper.check_delayed_names_r pi_state.pi_original_axioms in
  { pi_state with
    pi_process_query = process_query';
    pi_lemma = t_lemmas_list';
    pi_original_axioms = original_axioms'
  }

let move_new pi_state =
  let move_new_desc p_desc =
    { p_desc with
      proc = Movenew.move_new p_desc.proc;
      display_num = None;
      construction = MoveNew(p_desc) }
  in
  if !Param.move_new then
    let process_query' =
      match pi_state.pi_process_query with
      | Equivalence(p1, p2) -> Equivalence (move_new_desc p1, move_new_desc  p2)
      | SingleProcess(p, ql) -> SingleProcess(move_new_desc p, ql)
      | SingleProcessSingleQuery(p,q) -> SingleProcessSingleQuery(move_new_desc p, q)
    in
    { pi_state with
      pi_process_query = process_query' }
  else
    pi_state

let transl_to_clauses pi_state =
  if (Reduction_helper.get_process pi_state).bi_pro then
    Pitranslweak.transl pi_state
  else
    Pitransl.transl pi_state

(* [split pi_state next_f] calls [next_f] on each query in [pi_state].
   It guarantees that the state passed to [next_f] never has
   [pi_process_query = SingleProcess _]. This case is replaced with several calls
   using [SingleProcessSingleQuery]. *)

let split pi_state next_f =
  match pi_state.pi_process_query with
    SingleProcess(p,ql) ->
      List.iter (fun q ->
        next_f { pi_state with
                 pi_process_query = SingleProcessSingleQuery(p,q) }
          ) ql
  | _ -> next_f pi_state

let is_non_interf horn_state =
  match horn_state.h_solver_kind with
    Solve_Noninterf _ -> true
  | _ -> false

let interference_analysis horn_state pi_state =
  if (pi_state.pi_equations != []) && (is_non_interf horn_state) then
    Parsing_helper.input_warning "using \"noninterf\" in the presence of equations may yield many\nfalse attacks. If you observe false attacks, try to code the desired\nproperty using \"choice\" instead." Parsing_helper.dummy_ext;
  let (_,query) = Param.get_process_query pi_state in
  let result = Rules.bad_derivable horn_state in
  if result = [] then
    begin
      Display.Text.display_query_result query True;
      if !Param.html_output then
        Display.Html.display_query_result query True;
      True
    end
  else
    begin
      let l = List.map (fun rule ->
        Display.Text.print_string "goal reachable: ";
        Display.Text.display_rule_abbrev rule;
        if !Param.html_output then
          begin
            Display.Html.print_string "goal reachable: ";
            Display.Html.display_rule_abbrev rule
          end;
        try
          let new_tree = History.build_history None rule in
          let r =
          (* For weak secrets, the reconstructed attack really falsifies the
             equivalence; for other equivalences, it just reaches the program
             point at which we find the first difference of execution, which
             does not guarantee that the equivalence is false *)
            if (!Param.reconstruct_trace) && (!Param.reconstruct_derivation) then
              match query with
              | WeakSecret _ ->
                  Reduction.do_reduction None None pi_state.pi_original_axioms new_tree
              | NonInterfQuery _ ->
                  ignore (Reduction.do_reduction None None pi_state.pi_original_axioms new_tree);
                  false
              | ChoiceQuery | ChoiceQEnc _ ->
                  ignore (Reduction_bipro.do_reduction None None pi_state.pi_original_axioms new_tree);
                  false
              | _ ->
                  false
            else
              false
          in
          Terms.cleanup();
          r
        with Not_found ->
          (* When the derivation could not be reconstructed *)
          Terms.cleanup();
          false
          ) result
      in
      let result =
        if List.exists (fun x -> x) l then False else DontKnow
      in
      Display.Text.display_query_result query result;
      if !Param.html_output then
        Display.Html.display_query_result query result;
      result
    end

let get_out_file() =
  if !out_file = "" then
    Parsing_helper.user_error "you should provide the output filename by the option -o <filename>";
  incr out_n;
  !out_file ^ (if !out_n = 1 then "" else string_of_int (!out_n))

let horn_solve (horn_state, queries) =
  match !out_kind with
    Solve ->
     TermsEq.record_eqs horn_state;
     Rules.main_analysis horn_state queries
  | Spass ->
     Spassout.main (get_out_file()) horn_state.h_clauses queries

let corresp_solve (horn_state, pi_state) =
  Param.current_state := pi_state;
  match !out_kind with
    Solve ->
      Piauth.solve_auth horn_state pi_state
  | Spass ->
      Spassout.main (get_out_file()) horn_state.h_clauses
        (Encode_queries.query_to_facts pi_state);
      []

let equiv_solve (horn_state, pi_state) =
  Param.current_state := pi_state;
  match !out_kind with
    Solve ->
      interference_analysis horn_state pi_state
  | Spass ->
      Parsing_helper.user_error "the clauses generated by ProVerif for process equivalences cannot be\ntranslated to the Spass input format."

(*********************************************
                 Interface
**********************************************)

let display_process_desc p_desc =
  Display.Def.display_numbered_process false p_desc

let display_process pi_state =
  match pi_state.pi_process_query with
    Equivalence(p1, p2) ->
      display_process_desc p1;
      display_process_desc p2
  | SingleProcessSingleQuery(p, _) | SingleProcess(p,_) ->
      display_process_desc p

let is_corresp = function
  | CorrespQuery _ | CorrespQEnc _ -> true
  | _ -> false

let get_initial_query = function
    CorrespQEnc (qql, s_status) -> CorrespQuery(List.map fst qql,s_status)
  | ChoiceQEnc q -> CorrespQuery([q],Param.dummy_solve_status)
  | q -> q

let is_initial p_desc =
  match p_desc.construction with
  | Initial_process | Initial_process1 | Initial_process2 -> true
  | _ -> false

let display_query_header q_type pi_state =
  let (p,q) = Param.get_process_query pi_state in
  let initial_query = get_initial_query q in
  let multiple_encoded = match q with
    | CorrespQEnc (qql, _) -> List.length qql > 1
    | _ -> false
  in
  if (!Param.tulafale == 1) && (is_corresp initial_query) then
    Display.Text.print_line "-- Secrecy & events."
  else if multiple_encoded then
    begin
      Display.Text.print_string "-- ";
      Display.Text.display_query true q_type initial_query;
      Display.Text.newline();
      if !Param.html_output then
	begin
	  Display.Html.print_string "<LI><span class=\"query\">";
	  Display.Html.display_query true q_type initial_query;
	  Display.Html.print_string "</span><br>\n";
	  Display.Html.print_string "Encoding: ";
          Display.Html.display_query false q_type q;
          Display.Html.print_string "in "
	end
      else
	begin
 	  Display.Text.print_string "Encoding: ";
	  Display.Text.display_query false q_type q;
          Display.Text.print_string "in "
	end;
      Display.Def.display_process_or_link true p
    end
  else
    begin
      Display.Text.print_string "-- ";
      Display.Text.display_query true q_type q;
      if !Param.html_output then
	begin
	  Display.Html.print_string "<LI><span class=\"query\">";
	  Display.Html.display_query true q_type q;
	  Display.Html.print_string " in ";
	  Display.Def.display_process_or_link true p;
	  Display.Html.print_string "</span>\n";
	  Display.Text.print_string " in ";
	  Display.Text.display_process_link true p;
	  Display.Text.newline();
	end
      else
	begin
	  Display.Text.print_string " in ";
	  Display.Def.display_process_or_link true p
	end
    end;
  Param.current_process_number :=
     match p.display_num with
     | Some n -> n
     | _ -> Parsing_helper.internal_error "Process should have been displayed"

let solve pi_state =
  (* [set_event_status] sets whether each event is injective/non-injective
     depending on queries *)
  let pi_state1 = Pievent.set_event_status pi_state in
  (* [simplify_lemmas] depends on the status of events in queries to
     simplify lemmas *)
  let pi_state2 = Lemma.simplify_lemmas pi_state1 in
  let pi_state3 = Lemma.simplify_queries_for_induction pi_state2 in
  (* [update_event_status_with_lemmas] may add more events to consider
     (always non-injective) due to lemmas *)
  Pievent.update_event_status_with_lemmas pi_state3;
  (* [transl_to_clauses] translates the pi calculus process
     into Horn clauses. The translation depends on the status
     of events *)
  let horn_state1,pi_state4 = transl_to_clauses pi_state3 in
  (* [check_delayed_names] transforms references to bound names
     in queries into the corresponding patterns.
     The translation into Horn clauses must be done before that,
     to know which pattern is associated to each name. *)
  let pi_state5 = check_delayed_names pi_state4 in
  (* [transl_lemmas] translates lemmas into the needed information
     to apply the lemmas during resolution. *)
  let horn_state2 = Lemma.transl_lemmas horn_state1 pi_state5 in
  (* [display_query_header] displays the query.
     That must be done after [check_delayed_names] to have
     a correct display of bound names *)
  display_query_header Display.TQuery pi_state5;
  (* Finally perform the resolution and interpret the
     results. *)
  let (_,q) = Param.get_process_query pi_state5 in
  let result =
    match q with
    | CorrespQuery _ | CorrespQEnc _ ->
	corresp_solve (horn_state2, pi_state5)
    | _ ->
	[equiv_solve (horn_state2,pi_state5), q]
  in
  incr Param.current_query_number;
  result

exception UnprovedLemma of Pitypes.t_process_desc * Pitypes.t_query

(* Split [SingleProcess] and replace each query with the
   corresponding initial query *)

let to_single_initial_query pqrl =
  let rec aux accu = function
    | [] -> accu
    | (SingleProcess(p, ql), res)::rest ->
	aux ((List.rev_map (fun q -> SingleProcessSingleQuery(p, get_initial_query q), res) ql) @ accu) rest
    | (SingleProcessSingleQuery(p,q), res)::rest ->
	aux ((SingleProcessSingleQuery(p,get_initial_query q), res) :: accu) rest
    | (pq, res)::rest ->
	aux ((pq, res) :: accu) rest
  in
  aux [] pqrl

let display_summary results =
  Display.Text.newline ();
  Display.Text.print_string Display.Text.hline;
  Display.Text.print_line "Verification summary:";
  Display.Text.newline ();

  if !Param.html_output
  then
    begin
      Display.Html.newline ();
      Display.Html.print_string Display.Html.hline;
      Display.Html.print_string "<H2>Verification summary:</H2>\n<UL>";
    end;

  List.iter (fun sum ->
    (* Separate queries when there are no associated lemmas and axioms.
       Split [SingleProcess] and replace each query with the
				   corresponding initial query *)
    let queries' = to_single_initial_query sum.sum_queries in
    if sum.sum_lemmas == [] && sum.sum_axioms == [] then
      List.iter (fun query_res ->
	Display.Text.display_process_query_res query_res;
	Display.Text.newline();
	Display.Text.newline();
	if !Param.html_output
	  then
	  begin
	    Display.Html.print_string "\n<LI>";
	    Display.Html.display_process_query_res query_res;
	  end;
	) queries'
    else
      begin
	let q_to_string qtype q =
	  Display.Buf.display_query false qtype q;
	  Display.LangBuf.get_string()
	in
	let add_proc p l =
	  if List.memq p l then l else p::l
	in
        (* Group axioms *)
	let grouped_axioms = ref [] in
	List.iter (function
	  | SingleProcessSingleQuery(p,axiom) ->
	      begin
		let axiom_string = q_to_string Display.TAxiom axiom in
		try
		  let g = List.find (fun g -> g.axiom_string = axiom_string) (!grouped_axioms) in
		  g.axiom_proc <- add_proc p g.axiom_proc
		with Not_found ->
		  let new_g =
		    { axiom = axiom;
		      axiom_string = axiom_string;
		      axiom_proc = [p] }
		  in
		  grouped_axioms := new_g :: (!grouped_axioms)
	      end
	  | _ -> assert false
		) sum.sum_axioms;

	(* Group lemmas *)
	let grouped_lemmas = ref [] in
	List.iter (function
	  | (SingleProcessSingleQuery(p,lemma), error, res) ->
	      begin
		let lemma_string = q_to_string Display.TLemma lemma in
		let add_p g p error res =
		  begin
		    match res with
		    | True -> g.true_res <- add_proc p g.true_res
		    | False -> g.false_res <- add_proc p g.false_res
		    | DontKnow -> g.dont_know_res <- add_proc p g.dont_know_res
		  end;
		  if error == Error then g.error <- add_proc p g.error
		in
		try
		  let g = List.find (fun g -> g.lemma_string = lemma_string) (!grouped_lemmas) in
		  add_p g p error res
		with Not_found ->
		  let new_g =
		    { lemma = lemma;
		      lemma_string = lemma_string;
		      true_res = []; false_res = []; dont_know_res = []; error = [] }
		  in
		  add_p new_g p error res;
		  grouped_lemmas := new_g :: (!grouped_lemmas)
	      end
	  | _ -> assert false
		) sum.sum_lemmas;

	Display.Text.display_summary queries' (!grouped_axioms) (!grouped_lemmas);
	Display.Text.newline();
	if !Param.html_output
	  then
	  begin
	    Display.Html.print_string "\n<LI>";
	    Display.Html.display_summary queries' (!grouped_axioms) (!grouped_lemmas);
	  end

      end) results;

  Display.Text.print_string Display.Text.hline;
  Display.Text.newline ();
  if !Param.html_output then
    begin
      Display.Html.print_string "\n</UL>";
      Display.Html.print_string Display.Html.hline
    end

(* [is_axiom_filtering_needed p] determines if we should remove axioms
   on biprocesses that are not specific to one side of the biprocess.
   The conditions for filtering these axioms are as follows:
     - If a BarrierSwap was occured
     - If the biprocess is a merge of two processes
     - If the biprocess is a simplification of another biprocess
*)
let rec is_axiom_filtering_needed proc =
  if proc.bi_pro
  then
    match proc.construction with
      | Initial_process
      | BarrierNoSwap _
      | Encode _ ->
          (* When the process is an encoding of query real or random, the user
             must have specified that the axiom is for this specific query so
             we assume the user consciously declared its axiom, hence we
             don't filter. For all the other encodings, we don't need to filter
             as they are not equivalence proofs. *)
          false
      | Merge _
      | Simplify _
      | BarrierSwap _ -> true
      | MoveNew proc' -> is_axiom_filtering_needed proc'
      | Initial_process1
      | Initial_process2 -> Parsing_helper.internal_error "[main.ml >> is_axiom_filtering_needed] The process cannot be a biprocess while being Initial_process 1 or 2"
  else false

let get_t_lemmas_from_solved lemma solved_lemmas =
  let solved_lemmas2 =
    List.map (function
        | _,CorrespQEnc(ql,_) -> List.map (fun (qorig,q) -> { ql_query = q; ql_original_query = Some(qorig); ql_real_or_random = None; ql_index_query_for_induction = None; ql_application_side = AllSide }) ql
        | _,CorrespQuery(ql,_) -> List.map (fun q -> { ql_query =q; ql_original_query = None; ql_real_or_random = None; ql_index_query_for_induction = None; ql_application_side = AllSide}) ql
        | _,_ -> Parsing_helper.internal_error "[main.ml >> get_t_lemmas_from_solved] Lemmas should only be Correspondence queries."
      ) solved_lemmas
  in
  Lemma { lemma with lemmas = (List.concat solved_lemmas2); induction = false }

let prove_lemmas pi_state next_f =
  current_axioms := [];
  current_lemmas := [];
  let axiom_list,lemma_list =
    List.partition (function
      | Lemma { is_axiom = true; _} -> true
      | Lemma { is_axiom = false; _} -> false
      | _-> Parsing_helper.internal_error "[main.ml >> prove_lemmas] All lemmas should have been translated at this point."
    ) pi_state.pi_lemma
  in

  let convert_lemma_to_query lemma =
    let solve_status =
      {
      s_max_subset = lemma.max_subset;
      s_ind_sat_app = lemma.sat_app;
      s_ind_verif_app = lemma.verif_app;
      s_induction = lemma.induction
    }
    in

    if List.for_all (fun t_lem -> t_lem.ql_original_query = None) lemma.lemmas
    then CorrespQuery(List.map (fun t_lem -> t_lem.ql_query) lemma.lemmas,solve_status)
    else
      CorrespQEnc(List.map (fun t_lem -> match t_lem.ql_original_query with
      | None -> t_lem.ql_query, t_lem.ql_query
      | Some q -> q, t_lem.ql_query
            ) lemma.lemmas,solve_status)
  in

  let process = Reduction_helper.get_process pi_state in

  let axiom_list =
    if is_axiom_filtering_needed process
    then
      let axiom_list' =
        List.fold_left (fun acc -> function
          | Lemma axioms ->
              if axioms.keep_axiom
              then (Lemma axioms)::acc
              else
                let new_axioms =
                  List.filter (fun axiom ->
                    let axiom' = Lemma.convert_lemma_for_monoprocess axiom in
                    axiom'.ql_application_side <> AllSide
                  ) axioms.lemmas
                in

                if new_axioms = []
                then acc
                else (Lemma { axioms with lemmas = new_axioms }) :: acc
          | _ -> Parsing_helper.internal_error "[main.ml >> prove_lemmas] All lemmas should have been translated at this point (2)."
        ) [] axiom_list
      in
      List.rev axiom_list'
    else axiom_list
  in

  List.iter (function
    | Lemma axiom ->
        let axiom_query = convert_lemma_to_query axiom in
        let axiom_process = SingleProcessSingleQuery(process,axiom_query) in
        let pi_state1 =
          { pi_state with
            pi_process_query = axiom_process }
        in
        current_axioms := axiom_process :: (!current_axioms);
        display_query_header Display.TAxiom pi_state1
    | _ -> Parsing_helper.internal_error "[main.ml >> prove_lemmas] All lemmas should have been translated at this point. (2)"
    ) axiom_list;

  let rec prove_all_lemmas proved_lemmas_or_axioms = function
    | [] -> next_f { pi_state with pi_lemma = proved_lemmas_or_axioms }
    | (Lemma lemma)::l_list ->

        let process_t_query = convert_lemma_to_query lemma in
        let pi_state1 =
          { pi_state with
            pi_lemma = proved_lemmas_or_axioms;
            pi_process_query = SingleProcessSingleQuery(process,process_t_query)
          }
        in
	let solve_result = solve pi_state1 in
        (* Analyse the result of solving the lemmas. *)
        if lemma.max_subset
        then
          begin
            let solved_lemmas_result = List.filter (function True,_ -> true | _,_ -> false) solve_result in
            let solved_lemmas = get_t_lemmas_from_solved lemma solved_lemmas_result in

            current_lemmas := (List.map (fun (r,q) -> SingleProcessSingleQuery(process,q),Ok, r) solve_result) @ !current_lemmas;
            prove_all_lemmas (solved_lemmas::proved_lemmas_or_axioms) l_list
          end
        else
          begin
            let solved_lemmas = get_t_lemmas_from_solved lemma solve_result in
            current_lemmas := (List.map (fun (r,q) -> SingleProcessSingleQuery(process, q),(if r=True then Ok else Error), r) solve_result) @ !current_lemmas;
            if List.for_all (function True,_ -> true | _,_ -> false) solve_result
            then prove_all_lemmas (solved_lemmas::proved_lemmas_or_axioms) l_list
            else raise (UnprovedLemma(process,process_t_query))
          end
    | _ -> Parsing_helper.internal_error "[main.ml >> prove_lemmas] All lemmas should have been translated at this point. (3)"
  in

  prove_all_lemmas axiom_list lemma_list

let open_list_opt open_list pi_state next_f =
  let p_desc = Reduction_helper.get_process pi_state in
  let already_displayed =
    match p_desc.display_num with
    | Some _ -> true
    | None -> false
  in
  if open_list && not already_displayed then
    begin
      (* I display the current process and
	 open a list for all things we do with it *)
      if !Param.html_output then
	begin
	  Display.Html.print_string "<LI>";
	  display_process pi_state;
	  Display.Text.print_string "-- ";
	  Display.Text.display_process_link false p_desc;
	  Display.Html.print_string "<UL> ";
	  try
	    next_f pi_state;
	    Display.Html.print_string "</UL> "
	  with x ->
	    Display.Html.print_string "</UL> ";
	    raise x
	end
      else
	begin
          Display.Text.print_string "--  ";
          display_process pi_state;
	  next_f pi_state
	end
    end
  else
    next_f pi_state

let solve_simplified_process pi_state1 =
  Display.auto_cleanup_display (fun () ->
    let pi_state2 = Simplify.prepare_process pi_state1 in
    (* [set_min_choice_phase] determines the minimum phase
       that contains [choice]
       This step and the next one are useful only for biprocesses. *)
    let pi_state2 = Reduction_helper.set_min_choice_phase pi_state2 in
    (* [set_min_choice_phase] must be called before
       [translate_to_bi_lemma], to know whether attacker/mess/table
       should be transformed into unary or binary predicates *)
    let pi_state2 = Lemma.translate_to_bi_lemma pi_state2 in

    (* We prove the lemmas *)
    try
      open_list_opt (pi_state2.pi_lemma <> []) pi_state2 (fun pi_state2 ->
	prove_lemmas pi_state2 (fun pi_state3 ->
	  store_and_raise_determined false (solve pi_state3)
	      )
	  )
    with UnprovedLemma _ -> ()
  )

let simplify_and_solve_process pi_state1 =
  Display.Text.print_line "Looking for simplified processes ...";
  if (!Param.html_output) then
    begin
      Display.Html.newline ();
      Display.Html.print_line "Trying simplified processes."
    end;
  let found_simplified_process = ref false in
  try
    Simplify.simplify_state pi_state1 (fun pi_state2 ->
      if (not (!found_simplified_process)) && (!Param.html_output)
      then Display.Html.print_string "<UL>\n";

      found_simplified_process := true;
      solve_simplified_process pi_state2
    );
    if not (!found_simplified_process) then
      begin
        Display.Text.print_line "No simplified process found.";
        if (!Param.html_output) then
          Display.Html.print_line "No simplified process found.";
      end
    else if (!Param.html_output) then
      Display.Html.print_string "</UL>\n"
  with Is_determined(r) ->
    if (!Param.html_output)
    then Display.Html.print_string "</UL>\n";
    raise (Is_determined(r))

let rec interface_general_merg list_simpl_pi_state =
  let nb_biprocess = List.length list_simpl_pi_state in
  let conjug =
    if nb_biprocess = 1
    then ""
    else "es"
  in
  Printf.printf "\n----------------------------\n";
  Printf.printf "ProVerif has found %d simplified process%s equivalent to the initial process.\n" nb_biprocess conjug;
  Printf.printf "Possible actions:\n";
  Printf.printf "1- View them all\n";
  Printf.printf "2- Try solving equivalence for all of them\n";
  Printf.printf "   Note that this option stops when ProVerif finds an observationally equivalent biprocess\n";
  Printf.printf "3- Try solving equivalence for one specific process (enter 3-x with x the number of the process)\n";
  Printf.printf "4- Exit ProVerif\n";

  let result = read_line () in
  match result with
    | "1" ->
      let acc = ref 1 in
      List.iter (fun pi_state ->
	Display.auto_cleanup_display (fun () ->
          Printf.printf "\n---------------------------\n";
          Printf.printf "-- Simplified process %d --\n" !acc;
          Printf.printf "---------------------------\n";

          let (p,_) = Param.get_process_query pi_state in
          Display.Text.display_process_occ "" p.proc;
          Display.Text.newline();
          acc := !acc + 1
	     )
      ) list_simpl_pi_state;
      interface_general_merg list_simpl_pi_state
    | "2" ->
       begin try
         List.iter solve_simplified_process list_simpl_pi_state;
       with Is_determined _ -> ()
       end
    | r when (String.length r > 2) && (String.sub r 0 2 = "3-") ->
       let size = List.length list_simpl_pi_state in
       let n =
         try
           int_of_string (String.sub r 2 ((String.length r) - 2))
         with _ -> 0 in

       if n > 0 && n <= size
       then
         begin
           try
             solve_simplified_process (List.nth list_simpl_pi_state (n-1))
           with Is_determined _ -> ()
         end;

       interface_general_merg list_simpl_pi_state

    | "4" -> exit 0
    | _ -> interface_general_merg list_simpl_pi_state

let interface_for_merging_process pi_state =
  Display.Text.print_line "Check the process...";
  let (p,_) = Param.get_process_query pi_state in
  Simplify.verify_process [] p.proc;
  Display.Text.print_line "Calculate the simplified processes...";
  let simpl_state_list = ref [] in
  Simplify.simplify_state pi_state
    (fun pi_state' -> simpl_state_list := pi_state'::!simpl_state_list);
  if !simpl_state_list <> [] then
    begin
      if !Param.html_output then
        Display.Html.print_string "<UL>\n";
      interface_general_merg !simpl_state_list;
      if !Param.html_output then
        Display.Html.print_string "</UL>\n"
    end
  else
    Display.Text.print_line "No simplified process found"

let compile_barriers pi_state next_f =
  if !Param.has_barrier then
    begin
      (* Expand "sync" barriers if they are present *)
      if (!Param.key_compromise != 0) then
          Parsing_helper.user_error "Key compromise is incompatible with sync";
      if (pi_state.pi_max_used_phase > 0) then
          Parsing_helper.user_error "Phase is incompatible with sync";

      Proswapper.compile_barriers (fun pi_state2 ->
	if not (Reduction_helper.get_process pi_state2).bi_pro then
	  (* Display the proces with barriers compiled only for monoprocesses.
	     For biprocesses, it is displayed as part of a list later. *)
	  begin
            Display.Text.print_line "-- After compilation of barriers";
            if !Param.html_output then
              Display.Html.print_string "<LI><span class=\"query\">After compilation of barriers</span><br>\n";
            display_process pi_state2
	  end;
        next_f pi_state2) pi_state
    end
  else
    next_f pi_state

let prove_equivalence_with_choice pi_state =
  if (!Param.key_compromise != 0) then
    Parsing_helper.user_error "Key compromise is incompatible with choice";

  (* Remove lemmas and axioms with bound names *)
  let pi_state0 = remove_lemmas_with_bound_names pi_state in

  let pi_state1 = set_need_vars_in_names pi_state0 in

  group_summary := { sum_queries = [pi_state.pi_process_query, DontKnow];
		     sum_lemmas = [];
		     sum_axioms = [] };
  begin
  try
    (* Open a new list for the various expansions of barriers
       with swapping *)
    open_list_opt (!Param.has_barrier) pi_state1 (fun pi_state1 ->
      compile_barriers pi_state1 (fun pi_state2 ->
	let pi_state3 = Reduction_helper.set_min_choice_phase pi_state2 in
	let pi_state4 = Lemma.translate_to_bi_lemma pi_state3 in

	open_list_opt (pi_state4.pi_lemma <> []) pi_state4 (fun pi_state4 ->
          let apply_simplification () =
            if !Param.typed_frontend && not (!Param.has_barrier) then
              begin
              (* The untyped front-end do not support modifying processes *)
              (* Do not propose simplification of the process in case barriers are used.
                 That would lead to too many processes. (We might change that in the future.) *)
		if !Param.simplify_process = 2 then
                  interface_for_merging_process pi_state2
		else if !Param.simplify_process = 1 then
                  simplify_and_solve_process pi_state2
              end
          in
          try
            prove_lemmas pi_state4 (fun pi_state5 ->
	      store_and_raise_determined true (solve pi_state5);
              apply_simplification ()
		)
          with UnprovedLemma _ ->
	    group_summary :=
	       { !group_summary with
                 sum_lemmas = (!current_lemmas) @ (!group_summary).sum_lemmas;
                 sum_axioms = (!current_axioms) @ (!group_summary).sum_axioms };
            apply_simplification ()
	      )
	  )
	)
  with Is_determined _ -> ()
  end;
  full_summary := (!group_summary) :: (!full_summary)

let prove_equivalence_two_processes pi_state =
  if !Param.has_choice then
    Parsing_helper.user_error "When showing equivalence of two processes, the processes cannot contain choice";
  if !Param.has_barrier then
    Parsing_helper.user_error "When showing equivalence of two processes, the processes cannot contain sync";
  if (!Param.key_compromise != 0) then
    Parsing_helper.user_error "Key compromise is incompatible with equivalence";

  group_summary := { sum_queries = [pi_state.pi_process_query, DontKnow];
		     sum_lemmas = [];
		     sum_axioms = [] };

  (* Remove lemmas and axioms with bound names *)
  let pi_state1 = remove_lemmas_with_bound_names pi_state in

  if (!Param.html_output) then
    Display.Html.print_string "<span class=\"query\">Observational equivalence between two processes</span><br>\n";

  Display.Text.print_string "-- Observational equivalence between two processes\n";
  begin
  try
    let biprocess_found = ref false in

    (* [simplify_state] sets [need_vars_in_names] to empty;
       not/nounif with bound names will be
       ignored when they cannot be translated *)
    Simplify.simplify_state pi_state1 (fun pi_state2 ->
      biprocess_found := true;
      let pi_state3 = Simplify.prepare_process pi_state2 in
      let pi_state3 = Reduction_helper.set_min_choice_phase pi_state3 in
      let pi_state3 = Lemma.translate_to_bi_lemma pi_state3 in

      try
	open_list_opt (pi_state3.pi_lemma <> []) pi_state3 (fun pi_state3 ->
          prove_lemmas pi_state3 (fun pi_state4 ->
	    store_and_raise_determined true (solve pi_state4)
              )
	    )
      with UnprovedLemma _ ->
	    group_summary :=
	       { !group_summary with
                 sum_lemmas = (!current_lemmas) @ (!group_summary).sum_lemmas;
                 sum_axioms = (!current_axioms) @ (!group_summary).sum_axioms }
	  );
    if not (!biprocess_found) then
      begin
        Display.Text.print_line "RESULT no biprocess can be computed";
        if !Param.html_output
        then Display.Html.print_string "<LI><span class=\"result\">RESULT no biprocess can be computed</span><br>"
      end
  with Is_determined _ -> ()
  end;
  full_summary := (!group_summary) :: (!full_summary)

let is_some = function
    Some _ -> true
  | None -> false

(* When induction has been declared for a query and when query is not a group
of queries, we allow the saturation to apply inductive lemmas. This can be
activated by declaring max_subset to false *)
let update_maxsubset pi_state =
  let (p,q) = Param.get_process_query pi_state in
  let q' = match q with
    | CorrespQEnc(qql, s_status) when List.length qql = 1 -> CorrespQEnc(qql,{s_status with s_max_subset = false})
    | CorrespQuery(ql,s_status) when List.length ql = 1 -> CorrespQuery(ql,{s_status with s_max_subset = false})
    | _ -> q
  in
  { pi_state with pi_process_query = SingleProcessSingleQuery(p,q')}

let prove_monoprocess_queries pi_state =
  let pi_state1 = set_need_vars_in_names pi_state in
  let p_desc = Reduction_helper.get_process pi_state1 in
  let done_queries = ref [] in
  try
    open_list_opt true pi_state1 (fun pi_state1 ->
      (* [compile_barriers] always has a single possible output
         (there is no swapping for correspondences).
	 It displays the compiled process as an item in the list. *)
      compile_barriers pi_state1 (fun pi_state2 ->
        prove_lemmas pi_state2 (fun pi_state3 ->
          split pi_state3 (fun pi_state4 ->
            let pi_state5 = update_maxsubset pi_state4 in
	    let solve_result = solve pi_state5 in
            (* Add elements in done_queries *)
            done_queries := (List.rev_map (fun (r,q) -> (SingleProcessSingleQuery(p_desc, q), r)) solve_result) @ !done_queries
              )
            )
	  )
	);
    let group_summary =
      { sum_queries = (!done_queries);
	sum_lemmas = (!current_lemmas);
	sum_axioms = (!current_axioms) }
    in
    full_summary := group_summary :: (!full_summary)
  with UnprovedLemma(process,q) ->
    let group_summary =
      { sum_queries = [pi_state.pi_process_query, DontKnow];
	sum_lemmas = (!current_lemmas);
	sum_axioms = (!current_axioms) }
    in
    full_summary := group_summary :: (!full_summary)

(* At this stage, [pi_state] should only contain lemmas that correspond
   to the query. In particular,
     - If the query is an equivalence query then pi_lemma should only
       contain lemmas and axioms without public vars
     - If the query is a correspondence query then pi_lemma should only
       contain lemmas and axioms with the same public vars and without choice.
     - If the query is a non-interference or weaksecret then pi_lemma
       should only contain lemmas without public vars and without choice.
     - If the query is query secret x public_vars ... [real_or_random] then
       pi_lemma should only contain lemmas and axioms that have been declared
       for this particular query.
     - If the query is query secret x public_vars ... [reachability] then
       pi_lemma should only contain lemmas and axioms with the same public
       vars and without choice.
   Moreover, pi_original_axioms should be empty.
*)
let prove_queries pi_state =
  match pi_state.pi_process_query with
  | Equivalence _ ->
      prove_equivalence_two_processes pi_state
  | SingleProcessSingleQuery(_, (ChoiceQuery | ChoiceQEnc _)) ->
      (* Invariant: ChoiceQuery and ChoiceQEnc appear only with
         SingleProcessSingleQuery *)
      prove_equivalence_with_choice pi_state
  | _ ->
      prove_monoprocess_queries pi_state

(*********************************************
               Analyser
**********************************************)

let first_file = ref true

let anal_file s0 =
  if not (!first_file) then
    Parsing_helper.user_error "You can analyze a single ProVerif file for each run of ProVerif.\nPlease rerun ProVerif with your second file.";
  first_file := false;
  let s =
    (* Preprocess .pcv files with m4 *)
    let s_up = String.uppercase_ascii s0 in
    if Terms.ends_with s_up ".PCV" then
      let s' = Filename.temp_file "pv" ".pv" in
      let res = Unix.system("m4 -DProVerif " ^ s0 ^ " > " ^ s') in
      match res with
        Unix.WEXITED 0 -> s'
      | _ -> Parsing_helper.user_error ("Preprocessing of " ^ s0 ^ " by m4 failed.")
    else
      s0
  in
  let in_front_end = match !in_kind with
    | Default -> (* Set the front-end depending on the extension of the file *)
       let s_up = String.uppercase_ascii s in
       if Terms.ends_with s_up ".PV" then PiType else
       if Terms.ends_with s_up ".PI" then Pi else
       if Terms.ends_with s_up ".HORNTYPE" then HornType else
       Horn (* Horn is the default when no extension is recognized for compatibility reasons *)
    | x -> x
  in

  if (!Param.html_output) then
    begin
      Display.LangHtml.openfile ((!Param.html_dir) ^ "/index.html") "ProVerif: main result page";
      Display.Html.print_string "<H1>ProVerif results</H1>\n"
    end;
  begin
    match in_front_end with
      Default ->
        Parsing_helper.internal_error "The Default case should have been removed previously"
    | Horn ->
        (* If the input consists of Horn clauses, no explanation can be given *)
        Param.verbose_explain_clauses := Param.Clauses;
        Param.explain_derivation := false;
        Param.abbreviate_clauses := false;
        horn_solve (Syntax.parse_file s)
    | HornType ->
        (* If the input consists of Horn clauses, no explanation can be given *)
        Param.verbose_explain_clauses := Param.Clauses;
        Param.explain_derivation := false;
        Param.abbreviate_clauses := false;
        Param.typed_frontend := true;
        (* Param.ignore_types := false; *)
        horn_solve (Tsyntax.parse_file s)
    | SpassIn ->
        Parsing_helper.user_error "spass input not yet implemented"
    | PiType ->
        Param.typed_frontend := true;
        let pi_state0 = Pitsyntax.parse_file s in
        let pi_state1 = move_new pi_state0 in
        let pi_state2 = Simplify.prepare_process pi_state1 in
        TermsEq.record_eqs_with_destr pi_state2;

        (* Check if destructors are deterministic *)
        Destructor.check_deterministic pi_state2.pi_destructors_check_deterministic;

        (* Check that the disequations are valid *)
        check_disequations pi_state2.pi_disequations;

        (* Display the process(es) *)
        if not (Param.is_equivalence_two_processes pi_state2) then
          (* Start from process 0 in display *)
          decr Param.process_number;
        display_process pi_state2;

        let pi_state3 = transl_query pi_state2 in
        let pi_state4 = transl_lemma pi_state3 in

        if (!Param.html_output) then
          Display.Html.print_string "<UL>\n";

        Encode_queries.encode_secret_public_vars prove_queries pi_state4;
                (* The transformations that the encoding can make on the process are strongly limited:
                   They must not change the type of the arguments of names.
                   That seems plausible, but remains to be tested in more detail.
                   If the arguments of names change, I need to reset them by setting
                   their type to Param.tmp_type. Simplify.prepare_process does that.
                   For deeper transformation, I may need to reset need_vars_in_names. *)

        if (!Param.html_output) then
          Display.Html.print_string "</UL>\n";

        display_summary (List.rev !full_summary)
    | Pi ->
        let pi_state0 = Pisyntax.parse_file s in
        let pi_state1 = move_new pi_state0 in
        TermsEq.record_eqs_with_destr pi_state1;

        (* Check if destructors are deterministic *)
        Destructor.check_deterministic pi_state1.pi_destructors_check_deterministic;

        (* Display the original process *)
        decr Param.process_number;
        display_process pi_state1;

        let pi_state2 = transl_query pi_state1 in
        if (!Param.html_output) then
          Display.Html.print_string "<UL>\n";
        prove_queries pi_state2;
        if (!Param.html_output) then
          Display.Html.print_string "</UL>\n"

  end;
  if (!Param.html_output) then
    Display.LangHtml.close();
  (* Remove the preprocessed temporary file when everything went well *)
  if s0 <> s then
    Unix.unlink s

let _ =
  try
    Arg.parse
    [ "-test", Arg.Unit (fun () ->
        if !Param.tulafale == 0 then
          Param.verbose_explain_clauses := Param.ExplainedClauses),
        "\t\tdisplay a bit more information for debugging";
      "-in", Arg.String(fun s -> in_kind := up_in s),
        "<format> \t\tchoose the input format (horn, horntype, spass, pi, pitype)";
      "-out", Arg.String(fun s -> out_kind := up_out s),
        "<format> \tchoose the output format (solve, spass)";
      "-o", Arg.String(fun s -> out_file := s),
        "<filename> \tchoose the output file name (for spass output)";
      "-lib", Arg.String (fun s -> Param.lib_name := s),
        "<filename> \tchoose the library file (for pitype front-end only)";
      "-TulaFale", Arg.Int(fun n ->
        Param.tulafale := n;
        if n = 1 then
          begin
            Param.reconstruct_trace := false;
            Param.verbose_explain_clauses := Param.Clauses;
            Param.explain_derivation := false;
            Param.abbreviate_derivation := false;
            Param.redundant_hyp_elim := true;
            Param.redundant_hyp_elim_begin_only := true
          end
            ),
        "<version> \tindicate the version of TulaFale when ProVerif is used inside TulaFale";
      "-graph", Arg.String (fun s ->
        Param.graph_output := true;
        Param.trace_display_graphicx := Param.GraphDisplay;
        Param.html_dir := s),
      "\t\t\tcreate the trace graph from the dot file in the directory specified";
      "-commandLineGraph", Arg.String (fun s ->
        Param.command_line_graph_set := true;
        Param.command_line_graph := s;),
      "\t\t\tDefine the command for the creation of the graph trace from the dot file";
      "-gc", Arg.Set gc,
        "\t\t\tdisplay gc statistics";
      "-color", Arg.Set Param.ansi_color,
      "\t\t\tuse ANSI color codes";
      "-html", Arg.String (fun s ->
        Param.html_output := true;
        Param.html_dir := s;
        if !Param.tulafale == 0 then
          Param.verbose_explain_clauses := Param.ExplainedClauses),
        "\t\t\tHTML display"
    ]
    anal_file ("Proverif " ^ Version.version ^ ". Cryptographic protocol verifier, by Bruno Blanchet, Vincent Cheval, and Marc Sylvestre");
    if !gc then Gc.print_stat stdout
  with
  | InputError(mess, ext) ->
      Parsing_helper.display_input_error mess ext
  | e -> Parsing_helper.internal_error (Printexc.to_string e)
