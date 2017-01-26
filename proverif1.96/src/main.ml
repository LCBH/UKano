(*************************************************************
 *                                                           *
 *  Cryptographic protocol verifier                          *
 *                                                           *
 *  Bruno Blanchet, Vincent Cheval, and Marc Sylvestre       *
 *                                                           *
 *  Copyright (C) INRIA, CNRS 2000-2016                      *
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
  | _ -> Parsing_helper.user_error "-out should be followed by spass or solve\n"

let up_in = function
    "horn" -> Horn
  | "horntype" -> HornType
  | "spass" -> SpassIn
  | "pi" -> Pi
  | "pitype" -> PiType
  | _ -> Parsing_helper.user_error "-in should be followed by horn, horntype, spass, pi, or pitype\n"

exception Is_equivalent

let interference_analysis rulelist queries =
  if (TermsEq.hasEquations()) && (not (!Param.weaksecret_mode)) then
    Parsing_helper.input_warning "using \"noninterf\" in the presence of equations may yield many\nfalse attacks. If you observe false attacks, try to code the desired\nproperty using \"choice\" instead." Parsing_helper.dummy_ext;
  let result = Rules.bad_derivable rulelist in
  if result = [] then
    begin
      Display.Text.print_string "RESULT ";
      Display.Text.display_eq_query queries;
      Display.Text.print_line " is true (bad not derivable).";
      if !Param.html_output then
	begin
	  Display.Html.print_string "<span class=\"result\">RESULT ";
	  Display.Html.display_eq_query queries;
	  Display.Html.print_line " is <span class=\"trueresult\">true (bad not derivable)</span>.</span>"
	end;
      raise Is_equivalent
	
    end
  else
    begin
      let l = List.map (fun rule ->
        Display.Text.print_string "goal reachable: ";
        Display.Text.display_rule rule;
	if !Param.html_output then
	  begin
	    Display.Html.print_string "goal reachable: ";
            Display.Html.display_rule rule
	  end;
	try 
          let new_tree = History.build_history None rule in
	  let r = 
	  (* For weak secrets, the reconstructed attack really falsifies the
	     equivalence; for other equivalences, it just reaches the program
	     point at which we find the first difference of execution, which
	     does not guarantee that the equivalence is false *)
	    if (!Param.reconstruct_trace) && (!Param.reconstruct_derivation) then
	      if (!Param.weaksecret != None) then
		Reduction.do_reduction None None new_tree
	      else if (!Param.non_interference) then
		begin
		  ignore (Reduction.do_reduction None None new_tree);
		  false
		end
              else if (!Param.has_choice) then
		begin
		  ignore (Reduction_bipro.do_reduction new_tree);
		  false
		end
	      else
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
      Display.Text.print_string "RESULT ";
      Display.Text.display_eq_query queries;
      if List.exists (fun x -> x) l then
	Display.Text.print_line " is false."
      else
	Display.Text.print_line " cannot be proved (bad derivable).";
      if !Param.html_output then
	begin
	  Display.Html.print_string "<span class=\"result\">RESULT ";
	  Display.Html.display_eq_query queries;
	  if List.exists (fun x -> x) l then
	    Display.Html.print_line " is <span class=\"falseresult\">false</span>.</span>"
	  else
	    Display.Html.print_line " <span class=\"unknownresult\">cannot be proved (bad derivable)</span>.</span>"
	end
    end


let out solve query_to_facts clauses queries =
  match !out_kind with
    Solve ->
      solve clauses queries
  | Spass ->
      if !out_file = "" then
	Parsing_helper.user_error "Error: you should provide the output filename by the option -o <filename>\n";
      incr out_n;
      let out_name = !out_file ^ 
	    (if !out_n = 1 then "" else string_of_int (!out_n)) in
      Spassout.main out_name clauses (query_to_facts queries)
 
let solve_only solve query_to_facts clauses queries =
  match !out_kind with
    Solve ->
      solve clauses queries
  | Spass ->
      Parsing_helper.user_error "Error: the clauses generated by ProVerif for process equivalences cannot be\ntranslated to the Spass input format.\n"

let ends_with s sub =
  let l_s = String.length s in
  let l_sub = String.length sub in
  (l_s >= l_sub) && (String.sub s (l_s - l_sub) l_sub = sub)
  
(*********************************************
                 Interface
**********************************************) 

let display_process p biproc =
  incr Param.process_number;
  let text_bi,text_bi_maj = 
    if biproc
    then "bi","Bip"
    else "","P" in
  
  let process_num = string_of_int !Param.process_number in
  let process_num_opt = if !Param.process_number = 0 then "" else " " ^ process_num in
  if (!Param.html_output) then
    begin
      Display.LangHtml.openfile ((!Param.html_dir) ^ "/process_"^process_num^".html") ("ProVerif: "^text_bi^"process "^process_num_opt);
      Display.Html.print_string ("<H1>"^text_bi_maj^"rocess"^process_num_opt^"</H1>\n");
      Display.Html.display_process_occ "" p;
      Display.Html.newline();
      Display.LangHtml.close();
      Display.Html.print_string ("<A HREF=\"process_"^process_num^".html\" TARGET=\"process\">"^text_bi_maj^"rocess"^process_num_opt^"</A><br>\n");
      end
  else if (!Param.verbose_explain_clauses = Param.ExplainedClauses) || (!Param.explain_derivation) then
    begin
      Display.Text.print_string (text_bi_maj^"rocess"^process_num_opt^":\n");
      Display.Text.display_process_occ "" p;
      Display.Text.newline()
    end
  
let solve_simplified_process proc = 
  let proc = Simplify.prepare_process proc in
  Pitsyntax.reset_need_vars_in_names();

  if !Param.html_output then
    Display.Html.print_string "<span class=\"query\">Observational equivalence</span><br>\n";
      
  Display.Text.print_string "Observational equivalence";
  Display.Text.newline();
	          
  display_process proc true;
    
  Param.weaksecret_mode := true;
  Selfun.inst_constraints := true;
    
  let rules = Pitranslweak.transl proc in
    
  Printf.printf "Solving the clauses...\n";
  solve_only interference_analysis (fun q -> q) rules Pitypes.ChoiceQuery;
    
  Param.weaksecret_mode := false;
  Selfun.inst_constraints := false;
  incr Param.current_query_number
  
let simplify_and_solve_process p = 
  Printf.printf "Looking for simplified processes ...\n";
  let found_simplified_process = ref false in
  Simplify.simplify_process p (fun proc -> 
    found_simplified_process := true;
    solve_simplified_process proc);
  if not (!found_simplified_process) then
    Printf.printf "No simplified process found\n"
  
let rec interface_general_merg list_simpl_p =
  let nb_biprocess = List.length list_simpl_p in
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
  Printf.printf "3- Try solving equivalence for one specific process (enter 3-x wih x the number of the process)\n";
  Printf.printf "4- Exit ProVerif\n";
      
  let result = read_line () in
  match result with
    | "1" -> 
      let acc = ref 1 in
      List.iter (fun p ->
        Printf.printf "\n---------------------------\n";
        Printf.printf "-- Simplified process %d --\n" !acc;
        Printf.printf "---------------------------\n";
        
	Display.Text.display_process_occ "" p;
	Display.Text.newline();
	acc := !acc + 1
      ) list_simpl_p;
      interface_general_merg list_simpl_p
    (*| r when (String.length result > 2) && (String.sub r 0 2 = "2-") -> 
      let size = List.length list_simpl_p in
      let n = 
        try
          int_of_string (String.sub r 2 ((String.length r) - 2))
        with _ -> 0 in
      
      if n > 0 && n <= size
      then 
        begin
	  Printf.printf "\n---------------------------\n";
	  Printf.printf "-- Simplified process %d --\n" n;
	  Printf.printf "---------------------------\n";
	  
	  Display.Text.display_process_occ "" (List.nth list_simpl_p (n-1));
	  Display.Text.newline();
	  
          interface_general_merg list_simpl_p
        end
      else interface_general_merg list_simpl_p*)
    |"2" -> 
       begin try
         List.iter solve_simplified_process list_simpl_p;
       with Is_equivalent -> ()
       end
    | r when (String.length result > 2) && (String.sub r 0 2 = "3-") -> 
       let size = List.length list_simpl_p in
       let n = 
         try
           int_of_string (String.sub r 2 ((String.length r) - 2))
         with _ -> 0 in
      
       if n > 0 && n <= size
       then
         begin 
           try
             solve_simplified_process (List.nth list_simpl_p (n-1))
           with Is_equivalent -> ()
         end;
         
       interface_general_merg list_simpl_p  
       
    |"4" -> exit 0
    |_ -> interface_general_merg list_simpl_p

let interface_for_merging_process p = 
  Printf.printf "Check the process...\n";
  Simplify.verify_process [] p;
  Printf.printf "Calculate the simplified processes...\n";
  
  let simpl_process_list = ref [] in
  
  Simplify.simplify_process p (fun p' -> simpl_process_list := p'::!simpl_process_list);
  
  if !simpl_process_list <> []
  then interface_general_merg !simpl_process_list
  else Printf.printf "No simplified process found\n"  

(*********************************************
               Analyser
**********************************************)     
    
let first_file = ref true

let anal_file s =
  if not (!first_file) then
    Parsing_helper.user_error "Error: You can analyze a single ProVerif file for each run of ProVerif.\nPlease rerun ProVerif with your second file.\n";
  first_file := false;
  try
    let in_front_end =
      match !in_kind with
	Default -> (* Set the front-end depending on the extension of the file *)
	  let s_up = String.uppercase s in
	  if ends_with s_up ".PV" then PiType else
	  if ends_with s_up ".PI" then Pi else
          if ends_with s_up ".HORNTYPE" then HornType else
          Horn (* Horn is the default when no extension is recognized for compatibility reasons *)
      |	x -> x
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
	let p = Syntax.parse_file s in
	out (fun p q -> Rules.main_analysis p q)
	    (fun q -> q) p (!Syntax.query_facts)
    | HornType ->
	(* If the input consists of Horn clauses, no explanation can be given *)
	Param.verbose_explain_clauses := Param.Clauses;
	Param.explain_derivation := false;
	Param.abbreviate_clauses := false;
	Param.typed_frontend := true;
	(* Param.ignore_types := false; *)
	let p = Tsyntax.parse_file s in
	out (fun p q -> Rules.main_analysis p q)
	    (fun q -> q) p (!Tsyntax.query_facts)
    | SpassIn ->
	Parsing_helper.user_error "Error: spass input not yet implemented\n"
    | PiType ->
	Param.typed_frontend := true;
	(* Param.ignore_types := false; *)

	let p0, second_p0 = Pitsyntax.parse_file s in
	
	let p0 =
	  if !Param.move_new then
	    Pitransl.move_new p0
	  else p0 in

	let p0 = Simplify.reset_occurrence p0 in
	  
	TermsEq.record_eqs_with_destr();
	
	(* Check if destructors are deterministic *)
	
	Destructor.check_deterministic !Pitsyntax.destructors_check_deterministic;
	
	(* Display the original processes *)
	
	if !Param.equivalence
	then 
	begin
	  if !Param.has_choice
	  then Parsing_helper.user_error "When showing equivalence of two processes, the processes cannot contain choice\n";

	  if !Param.has_barrier
	  then Parsing_helper.user_error "When showing equivalence of two processes, the processes cannot contain sync\n";
	  
	  if (!Pitsyntax.query_list != [])
	    || (Pitsyntax.get_noninterf_queries() != [])
	    || (Pitsyntax.get_weaksecret_queries() != [])
	  then Parsing_helper.user_error "Queries are incompatible with equivalence\n";
	    
	  if (!Param.key_compromise != 0) then
	    Parsing_helper.user_error "Key compromise is incompatible with equivalence\n";
	  
	  let second_p0 = match second_p0 with
	    | None -> internal_error "[main.ml] Second process should exist"
	    | Some p2 -> 
	        if !Param.move_new then
	          Pitransl.move_new p2
	        else p2 in 

	  let second_p0 = Simplify.reset_occurrence second_p0 in
	
	  if (!Param.html_output) then
	    Display.Html.print_string "<span class=\"query\">Observational equivalence between two processes</span><br>\n"
	  else if (!Param.verbose_explain_clauses = Param.ExplainedClauses) || (!Param.explain_derivation) then
	    Display.Text.print_string "Observational equivalence between two processes\n";
	   
	  display_process (Simplify.prepare_process p0) false;
	  display_process (Simplify.prepare_process second_p0) false;

	  begin try
	    let biprocess_found = ref false in
	    Simplify.obtain_biprocess_from_processes p0 second_p0 (fun bi_proc ->
	      biprocess_found := true;
	      let bi_proc = Simplify.prepare_process bi_proc in
	      Pitsyntax.reset_need_vars_in_names();
	      if !Param.html_output then
	        Display.Html.print_string "<span class=\"query\">Observational equivalence</span><br>\n";
	        
	      display_process bi_proc true;
	      
	      Param.weaksecret_mode := true;
	      Selfun.inst_constraints := true;
	   
	      let rules = Pitranslweak.transl bi_proc in
	    
	      solve_only interference_analysis (fun q -> q) rules Pitypes.ChoiceQuery;
	      Param.weaksecret_mode := false;
	      Selfun.inst_constraints := false;
	      incr Param.current_query_number
	    );
	    if not (!biprocess_found) then
	      begin
		Display.Text.print_string "RESULT no biprocess can be computed\n";
		if !Param.html_output
		then Display.Html.print_string "<span class=\"result\">RESULT no biprocess can be computed</span><br>"
	      end  
	  with Is_equivalent -> ()
	  end  
	end    
	else 
	begin
	  let p = Simplify.prepare_process p0 in
	  Pitsyntax.set_need_vars_in_names();

	  decr Param.process_number;
	  display_process p false;

	  if !Param.has_choice then 
	  begin
	    if (!Pitsyntax.query_list != [])
	      || (Pitsyntax.get_noninterf_queries() != [])
	      || (Pitsyntax.get_weaksecret_queries() != [])
	      then Parsing_helper.user_error "Queries are incompatible with choice\n";
	    
	    if (!Param.key_compromise != 0) then
	      Parsing_helper.user_error "Key compromise is incompatible with choice\n";

	    if !Param.has_barrier then
	      begin
		if (!Param.max_used_phase > 0) then
		  Parsing_helper.user_error "Phase is incompatible with sync\n";

		try 
		  Proswapper.compile_barriers (fun p -> 
		    Display.Text.print_string "-- Observational equivalence after compilation of barriers";
		    Display.Text.newline();
		
		    if !Param.html_output then
		      Display.Html.print_string "<span class=\"query\">Observational equivalence after compilation of barriers</span><br>\n";
	      
		    display_process p true;
		    Param.weaksecret_mode := true;
		    Selfun.inst_constraints := true;
		    let rules = Pitranslweak.transl p in
		    solve_only interference_analysis (fun q -> q) rules Pitypes.ChoiceQuery;
		    Param.weaksecret_mode := false;
		    Selfun.inst_constraints := false;
		    incr Param.current_query_number;
	      
	          (*Do not propose simplification of the process in case barriers are used.
		    That would lead to too many processes. (We might change that in the future.)
		  if !Param.simplify_process = 2
	          then interface_for_merging_process p0
	          else if !Param.simplify_process = 1
	          then simplify_and_solve_process p0*)
		    ) p
		with Is_equivalent -> ()
	      end
	    else 
	      begin
		Display.Text.print_string "-- Observational equivalence";
		Display.Text.newline();
	    
		if !Param.html_output then
		  Display.Html.print_string "<span class=\"query\">Observational equivalence</span><br>\n";
	      
		Param.weaksecret_mode := true;
		Selfun.inst_constraints := true;
	   
		let rules = Pitranslweak.transl p in
	    
		try
		  solve_only interference_analysis (fun q -> q) rules Pitypes.ChoiceQuery;
		  Param.weaksecret_mode := false;
		  Selfun.inst_constraints := false;
		  incr Param.current_query_number;
		  
		  if !Param.simplify_process = 2
		  then interface_for_merging_process p0
		  else if !Param.simplify_process = 1
		  then simplify_and_solve_process p0
			
		with Is_equivalent -> ()
	      end
	  end
	  else 
	  begin
	    if !Param.html_output then
	      Display.Html.print_string "<UL>\n";

	    (* Expand "sync" barriers if they are present *)
	    let p =
	      if !Param.has_barrier then
		begin
		  if (!Param.key_compromise != 0) then
		    Parsing_helper.user_error "Key compromise is incompatible with sync\n";
		  if (!Param.max_used_phase > 0) then
		    Parsing_helper.user_error "Phase is incompatible with sync\n";
		  let p' = Proswapper.compile_barriers_corresp p in

		  if !Param.html_output then
		    Display.Html.print_string "<span class=\"query\">After compilation of barriers</span><br>\n"
		  else
		    begin
		      Display.Text.print_string "After compilation of barriers";
		      Display.Text.newline()
		    end;
		  display_process p' false;
		  p'
		end
	      else
		p
	    in
	    
            (* Secrecy and authenticity *)

	    List.iter (fun q ->
	      begin
	        let queries = Pitsyntax.transl_query q in
	        let rules = Pitransl.transl p in
	        let queries = List.map Reduction_helper.check_delayed_names queries in
                (* Note: pisyntax translates bindings let x = ... into PutBegin(false,[])
		   since these bindings are useless once they have been interpreted 
		   Such dummy PutBegin(false,[]) should not be displayed. *)
	        let queries' = List.filter (function Pitypes.PutBegin(_,[]) -> false | _ -> true) queries in
	        print_string ("-- Query ");
	        Display.Text.display_list Display.Text.display_corresp_putbegin_query "; " queries';
	        print_newline();
	        if !Param.html_output then
	          begin
	            Display.Html.print_string "<LI><span class=\"query\">Query ";
	            Display.Html.display_list Display.Html.display_corresp_putbegin_query "; " queries';
	            Display.Html.print_string "</span><br>\n"
	          end;
	        out Piauth.solve_auth Pitsyntax.query_to_facts rules queries;
	        incr Param.current_query_number
	      end
	    ) (!Pitsyntax.query_list);

            (* Key compromise is now compatible with authenticity
               or non-interference: Param.key_compromise := 0; *)

            (* Non-interference *)

	    List.iter (fun noninterf_queries ->
	      begin
	        let noninterf_queries_names = List.map fst noninterf_queries in
	        Param.secret_vars := noninterf_queries_names;
	        Param.secret_vars_with_sets := noninterf_queries;
	        Param.non_interference := true;
	        let _ = Pitsyntax.transl_query ([],[]) in (* Ignore all events *)
	        let rules = Pitransl.transl p in
	        print_string "-- ";
	        Display.Text.display_eq_query (Pitypes.NonInterfQuery noninterf_queries);
	        Display.Text.newline();
	        if !Param.html_output then
	          begin
		    Display.Html.print_string "<LI><span class=\"query\">";
		    Display.Html.display_eq_query (Pitypes.NonInterfQuery noninterf_queries);
		    Display.Html.print_string "</span><br>\n"
	          end;
	        
	        begin try
	          solve_only interference_analysis (fun q -> q) rules (Pitypes.NonInterfQuery noninterf_queries);
	        with Is_equivalent -> ()
	        end;
	    
	        Param.non_interference := false;
	        incr Param.current_query_number
	      end
	    ) (Pitsyntax.get_noninterf_queries());

	    (* Weak secrets *)

	    List.iter (fun weaksecret ->
	      begin
	        Param.weaksecret := Some weaksecret;
	        Param.weaksecret_mode := true;
	        Selfun.inst_constraints := true;
	        print_string ("-- Weak secret " ^ weaksecret.f_name ^ "\n");
	        if !Param.html_output then
	          Display.Html.print_string ("<LI><span class=\"query\">Weak secret " ^ weaksecret.f_name ^ "</span><br>\n");
	        let _ = Pitsyntax.transl_query ([],[]) in (* Ignore all events *)
	        let rules = Pitransl.transl p in
	        begin try
	          solve_only interference_analysis (fun q -> q) rules (Pitypes.WeakSecret weaksecret);
	        with Is_equivalent -> ()
	        end;
	        Param.weaksecret := None;
	        Param.weaksecret_mode := false;
	        Selfun.inst_constraints := false;
	        incr Param.current_query_number
	      end
	    ) (Pitsyntax.get_weaksecret_queries());

	    if (!Param.html_output) then
	      Display.Html.print_string "</UL>\n"
	  end;
	end

    | Pi ->
	let p0 = Pisyntax.parse_file s in
	
	let p = 
	  if !Param.move_new then
	    Pitransl.move_new p0
	  else
	    p0
	in
	TermsEq.record_eqs_with_destr();
	
	(* Check if destructors are deterministic *)
	
	Destructor.check_deterministic !Pisyntax.destructors_check_deterministic;
	
	(* Display the original process *)
	
	decr Param.process_number;
	display_process p false;

	if !Param.has_choice then
	  begin
	    if (!Pisyntax.query_list != [])
	    || (Pisyntax.get_noninterf_queries() != [])
	    || (Pisyntax.get_weaksecret_queries() != [])
	    then Parsing_helper.user_error "Queries are incompatible with choice\n";
	    if (!Param.key_compromise != 0) then
	      Parsing_helper.user_error "Key compromise is incompatible with choice\n";

	    if !Param.has_barrier then
	      begin
		if (!Param.max_used_phase > 0) then
		  Parsing_helper.user_error "Phase is incompatible with sync\n";
	    
		try 
		  Proswapper.compile_barriers (fun p -> 
		    Display.Text.print_string "-- Observational equivalence after compilation of barriers";
		    Display.Text.newline();
		
		    if !Param.html_output then
		      Display.Html.print_string "<span class=\"query\">Observational equivalence after compilation of barriers</span><br>\n";
	      
		    display_process p true;
		    Param.weaksecret_mode := true;
		    Selfun.inst_constraints := true;
		    let rules = Pitranslweak.transl p in
		    solve_only interference_analysis (fun q -> q) rules Pitypes.ChoiceQuery;
		    Param.weaksecret_mode := false;
		    Selfun.inst_constraints := false;
		    incr Param.current_query_number;
		    ) p
		with Is_equivalent -> ()
	      end
	    else
	      begin
		print_string "-- Observational equivalence"; print_newline();
		if !Param.html_output then
		  Display.Html.print_string "<span class=\"query\">Observational equivalence</span><br>\n";
		Param.weaksecret_mode := true;
		Selfun.inst_constraints := true;
		let rules = Pitranslweak.transl p in
		begin
		  try
		    solve_only interference_analysis (fun q -> q) rules Pitypes.ChoiceQuery;
		  with Is_equivalent -> ()
		end;
		Param.weaksecret_mode := false;
		Selfun.inst_constraints := false
	      end
	  end
	else
	  begin
	    if !Param.html_output then
	      Display.Html.print_string "<UL>\n";

	    (* Expand "sync" barriers if they are present *)
	    let p =
	      if !Param.has_barrier then
		begin
		  if (!Param.key_compromise != 0) then
		    Parsing_helper.user_error "Key compromise is incompatible with sync\n";
		  if (!Param.max_used_phase > 0) then
		    Parsing_helper.user_error "Phase is incompatible with sync\n";
		  let p' = Proswapper.compile_barriers_corresp p in
		
		  if !Param.html_output then
		    Display.Html.print_string "<span class=\"query\">After compilation of barriers</span><br>\n"
		  else
		    begin
		      Display.Text.print_string "After compilation of barriers";
		      Display.Text.newline()
		    end;
		  display_process p' false;
		  p'
		end
	      else
		p
	    in
	    
        (* Secrecy and authenticity *)

	List.iter (fun q ->
	  begin
	    let queries = Pisyntax.transl_query q in
	    let rules = Pitransl.transl p in
	    let queries = List.map Reduction_helper.check_delayed_names queries in
	    if !Param.tulafale != 1 then 
	      begin
                (* Note: pisyntax translates bindings let x = ... into PutBegin(false,[])
		   since these bindings are useless once they have been interpreted 
		   Such dummy PutBegin(false,[]) should not be displayed. *)
		let queries = List.filter (function Pitypes.PutBegin(_,[]) -> false | _ -> true) queries in
		print_string ("-- Query ");
		Display.Text.display_list Display.Text.display_corresp_putbegin_query "; " queries;
		print_newline();
		if !Param.html_output then
		  begin
		    Display.Html.print_string "<LI><span class=\"query\">Query ";
		    Display.Html.display_list Display.Html.display_corresp_putbegin_query "; " queries;
		    Display.Html.print_string "</span><br>\n"
		  end
	      end
	    else
	      print_string "-- Secrecy & events.\n";
	    out Piauth.solve_auth Pisyntax.query_to_facts rules queries;
	    incr Param.current_query_number
	  end) (!Pisyntax.query_list);

        (* Key compromise is now compatible with authenticity
           or non-interference: Param.key_compromise := 0; *)

        (* Non-interference *)

	List.iter (fun noninterf_queries ->
	  begin
	    let noninterf_queries_names = List.map fst noninterf_queries in
	    Param.secret_vars := noninterf_queries_names;
	    Param.secret_vars_with_sets := noninterf_queries;
	    Param.non_interference := true;
	    let _ = Pisyntax.transl_query [] in (* Ignore all events *)
	    let rules = Pitransl.transl p in
	    print_string "-- ";
	    Display.Text.display_eq_query (Pitypes.NonInterfQuery noninterf_queries);
	    Display.Text.newline();
	    if !Param.html_output then
	      begin
		Display.Html.print_string "<LI><span class=\"query\">";
		Display.Html.display_eq_query (Pitypes.NonInterfQuery noninterf_queries);
		Display.Html.print_string "</span><br>\n"
	      end;
	    begin try
	      solve_only interference_analysis (fun q -> q) rules (Pitypes.NonInterfQuery noninterf_queries);
	    with Is_equivalent -> ()
	    end;
	    Param.non_interference := false;
	    incr Param.current_query_number
	  end) (Pisyntax.get_noninterf_queries());

	(* Weak secrets *)

	List.iter (fun weaksecret ->
	  begin
	    Param.weaksecret := Some weaksecret;
	    Param.weaksecret_mode := true;
	    Selfun.inst_constraints := true;
	    print_string ("-- Weak secret " ^ weaksecret.f_name ^ "\n");
	    if !Param.html_output then
	      Display.Html.print_string ("<LI><span class=\"query\">Weak secret " ^ weaksecret.f_name ^ "</span><br>\n");
	    let _ = Pisyntax.transl_query [] in (* Ignore all events *)
	    let rules = Pitransl.transl p in
	    begin try
	      solve_only interference_analysis (fun q -> q) rules (Pitypes.WeakSecret weaksecret);
	    with Is_equivalent -> ()
	    end;
	    
	    Param.weaksecret := None;
	    Param.weaksecret_mode := false;
	    Selfun.inst_constraints := false;
	    incr Param.current_query_number
	  end) (Pisyntax.get_weaksecret_queries());

	    if (!Param.html_output) then
	      Display.Html.print_string "</UL>\n"
	  end

    end;
    if (!Param.html_output) then
      Display.LangHtml.close()

  with e ->
    Parsing_helper.internal_error (Printexc.to_string e)


let _ =
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
    anal_file "Proverif. Cryptographic protocol verifier, by Bruno Blanchet, Vincent Cheval, and Marc Sylvestre";
  if !gc then Gc.print_stat stdout
