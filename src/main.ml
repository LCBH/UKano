(*************************************************************
 *                                                           *
 *  Cryptographic protocol verifier                          *
 *                                                           *
 *  Bruno Blanchet and Vincent Cheval                        *
 *                                                           *
 *  Copyright (C) INRIA, CNRS 2000-2015                      *
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
open Ukano

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

(* This is only for debugging purpose. TODO: remove this *)
let log s = Display.Text.print_string s;Display.Text.newline()

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
  failwith "WIP in UKANO, I deleteded useless parts for better readability. You need to revert THIS COMMIT (do a git blame)."
	   
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
    
  if (!Param.html_output) then
    begin
      Display.LangHtml.openfile ((!Param.html_dir) ^ "/process_"^(string_of_int !Param.process_number)^".html") ("ProVerif: "^text_bi^"process "^(string_of_int !Param.process_number));
      Display.Html.print_string ("<H1>"^text_bi_maj^"rocess "^(string_of_int !Param.process_number)^"</H1>\n");
      Display.Html.display_process_occ "" p;
      Display.Html.newline();
      Display.LangHtml.close();
      Display.Html.print_string ("<A HREF=\"process_"^(string_of_int !Param.process_number)^".html\" TARGET=\"process\">"^text_bi_maj^"rocess "^(string_of_int !Param.process_number)^"</A><br>\n");
      end
  else if (!Param.verbose_explain_clauses = Param.ExplainedClauses) || (!Param.explain_derivation) then
    begin
      Display.Text.print_string (text_bi_maj^"rocess "^(string_of_int !Param.process_number)^":\n");
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
  failwith "WIP in UKANO, I deleteded useless parts for better readability. You need to revert THIS COMMIT (do a git blame)."

let interface_for_merging_process p = 
  failwith "WIP in UKANO, I deleteded useless parts for better readability. You need to revert THIS COMMIT (do a git blame)."

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
	    (fun q -> q) p (!Syntax.query_facts);
	if (!Param.html_output) then
	  Display.LangHtml.close()
    | HornType ->
	(* If the input consists of Horn clauses, no explanation can be given *)
	Param.verbose_explain_clauses := Param.Clauses;
	Param.explain_derivation := false;
	Param.abbreviate_clauses := false;
	Param.typed_frontend := true;
	(* Param.ignore_types := false; *)
	let p = Tsyntax.parse_file s in
	out (fun p q -> Rules.main_analysis p q)
	    (fun q -> q) p (!Tsyntax.query_facts);
	if (!Param.html_output) then
	  Display.LangHtml.close()
    | SpassIn ->
	Parsing_helper.user_error "Error: spass input not yet implemented\n"
    | PiType ->
	Param.typed_frontend := true;
	(* Param.ignore_types := false; *)

	(* Lucca: val parse_file : string -> process * process option 
           Cette fonction parse le fichier en renvoie un/deux processe MAIS ATTENTION
           ELLE A MASSE d'EFFETS de BORD. Elle va créerune théorie équationnelle absolue. *)
	let p0, second_p0 = Pitsyntax.parse_file s in
	
	let p0 =
	  if !Param.move_new then
	    Pitransl.move_new p0
	  else p0 in
	  
	(* Effet de bord: orient les égalités --> réductions *)
	TermsEq.record_eqs_with_destr();
	
	(* Check if destructors are deterministic *)
	
	Destructor.check_deterministic !Pitsyntax.destructors_check_deterministic;
	
	(* Display the original processes *)
	
	if !Param.equivalence
	then 
	  failwith "WIP in UKANO, I deleteded useless parts for better readability. You need to revert THIS COMMIT (do a git blame)."
	else 
	begin
	  let p = Simplify.prepare_process p0 in
	  Pitsyntax.set_need_vars_in_names();

	  incr Param.process_number;
	  
	  if (!Param.html_output) then
	    begin
	      failwith "WIP in UKANO, I deleteded useless parts for better readability. You need to revert THIS COMMIT (do a git blame).";
	    end 
	  else if not !Param.trad_ukano && ((!Param.verbose_explain_clauses = Param.ExplainedClauses) || (!Param.explain_derivation)) then
	    begin
	      print_string "Process:\n";
	      Display.Text.display_process_occ "" p;
	      Display.Text.newline()
	    end;
	  
	  if !Param.has_choice 
	  then   
	  begin
	    failwith "WIP in UKANO, I deleteded useless parts for better readability. You need to revert THIS COMMIT (do a git blame).";
	  end
	  else if !Param.trad_ukano
	  then begin
	      log "Bonjour UKANO, à toi de jouer, transforme moi le process:";
              (* Display.Text.display_process "" p; *)
              (* Display.Text.newline(); *)
	      Ukano.transC1 p;
	      Printf.printf "############## 2-agents protocol ###############\n";
	      Ukano.displayProto p;
	    end else begin
	      
	      if !Param.html_output then
	      Display.Html.print_string "<UL>\n";
	
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
		failwith "WIP in UKANO, I deleteded useless parts for better readability. You need to revert THIS COMMIT (do a git blame).";
	      end
	    ) (Pitsyntax.get_noninterf_queries());

	    (* Weak secrets *)

	    List.iter (fun weaksecret ->
	      begin
		failwith "WIP in UKANO, I deleteded useless parts for better readability. You need to revert THIS COMMIT (do a git blame).";
	      end
	    ) (Pitsyntax.get_weaksecret_queries());

	    if (!Param.html_output) then
	      Display.Html.print_string "</UL>\n"
	  end;
	end;
	
	if (!Param.html_output) then
	  Display.LangHtml.close()

    | Pi ->
       failwith "WIP in UKANO, I deleteded useless parts for better readability. You need to revert THIS COMMIT (do a git blame)."
		
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
      "-gc", Arg.Set gc, 
        "\t\t\tdisplay gc statistics";
      "-color", Arg.Set Param.ansi_color,
        "\t\t\tuse ANSI color codes";
      "-html", Arg.String (fun s -> 
	Param.html_output := true;
	Param.html_dir := s;
	if !Param.tulafale == 0 then
          Param.verbose_explain_clauses := Param.ExplainedClauses), 
      "\t\t\tHTML display";
      "-ukano",
      Arg.Unit (fun () -> 
		Param.trad_ukano := true),
      "\t\t\tUse Proverif to check UnlinKability and ANOnymity as explained in [1].";
    (* todo ref/hyperref *)
    ]
    anal_file "Proverif. Cryptographic protocol verifier, by Bruno Blanchet and Vincent Cheval";
  if !gc then Gc.print_stat stdout
