(*************************************************************
 *                                                           *
 *  UKano: UnlinKability and ANOnymity verifier              *
 *                                                           *
 *  Lucca Hirschi                                            *
 *  http://projects.lsv.ens-cachan.fr/ukano/                 *
 *  Copyright (C) Lucca Hirschi 2015-2018                    *
 *  Copyright (C) Bruno Blanchet, Vincent Cheval,            *
 *                INRIA, CNRS 2000-2015                      *
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

let gc = ref false
let out_file = ref ""
let out_n = ref 0
let pathProverif = ref "./proverif"
		       
(* This is only for debugging purpose. *)
let log s = Display.Text.print_string s;Display.Text.newline()

(* Helping message *)
let helpMess = 
  ("Only typed ProVerif files are accepted (the option '-in pitype' is enabled by default). See the folder './examples/' for examples\n"^
   "of files in the correct format. They can be used to bootsrap your own file. For more details, see the README file at the root of\n"^
   "the project or the manual of UKano at https://github.com/LCBH/UKano/wiki.\n")
let welcomeMess =
  "UKano v0.6: Cryptographic privacy verifier, by Lucca Hirschi. Based on Proverif v2.01, by Bruno Blanchet and Vincent Cheval."
    
(*********************************************
                 Interface
 **********************************************) 

let display_process p biproc =
  incr Param.process_number;
  let text_bi,text_bi_maj = 
    if biproc
    then "bi","Bip"
    else "","P" in
  
  Display.Text.print_string (text_bi_maj^"rocess "^(string_of_int !Param.process_number)^":\n");
  Display.Text.display_process_occ "" p;
  Display.Text.newline()


(*********************************************
               Analyser
 **********************************************)     
		      
let first_file = ref true

let anal_file s =
  if (s = "help" || s="") then begin Printf.printf "Error, you should enter a filename.\n%s\n" (Conditions.helpMess); exit(0); end;
  if not (!first_file) then
    Parsing_helper.user_error "Error: You can analyze a single ProVerif file for each run of UKano.\nPlease re-run UKano with your second file.\n";
  first_file := false;

  let p0, second_p0 = Pitsyntax.parse_file s in
  
  let p0 =
    if !Param.move_new then
      Pitransl.move_new p0
    else p0 in
  
  (* Compute reductions rules from equations *)
  TermsEq.record_eqs_with_destr();
  
  (* Check if destructors are deterministic *)
  Destructor.check_deterministic !Pitsyntax.destructors_check_deterministic;
  
  (* Simplification of the orginal process *)
  let p = Simplify.prepare_process p0 in
  Pitsyntax.set_need_vars_in_names();
  incr Param.process_number;

  (* Display the original processes *)
  if false then begin
      print_string "Process:\n";
      Display.Text.display_process_occ "" p;
      Display.Text.newline();
    end;
  
  
  (* Compute filename for the two produced ProVerif files *)
  let fileNameC1, fileNameC2 =
    try let splitDot = (Str.split (Str.regexp_string ".") s) in
	let prefix =
	  if List.length splitDot = 1
	  then List.hd splitDot
	  else (if s.[0] == '.' then "." else "")^
		 (String.concat "." (List.rev (List.tl (List.rev splitDot)))) in
	let prefixRel = if false && prefix.[0] = '/' then "."^prefix else prefix in
	(prefixRel^"_FOpa.pi", prefixRel^"_WAuth.pi")
    with _ -> ("OUTPUT_FOpa.pi","OUTPUT_WAuth.pi") in
  (* Compute and create the two ProVerif files checking the two conditions *)
  let listIdNames = Conditions.transBoth p s fileNameC1 fileNameC2 in
  (* Verify the conditions using ProVerif *)
  Proverif.verifyBoth (!pathProverif) fileNameC1 fileNameC2 listIdNames


(********************)
(* Handling options *)
(********************)
let _ =
  Arg.parse
    [
      "--proverif",  Arg.String (fun path -> pathProverif := path),
      "\t\tpath of the ProVerif executable to use (optional, default: './proverif')";
      "--ideal-no-check",  Arg.Unit (fun () -> Param.ideaAssumed := true),
      "\tassume the idealisation is conform (requires manual checks)";
      "--ideal-automatic",  Arg.Unit (fun () -> Param.ideaAutomatic  := true),
      "\tdo not take given idealisations into account, generate them automatically instead (using the default quasi-syntaxic heuristic)";
      "--ideal-semantic",  Arg.Unit (fun () -> Param.ideaGreedy  := true),
      "\tmodifies the idealisation heuristic: put fresh names for all non-tuple sub-terms";
      "--ideal-syntaxic",  Arg.Unit (fun () -> Param.ideaFullSyntax  := true),
      "\tmodifies the idealisation heuristic: go through all functions (including ones in equations) and replace identity names and let variables by holes. Conformity checks are modified accordingly.";
      "--only-fo",  Arg.Unit (fun () -> Param.onlyFO := true),
      "\t\tverifies the frame opacity condition only";
      "--only-wa",  Arg.Unit (fun () -> Param.onlyWA := true),
      "\t\tverifies the well-authentication condition only";
      "--fo-with-let",  Arg.Unit (fun () -> Param.letCatchFO := true),
      "\tverifies the frame opacity condition using old encodings based on nested 'let' constructs ";
      "--clean",  Arg.Unit (fun () -> Param.cleanFiles := true),
      "\t\tremove generated files after successful verification";
      "--less-verbose",  Arg.Unit (fun () -> Param.shortOutput := true),
      "\treduce the verbosity";
      "--log-proverif",  Arg.Unit (fun () -> Param.logAll := true),
      "\tlog in stdout all ProVerif outputs";
      "-gc", Arg.Set gc, 
      "\t\t\tdisplay gc statistics"
    ]
    anal_file welcomeMess;
  if !gc then Gc.print_stat stdout
