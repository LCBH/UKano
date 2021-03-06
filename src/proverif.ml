(*************************************************************
 *                                                           *
 *  UKano: UnlinKability and ANOnymity verifier              *
 *                                                           *
 *  Lucca Hirschi                                            *
 *  http://projects.lsv.ens-cachan.fr/ukano/                 *
 *  Copyright (C) Lucca Hirschi 2015-2017                    *
 *                                                           *
 *************************************************************)

open Unix
open Printf
       
(* This is only for printing purpose. *)
let pp s = printf "%s\n" s
let pps s = if not(!Param.shortOutput) then printf "%s" s
let ppError s = printf "[ERROR] %s\n" s; exit(0)
let flush _ = flush_all ()

			
(***********************************************************)
(*               PARSING PROVERIF                          *)
(***********************************************************)
(* Possible outputs *)
                (* TODO: much easier parsing by going to the last paragapg of the output and extract line per line the results *)
let result = "RESULT"
let okEquivalence = "Observational equivalence is true."
let noEquivalence = "Observational equivalence cannot be proved."
let okQuery = "true"
let falseQuery = "false"
let noQuery = "proved"

let parseQueryAnswer s =
  let err _ = ppError "ProVerif was not found or ProVerif crashed (query). Please pursue manually (launch ProVerif on generated files)." in
  let regexpIs = Str.regexp_string "is" in
  let last = String.length s in
  let cannotBeforeProved _ =
    try
      let cannotPresent = Str.search_backward
			    (Str.regexp_string "cannot")
			    s last in (* last position of "cannot" *)
      let provedPresent = Str.search_backward
			    (Str.regexp_string noQuery)
			    s last in (* last position of "proved" *)
      if provedPresent > cannotPresent
      then false       (* 'proved' after cannot 'is' -> NO *)
      else err ()
    with Not_found -> err () (* no 'proved' or 'cannot' *)
  in
  try let isPresent = Str.search_backward regexpIs s last in (* last position of "is" *)
      try
	let truePresent = Str.search_backward
			    (Str.regexp_string okQuery)
			    s last in (* last position of "true" *)
	if truePresent > isPresent
	then true	   (* 'true' after last 'is' -> OK *)
	else cannotBeforeProved ()
      with _ ->
	try
	  let falsePresent = Str.search_backward
			       (Str.regexp_string falseQuery)
			       s last in (* last position of "false" *)
	  if falsePresent > isPresent
	  then false
	  else  cannotBeforeProved () (* no 'true' after the last 'is', maybe 'false ? *)
	with Not_found -> cannotBeforeProved ()  (* no 'true', maybe 'false' ? *)
  with Not_found -> cannotBeforeProved ()	(* no 'is' maybe cannot proved? *)
				       
let extractEvent s =
  let err _ = ppError "ProVerif was not found or ProVerif crashed (event). Please pursue manually (launch ProVerif on generated files)." in
  try 
    let firstTest = (Str.search_forward
		       (Str.regexp_string "test_")
		       s 0) - 1 in (* first position of "test_..." *)  
    let firstRpar =(Str.search_forward
		      (Str.regexp_string "==")
		      s 0) - 15 in (* first position of "=", ugly hack *)  
    (String.sub s firstTest firstRpar)
  with Not_found -> err () 
    
(***********************************************************)
(*               BASIC IO                                  *)
(***********************************************************)
       
(* Run a command and return its results as a list of strings,
   one per line. *)
let read_process_lines command =
  let lines = ref [] in
  let in_channel = Unix.open_process_in command in
  begin
    try
      while true do
	let nextLine = input_line in_channel in
	if !Param.logAll
	then begin
	    Printf.printf "[PV] %s\n" nextLine;
	    flush_all();
	  end;
	lines := nextLine :: !lines
      done;
    with End_of_file ->
      ignore (Unix.close_process_in in_channel)
  end;
  List.rev !lines
	   
let launchProverif pathProverif pathFile =
  let command = sprintf "%s -in pitype %s" pathProverif pathFile in
  if not(!Param.shortOutput) then pp ("$"^command);
  flush ();
  read_process_lines command

let rec lastL = function
  | [x] -> x
  | x :: tl -> lastL tl
  | [] -> failwith ("Critical error [451].")

let rec subList = function
  | (l1,l2, 0) -> (l1,l2)
  | (l1,l2,n) -> subList ((List.hd l2) :: l1, (List.tl l2), n-1)
			  
let verifyBoth pathProverif sFO sWA namesIdAno =
  let verbose = not(!Param.shortOutput) in
  let establishedFO = ref false in
  let establishedWA = ref false in
  let establishedWAPart = ref false in
  pps "\n\n";
  pps (Display.title "VERIFICATION OF CONDITIONS");
  if not(!Param.onlyWA)
  then begin
      if verbose then pp (Display.header "Verification of frame opacity");
      if verbose then pp (sprintf "We now launch Proverif (path: '%s') on '%s' to verify Frame Opacity ..." pathProverif sFO);
      let outputFO = launchProverif pathProverif sFO in
      if List.length outputFO = 0
      then ppError "ProVerif was not found or ProVerif crashed. Please pursue manually (launch ProVerif on generated files)."
      else begin
	  if verbose then pp "[...]";
	  let regexpResult = Str.regexp_string result in
	  let subResults = List.filter (fun l -> Str.string_match regexpResult l 0) outputFO in
	  if verbose then List.iter (fun l -> pp l) subResults;
	  let okFO = (List.length subResults > 0) && ((=) okEquivalence (lastL subResults)) in
	  let noFO = (List.length subResults > 0) && ((=) noEquivalence (lastL subResults)) in
	  if okFO
	  then begin
	      establishedFO := true;
	      pp (Display.result "Frame Opacity has been established.")
	    end
	  else (if noFO
		then pp (Display.result "Frame Opacity could not be established.")
		else ppError "Proverif's output could not be parsed. Please pursue manually (launch ProVerif on the generated files).")
	end;
    end;

  if not(!Param.onlyFO)
  then begin
      if verbose then pp (Display.header (Printf.sprintf "Verification of %d sanity checks and well-authentication" !Conditions.nbSanityChecks));
      if verbose then pp (sprintf "We now launch Proverif (path: '%s') on '%s' to verify Well-Authentication ..." pathProverif sWA);
      let outputWA = launchProverif pathProverif sWA in
      if List.length outputWA = 0
      then ppError "ProVerif was not found or ProVerif crashed. Please puruse manually (launch ProVerif on generated files)."
      else begin
	  if verbose then pp "[...]";
	  let regexpResult = Str.regexp_string result in
	  let subResults = List.filter (fun l -> Str.string_match regexpResult l 0) outputWA in
	  if verbose then List.iter (fun l -> pp l) subResults;
	  let sanityResults, waResults =
	    try
	      subList ([], subResults,!Conditions.nbSanityChecks)
	    with _ -> ppError "Proverif's output could not be parsed. Please pursue manually (launch ProVerif on the generated files)." in
	  let sanityOk = List.filter (fun l -> not(parseQueryAnswer l)) sanityResults in
	  let subOk = List.filter (fun l -> parseQueryAnswer l) waResults in
	  let subNo = List.filter (fun l -> not(parseQueryAnswer l)) waResults in
	  let okWA = (List.length waResults == List.length subOk) in
	  let noWA = (List.length subOk == 0) in
	  begin
	    (if (List.length sanityResults == List.length sanityOk)
	     then pp (Display.result "All sanity checks have been established.")
	     else pp (Printf.sprintf "[WARNING] At least one of the %d sanity checks does not hold (or cannor be proved). This might be because one of the role cannot be fully executed." !Conditions.nbSanityChecks));
	    if (List.length waResults == 0)
	    then ppError "Proverif's output could not be parsed. Please pursue manually (launch ProVerif on the generated files)."
	    else (if okWA
		  then begin
		      establishedWA := true;
		      pp (Display.result "Well Authentication has been established.");
		    end
		  else if noWA then begin
		      pp (Display.result (sprintf "Well Authentication could be established for none of the test. It may be the case that all tests are safe though."));
		    end else begin
		      establishedWAPart := true;
		      pp (Display.result (sprintf "Well Authentication has been established for %d over %d tests. Please verify that the following queries correspond to safe conditionals that are not right after the first responder input (#)."
						  (List.length subOk) (List.length waResults)));
		      List.iter (fun l -> pp ("Well-Athentication could not be established for : "^extractEvent(l))) subNo;
		    end);
	  end;
	end;
    end;
  
  if  not(!Param.onlyFO) && not(!Param.onlyWA)
  then begin
      pps "\n\n";
      pps (Display.title ("CONCLUSION"));
      if !establishedFO && (!establishedWA || !establishedWAPart)
      then begin
	  if not(!establishedWA)
	  then (if verbose then pp "Frame Opacity and Well-Authentication have been established providing the conditionals listed above are safe (#).")
	  else (if verbose then pp "Frame Opacity and Well-Authentication have been established.");
	  if List.length namesIdAno == 0
	  then pp (Display.result "[RESULT: OK] Therefore, the input protocol ensures Unlinkability providing the conditionals listed above are safe.")
	  else begin
	      Printf.printf "%s" (Display.result "[RESULT: OK] Therefore, the input protocol ensures Unlinkability and Anonymity w.r.t. identity names: (");
	      List.iter (fun s -> Display.Text.display_function_name s; printf ", ") namesIdAno;
	      pp "), providing the conditionals listed above are safe.";
	    end;
	end
      else pp (Display.result
		 ("[RESULT: NO] Frame Opacity or Well-Authentication could not be established.\n"^
		    "This does not necessarily imply that the input protocol violates unlinkability or anonymity.\n"^
                      "\t1. Indeed, it may be the case that ProVerif could not establish the conditions\n"^
			"\t (due to over-approximations) while they actually hold --- in that case, please refer to\n"^
			  "\t ProVerif's manual. Or try another idealisation option (list them with './ukano --help').\n"^
			    "\t2. Or the conditions do not hold. In that case, UKano cannot currently conclude on your protocol.\n"^
			      "\t If you think this is the case, please send your input protocol at lucca.hirschi@inria.fr so\n"^
				"\t that we can investigate further and improve UKano."));
    end;
  
  if !Param.cleanFiles
  then begin
      pp (Printf.sprintf "We are now removing generated files %s and %s." sFO sWA);
      (try
	  Sys.remove sFO;
	with Sys_error _ -> pp (Printf.sprintf "No file %s, we skip that..." sFO));
      try
	Sys.remove sWA;
      with Sys_error _ -> pp (Printf.sprintf "No file %s, we skip that..." sWA)
    end
