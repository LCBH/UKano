(*************************************************************
 *                                                           *
 *  UKano                                                    *
 *                                                           *
 *  Lucca Hirschi                                            *
 *                                                           *
 *  Copyright (C) Lucca Hirschi 2015-2017                    *
 *                                                           *
 *************************************************************)

open Unix
open Printf
       
(* This is only for debugging purpose. *)
let log s = printf "%s\n" s
let header = "##############################"

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
	lines := input_line in_channel :: !lines
      done;
    with End_of_file ->
      ignore (Unix.close_process_in in_channel)
  end;
  List.rev !lines
	   
let launchProverif pathProverif pathFile =
  let command = sprintf "%s -in pitype %s" pathProverif pathFile in
  log command;
  read_process_lines command
		     
let verifyBoth pathProverif sFO sWA =
  log (header^" VERIFICATION OF FRAME OPACITY "^header);
  log (sprintf "We now launch Proverif (path: '%s') on '%s' to verify Frame Opacity ..." pathProverif sFO);
  let outputFO = launchProverif pathProverif sFO in
  if List.length outputFO = 0
  then log "Error"
  else log (List.hd outputFO);

  log (header^" VERIFICATION OF WELL-AUTHENTICATION "^header);
  log (sprintf "We now launch Proverif (path: '%s') on '%s' to verify Well-Authentication ..." pathProverif sWA);
  let outputWA = launchProverif pathProverif sWA in
  if List.length outputWA = 0
  then log "Error"
  else log (List.hd outputWA)
  
