(*************************************************************
 *                                                           *
 *  UKANO: UnlinKability and ANOnymity verifier              *
 *                                                           *
 *  Lucca Hirschi                                            *
 *                                                           *
 *  Copyright (C) 2015                                       *
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
(* This module provides functions from the UnlinKability and ANOnymity
   verifier built on top of ProVerif as described in [1]. (todo-lucca:ref) *)

open Types

(* For debugging purpose *)
let log s = Printf.printf "> %s\n" s

(* Raised when the inputted process is not a 2-agents protocol as defined
   in [1], the associated string is the reason/explanation. *)
exception NotInClass of string

(** Type of a 2-agents protocol as defined in [1] *)
type proto = {
    idNames : funsymb list;	(* identity names *)
    sessNames : funsymb list;	(* session names *)
    ini : process;		(* (open) process of the initiator *)
    res : process;		(* (open) process of the responder *)
  }
	       
(** Extract the protocol structure from a process and rise NotInClass if
    not of the expected form. *)
let extractProto process = 
  (* Accumulate all names from all starting creation of names and return the
     list of name plus the continuation of the protocol *)
  let rec getNames acc = function
    | Restr (idName,_,p',_) -> getNames (idName::acc) p'
    | _ as p -> acc, p in
  (* Check that the two given processes are dual roles of the correct form and
     return (initiator, responder). *)
  let rec checkRoles p1 p2 =
    (p1,p2) in			(* todo *)
  
  match process with
  | Repl (idProc,_) ->
     let idNames, idProc' = getNames [] idProc in
     (match idProc' with
      | Repl (sessProc,_) ->
	 let sessNames, sessProc' = getNames [] sessProc in
	 (match sessProc' with
	  | Par (p1,p2) ->
	     let ini,res = checkRoles p1 p2 in
	     {
	       idNames = idNames;
	       sessNames = sessNames;
	       ini = ini;
	       res = res;
	     }
	  | _ -> raise (NotInClass "After session names, we expect a parallel composition of two roles."))
      | _ -> raise (NotInClass "After the first replication and identity names, we expect a replication (for sessions)."))
  | _ -> raise (NotInClass "We expect a replication at the begging of the process.")
	       
		     
let transC1 p = 
  (* WIP: ici j'essaye juste d'ajouter un event *)
  log "Je vais essayer d'ajouter un event dans le proc et dans la théorie.";
  let proto = extractProto p in
  let fstSessName = List.hd proto.sessNames in (* funSymb *)
  let typeEvent = [{tname = "bitstring"}] in
  let funSymbEvent = {
      f_name = "Out3";
      f_type = (typeEvent, Param.event_type);
      f_cat = Eq[];
      f_initial_cat = Eq[];
      f_private = true;
      f_options = 0;
    } in
  let termEvent = FunApp (funSymbEvent, [FunApp (fstSessName, [])]) in
  let p' = Event (termEvent,p,Terms.new_occurrence ()) in
  p'


let displayProto p =
  let proto = extractProto p in
  let pp s= Printf.printf "%s" s in
  begin
    pp "{\n   Identity Names: ";
    List.iter (fun s -> Display.Text.display_function_name s; pp ", ") proto.idNames;
    pp  "\n   Session Names:  ";   
    List.iter (fun s -> Display.Text.display_function_name s; pp ", ") proto.sessNames;
    pp  "\n   Initiator:\n";
    Display.Text.display_process "" proto.ini;
    pp    "   Responder:\n";
    Display.Text.display_process "" proto.res;
    pp  "}\n";
  end

(** Check Condition 1 (outptuis are relation-free). *)
let checkC1 p = failwith "Not Implemented"

(** Check Condition 2 (tests do not leak information about agents). *)
let checkC2 p = failwith "Not Implemented"

