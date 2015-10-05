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

let pp s= Printf.printf "%s" s

(* For debugging purpose *)
let log s = Printf.printf "> %s\n" s

(* Raised when the inputted process is not a 2-agents protocol as defined
   in [1], the associated string is the reason/explanation. *)
exception NotInClass of string

let debProc p = 
  Display.Text.display_process ">   " p

let errorClass s p =
  log "Part of the process that violates the syntactical restrictions: ";
  Display.Text.display_process "   " p;
  raise (NotInClass s)

(** Type of a 2-agents protocol as defined in [1] *)
type proto = {
    comNames : funsymb list;	(* common names of all agents (created before the first !)  *)
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
  (* Check that a given role is of the expected form: optional arguments are used to make sure
     the role meets the alternation in/test*/out with same else branches in test*. *)
  let rec checkRole ?lastInp:(laI=false) ?lastOut:(laO=false)
		    ?lastCondi:(laC=false) ?lastElse:(laE=Nil)= function
    | Nil -> ()
    | Input (_,_,p,_) as proc ->
       if laI then errorClass ("Roles cannot perform two inputs in a row.") proc;
       checkRole ~lastInp:true ~lastOut:false ~lastCondi:false p
    | Output (_,_,p,_) as proc ->
       if laO then errorClass ("Roles cannot perform two outputs in a row.") proc;
       checkRole ~lastInp:false ~lastOut:true ~lastCondi:false p
    | Let (_,_,pt,pe,_)
    | Test (_,pt,pe,_) as proc ->
       if laO then errorClass "Roles cannot perform tests just after outputs." proc
       else begin
	   (match pe with
	    | Nil -> ()
	    | Output (_,_,Nil,_) as proc -> ()
	    | _ -> errorClass ("Else branches must be either Nil or Output.Nil.") pe);
	   if laC
	   then (match laE,pe with
		 | Nil, Nil -> checkRole pt
		 | (Output(t1,t2,Nil,_), Output(t1',t2',Nil,_)) when (t1=t1' && t2=t2') -> checkRole pt
		 | _ -> errorClass ("Two else branches from adjacent tests are not syntactical equal.") laE)
	   else checkRole ~lastCondi:true ~lastElse:pe pt;
	 end
    | p -> errorClass ("Only Nul,Input,Output,Test and Let are allowed in roles.") p in
  (* Check that the two given processes are dual roles of the correct form and
     return (initiator, responder). *)
  let checkRoles p1 p2 =
    checkRole p1;
    checkRole p2;
    match p1,p2 with
    | Output(_,_,_,_), Input(_,_,_,_) -> p1,p2
    | Input(_,_,_,_), Output(_,_,_,_) -> p2,p1
    | _ -> errorClass ("The two roles are not dual.") p1 in
  (* We now match the whole system against its expected form *)
  match (getNames [] process) with
  | (comNames, Repl (idProc,_)) ->
     let idNames, idProc' = getNames [] idProc in
     (match idProc' with
      | Repl (sessProc,_) ->
	 let sessNames, sessProc' = getNames [] sessProc in
	 (match sessProc' with
	  | Par (p1,p2) ->
	     let ini,res = checkRoles p1 p2 in
	     {
	       comNames = comNames;
	       idNames = idNames;
	       sessNames = sessNames;
	       ini = ini;
	       res = res;
	     }
	  | p -> errorClass ("After session names, we expect a parallel composition of two roles.") p)
      | p -> errorClass ("After the first replication and identity names, we expect a replication (for sessions).") p)
  | (_,p) -> errorClass ("A replication (possibly after some creation of names) is expected at the begging of the process.") p
			
			
let displayProtocol proto =
  pp "{\n   Common Names: ";
  List.iter (fun s -> Display.Text.display_function_name s; pp ", ") proto.comNames;
  pp  "\n   Identity Names: ";
  List.iter (fun s -> Display.Text.display_function_name s; pp ", ") proto.idNames;
  pp  "\n   Session Names:  ";   
  List.iter (fun s -> Display.Text.display_function_name s; pp ", ") proto.sessNames;
  let sep = "      >   " in
  pp  "\n   Initiator:\n";
  Display.Text.display_process sep proto.ini;
  pp    "   Responder:\n";
  Display.Text.display_process sep proto.res;
  pp  "}\n"
      
(** Display a representation of the 2-agents protocol associated to a given process. *)
let displayProcessProtocol p =
  let proto = extractProto p in
  displayProtocol proto

(* Given a protcol, diplay the process implementing the full system with multiple sessions *)
let displayProtocolProcess proto =
  let indent = " " in
  List.iter 
    (fun q -> Printf.printf "new %s : bitstring;\n" q.f_name)
    proto.comNames;
  pp " !\n";
  List.iter 
    (fun q -> Printf.printf "%snew %s : bitstring;\n" indent q.f_name)
    proto.idNames;
  pp (indent^indent^" !\n");
  List.iter 
    (fun q -> Printf.printf "%snew %s : bitstring;\n" (indent^indent^indent) q.f_name)
    proto.sessNames;
  pp (indent^indent^indent^"(\n");
  Display.Text.display_process (indent^indent^indent^indent) proto.ini;
  pp (indent^indent^indent^"|\n");
    Display.Text.display_process (indent^indent^indent^indent) proto.res;
  pp (indent^indent^indent^")\n")

(* [string -> term list -> term] (of the rigth form to put it under Event constructor) *)
let makeEvent name args =
  let typeEvent = [{tname = "bitstring"}] in
  let funSymbEvent = {
      f_name = name;
      f_type = (typeEvent, Param.event_type);
      f_cat = Eq[];
      f_initial_cat = Eq[];
      f_private = true;
      f_options = 0;
    } in
  FunApp (funSymbEvent, args)

(* create fresh occurence (to be associated to each news yntactical action) *)
let makeOcc () = Terms.new_occurrence ()
				      
(** Display a whole ProVerif file checking the first condition except for the theory (to be appended). *)      
let transC2 p = 
  let proto = extractProto p in
  let (sessName,idName) =
    try (List.hd proto.sessNames, List.hd proto.idNames) (* 2 funSymb *)
    with _ -> failwith "The protocol shoulv have at least one identity name and one session name." in
  let (sessTerm,idTerm) = FunApp (sessName, []), FunApp (idName, []) in
  (* add an event on top of a process with in addition [idTerm,sessTerm] *)
  let addEvent name args p = 	
    let newArgs = idTerm :: sessTerm :: args in
    Event (makeEvent name newArgs, p, makeOcc())in
  let addEventsRole proc prefixName =
    let countIn = ref 0 in
    let countOut = ref 0 in
    let rec goThrough = function
      | Input (tc,((PatVar bx) as patx),p,occ) -> (* bx: binder in types.mli *)
	 Input(tc,patx, goThrough p, occ)
      | Output (tc,tm,p,occ) ->
	 incr(countOut);
	 let nameEvent = (prefixName^"-out-"^(string_of_int !countOut)) in
	 let p' = addEvent nameEvent [tm] (goThrough p) in
	 Output(tc,tm,p',occ)
      | Let (pat,t,pt,pe,_) as p ->
	 p
      | Test (t,pt,pe,_)  as p-> 
	 p
      | Nil -> Nil
      | _ -> failwith "Critical error: transC2 is applied on a protocol that does not satisfy the syntactical restrictions. Should never happen." in
    goThrough proc
  in
  let iniEvents = addEventsRole proto.ini "INI" in
  let resEvents = addEventsRole proto.res "RES" in
  let protoEvents = { proto with
		      ini = iniEvents;
		      res = resEvents;
		    } in
  displayProtocolProcess protoEvents


let transC1 p = ()


(* To implement later on: *)
(** Check Condition 1 (outptuis are relation-free). *)
let checkC1 p = failwith "Not Implemented"

(** Check Condition 2 (tests do not leak information about agents). *)
let checkC2 p = failwith "Not Implemented"
