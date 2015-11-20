(*************************************************************
 *                                                           *
 *  UKANO: UnlinKability and ANOnymity verifier              *
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
   verifier built on top of ProVerif as described in [1]. *)

(* [1]: Submitted paper *)

open Types
open Pervasives

let pp s= Printf.printf "%s" s

(* For debugging purpose *)
let log s = Printf.printf "> %s\n" s

let splitTheoryString = "==PROTOCOL=="

(* Helping message *)
let helpMess = 
  (  "Only typed ProVerif files are accepted (the option '-in pitype' is enabled by default). See the folder './examples/' for examples\n"^
     "of files in the correct format. They can be used to bootsrap your own file. For more details, see the README file at the root of\n"^
     "the project.\n")

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

let typeBit = {tname = "bitstring"}

(* create fresh occurence (to be associated to each new syntactical action) *)
let makeOcc () = Terms.new_occurrence ()

(************************************************************)
(* Parsing Protocols                                        *)
(************************************************************)

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
		    ?lastCondi:(laC=false) ?lastElse:(laE=Nil) accN = function
    | Nil -> ()
    | Input (_,(PatVar bx),p,_) as proc ->
       if laI then errorClass ("Roles cannot perform two inputs in a row.") proc;
       checkRole ~lastInp:true ~lastOut:false ~lastCondi:false accN p
    | Input (_,_,_,_) as proc -> 
       errorClass ("Roles cannot user patterns in input.") proc;
    | Output (_,_,p,_) as proc ->
       if laO then errorClass ("Roles cannot perform two outputs in a row.") proc;
       checkRole ~lastInp:false ~lastOut:true ~lastCondi:false accN p
    | Let (_,_,pt,pe,_)
    | Test (_,pt,pe,_) as proc ->
       if laO then errorClass "Roles cannot perform tests just after outputs." proc
       else begin
	   (match pe with
	    | Nil -> ()
	    | Output (_,_,Nil,_) -> ()
	    | _ -> errorClass ("Else branches must be either Nil or Output.Nil.") pe);
	   if laC
	   then (match laE,pe with
		 | Nil, Nil -> checkRole accN pt
		 | (Output(t1,t2,Nil,_), Output(t1',t2',Nil,_)) when (t1=t1' && t2=t2') -> checkRole accN pt
		 (* START: this should be removed (for back-compatibility) *)
		 | Nil,_ -> checkRole accN pt
		 (* END *)
		 | _ -> errorClass ("Two else branches from adjacent tests are not syntactical equal.") pe)
	   else checkRole ~lastCondi:true ~lastElse:pe accN pt;
	 end
    | Restr (nameSymb, _, p, _) ->
       accN := nameSymb :: !accN;
       checkRole ~lastInp:laI ~lastOut:laO ~lastCondi:laC ~lastElse:laE accN p
    | p -> errorClass ("Only Nul,Input,Output,Test, Let and creation of names are allowed in roles.") p in
  (* true if fst observable action is an output *)
  let rec fstIsOut = function
    | Output(_,_,_,_) -> true
    | Let(_,_,pt,_,_) -> fstIsOut pt
    | Test(_,pt,_,_) -> fstIsOut pt
    | Restr(_,_,p,_) -> fstIsOut p
    | _ -> false in
  (* Check that the two given processes are dual roles of the correct form and
     return (initiator, responder). *)
  let checkRoles p1 p2 =
    let namesP1, namesP2 = ref [], ref [] in
    checkRole namesP1 p1;
    checkRole namesP2 p2;
    match (fstIsOut p1, fstIsOut p2) with
    | true,false -> (p1,!namesP1),(p2,!namesP2)
    | false,true -> (p2,!namesP2),(p1,!namesP1)
    | _ -> errorClass ("The two roles are not dual.") p1 in
  (* remove all restriction of names in roles *)
  let rec removeRestr = function
    | Nil -> Nil
    | Input (tc,patx,p,occ) -> Input(tc,patx,removeRestr p, occ)
    | Output (tc,tm,p,occ) -> Output(tc,tm,removeRestr p, occ)
    | Let (patx,t,pt,pe,occ) -> Let (patx,t,removeRestr pt, removeRestr pe, occ)
    | Test (t,pt,pe,occ)-> Test(t,removeRestr pt, removeRestr pe,occ)
    | Restr (_,_,p,_) -> removeRestr p
    | p -> errorClass ("Critical error, should never happen.") p in
  (* We now match the whole system against its expected form *)
  match (getNames [] process) with
  | (comNames, Repl (idProc,_)) ->
     let idNames, idProc' = getNames [] idProc in
     (match idProc' with
      | Repl (sessProc,_) ->
	 let sessNames, sessProc' = getNames [] sessProc in
	 (match sessProc' with
	  | Par (p1,p2) ->
	     let ((iniP,iniN),(resP,resN)) = checkRoles p1 p2 in
	     let iniPclean,resPclean = (removeRestr iniP, removeRestr resP) in
	     let sessName = {    f_name = "sess";
				 f_type = ([], typeBit);
				 f_cat = Name {prev_inputs=None; prev_inputs_meaning=[]};
				 f_initial_cat = Name {prev_inputs=None; prev_inputs_meaning=[]};
				 f_private = true;
				 f_options = 0;	} in
	     {
	       comNames = comNames;
	       idNames = idNames;
	       sessNames = sessName :: (List.rev sessNames) @ (List.rev iniN) @ (List.rev resN);
	       ini = iniPclean;
	       res = resPclean;
	     }
	  | p -> errorClass ("After session names, we expect a parallel composition of two roles.") p)
      | p -> errorClass ("After the first replication and identity names, we expect a replication (for sessions).") p)
  | (_,p) -> errorClass ("A replication (possibly after some creation of names) is expected at the begging of the process.") p



(************************************************************)
(* Display functions                                        *)
(************************************************************)

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
  pp (indent^indent^indent^"((\n");
  Display.Text.display_process (indent^indent^indent^indent) proto.ini;
  pp (indent^indent^indent^")|(\n");
    Display.Text.display_process (indent^indent^indent^indent) proto.res;
  pp (indent^indent^indent^"))\n")


(************************************************************)
(* Deal with IO                                             *)
(************************************************************)
(** Given an input file name, returns the string of all its theory definitions. *)
let theoryStr inNameFile =
  let inFile = open_in inNameFile in
  let sizeInFile = in_channel_length inFile in
  let inStr = String.create sizeInFile in
  really_input inFile inStr 0 sizeInFile;
  let theoStr =
    try let listSplit = (Str.split (Str.regexp_string splitTheoryString) inStr) in
	if List.length listSplit <= 1
	then begin
	    (* for back-compatibility: *)
	    let listSplit2 = (Str.split (Str.regexp_string "PROTOCOLS") inStr) in
	    if List.length listSplit2 <= 1
	    then failwith ""
	    else List.hd listSplit2;
	  end
	else List.hd listSplit
    with _ -> begin
	pp ("Your inputted file should contain the delimiter: '"^
	      splitTheoryString^
		"' between the theory and the protocol.\n");
	pp ("Rules: "^helpMess);
	failwith "Inputted file not compliant with our rules.";
      end in
  (* for back-compatibility: *)
  let theoStr = Str.global_replace (Str.regexp_string "key") "bitstring" theoStr in
  let theoStr = Str.global_replace (Str.regexp_string "nonce") "bitstring" theoStr in
  let theoStr = Str.global_replace (Str.regexp_string "type bitstring.") "" theoStr in
  theoStr


(************************************************************)
(* Push session names as far as possible                    *)
(************************************************************)
(* We suppose here that session names are not shared between agents
   (as defined in the paper. *)
let pushNames proto = 
  let sessNames = List.tl proto.sessNames in
  let sessNameEvent = List.hd proto.sessNames in
  let addNames names continuationProc = 
    List.fold_right (fun name proc ->
		     Restr(name, 
			   (None, Stringmap.StringMap.empty),
			   proc,makeOcc()))
		    names
		    continuationProc in
  let rec pushN accNames = function
    | Nil -> Nil
    | Input (tc,patx,p,occ) -> Input(tc,patx,pushN accNames p, occ)
    | Output (tc,tm,p,occ) -> 	(* is there a needed name in accNames ? *)
       let needNames = List.filter (fun name -> Terms.occurs_f name tm) accNames in
       if needNames <> []
       then 
	 let otherNames = List.filter (fun n -> not(List.mem n needNames)) accNames in
	 addNames needNames (Output(tc,tm,pushN otherNames p, occ))
       else Output(tc,tm,pushN accNames p, occ)
    | Let (patx,t,pt,pe,occ) -> (* is there a needed name in accNames ? *)
       let needNames = List.filter (fun name -> Terms.occurs_f name t) accNames in
       if needNames <> []
       then 
	 let otherNames = List.filter (fun n -> not(List.mem n needNames)) accNames in
	 addNames needNames (Let (patx,t,pushN otherNames pt, pushN otherNames pe, occ))
       else Let (patx,t,pushN accNames pt, pushN accNames pe, occ)
    | Test (t,pt,pe,occ)-> (* is there a needed name in accNames ? *)
       let needNames = List.filter (fun name -> Terms.occurs_f name t) accNames in
       if needNames <> []
       then 
	 let otherNames = List.filter (fun n -> not(List.mem n needNames)) accNames in
	 addNames needNames (Test(t,pushN otherNames pt, pushN otherNames pe,occ))
       else Test(t,pushN accNames pt, pushN accNames pe,occ)
    | Event(t,p,occ) -> (* is there a needed name in accNames ? *)
       let needNames = List.filter (fun name -> Terms.occurs_f name t) accNames in
       if needNames <> []
       then 
	 let otherNames = List.filter (fun n -> not(List.mem n needNames)) accNames in
	 addNames needNames (Event(t,pushN otherNames p, occ))
       else Event(t,pushN accNames p, occ)
    | Par (p1,Nil) -> pushN accNames p1
    | Par (Nil,p2) -> pushN accNames p2
    | Par (p1, (Output(tc,tm,Nil,occ) as p2)) -> (* this can happen because of translations done when checking Frame opacity *)
       let needNames = List.filter (fun name -> Terms.occurs_f name tm) accNames in
       if needNames <> []
       then 
	 let otherNames = List.filter (fun n -> not(List.mem n needNames)) accNames in
	 addNames needNames (Par (pushN otherNames p1, p2))
       else Par (pushN accNames p1, p2) 
    | Par (_,_) as p -> errorClass ("[UKANO] [pushN] [PAR] Critical error, should never happen.") p
    | Restr (_,_,_,_) -> failwith "WHAT RESTR"
    | p -> errorClass ("[UKANO] [pushN]Critical error, should never happen.") p in
  {
    proto with
    ini = pushN sessNames proto.ini;
    res = pushN sessNames proto.res;
    sessNames = [sessNameEvent];
  }

(************************************************************)
(* Handling events & checking well-authentication           *)
(************************************************************)
(* erase idealized version of outputs from protocols *)
let cleanChoice proto = 
  let rec rmProc = function
    | Nil -> Nil
    | Input (tc,patx,p,occ) -> Input(tc,patx,rmProc p, occ)
    | Output (tc,tm,p,occ) ->
       let tmClean =
	 match tm with
	 | FunApp (funSymb, tm1 :: tl) when funSymb.f_cat = Choice -> tm1
	 | _ -> tm in
       Output(tc,tmClean,rmProc p, occ)
    | Let (patx,t,pt,pe,occ) -> Let (patx,t,rmProc pt, rmProc pe, occ)
    | Test (t,pt,pe,occ)-> Test(t,rmProc pt, rmProc pe,occ)
    | Restr (_,_,p,_) -> rmProc p
    | p -> errorClass ("Critical error, should never happen.") p in
  { proto with
    ini = rmProc proto.ini;
    res = rmProc proto.res;
  }
	 
(* [string -> term list -> term] (of the rigth form to put it under Event constructor) *)
let makeEvent name args =
  let typeEvent = [typeBit] in
  let funSymbEvent = {
      f_name = name;
      f_type = (typeEvent, Param.event_type);
      f_cat = Eq[];
      f_initial_cat = Eq[];
      f_private = true;
      f_options = 0;
    } in
  FunApp (funSymbEvent, args)
				      
(** Display a whole ProVerif file checking the first condition except for the theory (to be appended). *)      
let transC2 p inNameFile nameOutFile = 
  let proto = cleanChoice (extractProto p) in
  let (sessName,idName) =
    try (List.hd proto.sessNames, List.hd proto.idNames) (* 2 funSymb *)
    with _ -> failwith "The protocol shoulv have at least one identity name and one session name." in
  let (sessTerm,idTerm) = FunApp (sessName, []), FunApp (idName, []) in
  let listEvents = ref [] in
  let iniPrefix, resPrefix = "I", "R" in
  let nameEvent prefixName nb actionName = Printf.sprintf "%s%s_%d" prefixName actionName nb in
  (* add an event on top of a process with args + in addition [idTerm,sessTerm] *)
  let addEvent name args p = 	
    let newArgs = idTerm :: sessTerm :: args in
    let event = makeEvent name newArgs in
    listEvents := (name, List.length newArgs) :: !listEvents;
    Event (event, p, makeOcc())in

  (* add all events to a role *)
  let addEventsRole proc prefixName isIni =
    let makeArgs listIn listOut =	(* create the list of arguments of events : terms list *)
      let rec merge = function
	| [], l -> l
	| l, [] -> l
	| a1 :: l1, a2 :: l2 -> a1 :: a2 :: (merge (l1,l2)) in
      if isIni
      then merge (List.rev listOut, List.rev listIn)
      else merge (List.rev listIn, List.rev listOut) in
    let rec goThrough listTest listIn listOut = function
      | Input (tc,((PatVar bx) as patx),p,occ) -> (* bx: binder in types.mli *)
	 let newListIn = (Var bx) :: listIn in
	 let subProc,lTest,nbOut = goThrough listTest newListIn listOut p in
	 let argsEv = makeArgs newListIn listOut
	 and nameEv = nameEvent prefixName (List.length newListIn) "in" in
	 let subProcEv = addEvent nameEv argsEv subProc in
	 (Input(tc,patx, subProcEv, occ), lTest, nbOut)
      | Output (tc,tm,p,occ) ->
	 let newListOut = tm :: listOut in
	 let subProc,lTest,nbOut = goThrough listTest listIn newListOut p in
	 let argsEv = makeArgs listIn newListOut
	 and nameEv = nameEvent prefixName (List.length newListOut) "out" in
	 let newProc = Output(tc,tm,subProc,occ) in
	 (addEvent nameEv argsEv newProc, lTest, nbOut)
      | Let (pat,t,pt,pe,occ) ->
	 (match pt with
	  | Test(_,_,_,_)
	  | Let(_,_,_,_,_) -> 	(* in that case we won't create query *)
	     let subProc,lTest,nbOut = goThrough listTest listIn listOut pt in
	     (Let(pat,t,subProc,pe,occ),lTest,nbOut)
	  | _ ->                (* last conditional: we do create query *)
	     let newListTest = (List.length listTest+1, List.length listIn) :: listTest in
	     let subProc,lTest,nbOut = goThrough newListTest listIn listOut pt in
	     let argsEv = makeArgs listIn listOut
	     and nameEv = nameEvent prefixName (List.length newListTest) "test" in
	     let subProcEv = addEvent nameEv argsEv subProc in
	     (Let(pat,t,subProcEv,pe,occ), lTest, nbOut))
      | Test (t,pt,pe,occ) -> 
	 (match pt with
	  | Test(_,_,_,_)
	  | Let(_,_,_,_,_) ->  	(* in that case we won't create query *)
	     let subProc,lTest,nbOut = goThrough listTest listIn listOut pt in
	     (Test(t,subProc,pe,occ),lTest,nbOut)
	  | _ -> 		(* last conditional: we do create query *)
	     let newListTest = (List.length listTest+1,List.length listIn) :: listTest in
	     let subProc,lTest,nbOut = goThrough newListTest listIn listOut pt in
	     let argsEv = makeArgs listIn listOut
	     and nameEv = nameEvent prefixName (List.length newListTest) "test" in
	     let subProcEv = addEvent nameEv argsEv subProc in
	     (Test(t,subProcEv,pe,occ), lTest, nbOut))
      | Nil -> (Nil, List.rev listTest, List.length listOut)
      | _ -> failwith "Critical error: transC2 is applied on a protocol that does not satisfy the syntactical restrictions. Should never happen." in
    goThrough [] [] [] proc in

  (* Generate a string for a query *)
  let generateQuery nb nbIn isInitiator =
    let prefix = "query k:bitstring, n1:bitstring, n2:bitstring,\n" in
    let nbArgs = if isInitiator	(* number of arguments to declare for this query *)
		 then 2*nbIn
		 else 2*nbIn-1 in
    let rec range = function | 0 -> [] | n -> n :: range (n-1) in
    let listArgs nb = 		(* generate a list of messages to give as arguments to events *)
      List.map (fun n -> Printf.sprintf "m%d" n) (List.rev (range nb)) in      
    let allListArgs nb role = 
      "k" :: (if role==iniPrefix then "n1" else "n2") :: (listArgs nb) in
    let listArgsDec = listArgs nbArgs in      
    let prefixArgs = "      "^
		       (String.concat ", "
				      (List.map (fun s -> Printf.sprintf "%s:bitstring" s) listArgsDec))
		       ^";\n" in
    let dual (p1,p2) = p2,p1 in
    let roles = iniPrefix,resPrefix in
    let dualRoles = dual roles in
    let rec produceEvents = function
      |	0 -> []
      | n  -> 
	 let outRole, inRole = if (n mod 2) = 0 then dualRoles else roles in
	 let n' = if (n mod 2) = 0 then n/2 else n/2+1 in
	   (* if (n mod 2) = 0 then n-1 else n in *)
	 (Printf.sprintf "event(%s(%s))" (nameEvent inRole n' "in") (String.concat "," (allListArgs n inRole)))
	 ::
	   (Printf.sprintf "event(%s(%s))" (nameEvent outRole n' "out") (String.concat "," (allListArgs n outRole)))
	 ::
	   produceEvents (n-1) in
    let listEvents = produceEvents (if isInitiator then 2*nbIn else 2*nbIn-1) in
    let thisRole = if isInitiator then fst roles else snd roles in
    let lastEvent = Printf.sprintf "event(%s(%s))" 
				   (nameEvent thisRole nb "test")
				   (String.concat "," (allListArgs nbArgs thisRole)) in
    let strImplications = String.concat "  ==>\n" 
					(List.map (fun ev -> Printf.sprintf "   (%s" ev)
						  (lastEvent :: listEvents)) in
    let rec repeat s = function | 0 -> "" | n -> s^(repeat s (n-1)) in
    if List.length listEvents = 0 then ""
    else prefix^prefixArgs^strImplications^
	   (repeat ")" (List.length listEvents+1))^"."
  in
  
  (* -- 1. -- COMPUTING EVENTS VERSION AND QUERIES *)
  let iniEvents,iniTests,iniNbOut = addEventsRole proto.ini iniPrefix true in
  let resEvents,resTests,resNbOut = addEventsRole proto.res resPrefix false in
  let protoEvents = { proto with
		      ini = iniEvents;
		      res = resEvents;
		    } in
  let allQueries = (List.map (fun (nb,nbIn) -> generateQuery nb nbIn true) iniTests) @ 
		     (List.map (fun (nb,nbIn) -> generateQuery nb nbIn false) resTests) in

  let displayEventsDec listEvents =
    let rec nBit = function
      | 0 -> []
      | n -> "bitstring" :: nBit (n-1) in
    List.iter 
      (fun (name, arity) ->
       Printf.printf "event %s(%s).\n" name (String.concat "," (nBit arity))
      ) listEvents in

  (* -- 2. -- GET the theory part of inNameFile *)
  let theoryStr = theoryStr inNameFile in
  
  (* -- 3. -- Print evrything using a HACK TO REDIRECT STDOUT *)
  let newstdout = open_out nameOutFile in
  print_newline ();		(* for flushing stdout *)
  Unix.dup2 (Unix.descr_of_out_channel newstdout) Unix.stdout;
  (* Print (=write in the file) the complete ProVerif file *)
(*  pp "\n\n(* == THEORY == *)\n"; *)
  pp theoryStr;
  pp " *)\n";
  pp "\n\n(* == DECLARATIONS OF EVENTS == *)\n";
  displayEventsDec !listEvents;
  pp "\n\n(* == DECLARATIONS OF QUERIES == *)\n";
  List.iter (fun s -> Printf.printf "%s\n" s) allQueries;
  pp "\n\n(* == PROTOCOL WITH EVENTS == *)\n";
  pp "let SYSTEM =\n";
  let toDisplay = pushNames protoEvents in
  displayProtocolProcess toDisplay;
  pp ".\nprocess SYSTEM\n"
(* END OF REDIRECTION *)


(************************************************************)
(* Handling nonce versions & checking Frame Opacity         *)
(************************************************************)

let choiceSymb = {
    f_name = "choice";
    f_type = ([typeBit;typeBit], typeBit);
    f_cat = Choice;
    f_initial_cat = Choice;
    f_private = false;		(* TODO *)
    f_options = 0;		(* TODO *)
  }
let letCatchSymb = {
    f_name = "";
    f_type = ([typeBit;typeBit;typeBit], typeBit);
    f_cat = LetCatch;
    f_initial_cat = LetCatch;
    f_private = true;		(* TODO *)
    f_options = 0;		(* TODO *)
  }
let hole =
  FunApp
    ( {
	f_name = "hole";
	f_type = ([], typeBit);
	f_cat = Tuple;
	f_initial_cat = Tuple;	f_private = true;
	f_options = 0;		(* TODO *)
      }
    , [])
let mergeOut = {
    sname = "mergeOut";
    vname = 0;
    unfailing = true;
    btype = typeBit;
    link = NoLink;
  }
		 
let debugF_type (tl,t) = 
  ""
let displayCat = function
  | Tuple -> "Tuple"
  | Name _ -> "Name"
  | _ -> "todo"

let debugFunSymb f = 
  Printf.printf 
    "Funsym[ name:%s, f_type:%s, f_cat: %s f_private %b f_options:%d]"
    f.f_name
    (debugF_type f.f_type)
    (displayCat f.f_cat)
    f.f_private
    f.f_options
    
(** Display a whole ProVerif file checking the first condition except for the theory (to be appended). *)      
let transC1 p inNameFile nameOutFile = 
  let proto = extractProto p in

  (* -- 1. -- Build nonce versions on the right *)
  let nonTransparentSymbList = ["enc"; "aenc"; "dec"; "adec"; "h"; "hash"; "xor"] in
  let isName funSymb = match funSymb.f_cat with Name _ -> true | _ -> false in
  let isPrivate funSymb = funSymb.f_private in
  let isConstant funSymb = isName funSymb && not(isPrivate funSymb) in
  let isTuple funSymb = match funSymb.f_cat with Tuple -> true | _ -> false in
  let rec guessIdeal = function
    | FunApp (f, []) as t
	 when isConstant f -> t	             (* public constants *)
    | FunApp (f, []) when isName f -> hole   (* (private) names *)
    | FunApp (f, _)
	 when (List.mem f.f_name nonTransparentSymbList) 
      -> hole	                             (* should be non-transparent *)
    | FunApp (f, listT)
	 when isTuple f
      -> FunApp (f, List.map guessIdeal listT) (* tuple *)
    | term -> begin
	log "Warning: some idealized messages are missing and it is unclear how to guess them. The idealization of : ";
	Printf.printf "     ";
	Display.Text.display_term term;
	Printf.printf "\n";
	log "will be a hole.\n";
	hole;
      end in
  let countNonces = ref 0 in
  let listNames = ref [] in
  let createNonce () = 
    incr(countNonces);
    let nameName = Printf.sprintf "n%d" !countNonces in
    let funSymb =
      {
	f_name = nameName;
	f_type = ([],typeBit);
	f_cat =  Name { prev_inputs = None; prev_inputs_meaning = []};
	f_initial_cat = Name { prev_inputs = None; prev_inputs_meaning = []};
	f_private = true;
	f_options = 0
      } in
    listNames := funSymb :: !listNames;
    FunApp (funSymb, []) in
  (* idealized term -> nonce term *)
  let rec noncesTerm = function
    | FunApp (f, tList) when f.f_name = "hole" -> createNonce()
    | FunApp (f, tList) -> FunApp (f, List.map noncesTerm tList)
    | Var _ -> errorClass ("Critical error, should never happen.") p in
  (* idealized process (some idealized output may miss) -> nonce process *)
  let rec noncesProc = function
    | Nil -> Nil
    | Input (tc,patx,p,occ) -> Input(tc,patx, noncesProc p, occ)
    | Output (tc,tm,p,occ) ->
       let (tmReal, tmIdeal) =
	 match tm with
	 | FunApp (funSymb, tm1 :: tm2 :: tl) when funSymb.f_cat = Choice -> (tm1, tm2) (* user already built idealization *)
	 | _ -> (* For debugging purpose: pp "\n"; 
                   (match tm with | FunApp (f, li) -> debugFunSymb f);
                   pp "\n"; Display.Text.display_term tm;
        	   pp " -> "; Display.Text.display_term (guessIdeal tm);  pp "\n"; *)
	    (tm, guessIdeal tm) in (* he did not, we need to guess it *)
       let tmNonce = noncesTerm tmIdeal in
       let tmChoice = FunApp (choiceSymb, [tmReal; tmNonce]) in
       Output(tc, tmChoice , noncesProc p, occ)
    | Let (patx,t,pt,pe,occ) -> Let (patx,t, noncesProc pt, noncesProc pe, occ)
    | Test (t,pt,pe,occ)-> Test(t, noncesProc pt, noncesProc pe,occ)
    | p -> errorClass ("Critical error, should never happen.") p in
  let noncesProto = 
    { proto with
      ini = noncesProc proto.ini;
      res = noncesProc proto.res;
      sessNames = proto.sessNames @ (List.rev !listNames);
    } in
  
  
  (* -- 2. -- Deal with conditionals (should not create false attacks for diff-equivalent) *)
  (* a) we push conditionals (Test and Let) and put them just before Output (when needed)
     b) we use a hack to be sure the 'Let' construct will never fail:
             let yn = dec(x,k) in
             out(c, choice[yn,n4]
        will be translated to
             let mergeOut = let yn = dec(x,k) in
                              choice[yn,n4]
                            else n4 in
             out(c, mergeOut).
        Function cleanTest cannot produce nested let (it is actually syntactic sugar
        and have no internal representation. We thus use a flag using a special funsymb
        letCatch with a specific f_cat to warn the display function that it is needed to
        put all following let/test construct INSIDE the first let mergeOut = [put here]. *)
  
(* Check if the term tm contains variables from some patterns in accLet *)
  let checkVar tm accLet = 
    let inPattern name (patx,_) = 
      let rec auxPatternTerm = function
	| Var binder -> binder.sname = name
	| FunApp (_,termList) -> List.exists auxPatternTerm termList in
      let rec auxPattern = function
	| PatVar binder -> name = binder.sname
	| PatTuple (_,patList) -> List.exists auxPattern patList
	| PatEqual t -> auxPatternTerm t in
      auxPattern patx in
    let rec auxTerm = function
      | Var binder -> 
	 List.exists (inPattern binder.sname) accLet
      | FunApp (_,termList) -> List.exists auxTerm termList in
    auxTerm tm in
  (* clean conditional by pushing them before output (when they need them)
     and using our special construction letCatch that cannot fail *)
  let rec cleanTest accTest accLet = function
    | Nil -> Nil
    | Input (tc,patx,p,occ) -> Input(tc,patx, cleanTest accTest accLet p, occ)
    | Output (tc,tm,p,occ) ->
       (* check if tm use variables binded by patterns in accLet *)
       if checkVar tm accLet
       then begin
	   (* we need to put a LetCatch construct here followed by all accLet,accTest *)
	   let tml,tmr =	(* left/right part of choice *)
	     (match tm with
	      | FunApp (funSymb, tm1 :: tm2 :: tl)
		   when funSymb.f_cat = Choice -> (tm1, tm2)
	      | _ -> failwith "Cannot happen") in
	   let letCatchTerm = FunApp (letCatchSymb, [tml;tmr;tm]) in
	   let letCatchPattern = PatVar mergeOut in
	   let rec addLetIf = function   (* add all accLet then accTest and the final Output *)
	     | [],[] -> Output(tc,Var mergeOut, cleanTest accTest accLet p, occ)
	     | (accT, (patx,t)::tl) -> Let (patx,t,addLetIf (accT,tl),Nil,makeOcc())
	     | (t::tl, []) -> Test (t,addLetIf (tl,[]),Nil,makeOcc()) in
	   Let (letCatchPattern, (* before all new Let/Test/Out, we put the Let mergeOut = LetCatch[tl,tm,tm] *)
		letCatchTerm,
		addLetIf (List.rev accTest, List.rev accLet),
		Nil, makeOcc())
	 end else begin
	   (* the output does need conditionals  *)
	   Output(tc,tm, cleanTest accTest accLet p, occ);
	 end
    | Let (patx,t,pt,pe,occ) ->
       Par(cleanTest accTest ((patx,t)::accLet) pt,
	   cleanTest accTest accLet pe)
    | Test (t,pt,pe,occ)-> Par(cleanTest (t::accTest) accLet pt, cleanTest accTest accLet pe)
    | p -> errorClass ("Critical error, should never happen.") p in
  let cond1Proto = 
    { noncesProto with
      sessNames = proto.sessNames @ (List.rev !listNames);
      ini = cleanTest [] [] noncesProto.ini;
      res = cleanTest [] [] noncesProto.res;
    } in

  (* -- 3. -- GET the theory part of inNameFile *)
  let theoryStr = theoryStr inNameFile in

  (* -- 4. -- Print evrything using a HACK TO REDIRECT STDOUT *)
  let newstdout = open_out nameOutFile in
  print_newline ();		(* for flushing stdout *)
  Unix.dup2 (Unix.descr_of_out_channel newstdout) Unix.stdout;
  (* Print (=write in the file) the complete ProVerif file *)
(*  pp "\n\n(* == THEORY == *)\n"; *)
  pp theoryStr;
  pp " *)\n";
  pp "\n\n(* == PROTOCOL WITH NONCE VERSIONS == *)\n";
  pp "let SYSTEM =\n";
  let toDisplay = pushNames cond1Proto in
  displayProtocolProcess toDisplay;
  pp ".\nprocess SYSTEM\n"
(* END OF REDIRECTION *)



(* To implement later on: *)
(** Check Frame Opacity (outptuis are relation-free). *)
let checkC1 p = failwith "Not Implemented"

(** Check Well-Authentication (tests do not leak information about agents). *)
let checkC2 p = failwith "Not Implemented"

(** Check UK & ANO *)
let check p =  checkC1 p && checkC2 p
