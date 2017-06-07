(*************************************************************
 *                                                           *
 *  UKano: UnlinKability and ANOnymity verifier              *
 *                                                           *
 *  Lucca Hirschi                                            *
 *  http://projects.lsv.ens-cachan.fr/ukano/                 *
 *  Copyright (C) Lucca Hirschi 2015-2017                    *
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
open Pervasives

(* flags *)
let ideaAssumed = ref false
let isLastOutputByIni = ref false

(* For debugging purpose *)
let email = " Please report this error with the input file to lucca.hirschi@lsv.ens-cachan.fr'."
let pp s= Printf.printf "%s" s
let log s = Printf.printf "> %s\n%!" s
let debug = ref false
let verbose = ref false
(* Helping message *)
let helpMess =
  ("Your input model is not conform. It should be a valid typed ProVerif model ('proverif -in pitype <path>' should accept it).\nMoreover, it should comply with requirements
    explained in the README. You can refer to the folder './examples/' for examples of files in the correct format.\n They can be used to bootstrap your own file.")
			    
let splitTheoryString = "==PROTOCOL=="

(* Raised when the inputted process is not a 2-agents protocol as specified
   in the README, the associated string is the reason/explanation. *)
exception NotInClass of string

let debProc p = 
  Display.Text.display_process ">   " p

let errorClass s p =
  log "Part of the process that violates the syntactical restrictions: ";
  Display.Text.display_process "   " p;
  raise (NotInClass s)

(** Type of a 2-agents protocol *)
type proto = {
    comNames : funsymb list;	(* common names of all agents (created before the first !)  *)
    idNames : funsymb list;	(* identity names *)
    idNamesANO : funsymb list;	(* subset of identity names to be revealed for anonymity *)
    idNamesShared : funsymb list; (* identity names shared by Ini and Res *)
    idNamesIni : funsymb list;	  (* identity names of ini *)
    idNamesRes : funsymb list;	  (* identity names of res *)
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

(** Remove duplications in lists *)
let rec remove_dups lst= match lst with
  | [] -> []
  | h::t -> h::(remove_dups (List.filter (fun x -> x<>h) t))

(** Extract the protocol structure from a process and rise NotInClass if
    not of the expected form. *)
let extractProto process = 
  (* Compute free names of roles *)
  let rec freeNames = function
    | Nil -> []
    | Input (_,_,p,_)  -> freeNames p
    | Output (_,tm,p,_) ->
       let newNames = Terms.list_f tm in
       newNames @ (freeNames p)
    | Let (pat,t,pt,pe,_) -> 
       let newNames = (Terms.list_f_pat pat) @ (Terms.list_f t) in
       newNames @ (freeNames pe) @ (freeNames pt)
    | Test (tm,pt,pe,_) ->
       let newNames = Terms.list_f tm in
       newNames @ (freeNames pe) @ (freeNames pt)
    | Restr (_, _, p, _) -> freeNames p
    | p -> errorClass ("Only Nul,Input,Output,Test, Let and creation of names are allowed in roles.") p in
  (* Accumulate all names from all starting creation of names and return the
     list of name plus the continuation of the protocol *)
  let rec getNames acc = function
    | Restr (idName,_,p',_) -> getNames (idName::acc) p'
    | _ as p -> acc, p in
  let numberIn = ref 0 in
  (* Check that a given role is of the expected form: optional arguments are used to make sure
     the role meets the alternation in/test*/out with same else branches in test*. *)
  let rec checkRole ?lastInp:(laI=false) ?lastOut:(laO=false)
		    ?lastCondi:(laC=false) ?lastElse:(laE=Nil) accN = function
    | Nil -> ()
    | Input (_,(PatVar bx),p,_) as proc ->
       if laI then errorClass ("Roles cannot perform two inputs in a row.") proc;
       incr(numberIn);
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
		 | Nil, Nil -> checkRole ~lastCondi:true ~lastElse:pe accN pt
		 | (Output(t1,t2,Nil,_), Output(t1',t2',Nil,_)) when (t1=t1' && t2=t2') -> checkRole ~lastCondi:true ~lastElse:pe accN pt
		 (* START: this should be removed (for back-compatibility) *)
		 | Nil,_ -> checkRole ~lastCondi:true ~lastElse:pe accN pt
		 (* END *)
		 | _ -> errorClass ("Two else branches from adjacent tests are not syntactically equal.") pe)
	   else checkRole ~lastCondi:true ~lastElse:pe accN pt;
	 end
    | Restr (nameSymb, _, p, _) ->
       accN := nameSymb :: !accN;
       checkRole ~lastInp:laI ~lastOut:laO ~lastCondi:laC ~lastElse:laE accN p
    | p -> errorClass ("Only Nul,Input,Output,Test, Let and creation of names are allowed in roles.") p in
  (* The next functions are implicitely assuming that roles have been checked agains 'checkRole' *)
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
    let numberInP1 = !numberIn in
    numberIn := 0;
    checkRole namesP2 p2;
    let numberInP2 = !numberIn in
    match (fstIsOut p1, fstIsOut p2) with
    | true,false -> if numberInP1 >= numberInP2 then isLastOutputByIni:= true;
		    (p1,!namesP1),(p2,!namesP2)
    | false,true -> if numberInP2 <= numberInP1 then isLastOutputByIni:= true;
		    (p2,!namesP2),(p1,!namesP1)
    | _ -> errorClass ("The two roles are not dual.") p1 in
  (* remove all restriction of names in roles *)
  let rec removeRestr = function
    | Nil -> Nil
    | Input (tc,patx,p,occ) -> Input(tc,patx,removeRestr p, occ)
    | Output (tc,tm,p,occ) -> Output(tc,tm,removeRestr p, occ)
    | Let (patx,t,pt,pe,occ) -> Let (patx,t,removeRestr pt, removeRestr pe, occ)
    | Test (t,pt,pe,occ)-> Test(t,removeRestr pt, removeRestr pe,occ)
    | Restr (_,_,p,_) -> removeRestr p
    | p -> errorClass ("Critical error, should never happen [1]." ^ email) p in

  (* We now match the whole system against its expected form *)
  match (getNames [] process) with (* this returns global names and the continuation (should be of the form \pM *)
  | (comNames, Repl (idProc,_)) ->
     let idNames, idProc' = getNames [] idProc in (* those are the identity names *)
     (match idProc' with
      | Repl (sessProc,_) ->
	 let sessNames, sessProc' = getNames [] sessProc in (* those are session names *)
	 (match sessProc' with
	  | Par (p1,p2) ->
	     let ((iniP,iniN),(resP,resN)) = checkRoles p1 p2 in
	     let iniPclean,resPclean = (removeRestr iniP, removeRestr resP) in
	     let sessName0 = { f_name = "sess";
			       f_type = ([], typeBit);
			       f_cat = Name {prev_inputs=None; prev_inputs_meaning=[]};
			       f_initial_cat = Name {prev_inputs=None; prev_inputs_meaning=[]};
			       f_private = true;
			       f_options = 0;	} in
	     let idNamesANO = List.filter (* id names for anonymity are prefixed with 'id' *)
				(fun s -> (String.length s.f_name) >= 2 && (s.f_name.[0] = 'i') && (s.f_name.[1] = 'd'))
				idNames in
	     let freeNamesIni, freeNamesRes = (freeNames iniPclean), (freeNames resPclean) in
	     let idNamesIni =  List.filter (fun n -> List.mem n idNames) (remove_dups freeNamesIni) in
	     let idNamesRes =  List.filter (fun n -> List.mem n idNames) (remove_dups (freeNamesRes)) in
	     let idNamesShared = List.filter (fun n -> List.mem n idNamesRes) idNamesIni in
	     let isShared = ref false in
	     if !verbose then begin
		 if List.length idNamesShared = 0
		 then log "Note: No identity name is shared between initiator and responder."
		 else log "Note: Some identity names are shared between initiator and responder.";
		 if  List.length idNamesIni = 0
		 then log "Note: Initiator does not use any identity name.";
		 if List.length idNamesRes = 0
		 then log "Note: Responder does not use any identity name.";
	       end;
	     (* Finally, we build the protocol *)
	     {
	       comNames = comNames;
	       idNames = idNames;
	       idNamesANO = idNamesANO;
	       idNamesShared =idNamesShared ;
	       idNamesIni = idNamesIni;
	       idNamesRes = idNamesRes;
	       sessNames = sessName0 :: (List.rev sessNames) @ (List.rev iniN) @ (List.rev resN);
	       ini = iniPclean;
	       res = resPclean;
	     }
	  | p -> errorClass ("After session names, we expect a parallel composition of two roles.") p)
      | p -> errorClass ("After the first replication and identity names, we expect a replication (for sessions).") p)
  | (_,p) -> errorClass ("A replication (possibly after some creation of names) is expected at the beginning of the process.") p



(************************************************************)
(* Display functions                                        *)
(************************************************************)

let noneOrList f l =
  if List.length l = 0
  then pp "none"
  else List.iter f l  

let displayProtocol proto =
  pp "{\n   Global names: ";
  noneOrList (fun s -> Display.Text.display_function_name s; pp ", ") proto.comNames;
  pp  "\n   Identity names: ";
  noneOrList (fun s -> Display.Text.display_function_name s; pp ", ") proto.idNames;
  pp  "\n   Session names:  ";   
  noneOrList (fun s -> Display.Text.display_function_name s; pp ", ") proto.sessNames;
  pp  "\n   Identity names to be revealed for checking anonymity (i.e., the ones starting with 'id'):  ";   
  noneOrList (fun s -> Display.Text.display_function_name s; pp ", ") proto.idNamesANO;
  pp  "\n   Shared (by initiator and responder) identity names:  ";   
  noneOrList (fun s -> Display.Text.display_function_name s; pp ", ") proto.idNamesShared;
  pp  "\n   Identity names of initiator:  ";   
  noneOrList (fun s -> Display.Text.display_function_name s; pp ", ") proto.idNamesIni;
  pp  "\n   Identity names of responder:  ";   
  noneOrList (fun s -> Display.Text.display_function_name s; pp ", ") proto.idNamesRes;
  let sep = "      >   " in
  pp  "\n   Initiator role:\n";
  Display.Text.display_process sep proto.ini;
  pp    "   Responder role:\n";
  Display.Text.display_process sep proto.res;
  pp  "}\n"
      
(** Display a representation of the 2-agents protocol associated to a given process. *)
let displayProcessProtocol p =
  let proto = extractProto p in
  displayProtocol proto

(* Given a protcol, diplay the process implementing the full system with multiple sessions *)
let displayProtocolProcess proto =
  let indent = "  " in
  let displayMultipleSessions () =
    pp (indent^indent^" !\n");
    List.iter 
      (fun q -> Printf.printf "%snew %s : bitstring;\n" (indent^indent^indent) q.f_name)
      proto.sessNames;
    pp (indent^indent^indent^"((\n");
    Display.Text.display_process (indent^indent^indent^indent) proto.ini;
    pp (indent^indent^indent^")|(\n");
    Display.Text.display_process (indent^indent^indent^indent) proto.res;
    pp (indent^indent^indent^"))\n")
  in
  (* Common names *)
  List.iter 
    (fun q -> Printf.printf "new %s : bitstring;\n" q.f_name)
    proto.comNames;
  pp "( !\n";
  (* Multiple identities *)
  List.iter 
    (fun q -> Printf.printf "%snew %s : bitstring;\n" indent q.f_name)
    proto.idNames;  
  (* Multiple sessions *)
  displayMultipleSessions ();
  pp ")\n";
  if proto.idNamesANO <> [] 
  then begin
      pp " | (!\n";
      (* Multiple identities whose idNamesANO are revealed *)
      List.iter 
	(fun q -> Printf.printf "%snew %s : bitstring;\n" indent q.f_name)
	proto.idNames;  
      (* Revealed idNamesANO *)
      List.iter 
	(fun q -> Printf.printf "%sout(c, %s);\n" indent q.f_name)
	proto.idNamesANO;  
      (* Multiple sessions *)
      displayMultipleSessions ();
      pp ")\n";
    end

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
	    then failwith ("Should never happen [12]."^email)
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
(* We suppose here that session names are not shared between agents. *)
let pushNames proto = 
  let sessNames = List.tl proto.sessNames in
  let sessNameEvent = List.hd proto.sessNames in
  (* Add restriction of names for names in 'names' *)
  let addNames names continuationProc = 
    List.fold_right (fun name proc ->
		     Restr(name, 
			   (None, Stringmap.StringMap.empty),
			   proc,makeOcc()))
		    names
		    continuationProc in
  (* push all names as close as possible to their first use *)
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
    | Let (patx,t,pt,pe,occ) -> (* is there a needed name in accNames ? Here, we should
                                   avoid to interleave creation of names and Let/If constructs
                                   (to avoid conflicting with display.ml hack for FO).
                                   We thus check for all next Let/Test. *)
       let rec accTermsTests acc = function
	 | Let (_,t',pt',_,_) -> accTermsTests (t' :: acc) pt'
         | Test (t',pt',_,_) -> accTermsTests (t' :: acc) pt'
	 | _ -> acc in
       let nextTermsTests = accTermsTests [t] pt in
       let needNames = List.filter (fun name ->
				    List.exists (fun term -> Terms.occurs_f name term) nextTermsTests
				   ) accNames in
       if needNames <> []
       then 
	 let otherNames = List.filter (fun n -> not(List.mem n needNames)) accNames in
	 addNames needNames (Let (patx,t,pushN otherNames pt, pushN otherNames pe, occ))
       else Let (patx,t,pushN accNames pt, pushN accNames pe, occ)
    | Test (t,pt,pe,occ) -> (* is there a needed name in accNames ? *)
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
    | Par (_,_) as p -> errorClass ("[UKANO] [pushN] [PAR] Critical error, should never happen [2]."^email) p
    | Restr (_,_,_,_) as p -> errorClass ("[UKANO] [pushN] [Restr] Critial error, should never happen [14]."^email) p
    | p -> errorClass ("[UKANO] [pushN] Critical error, should never happen [6]."^email) p in
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
    | p -> errorClass ("Critical error, should never happen [4]."^email) p in
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
				      
(** Display a whole ProVerif file checking well-authentication except for the theory (to be appended). *)      
let transWA proto p inNameFile nameOutFile = 
  let proto = cleanChoice proto in

  let (sessName,idName) =
    try (List.hd proto.sessNames, List.hd proto.idNames) (* 2 funSymb *)
    with _ -> errorClass "The protocol should have at least one identity name and one session name." p in
  let (sessTerm,idTerm) = FunApp (sessName, []), FunApp (idName, []) in (* argument of events describing session and identity *)
  let listEvents = ref [] in
  let iniPrefix, resPrefix = "I", "R" in
  let nameEvent prefixName nb actionName = Printf.sprintf "%s%s_%d" prefixName actionName nb in
  (* add an event on top of a process with args + in addition [idTerm,sessTerm] *)
  let addEvent name args p = 	
    let newArgs = idTerm :: sessTerm :: args in
    let event = makeEvent name newArgs in
    listEvents := (name, List.length newArgs) :: !listEvents;
    Event (event, p, makeOcc()) in

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
    let rec goThrough listTest listIn listOut = function (* rec. function adding events *)
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
	     if !verbose
	     then begin
		 pp (Printf.sprintf "Creation of event %s for consecutive tests ending with 'let (" nameEv);
		 Display.Text.display_pattern pat;
		 pp ") = ";
		 Display.Text.display_term t;
		 pp ")'.\n";
	       end;
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
	     if !verbose
	     then begin
		 pp (Printf.sprintf "Creation of event %s for consecutive tests ending with 'if (" nameEv);
		 Display.Text.display_term t;
		 pp ")'.\n";
	       end;
	     (Test(t,subProcEv,pe,occ), lTest, nbOut))
      | Nil -> (Nil, List.rev listTest, List.length listOut)
      | _ -> failwith ("Critical error: transWA is applied on a protocol that does not satisfy the syntactical restrictions. Should never happen [7]."^email) in
    goThrough [] [] [] proc in

  (* Generate a string for a query (depends on whether shared or not, number of actions before events, nb of in, role) *)
  let generateQuery isShared nb nbIn isInitiator =
    let prefix = if isShared
		 then "query k:bitstring, n1:bitstring, n2:bitstring,\n"
		 else "query k1:bitstring, k2:bitstring, n1:bitstring, n2:bitstring,\n" in
    let nbArgs = if isInitiator	(* number of arguments to declare for this query *)
		 then 2*nbIn
		 else max (2*nbIn-1) 0 in
    let rec range = function | 0 -> [] | n -> n :: range (n-1) in
    let listArgs nb = 		(* generate a list of messages to give as arguments to events *)
      List.map (fun n -> Printf.sprintf "m%d" n) (List.rev (range nb)) in      
    let allListArgs nb role = 	(* glue all arguments together for types of queries *)
      if isShared
      then "k" :: (if role==iniPrefix then "n1" else "n2") :: (listArgs nb)
      else (if role==iniPrefix then "k1" else "k2") ::
	     (if role==iniPrefix then "n1" else "n2") :: (listArgs nb) in
    let listArgsDec = listArgs nbArgs in      
    let prefixArgs = "      "^
		       (String.concat ", "
				      (List.map (fun s -> Printf.sprintf "%s:bitstring" s) listArgsDec))
		       ^";\n" in
    let dual (p1,p2) = p2,p1 in
    let roles = iniPrefix,resPrefix in
    let dualRoles = dual roles in
    let rec produceEvents = function (* produce the nested events in -> out -> in ... *)
      |	0 -> []
      | n  -> 
	 let outRole, inRole = if (n mod 2) = 0 then dualRoles else roles in (* involved roles depend on parity *)
	 let n' = if (n mod 2) = 0 then n/2 else n/2+1 in
	   (* if (n mod 2) = 0 then n-1 else n in *)
	 (Printf.sprintf "event(%s(%s))" (nameEvent inRole n' "in") (String.concat "," (allListArgs n inRole)))
	 ::
	   (Printf.sprintf "event(%s(%s))" (nameEvent outRole n' "out") (String.concat "," (allListArgs n outRole)))
	 ::
	   produceEvents (n-1) in
    let listEvents = produceEvents (if isInitiator then 2*nbIn else max (2*nbIn-1) 0) in
    let thisRole = if isInitiator then fst roles else snd roles in
    let lastEvent = Printf.sprintf "event(%s(%s))" (* the first event before the nested events in -> out ... *)
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
  (* Adding events IN roles *)
  let iniEvents,iniTests,iniNbOut = addEventsRole proto.ini iniPrefix true in
  let resEvents,resTests,resNbOut = addEventsRole proto.res resPrefix false in
  let protoEvents = { proto with
		      ini = iniEvents;
		      res = resEvents;
		    } in
  let toDisplay = pushNames protoEvents in
  let isShared = List.length proto.idNamesShared > 0 in
  if not(isShared) && !verbose
  then pp "> Note: Since no session name is shared, we create events accordingly.";

  (* Generating queries *)
  let allQueries = (List.map (fun (nb,nbIn) -> generateQuery isShared nb nbIn true) iniTests) @ 
		     (List.map (fun (nb,nbIn) -> generateQuery isShared nb nbIn false) resTests) in

  (* Generating type declarations of events *)
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
  
  (* -- 3. -- Print everything using a HACK TO REDIRECT STDOUT *)
  (* BEGINNING OF REDIRECTION *)
  let old_descr = Unix.dup Unix.stdout in
  let newstdout = open_out nameOutFile in
  print_newline ();		(* for flushing stdout *)
  Unix.dup2 (Unix.descr_of_out_channel newstdout) Unix.stdout;
  (* Print (=write in the file) the complete ProVerif file *)
(*  pp "\n\n(* == THEORY == *)\n"; *)
  pp "\n(********   This file has been automatically generated using the tool UKano. It encodes the well-authentication condition. ********)\n\n";
  pp theoryStr;
  pp " *)\n";
  pp "\n\n(* == DECLARATIONS OF EVENTS == *)\n";
  displayEventsDec !listEvents;
  pp "\n\n(* == DECLARATIONS OF QUERIES == *)\n";
  List.iter (fun s -> Printf.printf "%s\n" s) allQueries;
  pp "\n\n(* == PROTOCOL WITH EVENTS == *)\n";
  pp "let SYSTEM =\n";
  displayProtocolProcess toDisplay;
  Printf.printf ".\nprocess SYSTEM\n%!";
  flush_all ();
  close_out newstdout;
  Unix.dup2 old_descr Unix.stdout
(* END OF REDIRECTION *)


(************************************************************)
(* Handling nonce versions & checking Frame Opacity         *)
(************************************************************)
(** Some symbols we shall add *)
(* CHECK: works like this, better would be to understand what are those flags for *)
let choiceSymb = {
    f_name = "choice";
    f_type = ([typeBit;typeBit], typeBit);
    f_cat = Choice;
    f_initial_cat = Choice;
    f_private = false;		(* CHECK* *)
    f_options = 0;		(* CHECK* *)
  }
let letCatchSymb = {
    f_name = "";
    f_type = ([typeBit;typeBit;typeBit], typeBit);
    f_cat = LetCatch;
    f_initial_cat = LetCatch;
    f_private = true;		(* CHECK* *)
    f_options = 0;		(* CHECK* *)
  }
let hole_of_str s =
  FunApp
    ( {
	f_name = "hole__"^s;
	f_type = ([], typeBit);
	f_cat = Hole;
	f_initial_cat = Hole;
	f_private = true;
	f_options = 0;		(* CHECK* *)
      }
    , [])
let hole = hole_of_str ""
let hole_of_name f = hole_of_str f.f_name

let mergeOut = {
    sname = "mergeOut";
    vname = 0;
    unfailing = true;
    btype = typeBit;
    link = NoLink;
  }
		 
let debugF_type (tl,t) = ""

let displayCat = function
  | Tuple -> "Tuple"
  | Name _ -> "Name"
  | _ -> failwith ("Critial error [45]."^email)

let debugFunSymb f = 
  Printf.printf 
    "Funsym[ name:%s, f_type:%s, f_cat: %s f_private %b f_options:%d]"
    f.f_name
    (debugF_type f.f_type)
    (displayCat f.f_cat)
    f.f_private
    f.f_options
    
(** Display a whole ProVerif file checking the first condition except for the theory (to be appended). *)      
let transFO proto p inNameFile nameOutFile = 

  (* -- 1. -- Build idealized versions of outputson the right and check conformity *)
  let nonTransparentSymbList = ["enc"; "aenc"; "dec"; "adec"; "h"; "hash"; "xor"; "dh"; "exp"; "mac"] in
  let isArity0 funSymb = match funSymb.f_type with | ([], _) -> true | _ -> false in
  let isName funSymb = match funSymb.f_cat with Name _ -> true | _ -> false in
  let isSessName funSymb = List.mem funSymb proto.sessNames in
  let isName funSymb = List.mem funSymb (proto.comNames @ proto.idNames @ proto.sessNames) in
  let isConstant funSymb = isArity0 funSymb && not(isName funSymb) in
  let isPrivate funSymb = funSymb.f_private in
  let isTuple funSymb = match funSymb.f_cat with Tuple -> true | _ -> false in
  let isChoice funSymb = funSymb.f_name = "choice" in
  let isHole funSymb = funSymb.f_cat = Hole || funSymb.f_name = "hole" in
  (* Given a term, tries to guess an idealization *)
  let rec guessIdeal listVarIn = function
    | FunApp (f, []) as t
	 when isConstant f -> t (* public constants *)
    | FunApp (f, []) as t
	 when isSessName f -> t (* session name *)
    | FunApp (f, []) when isName f -> hole_of_name f (* (private) names *)
    | FunApp (f, listT)
	 when isTuple f -> FunApp (f, List.map (guessIdeal listVarIn) listT) (* tuple *)
    | FunApp (f, listT) as t ->
       let recT =		(* try to go through if f\notin E *)
	 if List.exists (fun s -> f.f_name = s) !Pitsyntax.funSymb_equation (* if there is a match with a function in equation *)
	 then hole
	 else FunApp (f, List.map (guessIdeal listVarIn) listT)  in
       if !Param.ideaFullSyntax
       then FunApp (f, List.map (guessIdeal listVarIn) listT)
       else (if !Param.ideaGreedy (* depends on options *)
	     then  hole
	     (* (if List.mem f.f_name nonTransparentSymbList (* should be non-transparent *)
	         then hole
   	         else recT) *)
	     else recT)
    | Var b as t when List.mem b.sname listVarIn -> t  (* variable of input *)
    | Var b -> hole_of_str b.sname (* variable of let *)
    | term -> (* if true then begin log "Warning: some idealized messages you gave do not use 'hole' and are extended. The idealization of : "; *)
       (* 	  Printf.printf "     "; *)
       (* 	  Display.Text.display_term term; *)
       (* 	  Printf.printf "\n"; *)
       (* 	  log "will be itself.\n"; *)
       (* 	  term; end else*)
       begin
	 log "WARNING: no idealisation was given for an output and UKano's heuristics failed to guess one. For the sake of soundness, we let the idealisation of : ";
	 Printf.printf "     ";
	 Display.Text.display_term term;
	 Printf.printf "   ";
	 pp "be a hole (i.e., fresh session name variable).\n";
	 hole;
       end in
  (* Given a term, check that its corresponds to a conform idealization.
   [insidehonest] describes if this output is inside the honest execution (i.e., not in else nor at
   the end of honest execution). *)
  let checkIdeal inHonest listVarIn t =
    let rec checkSyntax  = function
      | FunApp (f, []) when isConstant f -> true (* public constants *)
      | FunApp (f, []) when isHole f -> true     (* hole *)
      | FunApp (f, []) when (isName f && List.mem f proto.sessNames)
	-> true   (* session name *)
      | FunApp (f, []) when isName f -> false   (* (identity and global) names *)
      | FunApp (f, tl) ->
	 (* For debugging purposes: *)
	 (* List.iter (fun f -> Printf.printf "%s, " (\* Display.Text.display_function_name *\) f) !Pitsyntax.funSymb_equation; *)
	 if not(!Param.ideaFullSyntax) &&
	      List.exists (fun s -> f.f_name = s) !Pitsyntax.funSymb_equation (* if there is a match with a function in equation *)
	 then false		(* function in E *)
	 else List.for_all checkSyntax tl (* ok, pursue *)
      | Var b when List.mem b.sname listVarIn -> true  (* variable of input *)
      | Var b -> false	in	              	       (* variable of let *)
    let rec checkOneName = function
      | Var b -> false				 (* variable *)
      | FunApp (f, []) when isHole f -> true     (* hole *)
      | FunApp (f, []) when isName f && List.mem f proto.sessNames
	-> true   (* session name *)
      | FunApp (f, []) when isName f -> false   (* (private) names *)
      | FunApp (f, []) when isConstant f -> false (* public constants *)
      | FunApp (f, tl) -> List.exists checkOneName tl in (* ok, pursue *)
    if checkSyntax t
    then if !Param.ideaFullSyntax
	 then true		(* we will print a warning message in the only problematic case (=shared case)  *)
	 else (not(inHonest) || checkOneName t)
    else false in
  let suffix = ref "I" in	(* to create injective idealised nonces (\neq for roles) *)
  let countHoles = ref 0 in	(* to create injective idealised nonces from holes *)
  let listNameNames = ref [] in	(* assoc list: names of nonces -> 'idealized' name *)
  let listNewNames = ref [] in	(* created new nonces *)
  (* Create the next new session name to fill in a hole *)
  let rec inListName funSymb = function
    | [] -> false
    | x :: tl when x.f_name = funSymb.f_name -> true
    | x :: tl -> inListName funSymb tl in
  let createNonce funSymb = 
    let nameName =
      if funSymb.f_name == "hole"
      then begin
	  incr(countHoles);
	  Printf.sprintf "hole__%d" !countHoles;
	end else (if not(List.mem_assoc funSymb.f_name !listNameNames)
		  then begin
		      let s = Printf.sprintf "%s_%s" funSymb.f_name !suffix in (* need to avoid clash between two roles e.g., *)
		      listNameNames := (funSymb.f_name,s) :: !listNameNames;
		      s
		    end else List.assoc funSymb.f_name !listNameNames ) in 
    let newFunSymb =
      {
	f_name = nameName;
	f_type = ([],typeBit);
	f_cat =  Name { prev_inputs = None; prev_inputs_meaning = []};
	f_initial_cat = Name { prev_inputs = None; prev_inputs_meaning = []};
	f_private = true;
	f_options = 0
      } in
    if not(inListName newFunSymb !listNewNames)
    then listNewNames := newFunSymb :: !listNewNames;
    FunApp (newFunSymb, []) in
  (* idealized term -> nonce term *)
  let rec noncesTerm = function
    | FunApp (f, tList) when isHole f -> createNonce f
    | FunApp (f, tList) -> FunApp (f, List.map noncesTerm tList)
    | Var b -> Var b
    | t -> errorClass ("Critical error, should never happen [3]."^email) p in
  (* idealized process (some idealized output may miss) -> use heuristics from guessIdeal *)
  let ideaChecked = ref false in	(* whether given idealizations have been checked  *)
  (* [isIni] specifies whether the process is the initiator process or not *)
  let rec noncesProc ?inElse:(inE=false) isIni listVarIn = function
    | Nil -> Nil
    | Input (tc,patx,p,occ) ->
       let nameVar = match patx with
	 | PatVar binder -> binder.sname
	 | _ -> failwith ("Critical error."^email) in
       Input(tc,patx, noncesProc isIni (nameVar :: listVarIn) p, occ)
    | Output (tc,tm,p,occ) ->
       let lastOutHonest = match p with
	 | Nil -> if !isLastOutputByIni then isIni else not(isIni)
	 | _ -> false in
       let inHonest = not(inE) && not(lastOutHonest) in
       let (tmReal, tmIdeal) =
	 match tm with
	 | FunApp (funSymb, tm1 :: tm2 :: tl) when (!Param.ideaAutomatic && isChoice funSymb) ->
	    let tmIdeal = guessIdeal listVarIn tm1 in (* he did give an idealization but we'll recompute it *)
	    if checkIdeal inHonest listVarIn tmIdeal
	    then (tm1, tmIdeal)
	    else failwith ("Critial Error [458]."^email)
	 | FunApp (funSymb, tm1 :: tm2 :: tl) when (not(!Param.ideaAutomatic) && isChoice funSymb) ->
	    if !ideaAssumed || checkIdeal inHonest listVarIn tm2
	    then begin ideaChecked := true; (tm1, tm2); end (* user already built idealization and no option 'ideaAutomatic' *)
	    else begin pp "[ERROR] The following idealisation you built is not conform: ";
		       Display.Text.display_term tm2;
		       pp ".\n";
		       exit(2);
		 end
	 | _ -> let tmIdeal = guessIdeal listVarIn tm in (* he did not, we need to guess it *)
		if checkIdeal inHonest listVarIn tmIdeal
		then (tm, tmIdeal) 
		else failwith ("Critial Error [458]."^email) in
       (* if false then begin pp "\n";  *)  (* For debugging purpose: *)
       (* 			(match tm with | FunApp (f, li) -> debugFunSymb f); *)
       (* 			pp "\n"; Display.Text.display_term tm; *)
       (* 			pp " -> "; Display.Text.display_term (guessIdeal tm);  pp "\n"; *)
       (* 		  end; *)
       let tmNonce = noncesTerm tmIdeal in
       let tmChoice = FunApp (choiceSymb, [tmReal; tmNonce]) in
       Output(tc, tmChoice , noncesProc isIni listVarIn p, occ)
    | Let (patx,t,pt,pe,occ) -> Let (patx,t, noncesProc isIni listVarIn pt, noncesProc ~inElse:true isIni listVarIn pe, occ)
    | Test (t,pt,pe,occ)-> Test(t, noncesProc isIni listVarIn pt, noncesProc ~inElse:true isIni listVarIn pe,occ)
    | p -> errorClass ("Critical error, should never happen [5]."^email) p in
  let newIni = noncesProc true [] proto.ini in
  suffix := "R";
  listNameNames := [];
  let newRes = noncesProc false [] proto.res in
  let noncesProto = 
    { proto with
      ini = newIni;
      res = newRes;
      sessNames = proto.sessNames @ (List.rev !listNewNames);
    } in

  if !verbose && !ideaChecked
  then (if !ideaAssumed
	then log "Remember that we do not check that idealisations are conform (option '--idea-no-check'). You should check this yourself by inspecting the produced file."
	else log "All idealisations (including the ones you gave as input) have been checked (i.e., only constants, session names, holes, variables bind by inputs and functions not in E) and at least one hole or a session name in each idealised output (except in else branches and last honest output).");

  if !verbose && !Param.ideaFullSyntax
  then (let isShared = List.length proto.idNamesShared > 0 in
	if isShared
	then log "WARNING: you used the option '--idea-full-syntax' for a protocol in the shared case. Therefore, you should check condition Well-Authentication item (ii) separately.");
	 
	 
  (* -- 2. -- Deal with conditionals (should not create false attacks for diff-equivalence) *)
  (* a) we push conditionals (Test and Let) and put them just before Output (when needed)
     b) we use a hack to be sure the 'Let' construct will never fail:
             let yn = dec(x,k) in
             out(c, choice[yn,idealization]
        will be translated to
             let mergeOut = let yn = dec(x,k) in
                              choice[yn,iealization]
                            else iedalization in
             out(c, mergeOut).
        Function cleanTest cannot produce nested let (it is actually syntactic sugar
        and have no internal representation). We thus use a flag using a special funsymb
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
    | p -> errorClass ("Critical error, should never happen."^email) p in
  let condFOProto = 
    { noncesProto with
      sessNames = proto.sessNames @ (List.rev !listNewNames);
      ini = cleanTest [] [] noncesProto.ini;
      res = cleanTest [] [] noncesProto.res;
    } in

  (* -- 3. -- GET the theory part of inNameFile *)
  let theoryStr = theoryStr inNameFile in

  (* -- 4. -- Print evrything using a HACK TO REDIRECT STDOUT *)
  let old_descr = Unix.dup Unix.stdout in
  let newstdout = open_out nameOutFile in
  print_newline ();		(* for flushing stdout *)
  Unix.dup2 (Unix.descr_of_out_channel newstdout) Unix.stdout;
  (* Print (=write in the file) the complete ProVerif file *)
  (*  pp "\n\n(* == THEORY == *)\n"; *)
  pp "\n(********   This file has been automatically generated using the tool UKano. It encodes the frame opacity condition. ********)\n\n";
  pp theoryStr;
  pp " *)\n";
  pp "\n\n(* == PROTOCOL WITH IDEALISATION == *)\n";
  pp "let SYSTEM =\n";
  let toDisplay = pushNames condFOProto in
  displayProtocolProcess toDisplay;
  Printf.printf ".\nprocess SYSTEM\n%!";
  close_out newstdout;
  Unix.dup2 old_descr Unix.stdout
(* END OF REDIRECTION *)


let printHelp path =
  if !verbose
  then pp (Printf.sprintf "If you want to manually verify the condition, launch 'proverif -in pitype %s'.\n" path)
     
(** [transBoth p inNameFile outNameFileFO outNameFileWA] writes in the files [outNameFile*] complete ProVerif files checking respectively
frame opacity and well-authentication for the process [p] and the theory contained in [inNameFile]. *)
let transBoth  p inNameFile nameOutFileFO nameOutFileWA = 
  verbose := not(!Param.shortOutput);
  ideaAssumed := !Param.ideaAssumed;
  if !verbose then pp (Display.title "GENERATION OF MODELS ENCODING SUFFICIENT CONDITIONS");
  
  if !verbose
  then begin pp (Display.header "Parsing of the input model");
	     pp "\n";
       end;
  let proto1 = extractProto p in
  let proto2 = { proto1 with
		 ini = proto1.ini;
		 res = proto1.res } in  
  if !verbose
  then begin
      pp (Printf.sprintf "2-Party protocol extracted from your input model %s:\n"
			 (if !Param.has_choice then "(choice[ul,ur]'\nspecifies that 'ul' is the real output and 'ur' is the idealisation)" else ""));
      displayProtocol proto1;
      if false			(* debug *)
      then pp (Printf.sprintf "Is Initiator the role that outputs the last message in the honest execution? --> %b\n" !isLastOutputByIni );
    end;
  
  if not(!Param.onlyWA)
  then begin
      if !verbose then begin pp (Display.header "Generation of the model encoding frame opacity"); pp"\n"; end;
      transFO proto1 p inNameFile nameOutFileFO;
      pp (Display.result (Printf.sprintf "A ProVerif model encoding the frame opacity condition has been written in %s." nameOutFileFO));
      if !verbose then pp "\n";
      printHelp nameOutFileFO;
    end;

  if not(!Param.onlyFO)
  then begin
      if !verbose then begin
	  pp (Display.header "Generation of the model encoding well-authentication");  
	  pp "\n";
	end;
      transWA proto2 p inNameFile nameOutFileWA;
      pp (Display.result (Printf.sprintf "A ProVerif model encoding the well-authentication condition has been written in %s.\n" nameOutFileWA));
      printHelp nameOutFileWA;
    end;
  proto1.idNamesANO
