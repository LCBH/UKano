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
open Stringmap

let get_event_status_internal event_status_table f =
  try
    Hashtbl.find event_status_table f
  with Not_found ->
    Parsing_helper.internal_error ("event not found " ^ (Display.string_of_fsymb f))


let get_event_status pi_state f =
  match pi_state.pi_event_status_table with
  | Unset ->
     Parsing_helper.internal_error "event_status_table should be set before Pievent.get_event_status"
  | Set event_status_table ->
     get_event_status_internal event_status_table f


let set_event_status state =
  let event_status_table = Hashtbl.create 7 in

  let event_in_nested_premise = ref [] in

  (* When the "end" event is present and the "begin" event is injective,
     we set the "end" event injective as well, so that it has the
     same occurrence argument as the "begin" event, and we can remove
     the "begin" event from the clause that concludes "end" *)
  let set_event_status_e set_end set_begin = function
    | QSEvent(b,_,_,FunApp(f,_)) ->
      let fstatus = get_event_status_internal event_status_table f in
      if set_end then
        begin match b with
          | Some _ ->
              fstatus.end_status <- Inj
          | _ ->
              if fstatus.end_status = No
              then
                if fstatus.begin_status = Inj
                then fstatus.end_status <- Inj
                else fstatus.end_status <- NonInj
              else ()
        end;
      if set_begin then
        begin match b with
          | Some _ ->
              fstatus.begin_status <- Inj;
              if fstatus.end_status = NonInj
              then fstatus.end_status <- Inj
          | _ -> if fstatus.begin_status = No then fstatus.begin_status <- NonInj
        end
    | QSEvent2(FunApp(f,_),_) ->
        let fstatus = get_event_status_internal event_status_table f in
        if set_end
        then fstatus.end_status <- NonInj;
        if set_begin
        then fstatus.begin_status <- NonInj
    | _ -> ()
  in

  let rec set_event_status_r set_begin = function
    | Before(e, concl_q) ->
       List.iter (set_event_status_e true set_begin) e;
       set_event_status_c concl_q

  and set_event_status_c = function
    | QTrue
    | QFalse -> ()
    | QEvent e -> set_event_status_e false true e
    | NestedQuery (Before([QSEvent(_,_,_,FunApp(f,_))],_) as q) ->
        if not (List.memq f !event_in_nested_premise)
        then event_in_nested_premise := f:: !event_in_nested_premise;
        set_event_status_r true q
    | NestedQuery _ -> Parsing_helper.internal_error "[pievent.ml >> set_event_status] Nested query must only have one event as premise."
    | QAnd(concl1,concl2)
    | QOr(concl1,concl2) ->
        set_event_status_c concl1;
        set_event_status_c concl2
  in

  let set_event_status1 = function
    | PutBegin(i, l) ->
       List.iter (fun f ->
         let fstatus = get_event_status_internal event_status_table f in
         if i then fstatus.begin_status <- Inj else
           if fstatus.begin_status = No then fstatus.begin_status <- NonInj) l
    | RealQuery (q,_) ->
       set_event_status_r false q
    | QSecret _ ->
       ()
  in

  let set_event_status_q = function
    | QueryToTranslate _ ->
       Parsing_helper.internal_error "query should be translated before Pievent.set_event_status"
    | CorrespQuery(ql,_) ->
       List.iter set_event_status1 ql
    | CorrespQEnc(qql,_) ->
       List.iter (fun (_,q) -> set_event_status1 q) qql
    | ChoiceQEnc _ | ChoiceQuery | NonInterfQuery _ | WeakSecret _ ->
       ()
  in

  List.iter (fun d ->
      Hashtbl.add event_status_table d { end_status = No; begin_status = No }
    ) state.pi_events;

  (* Setting the events inside queries *)
  begin
    match state.pi_process_query with
      Equivalence _ -> ()
    | SingleProcess(p, ql) ->
       List.iter set_event_status_q ql
    | SingleProcessSingleQuery(_, q) ->
       set_event_status_q q
  end;

  (* Checking events in premise of nested queries.
     When an event is injective somewhere and appears in a premise
     of a nested query, we consider it injective both as begin and end.
     That improves precision for nested queries that mix injective
     and non-injective events. *)
  List.iter (fun f ->
    let fstatus = get_event_status_internal event_status_table f in
    if fstatus.end_status = Inj || fstatus.begin_status = Inj
    then
      begin
        fstatus.end_status <- Inj;
        fstatus.begin_status <- Inj
      end
  ) !event_in_nested_premise;

  { state with pi_event_status_table = Set event_status_table }

let update_event_status_with_lemmas state =
  let event_status_table = match state.pi_event_status_table with
    | Unset ->
       Parsing_helper.internal_error "[pievent.ml >> update_event_status_with_lemmas] Event_status_table should be set before update it with lemmas"
    | Set event_status_table -> event_status_table
  in

  (* Setting the events inside lemmas *)

  let set_event_status_e = function
    | QSEvent(_,_,_,FunApp(f,_)) | QSEvent2(_, FunApp(f,_)) ->
        let fstatus = get_event_status_internal event_status_table f in
        if fstatus.begin_status = No then fstatus.begin_status <- NonInj
    | _ -> ()
  in

  let rec set_event_status_c = function
    | QTrue
    | QFalse -> ()
    | QEvent e -> set_event_status_e e
    | NestedQuery _ -> Parsing_helper.internal_error "[pievent.ml >> update_event_status_with_lemmas] Lemmas should not contain nested queries at this point (should have been translated into conjunction)"
    | QAnd(concl1,concl2)
    | QOr(concl1,concl2) ->
        set_event_status_c concl1;
        set_event_status_c concl2
  in

  let set_event_status_r = function
    | Before(e, concl_q) ->
        List.iter set_event_status_e e;
        set_event_status_c concl_q
  in

  List.iter (function
    | LemmaToTranslate _ -> Parsing_helper.internal_error "[pievent.ml >> update_event_status_with_lemmas] Lemmas should have been translated at that point."
    | Lemma l_state ->
        List.iter (fun lem -> match lem.ql_query with
          | RealQuery(real_q,[]) -> set_event_status_r real_q
          | _ -> Parsing_helper.user_error "[pievent.ml >> update_event_status_with_lemmas] Lemmas should have been encoded at this point."
        ) l_state.lemmas
  ) state.pi_lemma
