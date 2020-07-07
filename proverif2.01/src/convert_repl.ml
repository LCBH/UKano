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
(* This file converts replications in the style of the interactive
   simulator (each replication of !P creates one copy P and keeps the
   initial process !P) to the style used in trace reconstruction
   (replication of !P n times creates n copies of P and !P disappears).
   To be used before graphical display of traces. *)

open Types
open Pitypes
open Reduction_helper

type repl_status =
  | NoRepl
  | CopiedRepl of int

(* Both [future_copies] and [rem_copies] are lists with one
 * element for each process in the state coming from
 * the interactive simulator. This element determines how
 * the corresponding process is replicated.
 *
 * In [future_copies],
 * [NoRepl] means that the process is not a replication.
 * [CopiedRepl(k)] means that the process is a replication that will
 * be copied [k] times in the future steps of the trace. Replications
 * are initialized to [CopiedRepl(0)] at the end of the trace.
 * [future_copies] is computed backwards.
 *
 * In [rem_copies],
 * [NoRepl] means that the process is not a replication, or is a
 * replication that has not been copied yet.
 * [CopiedRepl(k)] means that the process is a replication that
 * has already been copied at least once, and that there remains
 * [k] copies to make in the future steps of the trace.
 * [rem_copies] is computed forwards.
 *)

(* The indices of processes are renumbered due to the change of
   replication stye.
   [ind_map] is an array that maps the old indices to the new
   indices.
   [update_loc], [update_ni_goal], [update_goal], [update_div],
   [update_comment] update the respective elements of the
   trace with the new indices. *)

let update_loc ind_map = function
  | (LocAttacker _) as x -> x
  | LocProcess(n, proc) -> LocProcess(ind_map.(n), proc)

let update_ni_goal ind_map = function
  | (ApplyTest _ | NIFailTest _ | NIEqTest _) as x -> x
  | ProcessTest(hl, hypl, loc) ->
     ProcessTest(hl, hypl,
                 match loc with
                 | None -> None
                 | Some(n, proc) -> Some(ind_map.(n), proc))
  | InputProcessTest(hl, hypl, mess, loc) ->
     InputProcessTest(hl, hypl, mess,
                      match loc with
                      | None -> None
                      | Some(n, proc, loc_out) ->
                         Some(ind_map.(n), proc, update_loc ind_map loc_out))
  | CommTest(ch_in, ch_out, loc) ->
     CommTest(ch_in, ch_out,
              match loc with
                      | None -> None
                      | Some(loc_in, loc_out) ->
                         Some(update_loc ind_map loc_in, update_loc ind_map loc_out))

let update_goal ind_map = function
  | (CorrespGoal _ | WeakSecrGoal _ | NoGoal) as x -> x
  | NonInterfGoal g -> NonInterfGoal(update_ni_goal ind_map g)

let update_div ind_map = function
  | DEval(s, i, t, n, proc) -> DEval(s, i, t, ind_map.(n), proc)
  | DEvalOut(i, t1, t2, n, proc) -> DEvalOut(i, t1, t2, ind_map.(n), proc)
  | DEvalLet(i, t, pat, n, proc) -> DEvalLet(i, t, pat, ind_map.(n), proc)
  | DEvalFact(i, f, n, proc) -> DEvalFact(i, f, ind_map.(n), proc)
  | DTest(i, elsenil, fst, snd, t, n, proc) -> DTest(i, elsenil, fst, snd, t, ind_map.(n), proc)
  | DLetFilter(i, elsenil, fact, n, proc) -> DLetFilter(i, elsenil, fact, ind_map.(n), proc)
  | DGet(i, term, pat, t, n, proc) -> DGet(i, term, pat, t, ind_map.(n), proc)
  | DInputPat(i, recipe, result, pat, n, proc) -> DInputPat(i, recipe, result, pat, ind_map.(n), proc)
  | DIOPat(i, t, t', pat, nin, pin, nout, pout) -> DIOPat(i, t, t', pat, ind_map.(nin), pin, ind_map.(nout), pout)
  | DIO(i, cin, cout, nin, pin, nout, pout) -> DIO(i, cin, cout, ind_map.(nin), pin, ind_map.(nout), pout)
  | DChannel(s, i, ch, ch_result, recipe, result, n, proc) -> DChannel(s, i, ch, ch_result, recipe, result, ind_map.(n), proc)
  | (DFail _ | DEquality _) as x -> x
  | DOutputMess(mess, eval_mess, recipe, n, proc, div) ->
     DOutputMess(mess, eval_mess, recipe, ind_map.(n), proc, div)
       (* No need to update [div] here since it is always
          [DFail] or [DEquality] *)

let update_comment ind_map future_copies1 = function
  | (RRestrAtt _ | RAddpub _ | RInit | RPhase _) as x -> x
  | RNil(n) -> RNil(ind_map.(n))
  | RPar(n) -> RPar(ind_map.(n))
  | RRepl(n,_) ->
     begin
       match List.nth future_copies1 n with
       | CopiedRepl(k) -> RRepl(ind_map.(n), k)
       | NoRepl -> assert false
     end
  | RRestr(n,f,t) -> RRestr(ind_map.(n),f,t)
  | RLet_In(n,pat,t) -> RLet_In(ind_map.(n),pat,t)
  | RLet_Else(n,pat,t) -> RLet_Else(ind_map.(n),pat,t)
  | RLet_Remove(n,pat,t) -> RLet_Remove(ind_map.(n),pat,t)
  | RInput_Success(n, tc, pat, calc, mess_term) -> RInput_Success(ind_map.(n), tc, pat, calc, mess_term)
  | RInput_PatFails(n, tc, pat, calc, mess_term) -> RInput_PatFails(ind_map.(n), tc, pat, calc, mess_term)
  | RInput_Remove(n, tc, pat, cause) -> RInput_Remove(ind_map.(n), tc, pat, cause)
  | ROutput_Success(n, tc, calc, t) -> ROutput_Success(ind_map.(n), tc, calc, t)
  | ROutput_Remove(n, tc, t, cause) -> ROutput_Remove(ind_map.(n), tc, t, cause)
  | RTest_Then(n,t) -> RTest_Then(ind_map.(n),t)
  | RTest_Else(n,t) -> RTest_Else(ind_map.(n),t)
  | RTest_Remove(n,t,cause) -> RTest_Remove(ind_map.(n),t,cause)
  | REvent_Success(n, t, b) -> REvent_Success(ind_map.(n), t, b)
  | REvent_Remove(n, t, cause) -> REvent_Remove(ind_map.(n), t, cause)
  | RLetFilter_In(n, bl, tl, f) -> RLetFilter_In(ind_map.(n), bl, tl, f)
  | RLetFilter_Else(n, bl, f) -> RLetFilter_Else(ind_map.(n), bl, f)
  | RLetFilter_Remove(n, bl, f, cause) -> RLetFilter_Remove(ind_map.(n), bl, f, cause)
  | RIO(n, tc', pat, no, tc, may_calc, t, b) ->
     RIO(ind_map.(n), tc', pat, ind_map.(no), tc, may_calc, t, b)
  | RIO_PatRemove(n, tc', pat, no, tc, may_calc, t, b, input_fails) ->
     RIO_PatRemove(ind_map.(n), tc', pat, ind_map.(no), tc, may_calc, t, b, input_fails)
  | RInsert_Success(n, t, b) -> RInsert_Success(ind_map.(n), t, b)
  | RInsert_Remove(n, t, cause) -> RInsert_Remove(ind_map.(n), t, cause)
  | RGet_In(n, pat, t, m) -> RGet_In(ind_map.(n), pat, t, m)
  | RGet_Else(n, pat, t) -> RGet_Else(ind_map.(n), pat, t)
  | RGet_Remove(n, pat, t) -> RGet_Remove(ind_map.(n), pat, t)
  | RNamedProcess(n, s, tl) -> RNamedProcess(ind_map.(n), s, tl)
  | RDiverges div -> RDiverges(update_div ind_map div)

(* [copy_k k a l] adds [k] copies of [a] at the head of [l] *)

let rec copy_k k a l =
  assert (k>=0);
  if k = 0 then
    l
  else
    copy_k (k-1) a (a::l)

(* [copy_processes n n' ind_map rem_copies procl]
   takes as argument the list of processes [procl] with the old
   style of replication and returns the list of processes
   with the new style of replication.
   [rem_copies] determines the number of copies to
   make for each process:
   [NoRepl] -> keep the process as it is
   [CopiedRepl(k)] -> copy the process [k] times.
   This function also initializes the map of old to new
   indices [ind_map].
   It should be called with [n=0] (initial old index)
   and [n'=0] (initial new index). *)

let rec copy_processes n n' ind_map rem_copies procl =
  match procl, rem_copies with
    [],[] -> []
  | p::restp, copy1::rest_copy ->
     begin
     ind_map.(n) <- n';
     match copy1 with
       NoRepl ->
        p :: (copy_processes (n+1) (n'+1) ind_map rest_copy restp)
     | CopiedRepl(k) ->
        let rest = copy_processes (n+1) (n'+k) ind_map rest_copy restp in
        match p with
        | (Repl(p',_), _, _, _, _) ->
           (* Copy [p'] [k] times *)
           copy_k k (p', [], [], [], Nothing) rest
        | _ -> assert false
     end
  | _ -> (* Length error *) assert false

(* [initial_future_copies s] returns the initial value of
   [future_copies] for state s. *)

let initial_future_copies s =
  List.map (function
      | (Repl _, _, _, _, _) -> CopiedRepl(0)
      | _ -> NoRepl) s.subprocess

(* Main function that converts replications.
   Takes a argument the reduc_state [s0] generated by the
   interactive simulator, and the associated [future_copies]
   and returns the reduc_state [s0'] using replications
   in trace reconstruction style, as well as the [rem_copies]
   associated to [s0]. *)

let rec convert_repl_aux s0 future_copies0 =
  match s0.previous_state with
  | None ->
     (* Initial state *)
     (s0, [NoRepl])
  | Some s1 ->
     let future_copies1 =
       match s0.comment with
       | RRepl(n, cpn) ->
          (* In the interactive simulator, we always set cpn = 2,
             one for the newly created copy, one for the remaining
             replicated process *)
          assert(cpn == 2);
          begin
            match List.nth future_copies0 (n+1) with
            | CopiedRepl k ->
               replace_at n (CopiedRepl (k+1)) (remove_at n future_copies0)
            | NoRepl ->
               assert false
          end
       | RNil(n) | RInput_PatFails(n,_,_,_,_) | RInput_Remove(n,_,_,_)
         | ROutput_Remove(n,_,_,_) | RTest_Remove(n,_,_) | RLet_Remove(n,_,_) | REvent_Remove(n,_,_)
         | RLetFilter_Remove(n,_,_,_) | RInsert_Remove(n,_,_) | RGet_Remove(n, _, _) ->
          (* Process [n] terminates, so in [s1], there is one more
             process at [n], which disappears in [s0]. *)
          add_at n NoRepl future_copies0
       | RPar(n) ->
          replace_at n NoRepl (remove_at n future_copies0)
       | RRestrAtt _ | RAddpub _ | RDiverges _ ->
          future_copies0
       | RRestr(n,_,_) | RLet_In(n,_,_) | RLet_Else(n,_,_) | RInput_Success(n,_,_,_,_)
         | ROutput_Success(n,_,_,_) | RTest_Then(n,_) | RTest_Else(n,_) | REvent_Success(n,_,_)
         | RLetFilter_In(n,_,_,_) | RLetFilter_Else(n,_,_)
         | RInsert_Success(n,_,_) | RGet_In(n,_,_,_) | RGet_Else(n,_,_) 
         | RNamedProcess(n,_,_) ->
          replace_at n NoRepl future_copies0
       | RIO(n,_,_,n',_,_,_,_) ->
          replace_at n NoRepl (replace_at n' NoRepl future_copies0)
       | RIO_PatRemove(n,_,_,n',_,_,_,_,_) ->
          (* Input at [n] terminates; output at [n'] executed *)
          add_at n NoRepl (replace_at n' NoRepl future_copies0)
       | RInit ->
          (* RInit should happen only in the initial state *)
          assert false
       | RPhase(ph) ->
          initial_future_copies s1
     in
     let (s1', rem_copies1) = convert_repl_aux s1 future_copies1 in
     let rem_copies0 =
       match s0.comment with
       | RRepl(n,_) ->
          begin
            match List.nth rem_copies1 n with
            | NoRepl ->
               (* It is the first time we copy this replication.
                  Copy it as many times as we will do in the full trace *)
               begin
                 match List.nth future_copies0 (n+1) with
                 | CopiedRepl(k) ->
                    (* The process at [n] in [s1] will be copied
                       [(k+1)] times in [s0'].
                       In [s0], it is copied once at [n], with status
                       [NoRepl] and the replication appears at [n+1],
                       to be copied [k] times. *)
                    add_at (n+1) (CopiedRepl(k)) rem_copies1
                 | NoRepl ->
                    assert false
               end
            | CopiedRepl(k) ->
               assert (k>0);
               (* Already copied: we extract one more copy from the k copies
                  already existing *)
               add_at n NoRepl (replace_at n (CopiedRepl(k-1)) rem_copies1)
          end
       | RNil(n) | RLet_Remove(n,_,_) | RInput_PatFails(n,_,_,_,_) | RInput_Remove(n,_,_,_)
         | ROutput_Remove(n,_,_,_) | RTest_Remove(n,_,_) | REvent_Remove(n,_,_)
         | RLetFilter_Remove(n,_,_,_) | RInsert_Remove(n,_,_) | RGet_Remove(n, _, _) ->
          (* Process [n] terminates *)
          assert (List.nth rem_copies1 n == NoRepl);
          remove_at n rem_copies1
       | RPar(n) ->
          assert (List.nth rem_copies1 n == NoRepl);
          add_at n NoRepl rem_copies1
       | RRestrAtt _ | RAddpub _ | RDiverges _ ->
          rem_copies1
       | RRestr(n,_,_) | RLet_In(n,_,_) | RLet_Else(n,_,_) | RInput_Success(n,_,_,_,_)
         | ROutput_Success(n,_,_,_) | RTest_Then(n,_) | RTest_Else(n,_) | REvent_Success(n,_,_)
         | RLetFilter_In(n,_,_,_) | RLetFilter_Else(n,_,_)
         | RInsert_Success(n,_,_) | RGet_In(n,_,_,_) | RGet_Else(n,_,_)
         | RNamedProcess(n,_,_) ->
          assert (List.nth rem_copies1 n == NoRepl);
          rem_copies1
       | RIO(n,_,_,n',_,_,_,_) ->
          assert (List.nth rem_copies1 n == NoRepl);
          assert (List.nth rem_copies1 n' == NoRepl);
          rem_copies1
       | RIO_PatRemove(n,_,_,n',_,_,_,_,_) ->
          (* Input at [n] terminates; output at [n'] executed *)
          assert (List.nth rem_copies1 n == NoRepl);
          assert (List.nth rem_copies1 n' == NoRepl);
          remove_at n rem_copies1
       | RInit ->
          (* RInit should happen only in the initial state *)
          assert false
       | RPhase(ph) ->
          List.map (fun _ -> NoRepl) s0.subprocess
     in
     let s0' =
       match s0.comment with
       | RRepl(n,_) when (List.nth rem_copies1 n != NoRepl) ->
          (* Replication already copied, return the previous state *)
          s1'
       | _ ->
          let ind_map = Array.make (List.length future_copies0) 0 in
          let subproc' = copy_processes 0 0 ind_map rem_copies0 s0.subprocess in
          { s0 with
            previous_state = Some s1';
            subprocess = subproc';
            goal = update_goal ind_map s0.goal;
            comment = update_comment ind_map future_copies1 s0.comment }
     in
     (s0', rem_copies0)

let convert_repl s0 =
  let future_copies0 = initial_future_copies s0 in
  let (s0', _) = convert_repl_aux s0 future_copies0 in
  s0'
