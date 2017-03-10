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
(* Types module declares types of the abstract syntax
   tree and of sets of messages.
   There are recursive dependencies between these types,
   that is why they are included in the same module
*)

open Types

(* The type of processes has been moved to the module types.mli
   because it is needed in the environment values for letfun, and the
   environments are needed for terms in queries that cannot be
   expanded before process translation *)

(* Correspondence queries *)

type event =
    QSEvent of bool (* true when injective *) * term
  | QFact of predicate * term list
  | QNeq of term * term
  | QEq of term * term

type realquery = Before of event * hypelem list list

and hypelem =
    QEvent of event
  | NestedQuery of realquery

type query = 
    PutBegin of bool (* true when injective *) * funsymb list
  | RealQuery of realquery

type eventstatus =
    { mutable end_status : onestatus;
      mutable begin_status : onestatus }

(* Equivalence queries *)

type eq_query =
  | DestructorQuery
  | ChoiceQuery 
  | NonInterfQuery of (Types.funsymb * Types.term list option) list
  | WeakSecret of Types.funsymb

(* Types of reduction steps, for trace reconstruction *)

type reduc_type =
  | RNil of int
  | RPar of int 
  | RRepl of int * int
  | RRestr of int * funsymb * term
  | RLet1 of int * pattern * term 
  | RLet2 of int * pattern * term
  | RInput of int * term * pattern * term
  | ROutput1 of int * term * term 
  | ROutput2 of int * term * term
  | ROutput3 of int * term * term
  | RTest1 of int * term  
  | RTest2 of int * term 
  | RTest3 of int * term
  | RBegin1 of int * term
  | RBegin2 of int * term
  | REnd of int * term
  | RPhase of int
  | RLetFilter1 of int * binder list * fact 
  | RLetFilter2 of int * binder list * fact 
  | RLetFilter3 of int * binder list * fact 
  | RIO of int * term * pattern * int * term * term
  | RIO2 of int * term * pattern * int * term * term
  | RInsert1 of int * term 
  | RInsert2 of int * term
  | RGet of int * pattern * term * term
  | RGet2 of int
  | RInit

(* 'a may be term (for reduction.ml) or term * term (for reduction_bipro.ml) *)

type name_param_info = 
    arg_meaning * term * when_include

type 'a info = 
    InputInfo of 'a list * 'a list * 'a * name_param_info list * hypspec list * ('a * ('a list * 'a list) option) list
	(* Channel name after decomposition of tuples,
	   Public set of values at last test,
	   Channel name,
	   name_params, occs,
	   list of possible messages, possibly with their public status: the message after decomposition of tuples and the public set of values at last test.

	   Assume InputInfo(tc_list, oldpub, tc, name_params, occs, mess_list).
	   If tc_list != [], the first element of l is not in oldpub
	   we check whether the first element of
	   tc_list in is the part of public before oldpub. 
	   - If no, tc_list' = tc_list 
	   - If yes, we remove from the tail of l the first elements that 
	   are in public, yielding tc_list'. 
	   We replace the cache with InputInfo(tc_list',public,...)
	   If tc_list' is not empty, the channel is not public, 
	   try to perform (Res I/O). 
	   If tc_list' is empty, the channel is public, 
	   try to perform (Res In).
      	*)
  | OutputInfo of 'a list * 'a list
	(* the channel name after decomposition of tuples
	   the public set of values at last test.

	   Invariant: if we have OutputInfo(l,oldpub),
           the first element of l is not oldpub. 

	   When testing this output, we check whether the first element of
	   l in is the part of public before oldpub. 
	   - If no, we replace the cache with OutputInfo(l,public).
	   - If yes, we remove from the tail of l the first elements that 
	   are in public, yielding l'. If l' is not empty, we replace 
	   the cache with OutputInfo(l',public). If l' is empty,
	   we can execute the output: the channel is public.
	   *)
  | GetInfo of 'a list * 'a list
	(* the old contents of tables 
	   the list of possible entries *)
  | Nothing

type 'a sub_proc =
    process * (name_param_info list) * (hypspec list) * (fact list) * ('a info) 
      (* process (always closed -- only bound variables can occur; no variable with link *)
      (* list of name_params (terms received as input + session ids), always closed -- no variables *)
      (* list of occurrences of inputs and replications already seen in the reduction *)
      (* list of facts corresponding to already seen inputs -- no variables *)
      (* cached info for inputs *)

(* Types of locations (attacker or process) for steps in trace reconstruction *)

type 'a loc_info = 
    LocAttacker
  | LocProcess of int * 'a sub_proc

type weak_test =
    FailTest of term
  | EqTest of term * term

type 'a noninterf_test =
    ProcessTest of hypspec list * term list * (int * 'a sub_proc) option ref(*location where test found*)
  | InputProcessTest of hypspec list * term list * term * (int * 'a sub_proc) option ref(*location where test found*)
  | ApplyTest of funsymb * 'a list
  | NIFailTest of 'a
  | CommTest of 'a(*input channel*) * 'a(*output channel*) * 
	('a loc_info(*location where input found*) * 'a loc_info(*location where output found*)) option ref
  | InputTest of 'a(*input channel*) * ('a loc_info) option ref(*location where input found*)
  | OutputTest of 'a(*output channel*) * ('a loc_info) option ref(*location where output found*)
  | NIEqTest of 'a * 'a


type 'a goal_t =
    Fact of fact
  | WeakSecrGoal of (term * binder) list * weak_test * term * term
	(*
	  list of terms that the attacker has to know, with arbitrary variables
	  to store them,
	  the term that the attacker computes to test its guess,
	  the weak secret that the attacker wants to guess,
	  the symbol that represents the guess
	*)
  | NonInterfGoal of 'a noninterf_test
  | InjGoal of fact * term * int 
        (* The end event to execute, the second session in which it should
	   be executed, and the number of times it has already been met *)

type 'a reduc_state = 
    { 
      goal : 'a goal_t; (* goal to reach *)
      subprocess : 'a sub_proc list; (* process list *)
      public : 'a list; (* attacker knowledge *)
      tables : 'a list; (* contents of tables *)

      prepared_attacker_rule : (predicate * 'a list * 'a list) list; (* attacker rules *)
                               (* predicate, hypothesis, conclusion *)
      io_rule : (int * fact list * hypspec list * term list * fact) list; (* process rules *)
                (* rule number, hypotheses, occurrence labels, name params, conclusion *)

      previous_state : ('a reduc_state) option; (* previous semantic state *)
   
      hyp_not_matched : fact list;
      current_phase : int;
      comment : reduc_type  (* type of the reduction *)
    }


(* Indications of term occurrences that should be added to name_params *)

type term_occ =
      OTest of int
    | OLet of int
    | OInChannel of int
    | OEvent of int
    | OLetFilter of int
