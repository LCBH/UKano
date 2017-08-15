(*************************************************************
 *                                                           *
 *  Cryptographic protocol verifier                          *
 *                                                           *
 *  Bruno Blanchet, Vincent Cheval, and Marc Sylvestre       *
 *                                                           *
 *  Copyright (C) INRIA, CNRS 2000-2017                      *
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

(* Table of names -> function symbol representing that name,
   used in pitsyntax.ml *)

val glob_table : (string, funsymb) Hashtbl.t

(* [copy_process add_in_glob_table p] returns a copy of the process [p]
   * If [add_in_glob_table] is true, it renames each name created by
   a restriction to a fresh name, and adds these names to [glob_table].
   * It renames all bound variables to fresh distinct variables.
   When [add_in_glob_table] is true, these variables receive distinct
   numbers, so that they have distinct names when they are displayed.
   * New occurrences are created for each program point in the process.
   * Free variables of [p] may be linked to terms via [TLink t] on entry.
   In this case, these variables are substituted by the terms in question
   during the copy. Notice that variables that occur as arguments of
   restrictions [Restr] can only be linked to variables via
   [TLink (Var b)], not to other terms. *)
val copy_process : bool -> process -> process

(* [prepare_process p] returns a copy of the process [p], such that:
   * each name created by a restriction is renamed to a fresh name
   (these names are in [glob_table]);
   * all bound variables are renamed to fresh distinct variables,
   with distinct numbers;
   * new occurrences are created at each program point in the process,
   starting from 1. *)
val prepare_process : process -> process

(* [reset_occurrence p] creates a fresh copy of the process [p]
   with occurrences nicely numbered.
   Names and variables are fresh copies but keep their old name *)
val reset_occurrence : process -> process

(* [simplify_process p next_f] simplifies the process [p]
   by merging branches as much as possible, and calls [next_f p']
   for each obtained simplified process. *)
val simplify_process : process -> (process -> unit) -> unit

(* [verify_process l p] verifies that all free variables of 
   [p] are in the list [l]. 
   In particular, [verify_process [] p] verifies that
   the process [p] is closed. *)
val verify_process : binder list -> process -> unit

(* [obtain_biprocess_from_processes p1 p2 next_f] tries to merge
   the two processes [p1] and [p2] into a biprocess [p] and calls
   [next_f p] for each obtained biprocess [p]. *)
val obtain_biprocess_from_processes : process -> process -> (process -> unit) -> unit
