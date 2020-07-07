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
exception WrongChoice
exception WarningsAsError

val delete_NamedProcess: 'a Pitypes.reduc_state -> 'a Pitypes.reduc_state

(* In diff-mode, [is_in_public_test_div t] raise [(DivTermPub (i, t, ca, pub)], *)
(* when the public term [pub] (where [ca] is the recipe giving [pub]), *)
(* is equal to [t] only on side [i] *)
exception DivTermPub of int * term * term * term
(* see [display_div] for documentation *)

val get_proc : term Pitypes.reduc_state -> int -> process

exception Div of Pitypes.div_type

val has_div: term Pitypes.reduc_state -> bool
val exists_div: unit -> bool

val get_table_name: term -> string

(* [is_in_public_test_div public t] In standard mode, it s the function *)
(* [Evaluation_helper.is_in_public public t]. In diff-mode, Test if [t] is in [public]. *)
(* In diff-mode, raise [(DivTermPub (i, t, ca, pub)], when the public term *)
(* [pub] is equal to [t] only on side [i] *)
(* None, if [t] is not in public, and return [true] or [false] *)
val is_in_public_test_div: (term * term) list -> term -> bool

(* [decompose_term_all_mode (recipe, t)] decomposes tuples at the root
   of [t].
   Returns a list of pairs [(recipe_i, t_i)] corresponding to the tuple
   components of [t]. *)
val decompose_term_all_mode: term * term -> (term * term) list

(* [decompose_term_rev_all_mode t] decomposes tuples at the root of [t].
   Returns [(recipe, l)] where [l] is a list of pairs (recipe_i, t_i)
   where the [t_i]'s are the tuple components of [t], and [recipe_i]
   is a corresponding recipe variable. [recipe] is the recipe
   to rebuild [t] from the recipes of its components.
   This function is used for output messages: the [(recipe_i, t_i)]
   are added to public, and [recipe] is the label of the output arrow. *)
val decompose_term_rev_all_mode: term -> term * (term * term) list

(* [add_public_list_dec_all_mode state l], where [l] is a list
   [(recipe_i, t_i)] adds the terms [t_i] with their recipe [recipe_i]
   to public and returns the updated state.
   The tuples at the root of terms [t_i] must be decomposed before.
   If all terms [t_i] are already public, the state [state] is returned physically
   unchanged.
   In diff-mode, raises [Div] in case of divergence: when one component
   of [t_i] has a tuple at the root, or is equal to a term in public
   but not the other component. *)
val add_public_list_dec_all_mode : term Pitypes.reduc_state -> (term * term) list -> term Pitypes.reduc_state

(* [equal_terms_modulo_all_mode t1 t2] returns true when [t1 = t2] modulo
   the equational theory.
   In diff-mode, raise [FailOnlyOnSide i] when [t1] is different from [t2]
   only on side [i]. *)
val equal_terms_modulo_all_mode: term -> term -> bool

(* [evaluates_term_all_mode t] Evaluates [t] and returns the result.
   raise [Unify] when the evaluation of [t] fails.
   In diff-mode, raise [FailOnlyOnSide i] if only side [i] fails *)
val evaluates_term_all_mode: term -> term
(* [evaluates_2terms_all_mode t1 t2] Evaluates [t1] and [t2] and returns the result in a pair.
   raise [Unify] when the evaluation fails.
   In diff-mode, raise [FailOnlyOnSide i] if only side [i] fails *)
val evaluates_2terms_all_mode: term -> term -> (term * term)
(* [evaluates_term_to_true_all_mode t] Evaluates [t] and returns true when the result equals [true].
   returns false when the evaluation of [t] fails or returns a result different from [true].
   In diff-mode, raise [FailOnlyOnSide i] if only side [i] fails *)
val evaluates_term_to_true_all_mode: term -> bool
(* [match_pat_all_mode pat t] matches the term [t] with the pattern [pat]
   and links the variables in [pat] to the corresponding values.
   raise [Unify] when the match fails.
   In diff-mode, raise [FailOnlyOnSide i] when the match fails ony on side [i]. *)
val match_pat_all_mode: pattern -> term -> unit
(* [term_eval_match_pat_all_mode pat t] evaluates the term [t],
   matches the result with the pattern [pat]
   and links the variables in [pat] to the corresponding values.
   raise [Unify] when the evaluation or match fails.
   In diff-mode, raise [FailOnlyOnSide i] when it fails ony on side [i]. *)
val term_eval_match_pat_all_mode: pattern -> term -> unit

(* [match_terms_lst pat t n p] Return all the terms in the current state *)
(* tables that matches the pattern [pat] and evaluates to [true] after this *)
(* pattern-matching (for both sides in diff-mode). Might raise exceptions *)
(* (see [display_div]) *)
val match_terms_lst: term list -> pattern -> term -> int -> process -> term list

(* [is_auto_reductible state p] Return true if the n-th process [p] of [state] is auto reductible, *)
(* false otherwise. *)
val is_auto_reductible: term Pitypes.reduc_state -> process -> int -> bool

(* [equal_io_oi x y] returns true when [x] and [y] correspond to matching
   inputs and outputs (same channel); returns false when the channels differ
   or fail to evaluate on at least one side (in diff-mode, when it fails on
   one side only, that's a divergence case, but it will be treated when we try to
   reduce the corresponding process).
   In diff-mode, raises [Div (DIO(...))] when the channels are equal on one
   side only. *)
val equal_io_oi : Pitypes.io_r_t -> Pitypes.io_r_t -> bool

(* [reset_env ()] Reset the global environment, clear tables, restore some parameters. *)
(* Used to load a new file *)
val reset_env: unit -> unit

(* [input_error_box b mess ext] Create a message box with title "Error in your Recipe", and one *)
(* button. The message displayed is comming from an InputError(mess, ext) exception. If [b] *)
(* is true, the the message display the line number and the character number of the error. *)
(* Otherwise, its only display the character number *)
val input_error_box: bool -> string -> Parsing_helper.extent -> unit

(* [parse_term string] Return the term corresponding to the parsing of [string]. *)
(* Raise InputError if the parsing went wrong *)
val parse_term: string -> term

(* [question_box title string ()] Create a dialog box with title [title], displaying the string *)
(* string [string]. Return the string enter by the user, raise WrongChoice if no string is entered *)
(* Same as [GToolbox.question_box] but with pango markup *)
val question_box : title:string -> buttons:string list -> ?default:int
                   -> ?width:int -> ?height:int -> string -> int

(* [display_div state div] returns a state with the divergence [div] recorded.
   The divergence corresponds to a case in which a biprocess evaluates
   differently on the 2 sides, so diff-equivalence fails *)
val display_div : term Pitypes.reduc_state -> Pitypes.div_type -> term Pitypes.reduc_state

val show_div: Pitypes.div_type -> string * int option * int option


(* [proc_of_sub proc] Return the process corresponding to [sub] *)
val proc_of_sub: term Pitypes.sub_proc -> process

(* [sub_of_proc proc] Return the subprocess corresponding to [proc] *)
val sub_of_proc: process -> term Pitypes.sub_proc

(* [update_cur_state state] Update the current state with state *)
val update_cur_state: term Pitypes.reduc_state -> unit

(* [exists_auto ()] Return true if there exists a auto-reductible process in one of the *)
(* subprocess of the current state, false otherwise *)
val exists_auto: unit -> bool

(* [is_first_step ()] Return true if the current state is the initialise state, false otherwise *)
val is_first_step: unit -> bool

(* [get_state ()] Return the current state *)
val get_state: unit -> term Pitypes.reduc_state

(* [get_data ()] Return the current data associated to the current state *)
val get_data: unit -> Pitypes.data_model

val get_recipe : string -> string -> term
val get_new_vars: 'a Pitypes.reduc_state -> (term * 'a) list ->
  (term * term * 'a) list * term list
val expand_recipe : term list -> ('a * term) list -> term -> term

(* Set or get the reference [io_c] used to make RIO reductions *)
val set_io_c: Pitypes.io_r_t -> unit
val get_io_c: unit -> Pitypes.io_r_t

(* Function for forward step *)
val exists_forward: unit -> bool
val one_step_forward: unit -> unit
val add_to_forwards_lst: term Pitypes.reduc_state -> unit
val reset_forward_lst: unit -> unit
