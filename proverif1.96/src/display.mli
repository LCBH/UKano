(*************************************************************
 *                                                           *
 *  Cryptographic protocol verifier                          *
 *                                                           *
 *  Bruno Blanchet, Vincent Cheval, and Marc Sylvestre       *
 *                                                           *
 *  Copyright (C) INRIA, CNRS 2000-2016                      *
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

(* Return an abbreviated derivation and an association table where the names are abbreviated *)

val abbreviate_derivation : fact_tree -> (term * term) list * fact_tree

module LangHtml :
sig
val proverifurl : string ref
val openfile : string -> string -> unit
val close : unit -> unit
end


module LangGviz :
sig
val close : unit -> unit
val openfile : string -> string -> unit
val write_state_to_dot_file :
      'a Pitypes.reduc_state -> unit
end



(* Write HTML code in a file *)

module Html :
sig
val print_string : string -> unit
val newline : unit -> unit
val print_line : string -> unit

val display_occ : int -> unit
val display_keyword : string -> unit
val varname : binder -> string
val display_list : ('a -> unit) -> string -> 'a list -> unit
val display_item_list : ('a -> unit) -> 'a list -> unit
val display_term : term -> unit
val display_term_list : term list -> unit
val display_fact : fact -> unit
val display_fact_format : fact_format -> unit
val display_constra : constraints list -> unit
val display_constra_list : constraints list list -> unit
val display_rule_nonewline : reduction -> unit
val display_rule : reduction -> unit
val display_initial_clauses : reduction list -> unit
val display_eq : term * term -> unit
val display_red : funsymb -> (term list * term * (term * term) list) list -> unit

val display_term2 : term -> unit
val display_pattern : pattern -> unit
val display_fact2 : fact -> unit
val display_process : string -> process -> unit
val display_process_occ : string -> process -> unit
val display_corresp_query : Pitypes.realquery -> unit
val display_corresp_putbegin_query : Pitypes.query -> unit
val display_eq_query : Pitypes.eq_query -> unit

val display_function_name : funsymb -> unit
val display_phase : predicate -> unit


module WithLinks :
  sig
    val term : term -> unit
    val term_list : term list -> unit
    val fact : fact -> unit
    val constra : constraints list -> unit
    val constra_list : constraints list list -> unit
    val concl : bool -> fact -> hypspec list -> unit
  end

val display_history_tree : string -> fact_tree -> unit
val explain_history_tree : fact_tree -> unit
val display_abbrev_table : (term * term) list -> unit

val display_bi_term : term * term -> unit

val display_reduc_state :
      ('a -> unit) -> bool -> 'a Pitypes.reduc_state -> int
val display_labeled_trace :
      'a Pitypes.reduc_state -> unit
val display_goal :
      ('a -> unit) -> ('a Pitypes.noninterf_test -> string) -> 'a Pitypes.goal_t -> fact list -> unit

end

(* Display text on standard output *)

module Text : 
sig
val print_string : string -> unit
val newline : unit -> unit
val print_line : string -> unit

val display_occ : int -> unit
val display_keyword : string -> unit
val varname : binder -> string
val display_list : ('a -> unit) -> string -> 'a list -> unit
val display_item_list : ('a -> unit) -> 'a list -> unit
val display_term : term -> unit
val display_term_list : term list -> unit
val display_fact : fact -> unit
val display_fact_format : fact_format -> unit
val display_constra : constraints list -> unit
val display_constra_list : constraints list list -> unit
val display_rule_nonewline : reduction -> unit
val display_rule : reduction -> unit
val display_initial_clauses : reduction list -> unit
val display_eq : term * term -> unit
val display_red : funsymb -> (term list * term * (term * term) list) list -> unit

val display_term2 : term -> unit
val display_pattern : pattern -> unit
val display_fact2 : fact -> unit
val display_process : string -> process -> unit
val display_process_occ : string -> process -> unit
val display_corresp_query : Pitypes.realquery -> unit
val display_corresp_putbegin_query : Pitypes.query -> unit
val display_eq_query : Pitypes.eq_query -> unit

val display_function_name : funsymb -> unit
val display_phase : predicate -> unit


module WithLinks :
  sig
    val term : term -> unit
    val term_list : term list -> unit
    val fact : fact -> unit
    val constra : constraints list -> unit
    val constra_list : constraints list list -> unit
    val concl : bool -> fact -> hypspec list -> unit
  end

val display_history_tree : string -> fact_tree -> unit
val explain_history_tree : fact_tree -> unit
val display_abbrev_table : (term * term) list -> unit

val display_bi_term : term * term -> unit

val display_reduc_state :
      ('a -> unit) -> bool -> 'a Pitypes.reduc_state -> int
val display_labeled_trace :
      'a Pitypes.reduc_state -> unit
val display_goal :
      ('a -> unit) -> ('a Pitypes.noninterf_test -> string) -> 'a Pitypes.goal_t -> fact list -> unit

end

(* Display either HTML or text depending on the settings *)

module Def :
sig
val print_line : string -> unit
end
