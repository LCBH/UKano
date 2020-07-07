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

(** Return an abbreviated derivation and an association table where the names are abbreviated *)

val abbreviate_derivation : fact_tree -> (term * term) list * fact_tree

val auto_assign_abbrev_table : (unit -> unit) -> (term * term) list -> unit


(* [record_id s id ext] records the identifier [s] so that it will not be
   reused elsewhere.
   [record_id] must be called only before calls to
   [Terms.fresh_id] or [Terms.new_var_name] and before any display. *)
val record_id : string -> Parsing_helper.extent -> unit

(* Clear used ids. Used to reload a file in proverif interact mode *)
val init_used_ids : unit -> unit

(* [auto_cleanup_display f] runs [f()], considering the identifiers
   displayed by [f()] as having a local scope, so that the same
   identifiers can be reused after [auto_cleanup_display f] *)
val auto_cleanup_display : (unit -> 'a) -> 'a

(* [string_of_fsymb f] returns the string used to display the function
   symbol [f]. *)
val string_of_fsymb : funsymb -> string
(* [string_of_binder v] returns the string used to display the variable [v]. *)
val string_of_binder : binder -> string

(* Functions to convert a type 'a (bi term or term) to a term,
   introducing [choice] if necessary *)
val bi_term_to_term : term * term -> term
val term_to_term : term -> term

type cl = CFun | CName | CVar | CPred | CType | CExplain | CKeyword | CConn | CProcess | CQuery | CResult | CQTrue | CQFalse | CQDontKnow

type query_type =
  | TAxiom
  | TLemma
  | TQuery

module type LangSig =
  sig
    val indentstring : string
    val print_string : string -> unit
    val display_occ : occurrence -> unit
    val display_occ_ref : occurrence -> unit
    val display_clause_link : int -> unit
    val display_step_link : int -> unit
    val start_cl : cl -> unit
    val end_cl : cl -> unit
    val convert_funname : string -> string
    val and_connective : unit -> string
    val or_connective : unit -> string
    val impl_connective : string
    val red_connective : string
    val before_connective : string
    val diff_connective : string
    val equal_connective : string
    val eq1_connective : string
    val eq2_connective : string
    val geq_connective : string
    val hline : string
    val start_numbered_list : unit -> unit
    val end_numbered_list : unit -> unit
    val start_list : unit -> unit
    val end_list : unit -> unit
    val clause_item : int -> unit
    val lemma_item : int -> unit
    val history_item : int -> unit
    val basic_item : unit -> unit
    val dash_item : unit -> unit
    val wrap_if_necessary : unit -> unit
    val newline : unit -> unit
    val process_link : string -> int -> string
  end

module type LangDispSig =
sig
  val print_string : string -> unit
  val newline : unit -> unit
  val hline : string
  val print_line : string -> unit

  val display_occ : occurrence -> unit
  val display_keyword : string -> unit
  val display_list : ('a -> unit) -> string -> 'a list -> unit
  val display_item_list : ('a -> unit) -> 'a list -> unit
  val display_dash_list : ('a -> unit) -> 'a list -> unit
  val display_term : term -> unit
  val display_term_list : term list -> unit
  val display_fact : fact -> unit
  val display_fact_format : fact_format -> unit
  val display_constra : (term * term) list -> unit
  val display_constraints : constraints -> unit
  val display_rule_nonewline : reduction -> unit
  val display_rule : reduction -> unit
  val display_rule_indep : reduction -> unit
  val display_rule_abbrev : reduction -> unit
  val display_ordered_rule : ordered_reduction -> unit
  val display_ordered_rule_indep : ordered_reduction -> unit
  val display_ordered_rule_abbrev : ordered_reduction -> unit
  val display_inside_query : fact list -> constraints -> fact list -> fact list -> unit
  val display_inside_query_success : constraints -> unit
  val display_initial_clauses : reduction list -> unit
  val display_lemmas : lemma list -> unit
  val display_eq : term * term -> unit
  val display_red : funsymb -> (term list * term * constraints) list -> unit

  val display_term2 : term -> unit
  val display_pattern : pattern -> unit
  val display_fact2 : fact -> unit
  val display_process : string -> process -> unit
  val display_process_occ : string -> process -> unit
  val display_event : Pitypes.event -> unit
  val display_corresp_query : Pitypes.realquery -> unit
  val display_corresp_secret_putbegin_query : Pitypes.query -> unit
  val display_query : bool -> query_type -> Pitypes.t_query -> unit
  val display_result : ?partial:bool -> Pitypes.query_res -> unit
  val display_result_and_supplemental :
      ?partial:bool -> Pitypes.query -> Pitypes.query -> Pitypes.query_res ->
	(Pitypes.realquery * Pitypes.query_res) list -> unit
  val display_final_result : (Pitypes.query_res * Pitypes.t_query) list -> unit
  val display_query_result : Pitypes.t_query -> Pitypes.query_res -> unit
  val display_process_query_res : Pitypes.t_process_query * Pitypes.query_res -> unit
  val display_summary : (Pitypes.t_process_query * Pitypes.query_res) list -> Pitypes.grouped_axioms_t list -> Pitypes.grouped_lemmas_t list -> unit

  val display_function_name : funsymb -> unit
  val display_phase : predicate -> unit


  module WithLinks :
  sig
    val term : term -> unit
    val term_list : term list -> unit
    val fact : fact -> unit
    val constra : (term * term) list -> unit
    val constraints : constraints -> unit
    val concl : bool -> fact -> hypspec list -> unit
  end

  val display_history_tree : string -> fact_tree -> unit
  val explain_history_tree : fact_tree -> unit
  val display_abbrev_table : (term * term) list -> unit

  val display_reduc_state :
    ('a -> term) -> bool -> 'a Pitypes.reduc_state -> int
  val display_labeled_trace :
    'a Pitypes.reduc_state -> unit
  val display_goal :
    ('a -> term) ->
    ('a Pitypes.noninterf_test -> string) ->
    'a Pitypes.reduc_state -> bool -> unit

  val display_process_link : bool -> Pitypes.t_process_desc -> unit
  val display_full_construction : Pitypes.t_process_desc -> unit
  val display_last_construction : Pitypes.t_process_desc -> unit
end

module LangDisp : functor (Lang : LangSig) -> LangDispSig


module LangHtml :
sig
  val proverifurl : string ref
  val openfile : string -> string -> unit
  val close : unit -> unit
end

(* Display HTML *)
module Html : LangDispSig

(* Display text on standard output *)
module Text : LangDispSig

(* Display in a buffer *)
module LangBuf :
sig
  val get_string : unit -> string
end

module Buf : LangDispSig

(* Display either HTML or text depending on the settings *)
module Def :
sig
  val print_line : string -> unit

  (* [display_numbered_process in_sentence p_desc]
     displays the process described by [p_desc], if it was not already displayed.
     [in_sentence] should be true when the display occurs inside
     a sentence, to start with a lowercase letter.
     Returns true when the process is displayed. *)
  val display_numbered_process : bool -> Pitypes.t_process_desc -> unit

  val display_process_or_link : bool -> Pitypes.t_process_desc -> unit

end

(** Main module to display traces. *)
(** [write_state_to_dot_file fname a_to_term noninterf_test_to_string state] *)
(** writes the state [state] in .dot format in the file [fname]. *)
(** The function "create_pdf_trace" defined in reduction_helper *)
(** uses this function to create and display the pdf trace *)
module AttGraph :
sig
  val write_state_to_dot_file :
    string -> ('a -> term) -> ('a Pitypes.noninterf_test -> string) -> 'a Pitypes.reduc_state -> bool -> unit
end
