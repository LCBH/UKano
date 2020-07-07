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

val get_max_used_phase : process -> int
val get_min_used_phase : process -> int

val get_process : Pitypes.t_pi_state -> Pitypes.t_process_desc
val set_min_choice_phase : Pitypes.t_pi_state -> Pitypes.t_pi_state

val prove_att_phase : Pitypes.t_pi_state -> int -> bool

val reset_name_args : process -> unit
val check_inj_coherent : Pitypes.query -> Pitypes.query

val new_var_pat1 : pattern -> binder
val new_var_pat : pattern -> term
val get_pat_vars : binder list -> pattern -> binder list
val occurs_var_pat : binder -> pattern -> bool
val occurs_var_proc : binder -> process -> bool

val get_need_vars : Pitypes.t_pi_state -> funsymb -> (string * Parsing_helper.extent) list
val meaning_encode : arg_meaning -> string
val meaning_name : arg_meaning -> string

type include_info_t
val prepare_include_info :
    envElement Stringmap.StringMap.t -> binder list option -> Ptree.ident list -> include_info_t
val count_name_params : Pitypes.name_param_info list -> int
val extract_name_params_noneed : Pitypes.name_param_info list -> term list
val extract_name_params : funsymb -> include_info_t -> Pitypes.name_param_info list -> term list
val extract_name_params_meaning : funsymb -> include_info_t -> Pitypes.name_param_info list -> arg_meaning list
val extract_name_params_types : funsymb -> include_info_t -> Pitypes.name_param_info list -> typet list -> typet list

val findi : ('a -> bool) -> 'a list -> int * 'a
val skip : int -> 'a list -> 'a list
val replace_at : int -> 'a -> 'a list -> 'a list
val remove_at : int -> 'a list -> 'a list
val add_at : int -> 'a -> 'a list -> 'a list
val create : int -> 'a -> 'a list

val do_rnil : 'a Pitypes.reduc_state -> int -> 'a Pitypes.reduc_state

val equal_terms_modulo : term -> term -> bool
val equal_open_terms_modulo : term -> term -> bool
val equal_facts_modulo : fact -> fact -> bool
val match_modulo : (unit -> 'a) -> term -> term -> 'a
val match_modulo_list :
  (unit -> 'a) -> term list -> term list -> 'a

val get_name_charac : term -> funsymb list
val init_name_mapping : funsymb list -> unit
val add_name_for_pat : term -> funsymb
val add_new_name : typet -> funsymb

val display_tag : hypspec list -> term list -> unit

val public_free : term list ref

val match_equiv : (unit -> 'a) -> fact -> fact -> 'a
val match_equiv_list :
  (unit -> 'a) -> fact list -> fact list -> 'a

val fact_subst :
  fact -> funsymb -> term -> fact
val process_subst :
  process -> funsymb -> term -> process

val copy_process : process -> process

val instantiate_natural_predicates : (unit -> 'a) -> fact_tree -> 'a

val close_term : term -> unit
val close_destr_constraints : constraints -> unit
val close_tree : fact_tree -> unit

val copy_closed : term -> term
val copy_closed_remove_syntactic : term -> term

val rev_name_subst : term -> term
val rev_name_subst_list : term list -> term list
val rev_name_subst_fact : fact -> fact

val follow_link : term -> term
val close_tree_collect_links : (binder * linktype) list ref -> fact_tree -> unit

val getphase : predicate -> int

val is_fail : term -> bool

val update_name_params : when_include -> Pitypes.name_param_info list ->
  pattern -> Pitypes.name_param_info list

val transl_check_several_patterns : Pitypes.term_occ list ref -> Pitypes.term_occ -> term -> bool

(* Returns whether the considered term should be added in
   the arguments of names.
   This function uses [Param.cur_state]. *)
val reduction_check_several_patterns : Pitypes.term_occ -> bool

(* [check_delayed_names q] translates the fresh names in query [q]
   that could not be translated in [Pitsyntax.transl_query] because
   we need information on the arity/type of name function symbols.

   This function must be called after translating the process into
   clauses, because this translation determines the arguments of the
   name function symbols. *)
val check_delayed_names : Pitypes.query -> Pitypes.query
val check_delayed_names_r : Pitypes.realquery -> Pitypes.realquery

val collect_constraints : fact_tree -> constraints
val close_constraints : constraints -> unit

(* Functions handleling the occurence names as well as the precise events. *)

val get_occ_name : occurrence -> funsymb

val get_precise_events_of_occ : occurrence -> precise_info list
val exists_specific_precise_events_of_occ : occurrence -> precise_info -> bool
val add_precise_info_occ : occurrence -> precise_info -> unit
val reset_occ_precise_event : unit -> unit

val create_pdf_trace : ('a -> term) -> ('a Pitypes.noninterf_test -> string) -> string -> 'a Pitypes.reduc_state -> int

(* Creation of queries *)

val make_qand : Pitypes.conclusion_query -> Pitypes.conclusion_query -> Pitypes.conclusion_query
val make_qor : Pitypes.conclusion_query -> Pitypes.conclusion_query -> Pitypes.conclusion_query

(* Updating correspondance goals *)

val is_success_corresp_goal : 'a Pitypes.goal_t -> bool

val retrieve_goals_from_id : int list -> 'a list -> 'a list
val get_corresp_goals : fact_tree -> fact list * int list

val update_corresp_goal : 'a Pitypes.goal_t -> (occurrence * term list) option -> (fact -> bool) ->
  'a Pitypes.goal_t * bool * bool

val begin_of_end_event_fact : fact -> fact
