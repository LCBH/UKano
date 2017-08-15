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

val main_process : process ref
val min_choice_phase : int ref
val terms_to_add_in_name_params : Pitypes.term_occ list ref

val new_var_pat1 : pattern -> binder
val new_var_pat : pattern -> term
val get_pat_vars : binder list -> pattern -> binder list
val occurs_var_pat : binder -> pattern -> bool
val occurs_var_proc : binder -> process -> bool

val need_vars_in_names : (string * string * Parsing_helper.extent) list ref
val get_need_vars : string -> (string * Parsing_helper.extent) list
val meaning_encode : arg_meaning -> string
val meaning_name : arg_meaning -> string

type include_info_t 
val prepare_include_info : 
    envElement Stringmap.StringMap.t -> binder list option -> Ptree.ident list -> include_info_t
val count_name_params : Pitypes.name_param_info list -> int
val extract_name_params_noneed : Pitypes.name_param_info list -> term list
val extract_name_params : string -> include_info_t -> Pitypes.name_param_info list -> term list
val extract_name_params_meaning : string -> include_info_t -> Pitypes.name_param_info list -> arg_meaning list
val extract_name_params_types : string -> include_info_t -> Pitypes.name_param_info list -> typet list -> typet list

val findi : ('a -> bool) -> 'a list -> int * 'a
val skip : int -> 'a list -> 'a list
val replace_at : int -> 'a -> 'a list -> 'a list
val remove_at : int -> 'a list -> 'a list
val add_at : int -> 'a -> 'a list -> 'a list

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

val copy_binder : binder -> binder
val copy_pat : pattern -> pattern
val copy_process : process -> process

val close_term : term -> unit
val close_tree : fact_tree -> unit

val copy_closed : term -> term
val copy_closed_remove_syntactic : term -> term

val rev_name_subst : term -> term
val rev_name_subst_list : term list -> term list
val rev_name_subst_fact : fact -> fact

val follow_link : term -> term
val close_tree_collect_links : (binder * linktype) list ref -> fact_tree -> unit

val getphase : predicate -> int

val disequation_evaluation : term * term -> bool
val is_fail : term -> bool

val update_name_params : when_include -> Pitypes.name_param_info list -> 
  pattern -> Pitypes.name_param_info list

val transl_check_several_patterns : Pitypes.term_occ -> term -> bool
val reduction_check_several_patterns : Pitypes.term_occ -> bool

val check_delayed_names : Pitypes.query -> Pitypes.query

val create_pdf_trace : ('a -> term) -> ('a Pitypes.noninterf_test -> string) -> string -> 'a Pitypes.reduc_state -> int


