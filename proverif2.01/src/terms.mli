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
(* This modules contains basic functions to manipulate terms *)

open Types

(* Basic list functions *)

val split_list : int -> 'a list -> 'a list * 'a list

(* Basic string functions *)

(* [ends_with s sub] is true when the string [s] ends with [sub] *)
val ends_with : string -> string -> bool

(* [starts_with s sub] is true when the string [s] starts with [sub] *)
val starts_with : string -> string -> bool

val tuple_table : (typet list, funsymb) Hashtbl.t

(* [get_tuple_fun tl] returns the function symbol corresponding
   to tuples with arguments of types [tl] *)
val get_tuple_fun : typet list -> funsymb
val get_term_type : term -> typet
val get_pat_type : pattern -> typet

val is_var : term -> bool

val equal_types : typet -> typet -> bool

val term_of_pattern_variable : pattern -> term

val get_format_type : format -> typet
val copy_n : int -> 'a -> 'a list
val tl_to_string : string -> typet list -> string

(* [eq_lists l1 l2] tests the physical equality between
   the elements of [l1] and [l2] *)
val eq_lists : 'a list -> 'a list -> bool

(* Creates and returns a new identifier or variable *)

val get_id_n : string -> string * int

(* Converts an identifier (id,n) into a string id_n *)

val id_n2id : string * int -> string

(* Clear used_ids. Used to reload a file in proverif interact mode *)
val init_used_ids : unit -> unit

(* [record_id s id ext] records the identifier [s] so that it will not be
   reused elsewhere.
   [id] must be the conversion of [s] into a pair (string, int) by [get_id_n].
   [record_id] must be called only before calls to [fresh_id] or [new_var_name] *)
val record_id : string -> string * int -> Parsing_helper.extent -> unit

(* [fresh_id s] creates a fresh identifier by changing the number of [s]. *)
val fresh_id : string -> string

(* [new_id ~orig s] creates a fresh identifier with name built from [s].
   When [~orig] is true, the original name is set to [s], otherwise
   it is left empty to mean "no original name".
   By default, [~orig] is true. *)
val new_id : ?orig:bool -> string -> renamable_id

(* [copy_id ~orig id] creates a fresh identifier by renaming [id].
   When [~orig] is true, the original name is set to the original name of [id],
   otherwise it is left empty to mean "no original name".
   By default, [~orig] is true. *)
val copy_id : ?orig:bool -> renamable_id -> renamable_id

(* [new_var ~orig ~may_fail s t] creates a fresh variable with
   name built from [s] and type [t].
   When [~orig] is true, the original name is set to [s], otherwise
   it is left empty to mean "no original name".
   By default, [~orig] is true.
   When [~may_fail] is true, the variable may contain [fail].
   By default, [~may_fail] is false. *)
val new_var : ?orig:bool -> ?may_fail:bool -> string -> typet -> binder

(* [copy_var ~orig v] creates a fresh variable with the same type and failure
   status as [v] and a name renamed from the one of [v].
   When [~orig] is true, the original name is set to the original name of [v],
   otherwise it is left empty to mean "no original name".
   By default, [~orig] is true. *)
val copy_var : ?rename:bool -> ?orig:bool -> binder -> binder

(* [new_var_def ~may_fail t] creates a fresh variable with a default name
   and type [t].
   When [~may_fail] is true, the variable may contain [fail].
   By default, [~may_fail] is false. *)
val new_var_def : ?may_fail:bool -> typet -> binder
val new_var_def_term : ?may_fail:bool -> typet -> term

(* [val_gen tl] creates new variables of types [tl] and returns them in a
   list *)
val var_gen : typet list -> term list

(* [get_fsymb_basename f] returns the base name of [f]. This name is
   not unique in case several copies of [f] can be created by renaming.
   (All these copies have the same base name.)
   It is the fixed name of [f] when [f] cannot be renamed. *)
val get_fsymb_basename : funsymb -> string

(* [get_fsymb_origname f] returns the original name of [f].
   It is the fixed name of [f] when [f] cannot be renamed.
   It may be empty, in case [f] can be renamed and is not created from
   the initial process. *)
val get_fsymb_origname : funsymb -> string

(* [is_may_fail_term t] returns true if [t] is the constant [fail] or a may-fail variable *)
val is_may_fail_term : term -> bool

(* [is_unfailing_var t] returns true if [t] is the constant [fail] or a may-fail variable *)
val is_unfailing_var : term -> bool

(* [is_failure t] returns true if [t] is the constant [fail] *)
val is_failure : term -> bool

(* Basic functions for constraints *)

val exists_constraints : (term -> bool) -> constraints -> bool
val map_constraints : (term -> term) -> constraints -> constraints
val iter_constraints : (term -> unit) -> constraints -> unit

val true_constraints : constraints
val constraints_of_neq : term -> term -> constraints
val constraints_of_geq : term -> term -> constraints
val constraints_of_is_nat : term -> constraints
val constraints_of_is_not_nat : term -> constraints

val is_true_constraints : constraints -> bool

val wedge_constraints : constraints -> constraints -> constraints

(* [occurs_var v t] returns true when variable [v] occurs in [t] *)
val occurs_var : binder -> term -> bool
val occurs_var_format : binder -> format -> bool
val occurs_var_fact : binder -> fact -> bool
val occurs_var_constraints : binder -> constraints -> bool

(* [occurs_vars_all bl t] returns true when all variables occuring in [t] are in [bl]. *)
val occurs_vars_all : binder list -> term -> bool

(* [occurs_f f t] returns true when function symbol [f] occurs in [t] *)
val occurs_f : funsymb -> term -> bool
val occurs_f_pat : funsymb -> pattern -> bool
val occurs_f_fact : funsymb -> fact -> bool
val occurs_f_constra : funsymb -> constraints -> bool

(* Syntactic equality *)
val equal_terms : term -> term -> bool
val same_term_lists : term list -> term list -> bool
val equal_fact_formats : fact_format -> fact_format -> bool
val equal_facts : fact -> fact -> bool
val equal_facts_phase_geq : fact -> fact -> bool

(* General variables *)
val new_gen_var : typet -> bool -> funsymb
val generalize_vars_not_in : binder list -> term -> term
val generalize_vars_in : binder list -> term -> term

(* Copies. Variables must be linked only to other variables, with VLink. *)
val copy_term : term -> term
val copy_fact : fact -> fact
val copy_constra : constraints -> constraints
val copy_rule : reduction -> reduction
val copy_red : rewrite_rule -> rewrite_rule
(* To cleanup variable links after copies and other manipulations
   [current_bound_vars] is the list of variables that currently have a link.
   [cleanup()] removes all links of variables in [current_bound_vars],
   and resets [current_bound_vars] to the empty list.

   Furthermore, [cleanup_assoc_table_gen_and_ex] cleanup the association table.
 *)
val current_bound_vars : binder list ref
val cleanup : unit -> unit
val link : binder -> linktype -> unit
val link_var : term -> linktype -> unit
val auto_cleanup : (unit -> 'a) -> 'a

(* Exception raised when unification fails *)
exception Unify
val occur_check : binder -> term -> unit
(* Unify two terms/facts by linking their variables to terms *)
val unify : term -> term -> unit
val unify_facts : fact -> fact -> unit

(* Same as unify_facts except that f1 of phase n can be unified with f2 of phase m with n >= m.
   Used in history.ml to deal with lemmas. *)
val unify_facts_phase : fact -> fact -> unit
val unify_facts_phase_leq : fact -> fact -> unit
(* Copies. Variables can be linked to terms with TLink *)
val copy_term2 : term -> term
val copy_fact2 : fact -> fact
val copy_constra2 : constraints -> constraints
val copy_rule2 : reduction -> reduction
val copy_rule2_no_cleanup : reduction -> reduction
val copy_ordered_rule2 : ordered_reduction -> ordered_reduction
val copy_conclusion_query2 : Pitypes.conclusion_query -> Pitypes.conclusion_query
val copy_realquery2 : Pitypes.realquery -> Pitypes.realquery

exception NoMatch
val match_terms : term -> term -> unit
val match_facts : fact -> fact -> unit
(* Same as match_facts except that f1 of phase n can be matched with f2 of phase m with n >= m.*)
val match_facts_phase_geq : fact -> fact -> unit
(* Same as match_facts except that f1 of phase n can be matched with f2 of phase m with n <= m.*)
val match_facts_phase_leq : fact -> fact -> unit
val matchafact : fact -> fact -> bool
(* Same as matchafact except that it returns true only when some variable
   x is mapped to a term that is not a variable and that contains x by
   the matching substitution *)
val matchafactstrict : fact -> fact -> bool

(* Copy of terms and constraints after matching.
   Variables can be linked to terms with TLink, but the link
   is followed only once, not recursively *)
val copy_term3 : term -> term
val copy_fact3 : fact -> fact
val copy_constra3 : constraints -> constraints

(* [copy_term4] follows links [Tlink] recursively,
   but does not rename variables *)
val copy_term4 : term -> term
val copy_fact4 : fact -> fact
val copy_constra4: constraints -> constraints

(* Size of terms/facts *)
val term_size : term -> int
val fact_size : fact -> int

(* Return true when the term contains a variable *)
val has_vars : term -> bool

(* [get_var vlist t] accumulate in reference list [vlist] the list of variables
   in the term [t].
   [get_vars_constra vlist c] does the same for the constraint [c], and
   [get_vars_fact vlist f] for the fact f *)
val get_vars : binder list ref -> term -> unit
val get_vars_constra : binder list ref -> constraints -> unit
val get_vars_fact : binder list ref -> fact -> unit

(* [get_vars_pat accu pat] returns [accu] with the variables bound in [pat] added *)
val get_vars_pat : binder list -> pattern -> binder list

(* [replace_f_var vl t] replaces names in t according to
   the association list vl. That is, vl is a reference to a list of pairs
   (f_i, v_i) where f_i is a (nullary) function symbol and
   v_i is a variable. Each f_i is replaced with v_i in t.
   If an f_i in general_vars occurs in t, a new entry is added
   to the association list vl, and f_i is replaced accordingly. *)

val replace_f_var : (funsymb * binder) list ref -> term -> term

(* [rev_assoc v2 vl] looks for [v2] in the association list [vl].
   That is, [vl] is a list of pairs (f_i, v_i) where f_i is a
   (nullary) function symbol and v_i is a variable.
   If [v2] is a v_i, then it returns f_i[],
   otherwise it returns [v2] unchanged. *)

val rev_assoc : binder -> (funsymb * binder) list -> term

(* [follow_link var_case t] follows links stored in variables in [t]
   and returns the resulting term. Variables are translated
   by the function [var_case] *)

val follow_link : (binder -> term) -> term -> term

(* [replace name f t t'] replaces all occurrences of the name [f] (ie f[]) with [t]
   in [t'] *)

val replace_name : funsymb -> term -> term -> term

(* Do not select Out facts, blocking facts, or pred_TUPLE(vars) *)
val add_unsel : fact -> unit
val is_unselectable : fact -> bool

(* helper function for decomposition of tuples *)
val reorganize_fun_app : funsymb -> term list ->
  term list list

(* Symbols *)

val get_fail_symb : typet -> funsymb
val get_fail_term : typet -> term

(* Integer constants and functions *)

val zero_cst : funsymb
val succ_fun : funsymb
val minus_fun : int -> funsymb
val greater_fun : unit -> funsymb
val geq_fun : unit -> funsymb
val less_fun : unit -> funsymb
val leq_fun : unit -> funsymb
val is_nat_fun : unit -> funsymb
val is_syntactic_natural_number : term -> bool

val zero_term : term
val generate_nat : int -> term
val sum_nat_term : term -> int -> term

(* Constants *)

val true_cst : funsymb
val false_cst : funsymb

val true_term : term
val false_term : term

(* Fors injective events *)

val get_session_id_from_occurrence : term -> term option

(* Functions *)

val choice_in_term : int -> term -> term
val choice_in_fact : int -> fact -> fact
val choice_in_proc : int -> process -> process
val choice_in_pat : int -> pattern -> pattern
val make_choice : term -> term -> term
val is_true_fun : unit -> funsymb
val has_choice : term -> bool
val has_choice_pat : pattern -> bool
val has_choice_format : format -> bool

val equal_fun : typet -> funsymb
val diff_fun : typet -> funsymb
val or_fun : unit -> funsymb
val and_fun : unit -> funsymb
val not_fun : unit -> funsymb
val make_not : term -> term
val and_list : term list -> term
val or_not_list : term list -> term
val new_name_fun : typet -> funsymb

val glet_constant_fun : typet -> funsymb
val glet_constant_never_fail_fun : typet -> funsymb

val glet_fun : typet -> funsymb
val gtest_fun : typet -> funsymb
val success_fun : typet -> funsymb
val not_caught_fail_fun : typet -> funsymb

val complete_semantics_constructors : typet list -> typet -> rewrite_rules
val red_rules_fun : funsymb -> rewrite_rules

(* [clauses_for_function clauses_for_red_rules s f] generates clauses
   for a function [f], given a function [clauses_for_red_rules] such
   that [clauses_for_red_rules f red_rules] generates clauses for
   function that has rewrite rules [red_rules].
   (For constructors, the rewrite rules f(...fail...) -> fail are
   omitted from [red_rules]. The function [clauses_for_red_rules] must
   take this point into account. In practice, this is easy because the
   clauses that come from f(...fail...) -> fail are useless.  This
   however needs to be justified in each case.)
   [s] is unused. It helps for calling [clauses_for_function]
   as argument of [Hashtbl.iter]. *)
val clauses_for_function : (funsymb -> rewrite_rules -> unit) ->
  funsymb -> unit

val get_function_name : funsymb -> string
val projection_fun : funsymb * int -> funsymb
(* [get_all_projection_fun tuple_symb] returns the list of projection
   functions corresponding to the tuple function [tuple_symb] *)
val get_all_projection_fun : funsymb -> funsymb list


val reset_occurrence : unit -> unit
val new_occurrence : ?precise:bool -> unit -> occurrence
val put_lets : process -> (binder * term) list -> process

val create_name : ?allow_rename:bool -> ?orig:bool -> string -> typet list * typet -> bool -> funsymb
val copy_name : ?orig:bool -> funsymb -> typet list -> funsymb

exception False_inequality

val generate_destructor_with_side_cond : term list list ->
  term list -> term -> Parsing_helper.extent -> rewrite_rules

val fact_list_of_conclusion : fact -> fact list

