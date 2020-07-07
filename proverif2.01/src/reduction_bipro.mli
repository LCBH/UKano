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

val do_reduction : History.recheck_t -> Pitypes.realquery option -> Pitypes.realquery list -> Types.fact_tree -> bool

exception FailOnlyOnSide of int
val bi_action: (int -> 'a) -> 'a * 'a
val term_evaluation_fail : term -> int -> term
val term_evaluation_to_true : term -> int -> term
val is_in_public: (term * (term * term)) list ->
                  term * term -> term option
val decompose_term : term * (term * term) -> (term * (term * term)) list
val decompose_term_rev : binder * (term * term) -> (binder * (term * term)) list
val add_public:
  (term * term) Pitypes.reduc_state ->
  term * term -> term * (term * term) Pitypes.reduc_state
val match_pattern: pattern -> int -> term -> unit
val equal_bi_terms_modulo: term * term -> term * term -> bool
val noninterftest_to_string: 'a Pitypes.noninterf_test -> string
