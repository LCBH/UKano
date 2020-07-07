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

val never_select_weight : int
val match_concl_weight : int
val default_add_no_unif_weight : int
val default_user_no_unif_weight : int
val weight_of_user_weight : int -> int

val initialize : (fact_format * int * nounif_op) list -> t_solver_kind -> unit
val guess_no_unif : reduction Pvqueue.q -> unit
val selection_fun : reduction -> int
val selection_fun_nostatechange : reduction -> int

(* [induction_required ()] returns [true] if and only if some nounif have been
   declared with the option [ignoreOnce]. *)
val induction_required : unit -> bool

(* The i-th element of [induc_auth] indicates whether we can apply a resolution on
  the i-th hypothesis of the clause despite the declaration of a nounif. Note that
  such application can only occur if the matching nounif has been declared with the
  option [ignoreOnce].

  [selection_induction hyp induc_auth] checks whether one hypothesis of hyp can be
  matched with a nounif declared with option [ignoreOnce] and the application
  is authorized by [induc_auth]. When it is the case, the function returns the position [i]
  of the hypothesis in [hyp] as well as an updated authorization list in which the
  authorization for the [i]th hypothesis has been revoked. Typically, this new
  authorization list will be used after the resolution on the [i]th hypothesis
  to enforce that such resolution is applied only once per hypothesis.

  When no hypothesis is authorized, the function returns -1 and [induc_auth].
*)
val selection_induction : fact list -> ('a * bool) list -> int * ('a * bool) list

(* [find_inductive_variable_to_remove nextf rule] tries to find two facts in the
   hypotheses of [rule] that match the same nounif declared with the option
   [inductionOn]. When it is the case, by definition of the nounif, it extracts
   the two lists of variables in the hypotheses of [rule] corresponding to the
   nounif declaration, say v11,...,v1n and v21,...,v2n, and checks whether
     1) v11 >= v21 && v12 >= v22 && ... && v1n >= v2n
     2) or, v11 <= v21 && v12 <= v22 && ... && v1n <= v2n
   is implied by the constraints in [rule].
   In case 1: the function applies [nextf] to the list v21,...,v2n
   In case 2: the function applies [nextf] to the list v11,...,v1n
   Otherwise it raises Not_found. *)
val find_inductive_variable_to_remove : (binder list -> 'a) -> reduction -> 'a
