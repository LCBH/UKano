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
open GMain
open GdkKeysyms
open Types
open Pitypes
open Terms
open Reduction_bipro

exception WrongChoice

(* see [display_div] for documentation *)

exception Div of div_type


let debug_print s =  ()
(*  print_endline s *)

(* [initialize_state ()] Initialize or reset [cur_state] *)
let initialize_state () =
  { goal = NoGoal;
    subprocess = [];
    public = [];
    pub_vars = [];
    tables = [];
    prepared_attacker_rule = [];
    io_rule = [];
    previous_state = None;
    hyp_not_matched = [];
    assumed_false = [];
    current_phase = 0;
    comment = RInit;
    events = [];
    barriers = []
  }

(* [cur_state] Reference on the current state *)
let cur_state = ref (initialize_state ())

(* [get_state ()] Return the current state *)
let get_state () = !cur_state

(* [sub_of_proc proc] Return the subprocess corresponding to [proc] *)
let sub_of_proc proc = (proc, [], [], [], Nothing)

(* [proc_of_sub proc] Return the process corresponding to [sub] *)
let proc_of_sub sub =
  let (p, _, _, _, _) = sub in
  p

(* [get_proc state n] Return the n-th process in [state.subprocess] *)
let get_proc state n =
  let (proc, _, _, _, _) = List.nth state.subprocess n in
  proc

(* [get_proc_list state] Return the list of process obtain from state.subprocess *)
let get_proc_list state =
  let rec aux acc = function
      [] -> List.rev acc
    | (proc, _, _, _, _)::tl -> aux (proc::acc) tl
  in
  aux [] state.subprocess

(* [only_one_proc state] Return true if state.suprocess contains only one process, false otherwise. *)
let only_one_proc state = match state.subprocess with
  | p::[] -> true
  | _ -> false

(* About sides: left = 1, right = 2 *)

let get_left = choice_in_term 1
let get_right = choice_in_term 2

(* [match_pat_all_mode pat t] match the pattern [pat] with the term [t], *)
(* for all mode. Raise [FailOnlyOnSide i] in diff-mode if the pattern matching fails *)
(* on side [i] only, and [Unify] if it fails on both sides, or fails in standard mode *)
let match_pat_all_mode pat t =
  if !Param.bipro_i_mode then
    ignore(bi_action (fun side ->
               Reduction_bipro.match_pattern pat side (choice_in_term side t)))
  else
    Evaluation_helper.match_pattern pat t

(* [equal_terms_modulo_all_mode s t] In standard mode, this is the function *)
(* [Reduction_helper.equal_terms s t]. Otherwise, in diff mode, it returns *)
(* [true] if [s] and [t] are equals on both sides modulo the equational theory, or raise *)
(* [FailOnlyOnSide i] if the evaluation of each sides are *)
(* not equals or fails on side [i] only *)
let equal_terms_modulo_all_mode s t =
  if !Param.bipro_i_mode then
    begin
      try
        let _ = bi_action
                  (fun side ->
                    let s' = choice_in_term side s in
                    let t' = choice_in_term side t in
                    if not (Reduction_helper.equal_terms_modulo s' t') then
                      raise Unify)
        in
        true
      with
        Unify -> false
    end
  else
    begin
      Reduction_helper.equal_terms_modulo s t
    end

let term_evaluation_fail = Evaluation_helper.term_evaluation_fail

(* [evaluates_both_sides t] Return the evaluation of both sides of [t], [(fst(t)!,snd(t)!)]. *)
(* Raise [Unify] if the evaluation fails on both sides. *)
(* Raise [FailOnlyOnSide i] if it fails only on side [i] *)
let evaluates_both_sides t = bi_action (Reduction_bipro.term_evaluation_fail t)

let evaluates_both_sides_to_true t =
  Reduction_bipro.bi_action (Reduction_bipro.term_evaluation_to_true t)

let evaluates_term_to_true_all_mode t =
  if !Param.bipro_i_mode then
    try
      ignore (evaluates_both_sides_to_true t);
      true
    with
      Unify -> false
  else
    let t' = Evaluation_helper.term_evaluation_fail t in
    Reduction_helper.equal_terms_modulo t' true_term

(* [evaluates_2terms_both_sides t1 t2] Evaluate [t1] *)
(* and [t2] together using [evaluates_both_sides]. *)
(* Raise [FailOneSideOnly i] if side [i] only fails *)
(* Unify if both evaluations fail, and the evaluation of both sides otherwise *)
(* (first the left evaluations, then the right ones) *)
let evaluates_2terms_both_sides t1 t2 =
  bi_action (fun side ->
      (Reduction_bipro.term_evaluation_fail t1 side,
       Reduction_bipro.term_evaluation_fail t2 side))

(* [evaluates_term_all_mode tc] In standard mode, this is the fonction *)
(* [Reduction_helper.term_evaluation_fail]. Otherwise, in diff-mode  *)
(* it returns [choice(left(tc)!,right(tc)!)], or if the evaluation fails  *)
(* on both sides it raises [Unify], if it fails on side [i] only, it raised *)
(* [FailOneSideOnly i] *)
let evaluates_term_all_mode tc =
  if !Param.bipro_i_mode then
    let (tc1, tc2) = evaluates_both_sides tc in
    make_choice tc1 tc2
  else
    term_evaluation_fail tc

let evaluates_2terms_all_mode tc t =
  if !Param.bipro_i_mode then
    let ((tc1, t1), (tc2, t2)) = evaluates_2terms_both_sides tc t in
    (make_choice tc1 tc2, make_choice t1 t2)
  else
    (term_evaluation_fail tc, term_evaluation_fail t)

let term_eval_match_pat pat t =
   let t' = Evaluation_helper.term_evaluation_fail t in
    Evaluation_helper.match_pattern pat t';
    t'


let term_eval_match_pat_bipro pat t =
  bi_action (fun side ->
      let t' =  Reduction_bipro.term_evaluation_fail t side in
      Reduction_bipro.match_pattern pat side t';
      t')

let term_eval_match_pat_all_mode pat t =
  if !Param.bipro_i_mode then
    ignore(term_eval_match_pat_bipro pat t)
  else
    ignore(term_eval_match_pat pat t)

(* List of forwards steps done previously *)
let forwards_lst = ref []

let exists_forward () =
  match !forwards_lst with
    [] -> false
  | _ -> true

let reset_forward_lst () =
  forwards_lst := []

let add_to_forwards_lst state =
  forwards_lst := state::(!forwards_lst)

let has_div state =
  match state.comment with
    RDiverges _ -> true
  | _ -> false

let exists_div ()=
  has_div (get_state())

let disp_proc p =
  match Display_interact.GtkInteract.display_process p with
    s::[] -> s
  | s::tl  -> s ^ " ..."
  | [] -> ""

let disp_term = Display_interact.GtkInteract.display_term

let disp_fact = Display_interact.GtkInteract.display_fact

let disp_pat = Display_interact.GtkInteract.display_pattern

let disp_other_side = function
    1 -> "only on the right side."
  | 2 -> "only on the left side."
  | _ -> assert false

(* In diff-mode, [is_in_public_test_div t] raise [(DivTermPub (i, t, ca, pub)], *)
(* when the public term [pub] (where [ca] is the recipe giving [pub]), *)
(* is different from [t] only on side [i] *)
exception DivTermPub of int * term * term * term

let rec show_div t =
  let disp_proc n p =  "The "
                       ^ (if n = 0 then
                            "first process" else
                            "process number " ^ string_of_int (n+1))
                       ^ ":\n"
                       ^  (disp_proc p)
  in
  match t with
    DChannel(s, i, tc, tc', ca, pub, n, p) ->
     (((disp_proc n p)
       ^ "\nis an "^s^" such that the channel\n"
       ^ (disp_term tc)
       ^ "\nevaluates to\n"
       ^ (disp_term tc')
       ^ "\nwhich is equal to the public term\n"
       ^ (disp_term pub)
       ^ "\n" ^ (disp_other_side i)
       ^ "\nThe adversary can distinguish which side runs by making an "
       ^ (match s with
	 "input" -> "output"
       | "output" -> "input"
       | _ -> assert false)
       ^ " on this public channel.\n"
      ),
      Some n, None)
  | DOutputMess(t, t', recipe, n, p, div) ->
      let (mess, _, _) = show_div div in
     (((disp_proc n p)
       ^ "\noutputs\n"
       ^ (disp_term t)
       ^ "\nwhich evaluates to\n"
       ^ (disp_term t') ^ " = " ^ (disp_term recipe)
       ^ ".\n" ^ mess),
      Some n, None)
  | DEquality(i, recipe, result, ca, pub) ->
     (("There is a public term\n"
       ^ (disp_term pub)
       ^ "\nsuch that the evaluation\n"
       ^ (disp_term result)
       ^ "\nof the recipe\n"
       ^ (disp_term recipe)
       ^ "\nis equal to the public term\n"
       ^ (disp_term pub)
       ^ "\n" ^ (disp_other_side i)
       ^ "\nThe adversary can distinguish the processes by evaluating the recipe and comparing its result with this public term."),
      None, None)
  | DEval (s, i, tc, n, p) ->
     (((disp_proc n p)
       ^ "\nis "^s^"\n"
       ^ (disp_term tc)
       ^ "\nsucceeds "  ^ (disp_other_side i)
       ^ "\nThe adversary might distinguish which side runs."),
      Some n, None)
  | DEvalOut(i, tc, t, n, p) ->
     (((disp_proc n p)
       ^ "\nis an output such that the evaluation of the pair formed of the channel\n"
       ^ (disp_term tc)
       ^ "\nand the outputted term\n"
       ^ (disp_term t)
       ^ "\nsucceeds " ^ (disp_other_side i)
       ^ "\nThe adversary might distinguish which side runs."),
      Some n, None)
  | DEvalLet(i, t, pat, n, p) ->
     (((disp_proc n p)
       ^ "\nis a let such that the evaluation of the term\n"
       ^ (disp_term t)
       ^ "\nor the pattern-matching between this term and the pattern\n"
       ^ (disp_pat pat)
       ^ "\nsucceeds " ^ (disp_other_side i)
       ^ "\nThe adversary might distinguish which side runs."),
      Some n, None)
  | DEvalFact(i, f, n, p) ->
     (((disp_proc n p)
       ^ "\nis a test such that the evaluation of the fact\n"
       ^ (disp_fact f)
       ^ "\nsucceeds " ^ (disp_other_side i)
       ^ "\nThe adversary might distinguish which side runs."),
      Some n, None)
  | DInputPat(i, recipe, result, pat, n, p) ->
     (((disp_proc n p)
       ^ "\nis an input such that the pattern-matching between the expansion\n"
       ^ (disp_term result)
       ^ "\nof the recipe\n"
       ^ (disp_term recipe)
       ^ "\ngiven by the user, and the pattern\n"
       ^ (disp_pat pat)
       ^ "\nsucceeds " ^ (disp_other_side i)
       ^ "\nThe adversary might distinguish which side runs."), Some n, None)
  | DGet (i, term, pat, t, n, p) ->
     (((disp_proc n p)
       ^ "\nis a get such that the term\n"
       ^ (disp_term term)
       ^ "\nis in the table, but matches the conditions of get\n"
       ^ "(pattern "
       ^ (disp_pat pat)
       ^ (match t with
            FunApp(f,[]) when f == Terms.true_cst -> ""
          | _ -> ", condition " ^ (disp_term t))
       ^ ")\n"
       ^ (disp_other_side i)
       ^ "\nThe adversary might distinguish which side runs."),
      Some n, None)
  | DIO(i, cin, cout, nin, pin, nout, pout) ->
     (((disp_proc nin pin)
       ^ "\nis an input on a private channel\n"
       ^ (disp_term cin)
       ^ ".\n"
       ^ (disp_proc nout pout)
       ^ "\nis an output on a private channel\n"
       ^ (disp_term cout)
       ^ ".\nWhen we evaluate both channels, they are equal "
       ^ (disp_other_side i)
       ^ "\nThe adversary might distinguish which side runs."),
      Some nin, Some nout)
  | DIOPat( i, t, t', pat, nin, pin, nout, pout) ->
     (((disp_proc nin pin)
       ^"\nis an input.\n"
       ^  (disp_proc nout pout)
       ^"\nis an output "
       ^ "such that the pattern-matching between the pattern\n"
       ^ (disp_pat pat)
       ^ "\nand the evaluation\n"
       ^ (disp_term t')
       ^"\nof the output term\n"
       ^ (disp_term t)
       ^ "\nsucceeds "^ (disp_other_side i)
       ^ "\nThe adversary might distinguish which side runs."), Some nin, Some nout)
  | DTest(i, elsenil, fst, snd, t, n, p) ->
     let result i' =
       if i' = i then
         if elsenil then
           "something different from true or fails to evaluate"
         else
           "something different from true"
       else "true"
     in
     let branch i' =
       if i' = i then "else" else "then"
     in
     (((disp_proc n p)
       ^ "\nis a test such that the left side\n"
       ^ (disp_term fst)
       ^ "\nof the condition "
       (* ^(disp_term t) *)
       ^ "\nevaluates to " ^ (result 1) ^ " while the right side\n"
       ^ (disp_term snd)
       ^ "\nevaluates to " ^ (result 2) ^ "."
       ^ "\nThe adversary might distinguish that the left process takes the "
       ^ (branch 1)
       ^ " branch, while the right one takes the " ^ (branch 2) ^" branch.\n"),
      Some n, None)
  | DLetFilter(i, elsenil, f, n, p) ->
     let result i' =
       if i' = i then
         if elsenil then
           "false or fails to evaluate"
         else
           "false"
       else "true"
     in
     let branch i' =
       if i' = i then "else" else "then"
     in
     (((disp_proc n p)
       ^ "\nis a test such that the left side of the condition "
       ^ (disp_fact f)
       ^ "\nevaluates to " ^ (result 1) ^ " while the right side evaluates to " ^ (result 2) ^ "."
       ^ "\nThe adversary might distinguish that the left process takes the "
       ^ (branch 1)
       ^ " branch, while the right one takes the " ^ (branch 2) ^" branch.\n"),
      Some n, None)
  | DFail(i, r, exp) ->
     (("The evaluation\n"
       ^ (disp_term exp)
       ^ "\nof the recipe\n"
       ^ (disp_term r)
       ^ "\nsucceeds " ^ (disp_other_side i)
       ^ "\nThe adversary can distinguish which side runs by evaluating this recipe."),
      None, None)


(* [display_div state div] is called when process are not diff-equivalent. *)
(* It sets the field [comment] of the state with the divergence and returns the new state *)
let display_div state div =
  let rec get_goal t =
    match t with
      DChannel(s, i, tc, tc', ca, pub, n, p) ->
	begin
	  match s with
	    "input" ->
	      CommTest (tc, pub, Some (LocProcess (n, sub_of_proc p), LocAttacker(ca)))
	  | "output" ->
	      CommTest (pub, tc, Some (LocAttacker(ca), LocProcess (n, sub_of_proc p)))
	  | _ -> assert false
	end
    | DOutputMess(_, _, _, _, _, div) ->
	(* Corresponds to an output followed by a divergence (DEquality(...) or DFail(...))
           on the output message *)
       get_goal div
    | DEquality(i, recipe, result, ca, pub) ->
       NIEqTest ((result, Some (recipe)), (pub, Some (ca)))
    | DEval (_, _, _, n, p) | DEvalOut(_, _, _, n, p) | DEvalLet(_, _, _, n, p)
    | DEvalFact (_, _, n, p)
    | DGet (_, _, _, _, n, p) | DTest(_, _, _, _, _, n, p) | DLetFilter(_, _, _, n, p) ->
       ProcessTest ([], [], Some (n, sub_of_proc p))
    | DInputPat(i, recipe, result, pat, n, p) ->
       InputProcessTest ([], [], result, Some (n, sub_of_proc p, LocAttacker recipe))
    | DIO(i, cin, cout, nin, pin, nout, pout) ->
       CommTest (cin, cout, Some (LocProcess (nin, sub_of_proc pin), LocProcess (nout, sub_of_proc pout)))
    | DIOPat( i, t, t', pat, nin, pin, nout, pout) ->
       InputProcessTest ([], [], t', Some (nin, sub_of_proc pin, LocProcess(nout, sub_of_proc pout)))
    | DFail(i, r, exp) ->
       NIFailTest (exp, Some(r))
  in
  { state with
    goal = NonInterfGoal (get_goal div);
    comment = RDiverges div;
    previous_state = Some state }



(* [is_in_public_test_div public t] returns true if [t] is in [public].
   In diff-mode, raise [(DivTermPub (i, t, ca, pub)], when the public term
   [pub] (where [ca] is the recipe giving [pub]), is different from
   [t] only on side [i] *)

let rec is_in_public_test_div public t =
  if not (!Param.bipro_i_mode) then
    (Evaluation_helper.is_in_public public t != None)
  else
    let find_side_in_pub side_t side public =
      let (ca, pub) =
	List.find (fun (ca, pub) ->
	  Reduction_helper.equal_terms_modulo side_t (choice_in_term side pub)) public
      in
      (ca, (choice_in_term 1 pub, choice_in_term 2 pub))
    in
    (* [find_side_in_pub_decompose side_t side public] finds
       a public term whose side [side] is equal to [side_t].
       In case of success, returns [(ca, (pub1, pub2))]
       where [ca] is the recipe to compute this term,
       and this term is [choice[pub1,pub2]].
       In case of failure, raises [Not_found]. *)
    let rec find_side_in_pub_decompose side_t side public =
      match side_t with
	FunApp({f_cat = Tuple} as f, l) ->
	  let (cal, publ) =
	    List.split (List.map (fun t -> find_side_in_pub t side public) l)
	  in
	  let (publ1, publ2) = List.split publ in
	  (FunApp(f, cal), (FunApp(f, publ1), FunApp(f, publ2)))
      | _ ->
	  find_side_in_pub side_t side public
    in
    let fst_t = choice_in_term 1 t in
    let snd_t = choice_in_term 2 t in
    try
      let (ca, (pub1, pub2)) = find_side_in_pub_decompose fst_t 1 public in
      if Reduction_helper.equal_terms_modulo snd_t pub2 then
	(* [t] is public *)
	true
      else
	(* divergence: equality only on side 1 *)
	raise (DivTermPub (2, t, ca, make_choice pub1 pub2))
    with Not_found ->
      try
	let (ca, (pub1, pub2)) = find_side_in_pub_decompose snd_t 2 public in
	if Reduction_helper.equal_terms_modulo fst_t pub1 then
	  (* [t] is public -- in fact, should have been discovered above *)
	  true
	else
	  (* divergence: equality only on side 2 *)
	  raise (DivTermPub (1, t, ca, make_choice pub1 pub2))
      with Not_found ->
	(* [t] is not public *)
	false

(* [decompose_term_all_mode (recipe, t)] decomposes tuples at the root
   of [t].
   Returns a list of pairs [(recipe_i, t_i)] corresponding to the tuple
   components of [t]. *)

let decompose_term_all_mode recipe_term =
  if !Param.bipro_i_mode then
    let (recipe, t) = recipe_term in
    let fst_t = choice_in_term 1 t in
    let snd_t = choice_in_term 2 t in
    let recipe_pair_list = Reduction_bipro.decompose_term (recipe, (fst_t, snd_t)) in
    List.map (fun (recipe, (t1, t2)) -> (recipe, make_choice t1 t2)) recipe_pair_list
  else
    Evaluation_helper.decompose_term recipe_term

(* [decompose_term_rev_all_mode t] decomposes tuples at the root of [t].
   Returns [(recipe, l)] where [l] is a list of pairs (recipe_i, t_i)
   where the [t_i]'s are the tuple components of [t], and [recipe_i]
   is a corresponding recipe variable. [recipe] is the recipe
   to rebuild [t] from the recipes of its components.
   This function is used for output messages: the [(recipe_i, t_i)]
   are added to public, and [recipe] is the label of the output arrow. *)

let decompose_term_rev_all_mode t =
  let new_recipe = new_var ~orig:false "~M" (get_term_type t) in
  let l' =
    if !Param.bipro_i_mode then
      let fst_t = choice_in_term 1 t in
      let snd_t = choice_in_term 2 t in
      let l = Reduction_bipro.decompose_term_rev (new_recipe, (fst_t, snd_t)) in
      List.map (fun (b,(t1,t2)) -> (Var b, make_choice t1 t2)) l
    else
      let l = Evaluation_helper.decompose_term_rev (new_recipe, t) in
      List.map (fun (b,t) -> (Var b, t)) l
  in
  (Terms.copy_term4 (Var new_recipe), l')

(* [add_public_dec_all_mode state (recipe, term)] adds the term [term]
   the public terms in [state].
   The tuples at the root of term [term] must be decomposed before.
   If [term] is already public, the state [state] is returned physically
   unchanged.
   In diff-mode, raises [Div] in case of divergence: when one component
   of [term] has a tuple at the root, or is equal to a term in public
   but not the other component. *)

let add_public_dec_all_mode state ((recipe, term) as recipe_term) =
  if !Param.bipro_i_mode then
    let fst_t = choice_in_term 1 term in
    let snd_t = choice_in_term 2 term in
    match fst_t, snd_t with
    | FunApp({ f_cat = Tuple } as f, _), FunApp(f', _) when f == f' ->
	(* Should already be decomposed *)
	assert false
    | FunApp({ f_cat = Tuple } as f, _), _ ->
	let proj_1 = Terms.projection_fun (f, 1) in
	raise (Div(DFail(2, FunApp(proj_1, [recipe]), FunApp(proj_1, [term]))))
    | _, FunApp({ f_cat = Tuple } as f, _) ->
	let proj_1 = Terms.projection_fun (f, 1) in
	raise (Div(DFail(1, FunApp(proj_1, [recipe]), FunApp(proj_1, [term]))))
    | _ ->
	(* No tuple at the root of the sides *)
	if List.exists (fun (ca, pub) ->
	  let r1 = Reduction_helper.equal_terms_modulo fst_t (get_left pub) in
          let r2 = Reduction_helper.equal_terms_modulo snd_t (get_right pub) in
          if r1 && r2 then
            true
          else
            if r1 then
              raise (Div(DEquality(2, recipe, term, ca, pub)))
            else
              if r2 then
		raise (Div(DEquality(1, recipe, term, ca, pub))
)              else
		false) state.public
	then
	  state
	else
	  { state with
            public = recipe_term :: state.public }
  else
    if List.exists (fun (_, t) ->
      Reduction_helper.equal_terms_modulo t term) state.public then
      state
    else
      { state with
        public = recipe_term :: state.public }

let add_public_list_dec_all_mode state l =
  List.fold_left add_public_dec_all_mode state l

(* [match_pat_eval_bipro_to_true pat t term] Return [unit] if the *)
(* the pattern-matching between [pat] and [term] succeeds, and after it, *)
(* the evaluation of [t] modulo the equational theory is equal to [true] on both side *)
(* Raise [Unify] if the evaluation fails on both sides, or if both sides *)
(* evaluates to false. Raise [FailOneSideOnly i] if the evaluation fails on side [i] only *)
let match_pat_eval_bipro_to_true pat t term =
  ignore(bi_action (fun side ->
             let term' = choice_in_term side term in
             Reduction_bipro.match_pattern pat side term';
             let t' = Reduction_bipro.term_evaluation_fail t side in
             if not (Reduction_helper.equal_terms_modulo t' true_term) then
               raise Unify))


let match_pat_eval_to_true_all_mode pat t term =
  if !Param.bipro_i_mode then
    match_pat_eval_bipro_to_true pat t term
  else
    begin
      Evaluation_helper.match_pattern pat term;
      let t' = Evaluation_helper.term_evaluation_fail t in
      if (not (Reduction_helper.equal_terms_modulo t' true_term)) then
        raise Unify
    end

(* [match_terms_lst tables pat t n p] Return all the terms in the  *)
(* tables [tables] that match the pattern [pat] and [t] evaluates to [true] after this *)
(* pattern-matching (for both sides in diff-mode). Might raise exceptions *)
(* (see [display_div]) *)
let match_terms_lst tables pat t n p =
  List.filter (fun term ->
      try
        auto_cleanup (fun () ->
            match_pat_eval_to_true_all_mode pat t term;
            true
          )
      with
        Unify -> false
      | FailOnlyOnSide i ->
         raise (Div(DGet(i,term, pat, t, n, p)))
    )
    tables

(* [is_auto_reductible state p n] Return true if the n-th column of the view  is auto reductible, *)
(* false otherwise. *)
(* In diff-mode, used to detected most of the processes that diverges (except in private *)
(* communication cases). If process are divergent, [display_div] is called with the *)
(* appropriate parameter *)
let is_auto_reductible state p n =
  match p with
    Nil
  | Par _ | Restr _ | NamedProcess _
  | Let _ | LetFilter _ | Test _ | Event _ -> true
  | Output(tc, t, p', _)  ->
     begin
       try
         let (tc' , t) = evaluates_2terms_all_mode tc t in
         is_in_public_test_div state.public tc'
       with
         Unify
       | FailOnlyOnSide _
       | DivTermPub _ -> true
     end
  | Input(tc, _, _, _) ->
     begin
       if !Param.bipro_i_mode then
         begin
           try
             let (l, r) = evaluates_both_sides tc in
             let _ = is_in_public_test_div state.public (make_choice l r) in
             false
           with
           | FailOnlyOnSide _
           | DivTermPub _
           | Unify -> true
         end
       else
         try
           let _ = term_evaluation_fail tc in
	   false
         with Unify ->
           true
     end
  | Insert (t, _, _)->
     begin
       try
        let _ = evaluates_term_all_mode t in
        only_one_proc state
       with
         FailOnlyOnSide i -> true
       | Unify -> true
     end
  | Get(pat, t, _, _, _) ->
     if not !Param.bipro_i_mode then
       only_one_proc state
     else
       begin
         try
           let _ = match_terms_lst state.tables pat t n p in
           only_one_proc state
         with Div(div) ->
           true
       end
  | _ -> false


(* Same as GToolbox.question_box but with pango markup *)
let question_box ~title  ~buttons ?(default=1) ?(width=800) ?(height=280) message =
  let button_nb = ref 0 in
  let window = GWindow.dialog ~position:`CENTER ~width ~height ~allow_shrink:true ~modal:true ~title () in
  let s_win =  GBin.scrolled_window ~packing:(window#vbox#pack ~expand:true) () in
  let hbox = GPack.hbox ~border_width:10 ~packing:s_win#add_with_viewport () in
  let bbox = window#action_area in
  ignore (GMisc.label ~justify:`LEFT ~xalign:0. ~yalign:0. ~markup:message ~packing: hbox#pack ());
  (* the function called to create each button by iterating *)
  let rec iter_buttons n = function
      [] ->
       ()
    | button_label :: q ->
       let b = GButton.button ~label: button_label
                 ~packing:(bbox#pack ~expand:true ~padding:4) ()
       in
       let _ = b#connect#clicked ~callback:
                 (fun () -> button_nb := n; window#destroy ()) in
       (* If it's the first button then give it the focus *)
       if n = default then
         begin
           b#grab_default ();
           b#misc#grab_focus ();
         end;
       iter_buttons (n+1) q
  in
  iter_buttons 1 buttons;
  let _ = window#connect#destroy ~callback:GMain.Main.quit in
  window#set_position `CENTER;
  window#show ();
  GMain.Main.main ();
  !button_nb

(* [string_of_proc_first_line state proc] Return the string witch will be put as titles of *)
(* store columns to represent [proc], in respect to [state] *)
let string_of_proc_first_line state proc n =
  match proc with
  | Nil -> "Nil"
  | Par _ ->  "Par"
  | Repl _-> "Replication"
  | Restr _ -> "Restriction"
  | Test _ | LetFilter([], _, _, _, _) -> "Test"
  | Input(tin, _, _, _) ->
     begin
       try
         let tin' = evaluates_term_all_mode tin in
         if is_in_public_test_div state.public tin' then
           "Input (public)"
         else
           "Input (private)"
       with Unify ->
             if !Param.bipro_i_mode then
               "Input (channel fails on both sides)"
             else
               "Input (channel fails)"
          | FailOnlyOnSide _ | DivTermPub _ ->
             "Input (divergence)"

     end
  | Output(tc, mess, _, _) ->
     begin
       try
         let (tc',_) = evaluates_2terms_all_mode tc mess in
         if is_in_public_test_div state.public tc' then
           "Output (public)"
         else
           "Output (private)"
       with
         Unify -> if !Param.bipro_i_mode then
                    "Output (channel or message fails on both sides)"
                  else
                    "Output (channel or message fails)"
       | FailOnlyOnSide _ | DivTermPub _ ->
          "Output (divergence)"
     end
  | Let _ -> "Let"
  | LetFilter _ -> "Let...suchthat"
  | Event _ -> "Event"
  | Insert _ -> "Insert"
  | Get _ -> "Get"
  | Phase _ -> "Phase"
  | NamedProcess(s, _, _) -> "Process" ^ s
  (* This case should not happen. NamedProcess are erased *)
  | _ -> "Other"


let equal_io_oi x y =
  match x, y with
  | (I_O (cin, nin, _, _, pin), O_I (cout, nout, t, _, pout))
    | (O_I (cout, nout, t, _, pout), I_O (cin, nin, _, _, pin)) ->
     begin
         try
           (* If evaluation of cin or cout fails on only one side, *)
           (* an exception is raised *)
           (* when [is_auto_reductible] is called. So we don't need to *)
           (* test it here *)
           let (cout', _) = evaluates_2terms_all_mode cout t in
           let cin' = evaluates_term_all_mode cin in
           try
             equal_terms_modulo_all_mode cin' cout'
           with FailOnlyOnSide i ->
             raise (Div (DIO(i, cin, cout, nin, pin, nout, pout)))
         with
           Unify -> false
         | FailOnlyOnSide i ->
            false
     end
  | _ -> false

let string_of_events t = Display_interact.GtkInteract.display_term t

let rec get_table_name t =
  match t with
    FunApp({f_name = Fixed name},tl) ->
     if name = "choice" then
       get_table_name (List.hd tl)
     else
       name
  | _ -> assert false

(* [get_data_from_state ()] Return the data associated to the current state. *)
(* [is_auto_reductible] might raises an exception *)
let get_data_from_state () =
  debug_print "get_data";
  let string_lst_of_barriers barriers = [] (* TO DO *)
  in
  let state = get_state () in
  let exists_auto = ref false in
  let plst = get_proc_list state in
  let rec aux n tlst plst = function
    | [] -> (List.rev tlst, List.rev plst)
    | p::tl ->
       if is_auto_reductible state p n then
         exists_auto := true;
       let pt = string_of_proc_first_line state p n in
       let sp = Display_interact.GtkInteract.display_process p in
       let is_io_p = match p with
           Input (tin, pat, p, _) as proc -> I_O (tin, n, pat, p, proc)
         | Output (tou, t, q, _) as proc -> O_I (tou, n, t, q, proc)
         | _ -> Other in
       aux (n + 1) ((pt,is_io_p)::tlst) (sp::plst) tl
  in
  let last_id = ref None in
  let add_space_if_needed tables =
    let rec aux acc = function
        [] -> List.rev acc
      | t::tl ->
         let t' = Display_interact.GtkInteract.display_term t in
         let name = get_table_name t in
         begin
           match !last_id with
             None ->
              last_id := Some (name);
              aux (t'::acc) tl
           | Some(f') ->
              if not (name = f') then
                begin
                  last_id := Some name;
                  aux (t'::""::acc) tl
                end
              else
                aux (t'::acc) tl
         end
    in
    aux [] tables
  in
  let tables_lst = add_space_if_needed state.tables in
  let public_lst = Display_interact.GtkInteract.display_public state.public state.pub_vars in
  let barriers_lst = string_lst_of_barriers () in
  let (titles, proc_llst) = aux 0 [] [] plst in
  let events_lst = List.rev_map string_of_events state.events in
  {tables_lst; public_lst; titles = ("Tables", Other)::("Events", Other)::("Public", Other)::titles; proc_llst; no_auto = not !exists_auto; events_lst; barriers_lst}

(* [cur_data] Reference on the current data associated to [!cur_state] *)
let cur_data = ref (get_data_from_state ())

(* [get_data ()] Return the current data associated to the current state *)
let get_data () = !cur_data

(* [is_first_step ()] Return true if the current state is the initial state, false otherwise *)
let is_first_step () =
  let rec aux state = match state.previous_state, state.comment with
      None, _ -> true
    | Some (s), RNamedProcess(_) -> aux s
    | _ -> false
  in
  aux (!cur_state)


(* [exists_auto ()] Return true if there exists a auto-reductible process *)
(* in one of the subprocess of the current state, false otherwise *)
let exists_auto () = not (!cur_data.no_auto)

(* [update_cur_state state] Update the current state with [state], and the *)
(* current data associated to it *)
let update_cur_state state =
  cur_state := state;
  cur_data := get_data_from_state ()

(* [reset_env ()] Reset the global environment, clear tables, restore some parameters. *)
(* Used to load a new file *)
let reset_env () =
  reset_forward_lst();
  cur_state := initialize_state ()

(* [input_error_box b mess ext] Create a message box with title "Error in your Recipe", and one *)
(* button. The message displayed is comming from an InputError(mess, ext) exception. If [b] *)
(* is true, the the message display the line number and the character number of the error. *)
(* Otherwise, its only display the character number *)
let input_error_box b mess ext =
  let mess' = Parsing_helper.get_mess_from b "Error: " mess ext in
  let _ =  question_box "Error" ["OK"] mess' in
  ()

(* [add_var_env env b] Add the binder [b] to [env] *)
let add_var_env env b =
  let s = Display.string_of_binder b in
  Stringmap.StringMap.add s (EVar b) env

let args_to_string tl =
  let l = List.length tl in
  if l=0 then
    "0 argument"
  else if l=1 then
    "1 argument of type " ^ (tl_to_string ", " tl)
  else
    (string_of_int l) ^ " arguments of types " ^ (tl_to_string ", " tl)

let type_compatible ty1 ty2 =
  ty1 == ty2 || (Param.get_ignore_types() && (ty1 == Param.any_type || ty2 == Param.any_type))

let rec compatible_lists l1 l2 =
  match l1,l2 with
    [],[] -> true
  | a1::q1,a2::q2 -> (type_compatible a1 a2) && (compatible_lists q1 q2)
  | _,_ -> false

let type_error mess ext =
  if Param.get_ignore_types() then
    Parsing_helper.input_warning (mess ^ (Parsing_helper.add_point_if_necessary mess) ^
				    "\nThis is acceptable because types are ignored.") ext
  else
    Parsing_helper.input_error mess ext

let rec split_string s =
  try
    let pos_first_dash = String.index s '-' in
    let s1 = String.sub s 0 pos_first_dash in
    let s2 = String.sub s (pos_first_dash+1) (String.length s -pos_first_dash-1) in
    s1 :: split_string s2
  with Not_found ->
    [s]

let rec id_list_to_types = function
    [] -> raise Not_found
  | ["tuple"] -> []
  | [_] -> raise Not_found
  | a::r ->
     let ty = List.find (fun t -> t.tname = a) (!Param.current_state).pi_types in
     let ty_r = id_list_to_types r in
     ty::ty_r

let rec check_eq_term env (term,ext) =
  match term with
  | Pitptree.PFail -> None
  | (Pitptree.PIdent (s,ext)) ->
     let t =
       try
	 match Stringmap.StringMap.find s env with
	 | EVar v -> Var v
	 | EFun f ->
	    if fst f.f_type <> [] then
	      Parsing_helper.input_error ("function " ^ s ^ " expects " ^
					    (string_of_int (List.length (fst f.f_type))) ^
					      " arguments but is used without arguments") ext;
            if f.f_private then
              Parsing_helper.input_error ("identifier " ^ (Display.string_of_fsymb f) ^ " is private") ext;
            FunApp(f, [])
         | EName r ->
            if r.f_private then
              Parsing_helper.input_error ("identifier " ^ (Display.string_of_fsymb r) ^ " is private") ext;
            FunApp(r, [])
	 | _ -> Parsing_helper.input_error ("identifier " ^ s ^ " should be a function, a variable, or a name") ext
       with Not_found ->
	 Parsing_helper.input_error ("identifier " ^ s ^ " not defined") ext
     in
     Some (t, get_term_type t)
  | (Pitptree.PFunApp ((f,ext), tlist)) ->
     begin
       let tol = List.map (check_eq_term env) tlist in
       match f, tol with
	 "=", [to1;to2] ->
	  begin
            match to1, to2 with
            | Some (t1, ty1), Some (t2, ty2) ->
	       if not (type_compatible ty1 ty2) then
		 type_error ("function " ^ f ^ " expects two arguments of same type but is here given " ^ args_to_string [ty1;ty2]) ext;
	       Some(FunApp(equal_fun ty1, [t1; t2]), Param.bool_type)
            | _ ->
	       Some(get_fail_term Param.bool_type, Param.bool_type)
	  end
       | "<>", [to1;to2] ->
	  begin
	    match to1, to2 with
	    | Some (t1, ty1), Some (t2, ty2) ->
	       if not (type_compatible ty1 ty2) then
		 type_error ("function " ^ f ^ " expects two arguments of same type but is here given " ^
    		               args_to_string [ty1;ty2]) ext;
	       Some(FunApp(diff_fun ty1, [t1; t2]), Param.bool_type)
            | _ ->
	       Some(get_fail_term Param.bool_type, Param.bool_type)
	  end
       | ("=" | "<>"), _ ->
	  Parsing_helper.input_error (f ^ " expects two arguments") ext
       | "choice", _ ->
	  Parsing_helper.input_error "choice is not allowed in recipes" ext;
       | _ ->
	  try
	    match Stringmap.StringMap.find f env with
              EFun r ->
	       if (List.length (fst r.f_type)) != List.length tol then
      		 Parsing_helper.input_error ("function " ^ f ^ " expects " ^
        				       args_to_string (fst r.f_type) ^
        				         " but is here given " ^
        				           args_to_string (List.map (fun t ->
                                                                       match t with
                                                                         None -> Param.any_type
                                                                       | Some(_, ty) -> ty) tol)) ext;
	       let (tl', tyl) =
		 List.split (List.map2 (fun ty t ->
		                 match t with
		                 | None -> (get_fail_term ty, ty)
		                 | Some (t, ty') -> (t, ty')
			       ) (fst r.f_type) tol)
	       in
	       if not (compatible_lists (fst r.f_type) tyl) then
      		 type_error ("function " ^ f ^ " expects " ^
        		       args_to_string (fst r.f_type) ^
        		       " but is here given " ^
        		       args_to_string tyl) ext;
		 if r.f_private then
		   Parsing_helper.input_error ("identifier " ^ (Display.string_of_fsymb r) ^ " is private") ext;
		 if (r.f_options land Param.fun_TYPECONVERTER != 0) && (Param.get_ignore_types()) then
		   match tl' with
		     [t] -> Some (t, snd r.f_type)
		   | _ -> Parsing_helper.input_error ("type converter functions should always be unary") ext
		 else
		   Some (FunApp(r, tl'), snd r.f_type)
	     | x -> Parsing_helper.input_error (f ^ " should be a function") ext
	   with Not_found ->
	     Parsing_helper.input_error (f ^ " not defined") ext
     end
  | (Pitptree.PTuple tlist) ->
     let tl' = List.map (check_eq_term env) tlist in
     let (tl, tyl) =
       List.split (List.map (function
	               | None ->
	                  let ty = Param.bitstring_type in
	                  (get_fail_term ty, ty)
	               | Some (t',ty) ->
	                  (t', ty)) tl')
     in
     Some (FunApp (get_tuple_fun tyl, tl), Param.bitstring_type)
  | (Pitptree.PProj((f, ext), t)) ->
     let t' = check_eq_term env t in
     (* f is of the form "<integer>-proj-<identifier>"
	 <integer> is the position of the element extracted by the projection
	 <identifier> is the corresponding tuple function *)
     let f_split = split_string f in
     match f_split with
       n_str :: "proj" :: id_list ->
	begin
	  let n = int_of_string n_str in
	  let tuple_fun =
	    match id_list with
	      [fun_name] ->
	       begin
		 try
		   match Stringmap.StringMap.find fun_name env with
		     EFun r when r.f_cat == Tuple ->
		      r
		   | _ ->
		      Parsing_helper.input_error ("Projection " ^ f ^ " should refer to a [data] function") ext
		 with Not_found ->
		   Parsing_helper.input_error ("Function " ^ fun_name ^ " not defined. Projection " ^ f ^ " should refer to a [data] function") ext
	       end
	    | _ ->
	       if Param.get_ignore_types() then
		 (* The default tuple functions are written <n'>-tuple *)
		 match id_list with
		   [n_str'; "tuple"] ->
		    begin
		      try
			let n' = int_of_string n_str' in
			let tl = copy_n n' Param.any_type in
			get_tuple_fun tl
		      with _ ->
			Parsing_helper.input_error "After -proj-, we accept either an existing [data] function or a default tuple function written <n>-tuple" ext
		    end
		 | _ ->
		    Parsing_helper.input_error "After -proj-, we accept either an existing [data] function or a default tuple function written <n>-tuple" ext
	       else
		 (* The default tuple functions are written <typelist>-tuple *)
		 try
		   let tl = id_list_to_types id_list in
		   get_tuple_fun tl
		 with Not_found ->
		   Parsing_helper.input_error "After -proj-, we accept either an existing [data] function or a default tuple function written <type-list>-tuple" ext
	  in
	  if (n < 1) || (n > List.length (fst tuple_fun.f_type)) then
	    Parsing_helper.input_error ("Component does not exist in projection " ^ f) ext;
	  let proj_fun = projection_fun (tuple_fun, n) in
	  match t' with
	    Some(t'', ty) ->
	     if not (type_compatible ty (snd tuple_fun.f_type)) then
	       type_error ("function " ^ f ^ " expects " ^
        		     args_to_string (fst proj_fun.f_type) ^
        		       " but is here given " ^
        		         args_to_string [ty]) ext;
	     Some (FunApp(proj_fun, [t'']), snd proj_fun.f_type)
	    | None ->
	       let t'' = Terms.get_fail_term (snd tuple_fun.f_type) in
	       Some (FunApp(proj_fun, [t'']), snd proj_fun.f_type)
	end
     | _ -> Parsing_helper.internal_error "Bad projection name"

exception WarningsAsError

(* [parse_term string] Return the term corresponding to the parsing of [string]. *)
(* Call input_error if the parsing went wrong *)
let parse_term s =
  let state = get_state () in
  let lexbuf = Lexing.from_string s in
  let ptree =
    try
      Pitparser.term Pitlexer.token lexbuf
    with
      Parsing.Parse_error -> Parsing_helper.input_error ("Syntax error") (Parsing_helper.extent lexbuf)
  in
  let global_env =
    match (!Param.current_state).pi_global_env with
    | Set global_env -> global_env
    | Unset ->
       Parsing_helper.internal_error "global_env should be set"
  in
  let pub_vars = state.pub_vars in
  let env = List.fold_left
              (fun accu var ->
                match var with
                  Var x -> add_var_env accu x
                | FunApp(n,[]) ->
                   begin
	             match n.f_cat with
	               Name _ -> Stringmap.StringMap.add (Display.string_of_fsymb n) (EName n) accu
	             | _ -> accu
	           end
                | _ -> accu) global_env pub_vars
  in
  let term =
    match check_eq_term env ptree with
    | None -> get_fail_term Param.bitstring_type
    | Some(t, _) -> t
  in
  let warnings = Parsing_helper.get_warning_list() in
  if warnings != [] then
    begin
      let messages = String.concat "" (List.map (fun (mess, ext) ->
	                                   (Parsing_helper.get_mess_from false "Warning: " mess ext) ^ "\n") warnings) in
      let messages = messages ^ "Do you want to continue?" in
      match (question_box "Warnings" ["Yes"; "No"] messages ) with
	0 | 1 -> ()
        | _ -> raise WarningsAsError
    end;
  term

(* [delete_NamedProcess state] Return the state obtained after *)
(* applying recursively all the NamedProcess  *)
(* reductions steps to the subprocesses of state that are named *)
let delete_NamedProcess state =
  let proc_nb = List.length state.subprocess  in
  let rec aux state n =
    if n = proc_nb then state
    else
      let proc = get_proc state n in
      match proc with
      | NamedProcess (name, l, p') ->
         let n_sub = sub_of_proc p' in
         let n_state =
           {state with
             subprocess = Reduction_helper.replace_at n n_sub state.subprocess;
             comment = RNamedProcess (n, name, l);
             previous_state = Some state
           } in
         aux n_state n;
      | _ -> aux state (n + 1)
  in
  aux state 0


(* Callback function to make a forward step. Update the list of *)
(* forward steps *)
let one_step_forward () =
  match !forwards_lst with
    [] -> ()
  | hd::tl ->
     forwards_lst := List.tl !forwards_lst;
     update_cur_state (delete_NamedProcess hd)

(* Used for RIO reductions *)
let io_c = ref Pitypes.Other

let set_io_c c = io_c := c

let get_io_c () = !io_c

let ans = ref None

(* [get_recipe public_aux pref text] Display a window with title "Give Recipe, with public elements on the left", and a dialog box on the right *)
(* [pref] is used to display error messages if the user makes a mistake. *)
(* [text] is the message displayed in the dialog box. *)
(* The user enter a string. This string is parsed to a term. *)
(* If parsing failed, a new dialog window is opened, and the *)
(* parsing error message is shown. The user can enter a new string. *)
(* Otherwise, at the end of the call to [get_recipe_aux], *)
(* the reference [ans] contains [Some(t)] where [t] is the parsed *)
(* term corresponding to the input string (otherwise if the user *)
(* quits, the ref contains [None]. *)
let rec get_recipe_aux pref text =
  let rec do_ok m_win entry pref text () =
    try
      let str = entry#text in
      ans:= Some (parse_term str);
      m_win#destroy ()
    with
      Parsing_helper.InputError(mess, extent) ->
       let str = entry#text in
       let mess' = Parsing_helper.get_mess_from false "Error: " mess extent in
       let _ = m_win#destroy() in
       if str = "" then
         get_recipe_aux  "" text
       else
         get_recipe_aux ("entry: "  ^ str ^ "\n" ^ mess') text
    | WarningsAsError ->
       let _ = m_win#destroy() in
       get_recipe_aux "" text
  in
  (* Return the scrolled window containing a view with the public *)
  (*  elements of state *)
  let create_public state =
    let s_win = GBin.scrolled_window () in
    let c_lst = new GTree.column_list in
    let col_public = c_lst#add Gobject.Data.string in
    let store = GTree.list_store c_lst in
    let rec fill p =
      let iter = store#append () in
      store#set ~row:iter ~column:col_public p
    in
    List.iter fill (Display_interact.GtkInteract.display_public state.public state.pub_vars);
    let c_p = GTree.view_column ~title:"Public elements" ~renderer:(GTree.cell_renderer_text [], ["markup", col_public]) () in
    c_p#set_resizable true;
    let v = GTree.view ~enable_search:false ~width:640  ~packing:(s_win#add) ~model:store () in
    let _ = v#append_column c_p in
    s_win#coerce
  in
  ans := None;
  let state = get_state () in
  (* Main window *)
  let m_win = GWindow.dialog ~title:"Give recipe"
                ~width:640 ~height:400 ~allow_shrink:true ~border_width:5 () in
  let _ = m_win#connect#destroy ~callback:(fun () ->
              begin
                m_win#destroy();
                GMain.Main.quit()
              end) in
  let s_win = create_public state in
  let _ = m_win#vbox#pack ~expand:true s_win in
  (* Label with user text, packed after the view *)
  let _ = GMisc.label
            ~markup:(pref ^ "\n" ^ text) ~xalign:0.01
            ~packing:(m_win#vbox#pack) ()
  in
  (* Create entry, and link key_press events *)
  let entry = GEdit.entry  ~text:"" ~packing:(m_win#vbox#pack ~padding:3) () in
  let _ = entry#event#connect#key_press ~callback:(
              begin fun ev ->
              if GdkEvent.Key.keyval ev = GdkKeysyms._Return then
                do_ok m_win entry pref text ();
              if GdkEvent.Key.keyval ev = GdkKeysyms._Escape then
                m_win#destroy ();
              false
              end;) in
  (* Put the cursor on entry *)
  entry#misc#grab_focus ();
  (* Create ok and cancel button, with associated callbacks. *)
  (* Pack them in the action area of the main dialog window *)
  let ok_b = GButton.button ~stock:`OK ~packing:(m_win#action_area#pack ~padding:3) () in
  let c_b = GButton.button ~stock:`CANCEL ~packing:(m_win#action_area#pack ~padding:3) () in
  let _ = ok_b#connect#clicked ~callback:(do_ok m_win entry pref text) in
  let _ = c_b#connect#clicked ~callback:m_win#destroy in
  m_win#show ();
  ok_b#grab_default ();
  GMain.Main.main()

let get_recipe pref text =
  get_recipe_aux pref text;
  match !ans with
  | None -> raise WrongChoice
  | Some s -> s

(* [get_new_vars state public'] returns a pair:
   - list of elements of [public'] added at the head of [state.public]
   with an additional term used to designate them in recipes.
   - list of these additional terms added at the head of [state.pub_vars],
   so that this list is the new value of [state.pub_vars], corresponding
   to [public'].
   The fresh variables are generated in increasing order from the
   the queue of [public'] to its head, so that they appear in increasing
   order when the terms are displayed. *)
let get_new_vars state public' =
  (* [get_new_pub [] public public'] returns the elements
     of [public'] that have been added at the head of [public],
     in reverse order. *)
  let rec get_new_pub new_pub public public' =
    if public == public' then
      new_pub
    else
      match public' with
	a::l -> get_new_pub (a::new_pub) public l
      | _ -> assert false
  in
  let new_pub = get_new_pub [] state.public public' in
  (* [add_vars [] state.pub_vars new_pub] returns a pair
     - elements of [new_pub] with an additional term used to designate
     them in recipes, in reverse order.
     - those additional terms added to [state.pub_vars]. *)
  let rec add_vars new_pub_v new_v = function
      (p',mess)::l ->
       let q =
	 (* [q] is the term that user can use to designate
	     the message in recipes.
	     It is a fresh variable if the recipe is not
	     a variable or a constant. *)
          match p' with
            Var _ | FunApp(_, []) ->
	      p'
          | FunApp(f, _) ->
              Var (new_var ~orig:false "~M" (snd f.f_type))
	in
        add_vars ((q, p', mess)::new_pub_v) (q::new_v) l
    | [] -> (new_pub_v, new_v)
  in
  add_vars [] state.pub_vars new_pub

(* [expand_recipe pub_vars public recipe] expand the [recipe] according to variables linked to equations in public, *)
(* and returns the obtained term *)
let expand_recipe pub_vars public recipe =
  auto_cleanup (fun () ->
      List.iter2 (fun v (_,t') ->
          match v with
	    Var x -> link x (TLink t')
          | _ -> ()) pub_vars public;
      copy_term3 recipe)
