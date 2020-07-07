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
(* Types module declares types of the abstract syntax
   tree and of sets of messages.
   There are recursive dependencies between these types,
   that is why they are included in the same module
*)

open Stringmap

type occurrence = { occ : int; precise : bool }

(* Types *)

type typet = { tname : string }

(* Information for predicates. The integer argument corresponds
   to the phase of the predicate *)
type info =
    Attacker of int * typet
  | Mess of int * typet
  | InputP of int
  | OutputP of int
  | AttackerBin of int * typet
  | MessBin of int * typet
  | InputPBin of int
  | OutputPBin of int
  | AttackerGuess of typet
  | Compromise of typet
  | Equal of typet
  | Table of int
  | TableBin of int
  | TestUnifP of typet
  | PolymPred of string * int(*value of p_prop*) * typet list
  | Combined of predicate list
  | NegationPred of predicate

and predicate = { p_name: string;
                  p_type: typet list;
		  p_prop: int;
		  p_info: info list }

type when_include =
    Always
  | IfQueryNeedsIt

type eq_info =
    EqNoInfo
  | EqConvergent
  | EqLinear

(* Identifiers that can be renamed *)

type renamable_id = {
    orig_name : string; (* Original name in the input file.
                           Empty string if there is no original name.
                           When not empty, [orig_name] is used for display
                           if it is not already used for another identifier in
                           the same scope. *)
    name : string; (* Prefix of the name, to be kept during renaming.
                      Often the [orig_name] after removing an _nnn suffix if any *)
    idx : int; (* Index to be modified when renaming.
                  [name]_[idx] provides a unique name for that identifier.
                  [name] and [idx] are not used much now:
                  They provide a unique identifier for debugging purposes,
                  but they are not used for normal display. *)
    mutable display : string option (* The identifier as it is displayed.
                                       Several identifiers may be displayed with the same
                                       string in different scopes *)
  }

(* Some function symbols have a fixed name (constructors, destructors,
   free names in the typed front-end, ...)
   and some can be renamed (bound names, general variables, the symbol "any_val", ...).
   The type [fixed_or_renamable] allows to handle these two cases. *)

type fixed_or_renamable =
    Fixed of string
  | Renamable of renamable_id

(* Variables *)

type binder = { vname : renamable_id;
                unfailing : bool;
		btype : typet;
		mutable link : linktype }

(* Processes: patterns *)

and pattern =
    PatVar of binder
  | PatTuple of funsymb * pattern list
  | PatEqual of term

(* What can be linked from variables *)

and linktype =
    NoLink
  | VLink of binder
  | TLink of term
  | TLink2 of term (* used only in reduction.ml *)
  | FLink of format (* used only in syntax.ml *)
  | PGLink of (unit -> term) (* used only in pisyntax.ml and pitsyntax.ml *)

(* Meaning of arguments of names *)

and arg_meaning =
    MUnknown
  | MSid of int (* The argument represents a session identifier *)
  | MCompSid
  | MAttSid
  | MVar of binder * string option
	(* The argument represents a variable.
	   The string option is [Some x] when the argument can be
	   designated by the string [x] in "new a[x = ....]" *)

and name_info = { mutable prev_inputs : term option;
		  mutable prev_inputs_meaning : arg_meaning list }

and funcats =
    Red of rewrite_rules
  | Eq of (term list * term) list
  | Tuple
  | Name of name_info
  | SpecVar of binder
  | Syntactic of funsymb
  | General_var
  | General_mayfail_var
  | Choice
  | BiProj of side
  | Failure
  
and side = Left | Right

(* The following constraints represents the constraints that can occur in a clause,
  namely disequalties between terms, inequalities between natural numbers and
  predicates testing wheter a term is a natural number or not. *)
and constraints =
  {
    neq : (term * term) list list; (* A list of pair of term represents a disjunction of disequalities.
      [neq l] represents a conjunction of disjunctions of disequalities.
      TRUE can be represented by the list [].
      FALSE can be represented by any list that contains [].*)
    is_nat : term list; (* A list of terms that should be natural number. *)
    is_not_nat : term list; (* A list of terms that should not be natural number. *)
    geq : (term * int * term) list  (* [geq l] represents a conjunction of inequalities where each triple
      [(t,n,t')] in [l] means t + n >= t' *)
  }

and rewrite_rule = term list * term * constraints

and rewrite_rules = rewrite_rule list

(* Function symbols *)

and funsymb = { f_name : fixed_or_renamable;
		mutable f_type : typet list * typet; (* type of the arguments, type of the result *)
		mutable f_cat : funcats;
		f_initial_cat : funcats; (* Used to memorize f_cat before closing using the
                                            equational theory. The initial f_cat is used in reduction.ml,
					    and also in check_several_types *)
		f_private : bool; (* true when the function cannot be applied by the adversary *)
		f_options : int
              }

(* Terms *)

and term =
    Var of binder
  | FunApp of funsymb * term list

(* Format, to represent facts with jokers *)

and format =
    FVar of binder
  | FFunApp of funsymb * format list
  | FAny of binder

type fact_format = predicate * format list

type fact =
    Pred of predicate * term list

(* Type of a nounif declaration option *)

type nounif_single_op =
  | Hypothesis
  | Conclusion
  | InductionVerif
  | InductionSat of binder list

type nounif_op = nounif_single_op list

(* Environment elements; environments are needed for terms in queries
   that cannot be expanded before process translation, see link PGTLink
   below *)

type envElement =
    EFun of funsymb
  | EVar of binder
  | EName of funsymb
  | EPred of predicate
  | EEvent of funsymb
  | EType of typet
  | ETable of funsymb
  | ELetFun of (term list -> (term -> process) -> process) * (typet list) * typet
  | EProcess of binder list * process

(* Each restriction "new" is annotated with
   - optionally, the identifiers given between brackets after the "new",
   which serve to determine the arguments in the internal representation
   of the name
   - the current environment at the restriction, which serves to determine
   which variables to use in queries of the form "new a[x = ...]"

Events may also be annotated with identifiers between brackets.
They serve to determine the variables to include in the environment
used for proving injective correspondences.
*)

and new_args = binder list option * envElement StringMap.t

(* Processes *)

and process =
    Nil
  | Par of process * process
  | Repl of process * occurrence
  | Restr of funsymb * new_args * process * occurrence
  | Test of term * process * process * occurrence
  | Input of term * pattern * process * occurrence
  | Output of term * term * process * occurrence
  | Let of pattern * term * process * process * occurrence
  | LetFilter of binder list * fact * process * process * occurrence
  | Event of term  * new_args * process * occurrence
  | Insert of term * process * occurrence
  | Get of pattern * term * process * process * occurrence
  | Phase of int * process * occurrence
  | Barrier of int * string option * process * occurrence
  | AnnBarrier of int * string * funsymb * funsymb * (binder * term) list * process * occurrence
  | NamedProcess of string * term list * process

(* Rule descriptions for History.get_rule_hist *)

type rulespec =
  | RElem of predicate list * predicate
  | RApplyFunc of funsymb * predicate
  | RApplyProj of funsymb * int * predicate  (* For projections corresponding to data constructors *)

(* History of construction of rules *)

type onestatus =
    No | NonInj | Inj

type hypspec =
    ReplTag of occurrence * int(*Number of elements of name_params after it*)
  | InputTag of occurrence
  | PreciseTag of occurrence
  | BeginEvent of occurrence
  | BeginFact
  | LetFilterTag of occurrence (* Destructors succeed *)
  | LetFilterFact
  | OutputTag of occurrence
  | TestTag of occurrence
  | LetTag of occurrence
  | TestUnifTag of occurrence
  | TestUnifTag2 of occurrence
  | InputPTag of occurrence
  | OutputPTag of occurrence
  | InsertTag of occurrence
  | GetTag of occurrence
  | GetTagElse of occurrence

type label =
    ProcessRule of hypspec list * term list
  | Apply of funsymb * predicate
  | TestApply of funsymb * predicate
  | TestEq of predicate
  | LblEquiv
  | LblClause
  | LblEq
  | Rl of predicate * predicate
  | Rs of predicate * predicate
  | Ri of predicate * predicate
  | Ro of predicate * predicate
  | Rfail of predicate
  | TestComm of predicate * predicate
  | WeakSecr
  | Rn of predicate
  | Init
  | PhaseChange
  | TblPhaseChange
  | LblComp
  | LblNone
  | Elem of predicate list * predicate
  | TestUnif
  | TestDeterministic of funsymb
  | TestTotal of funsymb
  | Goal
  | GoalCombined
  | GoalInjective
  | GenerationNested

(* Rules *)

type injectivity =
  | DoubleIndex of int * int
  | SingleIndex of fact (* Conclusion fact*) * fact (* Fact to match *) * int
  | NoIndex of fact (* Conclusion facts*)

type history =
    Rule of int * label * fact list * fact * constraints
  | Removed of int (* Position of the fact removed *) * int (* Position of the duplicated fact *) * history
  | Any of int (* Position of the fact removed in elim_any_x *) * history
  | Empty of fact (* The history for the intial query goal *)
  | HMaxHyp of int * history
  | HEquation of int * fact * fact * history
  | Resolution of history * int * history
  | TestUnifTrue of int * history
  | HLemma of
      int (* Lemma number *) *
      (int * fact) list (* match of lemme's premises with hypothesis of the clause *) *
      (fact list * constraints * (term * term) list) (* Conclusion of lemma *) *
      history (* History of the rule on which the lemma is applied *)
  | HCaseDistinction of
      fact (* The conclusion of the clause *) *
      fact list (* The hypotheses *) *
      (term * term) list (* Substitution to apply *) *
      constraints (* Added constraints *) *
      history (* History of the rule on which the verification is applied *)
  | HInjectivity of injectivity * history
  | HNested of
      int list (* Index matching the premise of the nested query *) *
      int (* Nb of fact in the original clause's conclusion *) *
      history

type reduction = fact list * fact * history * constraints

type order =
  | Less
  | Leq

type ordering_function = (int * order) list (* Always sorted on the integer *)

type ordered_reduction =
  {
    rule : reduction;
    order_data : (ordering_function * bool) list option;
      (* The boolean indicates whether an hypothesis can be
        selected if they matched a nounif declaration with option [ignoreOnce] *)
  }

(* Equational theory *)

type equation = term * term

(* Proof history *)

type fact_tree_desc =
    FHAny
  | FEmpty
  | FRemovedWithMaxHyp
  | FRemovedWithProof of fact_tree
  | FRule of int * label * constraints * fact_tree list * constraints * fact_tree list
  | FEquation of fact_tree

and fact_tree =
    { mutable desc: fact_tree_desc;
      mutable thefact: fact
    }

(* type of input to the Horn clause resolution solver *)

type t_solver_kind =
    Solve_Standard
  | Solve_Equivalence
  | Solve_WeakSecret of (typet * history) list * int
        (* Weaksecr.attrulenum, max_used_phase *)
  | Solve_Noninterf of (funsymb * term list option) list

type t_lemma_application =
  | LANone (* Does not apply the lemma *)
  | LAOnlyWhenRemove (* Apply the lemma only when its application remove the clause afterwards *)
  | LAOnlyWhenInstantiate (* Apply the lemma when it does not create more than one clause and when it instantiate at least one variable *)
  | LAFull (* Fully apply the lemma *)

type lemma =
  {
    l_index : int;
    l_premise : fact list;
    l_conclusion : (fact list * constraints * (term * term) list) list;
    l_verif_app : t_lemma_application;
    l_sat_app : t_lemma_application;
    l_induction : int option
  }

type t_horn_state =
    { h_clauses : reduction list;
      h_equations : ((term * term) list * eq_info) list;
      h_close_with_equations : bool;
      h_not : fact list;
      h_elimtrue : (int * fact) list;
      h_equiv : (fact list * fact * int) list;
      h_nounif : (fact_format * int * nounif_op) list;
      h_clauses_to_initialize_selfun : reduction list;
      h_solver_kind : t_solver_kind;
      h_lemmas : lemma list;
      h_pred_prove : predicate list; (* Predicates that we are trying to prove,
         which must therefore not be removed by eliminating redundant clauses *)
      h_event_in_queries : funsymb list (*
         Events that occurs in the conclusion of the queries.
         Thus they cannot be removed even when they cannot be used for applying
         a lemma. *)
    }

(* For precise options *)

type precise_info =
  | Action of typet
