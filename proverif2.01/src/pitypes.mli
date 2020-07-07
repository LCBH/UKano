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
(** Types module declares types of the abstract syntax
   tree and of sets of messages.
   There are recursive dependencies between these types,
   that is why they are included in the same module.
   The type of processes has been moved to the module types.mli
   because it is needed in the environment values for letfun, and the
   environments are needed for terms in queries that cannot be
   expanded before process translation *)

open Types

(** {6 Correspondence queries} *)

type event =
    QSEvent of
      int option (* None when not injective. Some k indicates injective with k as index. *) *
      ordering_function (* The ordering function on query from input files are always [] *) *
      term option (* The occurrence. Always = None on query from input files. *) *
      term
  | QSEvent2 of term * term (* Event for biprocesses *)
  | QFact of predicate * ordering_function  * term list
  | QNeq of term * term
  | QEq of term * term
  | QGeq of term * term
  | QIsNat of term

type conclusion_query =
  | QTrue
  | QFalse
  | QEvent of event
  | NestedQuery of realquery
  | QAnd of conclusion_query * conclusion_query
  | QOr of conclusion_query * conclusion_query

and realquery = Before of event list * conclusion_query

type q_secret_opt =
    Reachability
  | RealOrRandom

(** The type used for query *)
type query =
    PutBegin of bool * funsymb list (** [PutBegin(true, f)] when [f] is injective *)
  | RealQuery of realquery * term list(*public variables, translated into terms *)
  | QSecret of term list(*secret terms*) * term list(*public variables, translated into terms *) * q_secret_opt

type eventstatus =
    { mutable end_status : onestatus;
      mutable begin_status : onestatus }

(** Indications of term occurrences that should be added to name_params *)
type term_occ =
      OTest of occurrence
    | OLet of occurrence
    | OInChannel of occurrence
    | OEvent of occurrence
    | OLetFilter of occurrence

(* Type of an element that can be either unset (initially)
   or set to its value *)

type 'a opt_set =
    Unset
  | Set of 'a

(* Encoding steps *)

type encode_step =
    Public_vars of (term * funsymb(* public channel *)) list
  | Secret_reach of term list * funsymb (* event *)
  | Secret_ror of term list * funsymb (* public channel *)

(* Type of an element whose value is not known yet,
   but can be computed. Initially, a function,
   then set to the result of the function. *)

type 'a computable =
    Function of (t_pi_state -> 'a)
  | Computed of 'a

(* Type of lemmas *)

and t_lemmas_application_side =
  | AllSide
  | LeftSide
  | RightSide

and t_one_lemma =
  {
    ql_query : query; (* the encoded query *)
    ql_real_or_random : term list option; (* Whether it was declared for a specific secret [real or random].
      Note that ql_query (and then ql_original_query) contains the public vars. *)
    ql_application_side : t_lemmas_application_side;
    ql_original_query : query option; (* The original query *)
    ql_index_query_for_induction : int option (* Index of the lemma. Will be used for induction *)
  }

and t_lemmas_state =
  {
    lemmas: t_one_lemma list;
    is_axiom : bool;
    max_subset : bool;
    verif_app : Types.t_lemma_application; (* Application condition during the verification *)
    sat_app : Types.t_lemma_application; (* Application condition during the saturation *)
    induction : bool;
    keep_axiom : bool (* Only used for axioms : Determine if we should keep the axiom after
      simplification, swapping and merging. *)
  }

and t_lemmas =
  | LemmaToTranslate of (t_pi_state -> t_lemmas)
  | Lemma of t_lemmas_state

(* Type of all queries *)

and t_solve_corresp_status =
  {
    s_max_subset : bool;
    s_ind_sat_app : Types.t_lemma_application;
    s_ind_verif_app : Types.t_lemma_application;
    s_induction : bool
  }


and t_query =
  | QueryToTranslate of (t_pi_state -> t_query)
        (* For queries that must be translated after Simplify.prepare_process *)
  | CorrespQuery of query list * t_solve_corresp_status
        (* Correspondence query. Several queries can be grouped
           together in the query list. *)
  | CorrespQEnc of (query(*original query*)  * query(*encoded query*)) list * t_solve_corresp_status
        (* Correspondence query, encoded as another correspondence query.
           Used for "public_vars" and for "query secret x [reachability]" *)
  | ChoiceQEnc of query (* original query, encoded as an equivalence
        for a process with choice. Used for "query secret x [real_or_random]" *)
  | ChoiceQuery
        (* Equivalence for a biprocess (process with choice/diff) *)
  | NonInterfQuery of (funsymb * term list option) list
  | WeakSecret of funsymb

and t_construction =
  | Initial_process
  | Initial_process1
  | Initial_process2
  | Merge of t_process_desc * t_process_desc
  | Simplify of t_process_desc
  | Encode of t_process_desc * encode_step list
  | BarrierNoSwap of t_process_desc
  | BarrierSwap of t_process_desc
  | MoveNew of t_process_desc

and t_process_desc =
    { proc : process;
      bi_pro : bool; (* true when [proc] is a biprocess *)
      mutable display_num : int option; (* [None] when the process has not been displayed yet;
                                           [Some n] when it has been displayed as process [n] *)
      construction : t_construction }

and t_process_query =
    Equivalence of t_process_desc * t_process_desc
        (* Equivalence between the two processes *)
  | SingleProcess of t_process_desc * t_query list
  | SingleProcessSingleQuery of t_process_desc * t_query
        (* Invariant: the queries ChoiceQuery and ChoiceQEnc
           appear only with SingleProcessSingleQuery *)

and t_pi_state =
    { pi_process_query : t_process_query;
         (* Process and associated queries *)
      pi_global_env : envElement Stringmap.StringMap.t opt_set;
         (* Environment that maps identifiers (strings) to their
            declaration. Set by Pitsyntax, not by Pisyntax. *)
      pi_glob_table : (string, funsymb) Hashtbl.t opt_set;
      pi_glob_table_var_name : (string, term) Hashtbl.t opt_set;
         (* Tables:
            - [pi_glob_table] maps strings [s] to bound name function symbols
            originally declared by [new s]. Used to interpret references
            [new s] in queries, [not] and [nounif] declarations.
            - [pi_glob_table_var_name] maps strings [s] to terms representing
            bound variables or names originally named [s]. Used to interpret
            [public_vars] and [query secret].
            Set by Simplify.prepare_process *)
      pi_types : typet list;
         (* List of types *)
      pi_funs : funsymb list;
         (* List of function symbols *)
      pi_freenames : funsymb list;
         (* List of free names *)
      pi_events : funsymb list;
         (* List of events *)
      pi_equations : ((term * term) list * eq_info) list;
         (* List of equations *)
      pi_max_used_phase : int;
         (* Maximum phase used by the process, queries, etc *)
      pi_input_clauses : (fact list * fact * constraints * label) list;
         (* Clauses given in the input file, to define predicates *)
      pi_elimtrue : fact list;
         (* [elimtrue] declarations *)
      pi_equivalence_clauses : (fact list * fact * int) list;
         (* Equivalence clauses H <-> C or H <=> C given in the input file.
            These declarations add a simplification rule to the clauses. *)
      pi_destructors_check_deterministic : funsymb list;
         (* Destructors using the old declaration.
            ProVerif checks that they are deterministic,
            by calling Destructor.check_deterministic *)
      pi_disequations : (term * term) list;
         (* Inequations declared in the input file.
            ProVerif just checks that they are valid: the terms
            do not unify modulo the equations theory. *)
      pi_event_status_table : (funsymb, eventstatus) Hashtbl.t opt_set;
         (* Status of events (injective, non-injective, unused).
            Set by Pievent.set_event_status *)
      pi_get_not : t_pi_state -> event list;
         (* Function that returns the [not] declarations of the input file.
            The computation must be done after translation into clauses,
            because it may need the arguments of names.
            Called in Pitransl and Pitranslweak. *)
      pi_get_nounif : t_pi_state -> (fact_format * int * nounif_op) list;
         (* Function that returns the [nounif] declarations of the input file.
            The second arg of each element of the list is the weight, and the third element
            is [true] when the nounif declaration applied on hypotheses of the clauses
            and [false] when it applies on the conclusion.
            The computation must be done after translation into clauses,
            because it may need the arguments of names.
            Called in Pitransl and Pitranslweak. *)
      pi_terms_to_add_in_name_params : term_occ list opt_set;
         (* Terms that must be added to the arguments of names.
            Set by [Pitransl] and [Pitranslweak].
            Used by [Reduction] and [Reduction_bipro]. *)
      pi_min_choice_phase : int opt_set;
         (* Minimum phase in which [choice] is used.
            Set by [Pitranslweak]. *)
      pi_need_vars_in_names : (funsymb * string * Parsing_helper.extent) list computable;
         (* List that determines the variables that must occur in
            arguments of bound names, because they are used in
            bound names [new s] in queries, [not], and [nounif]
            declarations.
            In the typed front-end, the computation must be done after
            calling Simplify.prepare_process. *)
      pi_name_args_exact : bool;
         (* true when we should throw an error in case an argument of name is not found;
            false when we should just drop silently the considered item (not/nounif declaration) in this case.
            Set of false when the processes are too transformed to keep track of arguments of names. *)

      pi_lemma: t_lemmas list;
        (* List of lemmas *)
      pi_original_axioms: realquery list;
        (* List of original axioms (before simplification but after encoding). Used for trace reconstruction. *)
      pi_precise_actions : funsymb list
        (* List of native precise actions events generated during the translation into clauses *)
    }

(* Type for displaying divergence cases *)
type div_type =
    (* 1. A process diverges because the evaluation of terms/patterns/tests/...
       fails on one side only. *)
  | DEval of string * int * term * int * process
	(* [DEval(s, i, t, n, proc)] means that the process [proc] (process number [n])
	   evaluates term [t] and that this fails only on side [i].
	   The string [s] explains more precisely the evaluation. *)
  | DEvalOut of int * term * term * int * process
	(* [DEvalOut(i, t1, t2, n, proc)] means that the process [proc] (process number [n])
	   is an output that evaluates terms [t1] and [t2] and that this fails only on side [i]. *)
  | DEvalLet of int * term * pattern * int * process
	(* [DEvalLet(i, t, pat, n, proc)] means that the process [proc] (process number [n])
	   is a [let t = pat in ...] which fails only on side [i] *)
  | DEvalFact of int * fact * int * process
        (* [DevalFact(i, f, n, proc)] means that the process [proc] (process number [n])
	   evaluates fact [f] and that this fails only on side [i]. *)
  | DTest of int * bool * term * term * term * int * process
	(* [DTest(i, elsenil, fst, snd, t, n, proc)] means that the process [proc] (process number [n])
	   makes a test [t] such that the two sides [fst] and [snd] give a different result:
	   the [else] branch is taken on side [i]. *)
  | DLetFilter of int * bool * fact * int * process
        (* [DLetFilter(i, elsenil, fact, n, proc)] means that the process [proc] (process number [n])
	   is [LetFilter([], fact, ...)] such that the two sides give a different result:
	   the [else] branch is taken on side [i]. *)
  | DGet of int * term * pattern * term * int * process
	(* [DGet(i, term, pat, t, n, proc)] means that the process [proc] (process number [n])
	   makes a [get pat suchthat t] and the term [term] in the table fails to match on
	   side [i] only. *)
     (* 1.1 An input process diverges because pattern matching fails on
	one side only. In this case, the received message must be provided
	either by the adversary (DInputPat) or by another process (DIOPat) *)
  | DInputPat of int * term * term * pattern * int * process
	(* [DInputPat(i, recipe, result, pat, n, proc)] means that the process [proc] (process number [n])
	   makes an input that receives the message [recipe] which evaluates to [result]
	   from the adversary, and this message fails to match [pat] only on side [i] *)
  | DIOPat of int * term * term * pattern * int * process * int * process
	(* [DIOPat(i, t, t', pat, nin, pin, nout, pout)] the process [pout] (process number [nout])
	   sends the message [t] which evaluates to [t'], to the process [pin] (process number [nin])
	   and this message fails to match [pat] only on side [i] *)
     (* 2. A communication succeeds on one side only (equality of channels
	on one side only) *)
  | DIO of int * term * term * int * process * int * process
	(* [DIO(i, cin, cout, nin, pin, nout, pout)]: the process [pin] (process number [nin])
	   makes an input on channel [cin], the process [pout] (process number [nout])
	   makes an output on channel [cout]. [cin] and [cout] are different only
	   on side [i]. *)
  | DChannel of string(*"input" or "output"*)* int(*side*) * term * term *  term * term * int(*process number*) * process
	(* [DChannel(s, i, ch, ch_result, recipe, result, n, proc)]
	   The process [proc] (process number [n]) makes an input/output (as determined by the string [s])
	   on channel [ch] which evaluates to [ch_result]. The adversary can make a communication
	   on channel [recipe] which evaluates to [result]. The communication fails
	   on side [i] only. *)
     (* 4. An adversary make a test (equality or fail) *)
  | DFail of int * term * term
	(* [DFail(i, recipe, expansion)]
	   The adversary evaluates the [recipe] which expands to [expansion],
           and it fails only on side [i] *)
  | DEquality of int * term * term *  term * term
	(* [EqualityDiv(i, recipe1, result1, recipe2, result2)]
           The adversary makes an equality test between two terms [recipe1] which evaluates to [result1] and
	   [recipe2] which evaluates to [result2] and it fails only on side [i] *)
     (* 4.1 [DOutputMess] Corresponds to an output followed by a test (DEquality(...) or DFail(...))
        on the output message *)
  | DOutputMess of term(*message in process*) * term(* evaluated message*) * term(*resulting recipe*) *
	int(*process number*) * process * div_type(*divergence met on the output message (DEquality(...) or DFail(...)) *)

(** Types of reduction steps, for trace reconstruction. An
  [int] is used to get the number of the reduced process in the list
    of processes.  *)
type remove_cause =
  | DestrFails
  | TestFails (* for tests with 0 else branch: we do not distinguish whether a destructor fails or the else branch is taken *)
  | Blocks

type reduc_type =
  | RNil of int (** [n] Process:  [0] *)
  | RPar of int (** [RPar(n)] Process [n]: parallel reduction [|] *)
  | RRepl of int * int (** [RRepl(n, cpn)] [n] process:  Reduction [!] [cpn] copies*)
  | RRestrAtt of term (** [RRestrAtt term] For interactive mode, attacker creating nonce *)
  | RAddpub of (term * term * term) list (** [RAddpub (variable, mess, recipe) list] For interactive mode, to add public [mess] with its [recipe] to the current state  *)
  | RRestr of int * funsymb * term
  (** [RRestr(n, na, n')] [n] Process: New [na.f_name] creating a new name n' *)
  | RLet_In of int * pattern * term
  (** [RLet_In(n, pat, t)] [n] process: [Let pat = t] succeeds -> in branch taken *)
  | RLet_Else of int * pattern * term
  (** [RLet_Else(n, pat, t)] [n] process: [Let pat = t] fails -> else branch taken *)
  | RLet_Remove of int * pattern * term
  (** [RLet_Remove(n, pat, t)] [n] process: [Let pat = t] blocks (succeeds on one side only, and we want to continue the trace) - Only in biprocess *)
  | RInput_Success of int * term * pattern * term * term
  (**[RInput_Success(n, tc, pat, calc, mess_term)] [n] process: [In(tc, pat)]
     done with message [mess_term] *)
  | RInput_PatFails of int * term * pattern * term * term
  (** Used only when the interactive mode is on. When the pattern matching failed *)
  | RInput_Remove of int * term * pattern * remove_cause
  (** Used in the interactive mode, when the evaluation of the channel fails,
      and in reduction_bipro, when the evaluation of the channel fails on one side only (the process blocks),
      and we want to continue the trace. *)
  | ROutput_Success of int * term * term * term
  (** [ROutput_Success(n, tc, calc, t)] [n] process: [Out(tc, t)] done with calc -> t  *)
  | ROutput_Remove of int * term * term * remove_cause
  (** [ROutput_Remove(n, tc, t, cause)] [n] process :[Out(tc, t)] destructor fails
      or blocks: destructor fails on one side only in biprocess, and we want to continue the trace *)
  | RTest_Then of int * term
  (** [RTest_Then(n,t)] [n] process: [If t] succeeds*)
  | RTest_Else of int * term
  (** [RTest_Else(n,t)] [n] process: [If t] else branch taken *)
  | RTest_Remove of int * term * remove_cause
  (** [RTest_Remove(n,t,cause)] [n] process: [If t] destructor fails, or empty else branch taken, or blocks - Only in biprocess *)
  | REvent_Success of int * term * bool
  (** [REvent_Success(n, t, b)] [n] process: [Event(t)] executed; b is true when an attack has been found*)
  | REvent_Remove of int * term * remove_cause
  (** [REvent_Remove(n, t)] [n] process: [Event(t)] destructors fails or event blocks *)
  | RPhase of int
  (** [RPhase(n)] switch to phase [n] *)
  | RLetFilter_In of int * binder list * term list * fact
  (** [RLetFilter_In(n, bl, tl, f)]  [n] process: [let(b1,..,bm) suchthat f] executed ([bl = [b1,...,bm]]) *)
  | RLetFilter_Else of int * binder list * fact
  (** [RLetFilter_Else(n, bl, f)]  [n] process: [let(b1,..,bm) suchthat f] else branch taken *)
  | RLetFilter_Remove of int * binder list * fact * remove_cause
  (** [RLetFilter_Remove(n, bl, f)]  [n] process: [let(b1,..,bm) suchthat f] destructor fails or
  [let... suchthat] blocks*)
  | RIO of int * term * pattern * int * term * term option * term * bool
  (** [RIO(n, tc', pat, no, tc, may_calc, t, b)] [In(tc', pat);Pn] reduces  with [out(tc,t);Pno] *)
  | RIO_PatRemove of int * term * pattern * int * term * term option * term * bool * bool
  (** Reduction goes, but the pattern-matching after the input fails if the final bool is true,
      and blocks if it is false. *)
  | RInsert_Success of int * term * bool
  (** [RInsert_Success(n, t, b)] [Insert(t);Pn] when every thing is OK, b is true when an attack has been found *)
  | RInsert_Remove of int * term * remove_cause (** [Insert] destructor fails
       or blocks: destructor fails on one side only in biprocess, and we want to continue the trace *)
  | RGet_In of int * pattern * term * term
  (**  [RGet_In(n, pat, t, m)] [Get] when the match exists (first branch of Get taken)*)
  | RGet_Else of int * pattern * term (** [Get] when the [else] branch is taken *)
  | RGet_Remove of int * pattern * term
  | RNamedProcess of int * string * term list
  | RInit (** Initial State *)
  | RDiverges of div_type

type name_param_info =
    arg_meaning * term * when_include

(**{6 Reduction and reduction of biprocess} *)

(**The 'a may be term (for reduction.ml) or term * term (for reduction_bipro.ml) *)

type 'a info =
    InputInfo of (binder * 'a) list * (term * 'a) list * 'a * name_param_info list * hypspec list *
                 ('a * (term * (binder * 'a) list * (term * 'a) list) option) list
        (** Channel name after decomposition of tuples,
           Public set of values at last test,
           Channel name,
           name_params, occs,
           list of possible messages, possibly with their recipe and their public status: the message after decomposition of tuples and the public set of values at last test.

           Assume
           [InputInfo(tc_list, oldpub, tc, name_params, occs, mess_list)].
           - If [tc_list != []], the first element of [l] is not in [oldpub]
           we check whether the first element of
           [tc_list] is the part of public before [oldpub].
           - If no,  [tc_list' = tc_list]
           - If yes, we remove from the tail of [l] the first elements that
           are in public, yielding [tc_list'].
           We replace the cache with  [InputInfo(tc_list',public,...)],
           If [tc_list'] is not empty, the channel is not public,
           try to perform (Res I/O).
           If [tc_list'] is empty, the channel is public,
           try to perform (Res In).
      *)
  | OutputInfo of (binder * 'a) list * (term * 'a) list
        (** the channel name after decomposition of tuples:
               this is a list containing 'a, and the corresponding recipe
               of type binder; the actual recipe will be stored in this
               binder when it is known.
           the public set of values at last test.
           Invariant: if we have [OutputInfo(l,oldpub)],
           the first element of [l] is not [oldpub].

           When testing this output, we check whether the first element of
           [l] in is the part of public before oldpub.
           - If no, we replace the cache with [OutputInfo(l,public)].
           - If yes, we remove from the tail of [l] the first elements that
           are in public, yielding [l']. If [l'] is not empty, we replace
           the cache with [OutputInfo(l',public)]. If [l'] is empty,
           we can execute the output: the channel is public.
           *)
  | GetInfo of 'a list * 'a list
        (** the old contents of tables
           the list of possible entries *)
  | Nothing

type 'a sub_proc =
    process * (name_param_info list) * (hypspec list) * (fact list) * ('a info)
      (**
      A process (always closed -- only bound variables can occur;
      no variable with link).
      - list of name_params (terms received as input + session ids),
      always closed -- no variables.
      - list of occurrences of inputs and replications already seen in the reduction
      - list of facts corresponding to already seen inputs -- no variables
      - cached info for inputs *)

(** Types of locations (attacker or process) for steps in trace reconstruction *)
type 'a loc_info =
    LocAttacker of term (* recipe used to compute a term at that location *)
  | LocProcess of int * 'a sub_proc

type weak_test =
    FailTest of term
  | EqTest of term * term

type 'a noninterf_test =
    ProcessTest of hypspec list * term list * (int * 'a sub_proc) option
    (**location where test found*)
  | InputProcessTest of hypspec list * term list * term(* message received by the input *) *
        (int * 'a sub_proc (*location of the input that makes the test*) *
         'a loc_info (*location of the output that sends the message*)) option
  | ApplyTest of funsymb * ('a * term option) list
  | NIFailTest of 'a * term option (* recipe *)
  | CommTest of 'a(**input channel*) * 'a(**output channel*) *
        ('a loc_info * 'a loc_info) option
        (** [CommTest(input_channel, output_channel, Some(input_location, output_location))]*)
  | NIEqTest of ('a * term option) * ('a * term option)

type corresp_goal_t =
    Fact of fact * term list option (* the second component stores the recipes used to
                                       by the adversary to compute terms in the fact *)
        * bool (* true when the fact has been met *)
  | EventGoal of fact * (occurrence * term list) option
        (** [InjGoal(f,occ_op)] The end event [f] to execute, occ_op = Som(occ,sid_list) when
            the event [f] was executed at the occurence [occ] of the process within
            the session's copy [sid_list]. *)

type 'a goal_t =
  | CorrespGoal of corresp_goal_t list
  | WeakSecrGoal of (term * binder * term option (*recipe*)) list * weak_test * term * term
        (**  [WeakSecrGoal(l, t, w1, w2)] where [l] is the
          list of terms that the attacker has to know with the recipies to obtain them,
          with arbitrary variables
          to store them, [t] is
          the term that the attacker computes to test its guess,
          [w1] is the weak secret that the attacker wants to guess,
          [w2] is the symbol that represents the guess
        *)
  | NonInterfGoal of 'a noninterf_test
  | NoGoal (* for reduction_interact *)

type 'a reduc_state =
    {
      goal : 'a goal_t; (** goal to reach *)
      subprocess : 'a sub_proc list; (** process list *)
      public : (term * 'a) list; (** attacker knowledge, and the calculus that leads to it, of the for recipe = term *)
      pub_vars : term list; (** List of variables associated to public *)
      (* for the simulator mode *)
      tables : 'a list; (** contents of tables *)
      prepared_attacker_rule : (predicate * (binder * 'a) list * (term * 'a)) list;
      (** attacker rules: predicate, hypothesis, conclusion *)
      io_rule : (int * fact list * hypspec list * term list * fact) list; (** process rules *)
                (** rule number, hypotheses, occurrence labels, name params, conclusion *)

      previous_state : ('a reduc_state) option; (** previous semantic state *)

      hyp_not_matched : (term option * fact) list;
      assumed_false : fact list list; (* Blocking facts that need to be assumed false to execute the considered trace,
                                         to execute else branches of let...suchthat.
                                         More precisely, for each list of facts [f1; ..., fn] in [assumed_false],
                                         we assume [not (f1 && ... && fn)]. *)
      current_phase : int;
      comment : reduc_type;  (** type of the reduction *)
      events : term list;
      barriers : (int * int) list
    }



(* Type used to treat IO reductions. If we made an output reduction on channel [tou], *)
(* then [Menu_helper.set_io_c tou] is called, and we keep a trace of it. The view is changed, *)
(* and only processes waiting for an input on [tou] are shown. The user then click on the process of *)
(* his choice, and the reduction is made. This is possible since in data_model type, *)
(* there is a io_r_t parameter for each title. We set correctly this parameter using the *)
(* function Menu_helper.get_data () *)
type io_r_t =
    Other
  | I_O of term * int * pattern * process * process (* last parameter for [Menu_helper.display_exn] only *)
  | O_I of term * int * term * process * process (* last parameter for [Menu_helper.display_exn] only *)

(* The model used in the interactive model to fill the treeview model *)
type data_model  =
    { tables_lst : string list;
      public_lst : string list;
      titles : (string * io_r_t) list;
      proc_llst : string list list;
      no_auto :bool;
      events_lst : string list;
      barriers_lst : string list
    }


(* Result of a query *)

type query_res = True | False | DontKnow

type is_error =
  | Ok
  | Error

type group_summary_t =
    { sum_queries : (t_process_query * query_res) list;
      sum_lemmas : (t_process_query * is_error * query_res) list;
      sum_axioms : t_process_query list }


type grouped_axioms_t =
    { axiom : t_query;
      axiom_string : string;
      mutable axiom_proc : t_process_desc list }

type grouped_lemmas_t =
    { lemma : t_query;
      lemma_string : string;
      mutable true_res : t_process_desc list;
      mutable false_res : t_process_desc list;
      mutable dont_know_res : t_process_desc list;
      mutable error : t_process_desc list }
