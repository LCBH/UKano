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
open Pitypes
open Reduction_helper

(****************************************
  Simplification of queries into lemmas
*****************************************)

(* The function [simplify_lemmas pi_st] considers the queries of [pi_st]
   and simplifies the lemmas accordingly into implied lemmas.
   For equivalence queries, a lemma is transformed into a restricted lemma
   (without events in its conclusion.).
   When the simplified lemma is of the form F => true then the exception
   [Useless_lemma] is raised.
*)

exception Useless_lemma

let rec simplify_conclusion_query pi_state = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QEvent(QSEvent(_,_,_,FunApp(f,args))) ->
      let fstatus = Pievent.get_event_status pi_state f in
      if fstatus.begin_status = Inj
      then QTrue
      else QEvent(QSEvent(None,[],None,FunApp(f,args)))
  | QEvent(QSEvent _) -> Parsing_helper.internal_error "Events should be function applications (lemma.ml, simplify_conclusion_query)"
  | QEvent _ as qev -> qev
  | NestedQuery _ -> Parsing_helper.internal_error "[lemma.ml >> simplify_conclusion_query] Lemmas should not contain nested queries."
  | QAnd(concl1,concl2) ->
      let concl1' = simplify_conclusion_query pi_state concl1
      and concl2' = simplify_conclusion_query pi_state concl2 in
      make_qand concl1' concl2'
  | QOr(concl1,concl2) ->
      let concl1' = simplify_conclusion_query pi_state concl1
      and concl2' = simplify_conclusion_query pi_state concl2 in
      make_qor concl1' concl2'

let simplify_realquery pi_state = function
  | Before(ev_l,concl_q) ->
      let ev_l_1 =
        List.map (function
          | QSEvent(_,_,_,FunApp(f,args)) ->
              let fstatus = Pievent.get_event_status pi_state f in

              if fstatus.begin_status = Inj
              then QSEvent(Some(-1),[],None,FunApp(f,args))
              else QSEvent(None,[],None,FunApp(f,args))
          | ev -> ev
        ) ev_l
      in

      let concl_q' = simplify_conclusion_query pi_state concl_q in

      if concl_q' = QTrue
      then raise Useless_lemma;

      Before(ev_l_1,concl_q')

let simplify_query pi_state = function
  | RealQuery(q,[]) -> RealQuery(simplify_realquery pi_state q,[])
  | _ -> Parsing_helper.internal_error "[lemma.ml >> simplify_query] Lemmas should have been encoded at that point, i.e. they should only be real query without public variables."

let simplify_lemmas pi_state =
  let original_axioms = ref [] in

  let rec simplify_t_lemma_list = function
    | [] -> []
    | t_lem :: q ->
        let q' = simplify_t_lemma_list q in
        try
          { t_lem with ql_query = simplify_query pi_state t_lem.ql_query } :: q'
        with Useless_lemma -> q'
  in

  let rec simplify_lemma_state = function
    | [] -> []
    | (LemmaToTranslate _) :: _ -> Parsing_helper.internal_error "[lemma.ml >> simplify_lemmas] Lemmas should have been translated at that point."
    | (Lemma lem_state)::q ->
        if lem_state.is_axiom
        then
          original_axioms :=
            List.fold_left (fun acc lem -> match lem.ql_query with
              | RealQuery(rq,[]) -> rq::acc
              | _ -> Parsing_helper.internal_error "[lemma.ml >> simplify_lemmas] Lemmas should have been encoded at that point."
            ) !original_axioms lem_state.lemmas;

        if lem_state.verif_app = LANone && lem_state.sat_app = LANone
        then simplify_lemma_state q
        else
          let lemmas_1 = simplify_t_lemma_list lem_state.lemmas in

          if lemmas_1 = []
          then simplify_lemma_state q
          else (Lemma { lem_state with lemmas = lemmas_1 }) :: (simplify_lemma_state q)
  in
  let simplified_lemmas = simplify_lemma_state pi_state.pi_lemma in

  { pi_state with
    pi_lemma = simplified_lemmas;
    pi_original_axioms = !original_axioms
  }

(* The function [simplify_queries_for_induction pi_st] consider the query
   of [pi_st] and simplifies it to see if it can be proved by induction. *)

let rec simplify_induction_conclusion_query pi_state = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QEvent(QSEvent(_,_,_,FunApp(f,args))) ->
      let fstatus = Pievent.get_event_status pi_state f in
      if fstatus.begin_status = Inj || fstatus.end_status = Inj
      then QTrue
      else QEvent(QSEvent(None,[],None,FunApp(f,args)))
  | QEvent(QSEvent _) ->
     Parsing_helper.internal_error "Events should be function applications (lemma.ml, simplify_induction_conclusion_query)"
  | QEvent(QFact(p,_,_)) as qev ->
      if p.p_prop land Param.pred_BLOCKING == 0
      then QTrue
      else qev
  | QEvent(QSEvent2 _ | QNeq _ | QEq _ | QGeq _ | QIsNat _ ) as qev -> qev
  | NestedQuery(Before(evl,concl)) ->
      let query' =
        List.fold_left (fun acc ev ->
          QAnd(acc,QEvent(ev))
        ) concl evl
      in
      simplify_induction_conclusion_query pi_state query'
  | QAnd(concl1,concl2) ->
      let concl1' = simplify_induction_conclusion_query pi_state concl1
      and concl2' = simplify_induction_conclusion_query pi_state concl2 in
      make_qand concl1' concl2'
  | QOr(concl1,concl2) ->
      let concl1' = simplify_induction_conclusion_query pi_state concl1
      and concl2' = simplify_induction_conclusion_query pi_state concl2 in
      make_qor concl1' concl2'

let allowed_pred = function
  | QSEvent(None,_,_,_) -> true
  | QSEvent _ -> false
  | QSEvent2 _ -> true
  | QFact(p,_,_) ->
      begin match p.p_info with
        | [Attacker _] | [Mess _] | [Table _] | [AttackerBin _] | [MessBin _] | [TableBin _]-> true
        | _ -> false
      end
  | QNeq _ | QEq _ | QGeq _ | QIsNat _ -> Parsing_helper.internal_error "[lemma.ml >> vars_and_allowed_pred] Equalities and disequalities should not occur in the premise of the query."

let simplify_queries_for_induction pi_state =
  let (_,q) = Param.get_process_query pi_state in

  let analyze q_l solve_status =
    let sat_app =
      (* When we want to prove all queries, or when there is a single
	 query, we can apply it as induction hypothesis in the saturation *)
      if solve_status.s_max_subset && List.length q_l > 1
      then LANone
      else solve_status.s_ind_sat_app
    in

    if (sat_app = LANone && solve_status.s_ind_verif_app = LANone) || not solve_status.s_induction
    then pi_state
    else
      let (simplified_queries,_) =
        List.fold_left (fun (acc,i) -> function
          | RealQuery(Before(evl,concl),[]) ->
              if List.for_all allowed_pred evl
              then
                let simp_concl = simplify_induction_conclusion_query pi_state concl in
                if simp_concl <> QTrue
                then ({ ql_query = RealQuery(Before(evl,simp_concl),[]) ; ql_original_query = None; ql_real_or_random = None; ql_index_query_for_induction = Some i; ql_application_side = AllSide }::acc,i+1)
                else (acc,i+1)
              else (acc,i+1)
          | _ -> (acc,i+1)
        ) ([],0) q_l
      in

      if simplified_queries = []
      then pi_state
      else
        let lem_state =
          {
            lemmas = simplified_queries;
            is_axiom = false;
            max_subset = solve_status.s_max_subset;
            verif_app = solve_status.s_ind_verif_app;
            sat_app = sat_app;
            induction = true;
            keep_axiom = false
          }
        in
        { pi_state with pi_lemma = (Lemma lem_state)::pi_state.pi_lemma}
  in

  match q with
    | CorrespQuery(q_l,solve_status) -> analyze q_l solve_status
    | CorrespQEnc(qql,solve_status) -> analyze (List.map (fun (_,q) -> q) qql) solve_status
    | NonInterfQuery _
    | WeakSecret _
    | ChoiceQuery | ChoiceQEnc _ -> pi_state
    | _ -> Parsing_helper.internal_error "[lemma.ml >> simplify_queries_for_induction] Queries should have been translated"

(****************************************************
  Detection of a lemma with choice for monoprocess
*****************************************************)

(* [convert_lemma_for_monoprocess lem] checks whether the bilemma corresponds in fact to
   a lemma on one side of the biprocess. If it is the case, it returns the lemma for the
   corresponding side of the biprocess (ql_application_side is set to LeftSide or RightSide).
   When it is not the case, [lem] is returned.

   Note that technically, a lemma could correspond to both sides of the biprocess.
    ex : lemma event(A(x,y)) ==> event(B(x',y'))
   But in this case, it is sufficient to prove only one side of the lemma. In the case
   the lemma would be proved on one side but not on the other, it means that the biprocess
   diverges before the premises are triggered and so the lemma would not help anyway in the
   proof of equivalence. *)
let convert_lemma_for_monoprocess lemma =

  let explore_one_side left_side evl concl_q =
    let vars_side_to_keep = ref [] in
    let vars_side_to_check = ref [] in

    let add_variables vars =
      (* We check that terms in side_to_check are just distinct variables *)
      List.iter (function
        | Var v ->
            if List.memq v !vars_side_to_check || List.memq v !vars_side_to_keep
            then raise Not_found;
            vars_side_to_check := v :: !vars_side_to_check
        | _ -> raise Not_found
      ) vars
    in

    let rec check_keep_variables = function
      | Var v ->
          if List.memq v !vars_side_to_check
          then raise Not_found;

          if not (List.memq v !vars_side_to_keep)
          then vars_side_to_keep := v :: !vars_side_to_keep
      | FunApp(_,args) -> List.iter check_keep_variables args
    in

    let analyse_events = function
      | QSEvent2(FunApp(f1,args1),FunApp(f2,args2)) ->
	  assert (f1 == f2);
          let (side_to_check,side_to_keep) =  if left_side then (args2,args1) else (args1,args2) in
          add_variables side_to_check;
          List.iter check_keep_variables side_to_keep;
          QSEvent(None,[],None,FunApp(f1,side_to_keep))
      | QSEvent2 _ -> Parsing_helper.internal_error "[lemma.ml >> is_for_monoprocess] Argument of events should be a function application"
      | QFact(pred,_,args) ->
          let (new_pred,side_to_check, side_to_keep) = match pred.p_info, args with
            | [AttackerBin(n,ty)], [t1;t2] ->
                let (side_to_check,side_to_keep) = if left_side then ([t2],[t1]) else ([t1],[t2]) in
                Param.get_pred (Attacker(n,ty)), side_to_check, side_to_keep
            | [MessBin(n,ty)], [tc1;t1;tc2;t2] ->
                let (side_to_check,side_to_keep) = if left_side then ([tc2;t2],[tc1;t1]) else ([tc1;t1],[tc2;t2]) in
                Param.get_pred (Mess(n,ty)), side_to_check, side_to_keep
            | [TableBin n], [FunApp(tbl1,args1);FunApp(tbl2,args2)] ->
                let (side_to_check,side_to_keep) = if left_side then (args2,[FunApp(tbl1,args1)]) else (args1,[FunApp(tbl2,args2)]) in
                Param.get_pred (Table n), side_to_check, side_to_keep
            | [Attacker _], _
            | [Mess _], _
            | [Table _], _ -> pred, [], args
            | _ , _ -> Parsing_helper.internal_error "[lemma.ml >> is_for_monoprocess] User defined predicates are not allowed for equivalence queries."
          in

          add_variables side_to_check;
          List.iter check_keep_variables side_to_keep;
          QFact(new_pred,[],side_to_keep)
      | (QNeq(t1,t2) | QEq(t1,t2) | QGeq(t1,t2)) as p ->
          check_keep_variables t1;
          check_keep_variables t2;
          p
      | QIsNat t as p ->
          check_keep_variables t;
          p
      | QSEvent _ -> Parsing_helper.internal_error "[lemma.ml >> is_for_monoprocess] Event should have been translated into bievents at that point."
    in

    let rec analyse_concl = function
      | QTrue -> QTrue
      | QFalse -> QFalse
      | QEvent ev -> QEvent (analyse_events ev)
      | NestedQuery _ -> Parsing_helper.internal_error "[lemma.ml >> is_for_monoprocess] Lemmas should not contain nested queries."
      | QAnd(concl1,concl2) -> QAnd(analyse_concl concl1, analyse_concl concl2)
      | QOr(concl1,concl2) -> QOr(analyse_concl concl1, analyse_concl concl2)
    in

    RealQuery(Before(List.map analyse_events evl, analyse_concl concl_q),[])
  in

  match lemma.ql_query with
    | RealQuery(Before(evl,concl_q),_) ->
        (* We try the left side *)
        begin
          try
            let rq = explore_one_side true evl concl_q in
            { lemma with ql_application_side = LeftSide; ql_query = rq }
          with Not_found ->
            (* We try the right side *)
            try
              let rq = explore_one_side false evl concl_q in
              { lemma with ql_application_side = RightSide; ql_query = rq }
            with Not_found -> lemma
        end
    | _ -> Parsing_helper.internal_error "[lemma.ml >> is_for_monoprocess] Lemmas should only be correspondence queries."

(****************************************
  Translate to bi-lemmas
*****************************************)

(* [encode_event_equiv qev] transforms the query event [qev] into a fact for
   biprocess. Note that we do not allow disequalities, inequalities and equalities
   to contain choice. Moreover, since we do not allow user defined predicates for
   equivalence proofs, only Attacker, Mess and Table can have choice. Finally,
   user defined predicates are always considered as true when used for equivalence proofs. *)
let encode_event_equiv min_choice_phase next_f = function
  | QSEvent(_,_,_,ev) ->
      let ev1 = Terms.choice_in_term 1 ev
      and ev2 = Terms.choice_in_term 2 ev in
      next_f (QSEvent2(ev1,ev2))
  | QSEvent2 _ -> Parsing_helper.internal_error "[lemma.ml >> encode_event_equiv] Event for biprocess should not occur before encoding."
  | QFact(pred,_,args) ->
      let n, bin_pred_spec =
	match pred.p_info with
	| [Attacker(n,ty)] -> n, AttackerBin(n,ty)
	| [Mess(n,ty)] -> n, MessBin(n,ty)
	| [Table n] -> n, TableBin n
	| _ -> raise Useless_lemma
      in
      let l1 = List.map (Terms.choice_in_term 1) args
      and l2 = List.map (Terms.choice_in_term 2) args in
      if n < min_choice_phase then
	TermsEq.unify_modulo_list (fun () -> next_f (QFact(pred,[],l1))) l1 l2
      else
	next_f (QFact(Param.get_pred bin_pred_spec,[], l1 @ l2))
  | QNeq _ | QEq _ | QGeq _ | QIsNat _ ->
      Parsing_helper.internal_error "[lemma.ml >> encode_event_equiv] Inequalities, disequalities, equalities or is_nat cannot occur before ==> in queries"

let rec encode_event_equiv_list min_choice_phase next_f = function
    [] -> next_f []
  | a::l ->
      encode_event_equiv min_choice_phase (fun a' ->
	encode_event_equiv_list min_choice_phase (fun l' -> next_f (a'::l')) l
	  ) a

let rec encode_conclusion_query = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | (QEvent e) as ev0 ->
      begin
	match e with
	| QSEvent(_,_,_,ev) ->
	    let ev1 = Terms.choice_in_term 1 ev
	    and ev2 = Terms.choice_in_term 2 ev in
	    QEvent(QSEvent2(ev1,ev2))
	| QNeq(t1,t2) | QEq(t1,t2) | QGeq(t1,t2) ->
	    if Terms.has_choice t1 || Terms.has_choice t2
	    then Parsing_helper.internal_error "Disequalities, inequalities and equalities in queries should not contain choice.";
	    ev0
	| QIsNat t ->
	    if Terms.has_choice t
	    then Parsing_helper.internal_error "Predicates is_nat in queries should not contain choice.";
	    ev0
	| _ -> QTrue
      end
  | NestedQuery _ -> Parsing_helper.internal_error "[lemma.ml >> encode_conclusion_query] Lemmas should not contain nested queries."
  | QAnd(concl1,concl2) ->
      let concl1' = encode_conclusion_query concl1
      and concl2' = encode_conclusion_query concl2 in
      make_qand concl1' concl2'
  | QOr(concl1,concl2) ->
      let concl1' = encode_conclusion_query concl1
      and concl2' = encode_conclusion_query concl2 in
      make_qor concl1' concl2'

let translate_to_bi_lemma pi_state =
  match pi_state.pi_min_choice_phase with
  | Unset ->
      (* When pi_min_choice_phase is unset at this point, the process is not a biprocess *)
      if (Reduction_helper.get_process pi_state).bi_pro then
        Parsing_helper.internal_error "[lemma.ml >> translate_to_bi_lemma] pi_min_choice_phase should be set";
      pi_state
  | Set min_choice_phase ->
      let new_lemmas =
        List.fold_left (fun acc1 -> function
          | LemmaToTranslate _ -> Parsing_helper.internal_error "[lemma.ml >> translate_to_bi_lemma] Lemmas should have been translated."
          | Lemma lem_state ->
              let lemma_list =
                List.fold_left (fun acc2 lem -> match lem.ql_query with
                | RealQuery(Before(evl,concl_q),pubvars) ->
                    begin
                      let concl_q' = encode_conclusion_query concl_q in
                      if concl_q' = QTrue then
                        acc2
                      else
                        let accu = ref acc2 in
                      (* Generate all lemmas with the various unification possibilities
                         for terms *)
                        try
                          Terms.auto_cleanup (fun () ->
                            encode_event_equiv_list min_choice_phase (fun evl' ->
                              accu :=
                                 { lem with
                          ql_query = RealQuery(Terms.copy_realquery2 (Before(evl',concl_q')),pubvars);
                          ql_original_query =
                          match lem.ql_original_query with
                          | (Some _) as previous_original -> previous_original
                          | None -> Some(lem.ql_query) } :: (!accu);
                              raise Terms.Unify) evl
                              )
                        with
                        | Terms.Unify ->
                            if !accu == acc2 then
                              begin
                                Display.Text.print_string "Warning: lemma ";
                                Display.Text.display_corresp_secret_putbegin_query lem.ql_query;
                                Display.Text.print_string " ignored because it uses choice in phases without choice, and the two sides do not unify.\n";
                                if !Param.html_output then
                                  begin
                                    Display.Html.print_string "Warning: lemma ";
                                    Display.Html.display_corresp_secret_putbegin_query lem.ql_query;
                                    Display.Html.print_string " ignored because it uses choice in phases without choice, and the two sides do not unify.\n"
                                  end;
                              end;
                            !accu
                        | Useless_lemma -> acc2
                    end
                | _ -> acc2
                      ) [] lem_state.lemmas
              in
              if lemma_list = []
              then acc1
              else (Lemma { lem_state with lemmas = List.rev lemma_list })::acc1
                                                                               ) [] pi_state.pi_lemma
      in
      { pi_state with pi_lemma = List.rev new_lemmas }

(****************************************
  Encode lemmas
*****************************************)

let encode_lemmas pi_state pubvars ror_opt =
  let new_lemmas =
    List.fold_left (fun acc1 -> function
      | LemmaToTranslate _ -> Parsing_helper.internal_error "[lemma.ml >> encode_lemmas_for_correspondence] Lemmas should have been translated."
      | Lemma lem_state ->
          let lemma_list =
            List.fold_left (fun acc2 lem ->
              let same_ror = match ror_opt, lem.ql_real_or_random with
                | None, None -> true
                | Some vl, Some vl' -> Terms.same_term_lists vl vl'
                | _ -> false
              in
              if same_ror
              then
                begin match lem.ql_query with
                  | RealQuery(rq,pubvars') when Terms.same_term_lists pubvars' pubvars ->
                      if pubvars = []
                      then lem::acc2
                      else { ql_query = RealQuery(rq,[]); ql_original_query = Some(lem.ql_query); ql_real_or_random = lem.ql_real_or_random; ql_index_query_for_induction = None; ql_application_side = AllSide } :: acc2
                  | _ ->
                      (* Lemmas that do not have the same public vars are ignored. *)
                      acc2
                end
              else
                (* Lemmas that do not correspond to the same query secret real_or_random are ignored. *)
                acc2
            ) [] lem_state.lemmas
          in
          if lemma_list = []
          then acc1
          else (Lemma { lem_state with lemmas = List.rev lemma_list })::acc1
    ) [] pi_state.pi_lemma
  in
  { pi_state with pi_lemma = List.rev new_lemmas }

let encode_lemmas_for_equivalence_queries pi_state =
  let new_lemmas =
    List.fold_left (fun acc1 -> function
      | LemmaToTranslate _ -> Parsing_helper.internal_error "[lemma.ml >> encode_lemmas_for_correspondence] Lemmas should have been translated."
      | Lemma lem_state ->
          let lemma_list =
            List.filter (fun lem -> match lem.ql_query, lem.ql_real_or_random with
              | RealQuery(_,[]), None -> true
              | _ -> false
            ) lem_state.lemmas
          in
          if lemma_list = []
          then acc1
          else (Lemma { lem_state with lemmas = lemma_list })::acc1
    ) [] pi_state.pi_lemma
  in
  { pi_state with pi_lemma = List.rev new_lemmas }

(****************************************
  Translation of lemmas for horn clauses
*****************************************)

(* Copy functions *)

let copy_occurrence = function
  | None -> None
  | Some o -> Some (Terms.copy_term o)

let copy_event = function
  | QSEvent(b,ord_fun,occ,t) -> QSEvent(b,ord_fun,copy_occurrence occ,Terms.copy_term t)
  | QSEvent2(t1,t2) -> QSEvent2(Terms.copy_term t1, Terms.copy_term t2)
  | QFact(p,ord_fun,tl) -> QFact(p,ord_fun,List.map Terms.copy_term tl)
  | QNeq(t1,t2) -> QNeq(Terms.copy_term t1, Terms.copy_term t2)
  | QEq(t1,t2) -> QEq(Terms.copy_term t1, Terms.copy_term t2)
  | QGeq(t1,t2) -> QGeq(Terms.copy_term t1, Terms.copy_term t2)
  | QIsNat t -> QIsNat (Terms.copy_term t)

let rec copy_conclusion_query = function
  | QTrue -> QTrue
  | QFalse -> QFalse
  | QEvent e -> QEvent(copy_event e)
  | QAnd(concl1,concl2) -> QAnd(copy_conclusion_query concl1,copy_conclusion_query concl2)
  | QOr(concl1,concl2) -> QOr(copy_conclusion_query concl1,copy_conclusion_query concl2)
  | _ -> Parsing_helper.internal_error "[lemma.ml >> copy_hypelem] Lemma should not have nested queries."

let copy_realquery = function
  | Before(el, concl_q) -> Before(List.map copy_event el, copy_conclusion_query concl_q)

let copy_query = function
  | RealQuery(rq,[]) -> RealQuery(copy_realquery rq,[])
  | _ -> Parsing_helper.internal_error "[lemma.lm >> copy_query] Should be a real query without public vars"

let copy_lemma lemma = { lemma with ql_query = copy_query lemma.ql_query }

let copy_lemma_state lem_state = { lem_state with lemmas = List.map copy_lemma lem_state.lemmas }

(* Verification of conditions on lemmas and queries *)

(* In a query 'F ==> H', F cannot contain function symbols
   that can be reduced by the equational theory.
   Same thing for the nested queries in H.

   This is difficult to check in pitsyntax.ml/pisyntax.ml
   because the equations are not translated yet into rewrite
   rules, so we do not know which symbols have (Eq l) with l <> []. *)

exception Bad_symbol_in_query of funsymb

let rec verify_Eq_not_in_term = function
  | Var _ -> ()
  | FunApp({f_cat = Eq l; _} as f,args)
     when l <> [] && (List.exists Terms.has_vars args) ->
       raise (Bad_symbol_in_query f)
  | FunApp(_,args) -> List.iter verify_Eq_not_in_term args

let verify_Eq_not_in_event = function
  | QSEvent(_,_,_,t) -> verify_Eq_not_in_term t
  | QSEvent2(t1,t2) ->
      verify_Eq_not_in_term t1;
      verify_Eq_not_in_term t2
  | QFact(p,_,t_list) -> List.iter verify_Eq_not_in_term t_list
  | _ -> Parsing_helper.internal_error "[lemma.ml >> verify_Eq_not_in_event] no Neq and Eq the premises of queries, lemmas and axioms"

let rec verify_Eq_not_in_conclusion_query = function
  | NestedQuery query -> verify_Eq_not_in_realquery query
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) ->
      verify_Eq_not_in_conclusion_query concl1;
      verify_Eq_not_in_conclusion_query concl2
  | _ -> ()

and verify_Eq_not_in_realquery = function
  | Before(el,concl_q) ->
      List.iter verify_Eq_not_in_event el;
      verify_Eq_not_in_conclusion_query concl_q

let verify_Eq_not_in_query query =
  try
    match query with
      | PutBegin _ | QSecret _ -> ()
      | RealQuery (real_query,_) -> verify_Eq_not_in_realquery real_query
  with Bad_symbol_in_query f ->
    print_string "The following query contains the invalid function symbol ";
    Display.Text.display_function_name f;
    print_string ". The premise of a query cannot contain function symbols that can be reduced by the equational theory. Same thing for the nested queries.\n";
    Display.Text.display_corresp_secret_putbegin_query query;
    print_newline();
    Parsing_helper.user_error "Incorrect query"

let verify_Eq_not_in_lemma lem_state =
  List.iter (fun lem ->
    try
      verify_Eq_not_in_query lem.ql_query
    with Bad_symbol_in_query f ->
      print_string "The following lemma or axiom contains the invalid function symbol ";
      Display.Text.display_function_name f;
      print_string ". The premise of a lemma or axiom cannot contain function symbols that can be reduced by the equational theory.\n";
      begin match lem.ql_query with
        | RealQuery(rq,[]) -> Display.Text.display_corresp_query rq
        | _ -> Parsing_helper.internal_error "[lemma.ml >> verify_Eq_not_in_lemma] Unexpected query."
      end;
      print_newline();
      Parsing_helper.user_error "Incorrect query"
  ) lem_state.lemmas

(* Native axioms *)

let precise_action equiv ev_act id =
  let ty = match fst ev_act.f_type with
    | [_;ty] -> ty
    | _ -> Parsing_helper.internal_error "[lemma.ml >> precise_action] Event precise action should only have two arguments."
  in

  if equiv
  then
    let occ = Var(Terms.new_var ~orig:false "occ" Param.occurrence_type)
    and x = Var(Terms.new_var ~orig:false "x" ty)
    and y = Var(Terms.new_var ~orig:false "y" ty)
    and x' = Var(Terms.new_var ~orig:false "x'" ty)
    and y' = Var(Terms.new_var ~orig:false "y'" ty) in

    let ev1 = Pred(Param.begin2_pred,[FunApp(ev_act,[occ;x]);FunApp(ev_act,[occ;x'])])
    and ev2 = Pred(Param.begin2_pred,[FunApp(ev_act,[occ;y]);FunApp(ev_act,[occ;y'])]) in

    {
      l_index = id;
      l_premise = [ev1;ev2];
      l_conclusion = [([],Terms.true_constraints,[x,y; x',y'])];
      l_verif_app = LAOnlyWhenInstantiate;
      l_sat_app = LAOnlyWhenInstantiate;
      l_induction = None
    }
  else
    let occ = Var(Terms.new_var ~orig:false "occ" Param.occurrence_type)
    and x = Var(Terms.new_var ~orig:false "x" ty)
    and y = Var(Terms.new_var ~orig:false "y" ty) in

    let ev1 = Pred(Param.begin_pred,[FunApp(ev_act,[occ;x])])
    and ev2 = Pred(Param.begin_pred,[FunApp(ev_act,[occ;y])]) in

    {
      l_index = id;
      l_premise = [ev1;ev2];
      l_conclusion = [([],Terms.true_constraints,[x,y])];
      l_verif_app = LAOnlyWhenInstantiate;
      l_sat_app = LAOnlyWhenInstantiate;
      l_induction = None
    }

(* Translating functions *)

type transl_state_lemma =
  {
    l_facts : fact list;
    l_constra : constraints;
  }

let transl_premise_event next_f = function
  | QSEvent(_,_,_,t) -> TermsEq.close_term_eq (fun t1 -> next_f (Pred(Param.begin_pred,[t1]))) t
  | QSEvent2(t1,t2) ->
      TermsEq.close_term_eq (fun t1' ->
        TermsEq.close_term_eq (fun t2' ->
          next_f (Pred(Param.begin2_pred,[t1';t2']))
        ) t2
      ) t1
  | QFact(p,_,tl) -> TermsEq.close_term_list_eq (fun tl1 -> next_f (Pred(p,tl1))) tl
  | _ -> Parsing_helper.internal_error "[lemma.ml >> transl_premise_event] Premise of a lemma should not contain equalities or disequalities"

let rec transl_premise next_f = function
  | [] -> next_f []
  | ev::q ->
      transl_premise_event (fun fact ->
        transl_premise (fun q' -> next_f (fact::q')
        ) q
      ) ev

let rec transl_conclusion_query next_f cur_state = function
  | QTrue -> next_f cur_state
  | QFalse -> ()
  | QEvent(QSEvent(_,_,_,t)) ->
      TermsEq.close_term_eq (fun t1 ->
        next_f { cur_state with l_facts = Pred(Param.begin_pred,[t1]) :: cur_state.l_facts }
      ) t
  | QEvent(QSEvent2(t1,t2)) ->
      TermsEq.close_term_eq (fun t1' ->
        TermsEq.close_term_eq (fun t2' ->
          next_f { cur_state with l_facts = Pred(Param.begin2_pred,[t1';t2']) :: cur_state.l_facts }
        ) t2
      ) t1
  | QEvent(QFact(p,_,args)) ->
      TermsEq.close_term_list_eq (fun args1 ->
        next_f { cur_state with l_facts = Pred(p,args1) :: cur_state.l_facts }
      ) args
  | QEvent(QNeq(t1,t2)) -> next_f { cur_state with l_constra = { cur_state.l_constra with neq = [t1,t2] :: cur_state.l_constra.neq } }
  | QEvent(QGeq(t1,t2)) ->
      TermsEq.close_term_eq (fun t1' ->
        TermsEq.close_term_eq (fun t2' ->
          next_f { cur_state with l_constra = { cur_state.l_constra with geq = (t1',0,t2') :: cur_state.l_constra.geq } }
        ) t2
      ) t1
  | QEvent(QIsNat t) ->
      TermsEq.close_term_eq (fun t' ->
        next_f { cur_state with l_constra = { cur_state.l_constra with is_nat = t' :: cur_state.l_constra.is_nat } }
      ) t
  | QEvent(QEq(t1,t2)) ->
      TermsEq.close_term_eq (fun t1' ->
        TermsEq.close_term_eq (fun t2' ->
          try
            Terms.auto_cleanup (fun () ->
              Terms.unify t1' t2';
              next_f cur_state
            )
          with Terms.Unify -> ()
        ) t2
      ) t1
  | NestedQuery _ -> Parsing_helper.internal_error "[lemma.ml >> transl_premise_event] Lemma should not have nested queries."
  | QAnd(concl1,concl2) ->
      transl_conclusion_query (fun cur_state1 ->
        transl_conclusion_query next_f cur_state1 concl2
      ) cur_state concl1
  | QOr(concl1,concl2) ->
      transl_conclusion_query next_f cur_state concl1;
      transl_conclusion_query next_f cur_state concl2

let transl_realquery next_f = function
  | Before(ev_l,concl_q) ->
      transl_premise (fun premise ->
        let vars_premise = ref [] in
        List.iter (Terms.get_vars_fact vars_premise) premise;

        let concl_accu = ref [] in
        let cur_state_0 = { l_facts = []; l_constra = Terms.true_constraints } in

        transl_conclusion_query (fun cur_state1 ->
          try
            (* Follow the links *)
            let constra1 = Terms.copy_constra4 cur_state1.l_constra in
            let fact_list1 = List.map Terms.copy_fact4 cur_state1.l_facts in

            let keep_vars = ref !vars_premise in
            List.iter (Terms.get_vars_fact keep_vars) fact_list1;
            List.iter (fun v -> match v.link with
              | TLink t -> Terms.get_vars keep_vars (Terms.copy_term4 t)
              | _ -> ()
            ) !vars_premise;

            let next_step constra =
              let eq_list1 =
                List.fold_left (fun acc v ->
                  match v.link with
                    | NoLink -> acc
                    | TLink t -> (Var v,Terms.copy_term4 t)::acc
                    | _ -> Parsing_helper.internal_error "[lemma.ml >> transl_realquery] Unexpected link."
                ) [] !vars_premise
              in

              (* Removing simple equations *)

              Terms.auto_cleanup (fun () ->
                let eq_list2 =
                  List.fold_left (fun acc (t1,t2) -> match t2 with
                    | Var v when v.link = NoLink && not (List.memq v !vars_premise) ->
                        Terms.link v (TLink t1);
                        acc
                    | _ -> (t1,t2)::acc
                  ) [] eq_list1
                in

                let eq_list3 = List.map (fun (t1,t2) -> t1, Terms.copy_term3 t2) eq_list2 in
                let constra3 = Terms.copy_constra3 constra in
                let fact_list2 = List.map Terms.copy_fact3 fact_list1 in

                concl_accu := (fact_list2,constra3,eq_list3) :: !concl_accu
              )
            in

            TermsEq.simplify_constraints_keepvars next_step next_step !keep_vars constra1
          with Terms.Unify | TermsEq.FalseConstraint -> ()
        ) cur_state_0 concl_q;
        next_f premise !concl_accu
      ) ev_l

let rec transl_lemmas horn_state pi_state =
  let h_lemmas = ref [] in
  let pred_prove = ref horn_state.h_pred_prove in
  let nb_lemmas = ref 0 in
  let equiv = horn_state.h_solver_kind = Solve_Equivalence in

  let add_pred p =
    if not (List.memq p (!pred_prove)) then
      pred_prove := p :: (!pred_prove)
  in

  (* Adding the native precise actions *)
  List.iter (fun ev ->
    let lemma = precise_action equiv ev !nb_lemmas in
    incr nb_lemmas;
    h_lemmas := lemma :: !h_lemmas
  ) pi_state.pi_precise_actions;

  List.iter (function
    | Lemma lem_state ->
        let lem_state' = Terms.auto_cleanup (fun _ -> copy_lemma_state lem_state ) in
        (* Check that the lemmas does not contain destructor. Moreover, we also check that the
           function symbols of the premises are not reduced by the equational theory. *)
        verify_Eq_not_in_lemma lem_state';

        List.iter (fun lem -> match lem.ql_query with
        | RealQuery(rq,[]) ->
            (* Add predicates to [pred_prove]
               The predicates in assumptions of lemmas must be added
               to [pred_prove] because, when we apply a lemma,
               we must be sure that the predicate is actually true.
               Therefore, we must not resolve on this predicate in
               elimination of redundant clauses, to avoid removing
               a clause that does not have this predicate in hypothesis.

               Queries proved by induction are already included in lemmas
               at this stage, so we do not need to handle them separately. *)
            let Before(hyp,_) = rq in
            List.iter (function
              | QSEvent _ | QSEvent2 _ -> ()
              | QFact(p,_,_) -> add_pred p
              | _ -> Parsing_helper.internal_error "[lemma.ml >> transl_lemmas] Premise of a lemma should not contain equalities or disequalities"
            ) hyp;

            transl_realquery (fun premise concl ->
              let lemma =
                {
                  l_index = !nb_lemmas;
                  l_premise = premise;
                  l_conclusion = concl;
                  l_verif_app = lem_state.verif_app;
                  l_sat_app = lem_state.sat_app;
                  l_induction = lem.ql_index_query_for_induction
                }
              in
              incr nb_lemmas;
              h_lemmas := lemma :: !h_lemmas
            ) rq
          | _ -> Parsing_helper.internal_error "[lemma.ml >> transl_lemmas] Unexpected query"
        ) lem_state.lemmas
    | LemmaToTranslate _ -> Parsing_helper.internal_error "[pitransl.ml >> transl_lemmas_for_correspondence] Lemma should be translated at this point."
  ) pi_state.pi_lemma;

  { horn_state with
    h_lemmas = List.rev !h_lemmas;
    h_pred_prove = !pred_prove }

(************************************************
  Verification of axioms on reconstructed trace
*************************************************)

let continue_searching ev state = match ev with
  | QFact({ p_info = [Mess(n,_)]; _},_,_) when state.current_phase < n -> false
  | QEq _ | QNeq _ | QGeq _ | QIsNat _ -> false
  | _ -> true

let unify_hyp f_next ev state = match ev with
  | QFact({ p_info = [Attacker(n,_)]; _},_,[tq]) when state.current_phase <= n->
      begin match state.comment with
        | RInput_Success(_,_,_,_,t)
        | ROutput_Success(_,_,_,t)
	    (* RIO/RIO_PatRemove send on a public channel only when the adversary
	       is passive. When the channel is public, the recipe is set to "Some ..." *)
        | RIO(_,_,_,_,_,Some _,t,_)
        | RIO_PatRemove(_,_,_,_,_,Some _,t,_,_) ->
	    (* In case we work with biprocesses, in a phase < min_choice_phase,
	       we may have a fact Attacker and still a biterm in the trace. *)
	    let t1 = Terms.choice_in_term 1 t in
	    let t2 = Terms.choice_in_term 2 t in
            TermsEq.unify_modulo_list f_next [tq;t2] [t1;t1]
        | _ -> raise Terms.Unify
      end
  | QFact({ p_info = [AttackerBin(n,_)]; _},_,[tq1;tq2]) when state.current_phase <= n->
      begin match state.comment with
        | RInput_Success(_,_,_,_,t)
        | ROutput_Success(_,_,_,t)
	    (* RIO/RIO_PatRemove send on a public channel only when the adversary
	       is passive. When the channel is public, the recipe is set to "Some ..." *)
        | RIO(_,_,_,_,_,Some _,t,_)
        | RIO_PatRemove(_,_,_,_,_,Some _,t,_,_) ->
	    let t1 = Terms.choice_in_term 1 t in
	    let t2 = Terms.choice_in_term 2 t in
            TermsEq.unify_modulo_list f_next [tq1;tq2] [t1;t2]
        | _ -> raise Terms.Unify
      end
  | QFact({ p_info = [Mess(n,_)]; _},_,[c;tq]) when state.current_phase = n ->
      begin match state.comment with
        | RInput_Success(_,tc,_,_,t)
        | ROutput_Success(_,tc,_,t)
        | RIO(_,tc,_,_,_,_,t,_)
        | RIO_PatRemove(_,tc,_,_,_,_,t,_,_) ->
	    (* In case we work with biprocesses, in a phase < min_choice_phase,
	       we may have a fact Mess and still biterms in the trace. *)
	    let t1 = Terms.choice_in_term 1 t in
	    let t2 = Terms.choice_in_term 2 t in
	    let tc1 = Terms.choice_in_term 1 tc in
	    let tc2 = Terms.choice_in_term 2 tc in
            TermsEq.unify_modulo_list f_next [c;tc2;tq;t2] [tc1;tc1;t1;t1]
        | _ -> raise Terms.Unify
      end
  | QFact({ p_info = [MessBin(n,_)]; _},_,[c1;tq1;c2;tq2]) when state.current_phase = n ->
      begin match state.comment with
        | RInput_Success(_,tc,_,_,t)
        | ROutput_Success(_,tc,_,t)
        | RIO(_,tc,_,_,_,_,t,_)
        | RIO_PatRemove(_,tc,_,_,_,_,t,_,_) ->
	    let t1 = Terms.choice_in_term 1 t in
	    let t2 = Terms.choice_in_term 2 t in
	    let tc1 = Terms.choice_in_term 1 tc in
	    let tc2 = Terms.choice_in_term 2 tc in
            TermsEq.unify_modulo_list f_next [c1;c2;tq1;tq2] [tc1;tc2;t1;t2]
        | _ -> raise Terms.Unify
      end
  | QFact({ p_info = [Table(n)]; _},_,[tq]) when state.current_phase = n ->
      begin match state.comment with
        | RInsert_Success(_,t,_) ->
	    (* In case we work with biprocesses, in a phase < min_choice_phase,
	       we may have a fact Table and still a biterm in the trace. *)
	    let t1 = Terms.choice_in_term 1 t in
	    let t2 = Terms.choice_in_term 2 t in
            TermsEq.unify_modulo_list f_next [t1;t1] [tq;t2]
        | _ -> raise Terms.Unify
      end
  | QFact({ p_info = [TableBin(n)]; _},_,[tq1;tq2]) when state.current_phase = n ->
      begin match state.comment with
        | RInsert_Success(_,t,_) ->
	    let t1 = Terms.choice_in_term 1 t in
	    let t2 = Terms.choice_in_term 2 t in
            TermsEq.unify_modulo_list f_next [tq1;tq2] [t1;t2]
        | _ -> raise Terms.Unify
      end
  | QFact(p,_,args) when p.p_prop land Param.pred_BLOCKING != 0 ->
      begin match state.comment with
        | RLetFilter_In(_,[],[],Pred(p',args')) when p == p' -> TermsEq.unify_modulo_list f_next args args'
        | _ -> raise Terms.Unify
      end
  | QSEvent(_,_,_,ev') ->
      begin match state.comment with
        | REvent_Success(_,ev'',_) -> TermsEq.unify_modulo f_next ev' ev''
        | _ -> raise Terms.Unify
      end
  | QSEvent2(ev1,ev2) ->
      begin match state.comment with
        | REvent_Success(_,ev'',_) ->
	    let ev1'' = Terms.choice_in_term 1 ev'' in
	    let ev2'' = Terms.choice_in_term 2 ev'' in
	    TermsEq.unify_modulo_list f_next [ev1;ev2] [ev1'';ev2'']
        | _ -> raise Terms.Unify
      end
  | QEq(t1,t2) -> TermsEq.unify_modulo f_next t1 t2
  | _ -> raise Terms.Unify

(* Event in match conclusion should be ground (no variables) *)
let rec match_conclusion restwork state ev =
  try
    unify_hyp restwork ev state
  with Terms.Unify ->
    if continue_searching ev state
    then
      match state.previous_state with
        | None -> raise Terms.Unify
        | Some state' -> match_conclusion restwork state' ev
    else raise Terms.Unify

let rec match_conclusion_query restwork state constra = function
  | QTrue -> restwork constra
  | QFalse -> raise Terms.Unify
  | QEvent (QNeq(t1,t2)) ->
      restwork { constra with neq = [t1,t2]::constra.neq }
  | QEvent (QGeq(t1,t2)) ->
      TermsEq.close_term_eq_synt (fun t1' ->
        TermsEq.close_term_eq_synt (fun t2' ->
          restwork { constra with geq = (t1',0,t2)::constra.geq }
        ) t2
      ) t1
  | QEvent (QIsNat t) ->
      TermsEq.close_term_eq_synt (fun t' ->
        restwork { constra with is_nat = t'::constra.is_nat }
      ) t
  | QEvent ev ->
      match_conclusion (fun () -> restwork constra) state ev
  | NestedQuery _ -> Parsing_helper.internal_error "[lemma.ml >> match_conclusion_query] Axioms should not contain nested correspondence"
  | QAnd(concl1,concl2) ->
      match_conclusion_query (fun constra1 ->
        match_conclusion_query restwork state constra1 concl2
      ) state constra concl1
  | QOr(concl1,concl2) ->
      try
        match_conclusion_query restwork state constra concl1
      with Terms.Unify ->
        match_conclusion_query restwork state constra concl2

let rec match_one_premise f_next state ev =
  try
    unify_hyp f_next ev state;
    raise Terms.Unify
  with Terms.Unify ->
    if continue_searching ev state
    then
      match state.previous_state with
        | None -> ()
        | Some state' -> match_one_premise f_next state' ev

let rec not_ground = function
  | Var { link = TLink t } -> not_ground t
  | Var _ -> true
  | FunApp(_,args) -> List.exists not_ground args

let check_one_axiom final_state = function
  | Before(evl,concl_q) ->
      let rec match_premises state = function
        | [] -> (* Premise have been matched *)
            let exists_existential_vars = ref false in

            begin
              try
                match_conclusion_query (fun constra ->
                  try
                    let constra1 = Terms.map_constraints TermsEq.remove_syntactic_term constra in
                    let constra2 =
                      TermsEq.simplify_constraints_keepvars (fun c -> c) (fun _ ->
                        Parsing_helper.internal_error "[lemma.ml >> check_one_axiom] Should not occur since we have kept no variables."
                      ) [] constra1
                    in
                    TermsEq.check_constraints constra2;

                    (* When there are still natural number in the constra, we cannot
                       correctly verify that the axiom is not verified by the trace.
                       In such a case, we will display a warning saying that we could not verify
                       the axiom *)

                    if Terms.exists_constraints not_ground constra2
                    then
                      begin
                        exists_existential_vars := true;
                        raise Terms.Unify
                      end;
                  with TermsEq.FalseConstraint -> raise Terms.Unify
                ) state Terms.true_constraints concl_q;
              with Terms.Unify ->
                if !exists_existential_vars
                then
                  begin
                    Display.Text.newline();
                    Display.Text.print_line "Warning: We could not verify that the following axiom is satisfied by the attack trace.";
                    Display.Text.display_corresp_query (Before(evl,concl_q));
                    Display.Text.newline();
                  end
                else
                  begin
                    Display.Text.newline();
                    Display.Text.print_line "The attack trace does not satisfy the following declared axiom:";
                    Display.Text.display_corresp_query (Before(evl,concl_q));
                    Display.Text.newline();
                    Parsing_helper.user_error "False axiom."
                  end
            end
        | ev::q_ev ->
            match_one_premise (fun () ->
              match_premises state q_ev
            ) state ev

      and match_state state prev_ev = function
        | [] ->
            begin match state.previous_state with
              | None -> ()
              | Some state' -> match_state state' [] evl
            end
        | ev::q_ev ->
            try
              unify_hyp (fun () -> match_premises state (prev_ev @ q_ev)) ev state;
              raise Terms.Unify
            with Terms.Unify -> match_state state (ev::prev_ev) q_ev
      in

      match_state final_state [] evl

let check_axioms final_state axioms =
  List.iter (check_one_axiom final_state) axioms

(************************************************
   Verification that lemmas do not contain PGLink
 *************************************************)

let rec no_bound_name_term = function
  | Var { link = PGLink _ } -> false
  | Var { link = TLink t } -> no_bound_name_term t
  | Var _ -> true
  | FunApp(_,args) -> List.for_all no_bound_name_term args

let no_bound_name_event = function
  | QSEvent(_,_,_,t)
  | QIsNat t -> no_bound_name_term t
  | QFact(_,_,args) -> List.for_all no_bound_name_term args
  | QNeq(t1,t2)
  | QEq(t1,t2)
  | QGeq(t1,t2)
  | QSEvent2(t1,t2) -> no_bound_name_term t1 && no_bound_name_term t2

let rec no_bound_name_conclusion_query = function
  | QTrue
  | QFalse -> true
  | QEvent ev -> no_bound_name_event ev
  | NestedQuery r -> no_bound_name_realquery r
  | QAnd(concl1,concl2)
  | QOr(concl1,concl2) -> no_bound_name_conclusion_query concl1 && no_bound_name_conclusion_query concl2

and no_bound_name_realquery = function
  | Before(evl,concl) ->
      List.for_all no_bound_name_event evl &&
      no_bound_name_conclusion_query concl

let no_bound_name_query = function
  | RealQuery(q,_) -> no_bound_name_realquery q
  | _ -> Parsing_helper.internal_error "[lemma.ml >> no_bound_name_query] Unexpected query."

let no_bound_name_t_lemmas = function
  | LemmaToTranslate _ -> Parsing_helper.internal_error "[lemma.ml >> no_bound_name_t_lemmas] Lemma should be translated at that point."
  | Lemma lem_st -> List.for_all (fun lem -> no_bound_name_query lem.ql_query) lem_st.lemmas
