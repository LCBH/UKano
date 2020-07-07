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
open Parsing_helper
open Ptree
open Pitptree
open Types
open Pitypes
open Stringmap


let no_param_option = function
  | (s,ext), None -> (s,ext)
  | (s,ext), _ -> input_error "This option should not have any parameter." ext

let check_no_param_option ((s,ext),arg) =
  if arg != None
  then input_error ("The option "^ s ^" should not have any parameter.") ext

let get_param_option ((s,ext),arg) = match arg with
  | None -> input_error ("The option "^ s ^" expects a parameter.") ext
  | Some i -> i

let no_param_option_list = List.map no_param_option

(* We put the next functions

   get_need_vars_in_names
   transl_query
   get_not
   get_nounif

   first in this module, because they must not
   use the state of the parsing function. They appear in the state
   returned by the parsing function and are called afterwards. *)

(* Functions to access the environment *)

let special_functions = ["choice"; "||"; "&&"; "="; "<>"; "<"; ">"; "<="; ">="]

let args_to_string tl =
  let l = List.length tl in
  if l=0 then
    "0 argument"
  else if l=1 then
    "1 argument of type " ^ (Terms.tl_to_string ", " tl)
  else
    (string_of_int l) ^ " arguments of types " ^ (Terms.tl_to_string ", " tl)

let get_apply_symb env (s,ext) tl =
  match s, tl with
    "=", [t1;t2] ->
      if t1 != t2 then
        input_error ("function " ^ s ^ " expects two arguments of same type but is here given " ^
          (args_to_string tl)) ext;
      (EFun (Terms.equal_fun t1), Param.bool_type)
  | "<>", [t1;t2] ->
      if t1 != t2 then
        input_error ("function " ^ s ^ " expects two arguments of same type but is here given " ^
          (args_to_string tl)) ext;
      (EFun (Terms.diff_fun t1), Param.bool_type)
  | "choice", [t1;t2] ->
      if t1 != t2 then
        input_error ("function " ^ s ^ " expects two arguments of same type but is here given " ^
          (args_to_string tl)) ext;
      (EFun (Param.choice_fun t1), t1)
  | ("=" | "<>" | "choice"), _ ->
      input_error (s ^ "expects two arguments") ext
  | str,[t] when str.[0] = '-' ->
      if (t != Param.nat_type)
      then input_error ("function minus expects 1 argument of type nat but is here given " ^ (args_to_string tl)) ext;

      let n = int_of_string (String.sub str 2 ((String.length str) - 2)) in
      (EFun (Terms.minus_fun n), Param.nat_type)
  | _ ->
  try
    match StringMap.find s env with
    | (EFun r) as x ->
        if not (Terms.eq_lists (fst r.f_type) tl) then
          input_error ("function " ^ s ^ " expects " ^
                       (args_to_string (fst r.f_type)) ^
                       " but is here given " ^
                       (args_to_string tl)) ext;
        (x, snd r.f_type)
    | (EPred r) as x ->
        if not ((List.length r.p_type == List.length tl) &&
                (List.for_all2 (fun t1 t2 -> t1 == t2 || t1 == Param.any_type) r.p_type tl)) then
          input_error ("predicate " ^ s ^ " expects " ^
                       (args_to_string r.p_type) ^
                       " but is here given " ^
                       (args_to_string tl)) ext;
        if List.exists (fun t -> t == Param.any_type) r.p_type then
          (EPred (Param.get_pred (PolymPred(r.p_name, r.p_prop, tl))), Param.bool_type)
        else
          (x, Param.bool_type)
    | (ELetFun (func_proc_layer, arg_type_list, result_type)) as x ->
        if not (Terms.eq_lists tl arg_type_list) then
          input_error ("letfun function " ^ s ^ " expects " ^
                       (args_to_string arg_type_list) ^
                       " but is here given " ^
                       (args_to_string tl)) ext;
        (x, result_type)
    | x -> (x, Param.any_type) (* This case will cause an error in the caller of get_apply_symb *)
  with Not_found ->
    input_error (s ^ " not defined") ext

(* The difference with the previous get_fun is that =, <>, &&, ||, choice are allowed
   get_fun returns the function symbol and the type of the result.
   (The type of the result is often (snd r.f_type), but
   this is not true for choice when we ignore types: in that case,
   (snd r.f_type) is Param.any_type, while the real return type is the
   type of the argument of choice.) *)
let get_fun env (s,ext) tl =
  match get_apply_symb env (s,ext) tl with
    (EFun r, result_type) -> (r, result_type)
  | _ -> input_error (s ^ " should be a function") ext

(* The only difference with the previous get_pred is in error messages:
   when using =, <>, choice, you get "should be a predicate" rather than "not defined". *)
let get_pred env (c, ext) tl =
  match get_apply_symb env (c,ext) tl with
    (EPred r, result_type) -> r
  | _ -> input_error (c ^ " should be a predicate") ext

let get_event_fun env (s,ext) tl =
  try
    let r = StringMap.find s env in
    match r with
      EEvent p ->
        if not (Terms.eq_lists (fst p.f_type) tl) then
          input_error ("function " ^ s ^ " expects " ^
                       (args_to_string (fst p.f_type)) ^
                       " but is here given " ^
                       (args_to_string tl)) ext;
        p
    | _ -> input_error (s ^ " should be an event") ext
  with Not_found ->
    input_error ("event " ^ s ^ " not defined") ext

let get_table_fun env (s,ext) tl =
  try
    let r = StringMap.find s env in
    match r with
      ETable p ->
        if not (Terms.eq_lists (fst p.f_type) tl) then
          input_error ("table " ^ s ^ " expects " ^
                       (args_to_string (fst p.f_type)) ^
                       " but is here given " ^
                       (args_to_string tl)) ext;
        p
    | _ -> input_error (s ^ " should be a table") ext
  with Not_found ->
    input_error ("table " ^ s ^ " not defined") ext

let get_type_polym env polym sid_allowed (s, ext) =
  if s = "any_type" then
    if polym then
      Param.any_type
    else
      input_error "polymorphic type not allowed here" ext
  else if s = "sid" then
    if sid_allowed then
      Param.sid_type
    else
      input_error "sid type not allowed here" ext
  else
  try
    if s = "nat"
    then Param.has_integer := true;

    match StringMap.find s env with
      EType t -> t
    | _ -> input_error (s ^ " should be a type") ext
  with Not_found ->
    input_error ("type " ^ s ^ " not declared") ext

let add_env sid_allowed env l =
  let env_ref = ref env in
  List.iter (fun ((s,ext),ty) ->
      let t = get_type_polym env false sid_allowed ty in
      begin
        try
          match StringMap.find s (!env_ref) with
            EVar _ -> input_error ("variable " ^ s ^ " already defined") ext
          | _ -> input_warning ("identifier " ^ s ^ " rebound") ext
        with Not_found -> ()
      end;
      let v = Terms.new_var s t in
      env_ref := StringMap.add s (EVar v) (!env_ref)
    ) l;
  !env_ref

(* State for the functions get_need_vars_in_names, transl_query, transl_lemma, get_not,
   and get_nounif. *)

type t_q_state =
    { q_env : envElement StringMap.t;
      q_glob_table : (string, funsymb) Hashtbl.t;
      q_glob_table_var_name : (string, term) Hashtbl.t;
      q_max_phase : int;
      q_name_args_exact : bool;
      q_choice_message : string option; (* Error message displayed when Choice is used and it should not. None when Choice is allowed. *)
      q_is_lemma : bool;
      q_is_equivalence_query : bool;
      q_must_encode_names : bool
     }

let build_q_state must_encode_names pi_state =
  match pi_state.pi_global_env, pi_state.pi_glob_table, pi_state.pi_glob_table_var_name with
    Set global_env, Set glob_table, Set glob_table_var_name ->
      { q_env = global_env;
        q_glob_table = glob_table;
        q_glob_table_var_name = glob_table_var_name;
        q_max_phase = pi_state.pi_max_used_phase;
        q_name_args_exact = pi_state.pi_name_args_exact;
        q_choice_message = None;
        q_is_lemma = false;
        q_is_equivalence_query = false;
        q_must_encode_names = must_encode_names
      }
  | _ ->
      Parsing_helper.internal_error "glob_table should be set"

(* [find_name_in_glob_table id] returns the name corresponding to
   identifier [id] in that global environment.
   Raise BadBoundName in case no name corresponds or several
   names correspond. *)

exception BadBoundName of string * Parsing_helper.extent * funsymb list

let find_name_in_glob_table state (s,ext) =
  match Hashtbl.find_all state.q_glob_table s with
  | [n] -> n
  | l -> raise (BadBoundName (s, ext, l))

(* [find_all_var_name_in_glob_table id] returns all names and variables
   corresponding to identifier [id] in that global environment.
   Stop the program in case no name nor variable corresponds. *)

let find_all_var_name_in_glob_table state (s,ext) =
  match Hashtbl.find_all state.q_glob_table_var_name s with
    [] -> input_error (s ^ " should be a bound name or a variable") ext
  | l -> l

(* Compute need_vars_in_names: the list of pairs (restriction, variable name)
   such that the variable "variable name" must occur as argument in the
   pattern that models names created by "restriction", because the
   structure "restriction[... variable name = ... ]" is used in the input
   file. *)

let rec nvn_t state accu (term, ext0) =
  match term with
    PGIdent _ -> accu
  | PGFunApp(_,l) | PGPhase(_,l, _) | PGTuple l ->
      List.fold_left (nvn_t state) accu l
  | PGName (id,bl) ->
      List.fold_left (fun accu ((s',ext'),t) ->
        (* The replication indices do not need to be added in
           need_vars_in_names, because they are always included as
           arguments of names, whether or not they occur in
           the input file.
           They must not be added to need_vars_in_names, because
           they are not correctly computed by trace reconstruction,
           so adding them would cause bugs in trace reconstruction. *)
        let accu' = nvn_t state accu t in
        if (s' <> "") && (s'.[0] != '!') then
          begin
            let r = find_name_in_glob_table state id in
            (* print_string ("Need " ^ s' ^ " in " ^ r.f_name ^ "\n");  *)
            (r, s',ext') :: accu'
          end
        else
          accu'
            ) accu bl
  | PGLet(_,t,t') -> nvn_t state (nvn_t state accu t') t

let nvn_q state accu = function
    PRealQuery (q,_) -> nvn_t state accu q
  | PPutBegin _ | PQSecret _ -> accu

let rec nvn_f state accu (f,ext0) =
  match f with
    PFGIdent _ | PFGAny _ -> accu
  | PFGFunApp(_,l) | PFGTuple l ->
      List.fold_left (nvn_f state) accu l
  | PFGName (id,bl) ->
      List.fold_left (fun accu ((s',ext'),t) ->
        (* The replication indices do not need to be added in
           need_vars_in_names, because they are always included as
           arguments of names, whether or not they occur in
           the input file.
           They must not be added to need_vars_in_names, because
           they are not correctly computed by trace reconstruction,
           so adding them would cause bugs in trace reconstruction. *)
        let accu' = nvn_f state accu t in
        if (s' <> "") && (s'.[0] != '!') then
          begin
            let r = find_name_in_glob_table state id in
            (* print_string ("Need " ^ s' ^ " in " ^ r.f_name ^ "\n");  *)
            (r, s',ext') :: accu'
          end
        else
          accu'
            ) accu bl
  | PFGLet(_,t,t') -> nvn_f state (nvn_f state accu t') t

let rec nvn_nounif state accu = function
    BFLet(_,t,nounif) ->  nvn_f state (nvn_nounif state accu nounif) t
  | BFNoUnif((id,fl,n),_) -> List.fold_left (nvn_f state) accu fl

let get_need_vars_in_names query_list not_list nounif_list pi_state =
  if not pi_state.pi_name_args_exact then
    []
  else
    let q_state = build_q_state false pi_state in
    let accu1 = List.fold_left (fun accu (_, q) -> List.fold_left (nvn_q q_state) accu q) [] query_list in
    let accu2 = List.fold_left (fun accu (_, no) -> nvn_t q_state accu no) accu1 not_list in
    List.fold_left (fun accu (_, nounif,_) -> nvn_nounif q_state accu nounif) accu2 nounif_list

(* queries *)

let non_compromised_session = FunApp(Param.session1, [])

(* The exception [MissingNameArg(s,s',ext)] is raised when
   the variable [s'] at postition [ext] is not defined at restriction [s],
   and it is needed in a query, not, or nounif declaration *)
exception MissingNameArg of string * string * Parsing_helper.extent

(* Note: when check_query, get_queries are applied before the
   translation of the process into Horn clauses has been done,
   the arity of names may not be correctly initialized. In this case,
   update_type_names should be called after the translation of the
   process to update it.  *)

let get_ident_any state (s, ext) =
   try
     match StringMap.find s state.q_env with
         EVar b ->
           begin
             match b.link with
               TLink t -> t
             | NoLink -> Var b
             | _ -> internal_error "unexpected link in get_ident_any"
           end
       | EName r ->
           FunApp(r, [])
       | EFun f ->
           begin
             match f.f_cat with
               Eq _ | Tuple -> ()
             | _ ->  input_error ("function " ^ s ^ " is defined by \"reduc\". Such a function should not be used in a query") ext
           end;
           if fst f.f_type == [] then
             FunApp(f,[])
           else
             input_error ("function " ^ s ^ " has expects " ^
                          (string_of_int (List.length (fst f.f_type))) ^
                          " arguments but is used without arguments") ext
       | _ -> input_error ("identifier " ^ s ^ " should be a variable, a free name, or a function") ext
   with Not_found ->
     input_error ("identifier " ^ s ^ " not defined") ext

let rec check_query_term state (term, ext0) = match term with
  | PGIdent i ->
      let t = get_ident_any state i in
      (t, Terms.get_term_type t)
  | PGPhase _ -> input_error ("phase unexpected in query terms") ext0
  | PGFunApp((s,ext),l) ->
      (* FunApp: only constructors allowed *)
      if List.mem s ["="; "<>"; "<="; ">="; ">"; "<"; "is_nat"; "==>"; "&&"; "||"; "event"; "inj-event"; "table"] then
        input_error (s ^ " unexpected in query terms") ext;
      let (l', tl') = List.split (List.map (check_query_term state) l) in
      let (f, result_type) = get_fun state.q_env (s,ext) tl' in
      begin
        match f.f_cat with
        | Eq _ | Tuple -> ()
	| Choice ->
	    begin
	      match state.q_choice_message with
	      | None -> ()
	      | Some err_message -> input_error err_message ext
	    end
        | _ ->  input_error ("function " ^ s ^ " is defined by \"reduc\". Such a function should not be used in a query") ext
      end;
      if (f.f_options land Param.fun_TYPECONVERTER != 0) && (Param.get_ignore_types()) then
        match l' with
          | [t] -> (t, result_type)
          | _ -> internal_error "type converter functions should always be unary"
      else
             (FunApp(f, l'), result_type)
  | PGTuple l ->
      let (l', tl') = List.split (List.map (check_query_term state) l) in
      (FunApp(Terms.get_tuple_fun tl', l'), Param.bitstring_type)
  | PGName ((s,ext) as id,bl) ->
      let r = find_name_in_glob_table state id in
      if fst r.f_type == Param.tmp_type then
        begin
          if state.q_must_encode_names then
            Parsing_helper.input_error ("You are referring to name " ^ s ^ " in this query or secrecy assumption, but this name will never be generated") ext
          else
            let v = Terms.new_var_def (snd r.f_type) in
            v.link <- PGLink (fun () -> fst (check_query_term { state with q_must_encode_names = true } (term,ext0)));
            (Var v, snd r.f_type)
        end
      else
        begin
          match r.f_cat with
            | Name { prev_inputs_meaning = sl } ->
                List.iter (fun ((s',ext'),_) ->
                      if not (List.exists (fun m -> Reduction_helper.meaning_encode m = s') sl) then
                  raise (MissingNameArg(s,s',ext))
                        (*input_error ("variable " ^ s' ^ " not defined at restriction " ^ s) ext'*)
                ) bl;
                let p =
                  List.map2 (fun m ty ->
                    match m with
                      | MCompSid -> non_compromised_session
                      | _ -> binding_find state (Reduction_helper.meaning_encode m) ty bl
                  ) sl (fst r.f_type)
                in
                (FunApp(r, p), snd r.f_type)
          | _ -> internal_error "name expected here"
        end
  | PGLet(id,t,t') -> check_query_term (add_binding state (id,t)) t'

and binding_find state s ty = function
    [] -> Terms.new_var_def_term ty
  | ((s',ext),t)::l ->
      if s' = s then
        begin
          let (t', ty') = check_query_term state t in
          if ty' != ty then
            input_error ("this variable is of type " ^ ty.tname ^ " but is given a value of type " ^ ty'.tname) ext;
          if (s <> "") && (s.[0] = '!') then
            begin
              match t' with
                Var _ -> ()
              | _ -> input_error "session identifiers should be variables" ext
            end;
          t'
        end
      else
        binding_find state s ty l

and add_binding state ((i,ext),t) =
  begin
    try
      match StringMap.find i state.q_env with
        EVar _ -> input_error ("variable " ^ i ^ " already defined") ext
      | _ -> ()
    with Not_found -> ()
  end;
  let (t', ty') = check_query_term state t in
  let v = Terms.new_var i ty' in
  v.link <- TLink t';
  { state with q_env = StringMap.add i (EVar v) state.q_env }

let check_mess state e tl n =
  match tl with
    [t1;t2] ->
      let (t1', ty1) = check_query_term state t1 in
      let (t2', ty2) = check_query_term state t2 in
      if ty1 != Param.channel_type then
        input_error ("First argument of mess is of type " ^ ty1.tname ^ " and should be of type channel") e;
      let mess_n = Param.get_pred (Mess((if n = -1 then state.q_max_phase else n),
                                        ty2))
      in
      QFact(mess_n, [],[t1';t2'])
  | _ ->
      input_error "arity of predicate mess should be 2" e

let check_attacker state e tl n =
  match tl with
    [t1] ->
      let (t1', ty1) = check_query_term state t1 in
      let att_n = Param.get_pred (Attacker((if n = -1 then state.q_max_phase else n),
                                           ty1))
      in
      QFact(att_n,[],[t1'])
  | _ ->
      input_error "arity of predicate attacker should be 1" e

let rec check_table_term state (term, ext0) =
  match term with
  | PGFunApp((s,ext),l) ->
      (* FunApp: only tables allowed *)
      if List.mem s ["="; "<>"; "==>"; "&&"; "||"; "event"; "inj-event"; "table"] then
        input_error (s ^ " unexpected in query terms") ext;
      let (l', tl') = List.split (List.map (check_query_term state) l) in
      let f = get_table_fun state.q_env (s,ext) tl' in
      FunApp(f, l')
  | _ -> input_error "Table term expected" ext0

let check_table state e tl n =
  match tl with
    [t1] ->
      let t1' = check_table_term state t1 in
      let table_n = Param.get_pred (Table(if n = -1 then state.q_max_phase else n)) in
      QFact(table_n,[],[t1'])
  | _ ->
      input_error "arity of predicate table should be 1" e

let rec check_event state (f,e) = match f with
    (* FunApp: predicates, =, <>, event, inj-event, attacker, mess, table allowed *)
  | PGFunApp(("<>", _), [t1; t2]) ->
      let state' = { state with q_choice_message = Some "Disequalities in queries, lemmas, and axioms should not contain choice." } in
      let (t1', ty1) = check_query_term state' t1 in
      let (t2', ty2) = check_query_term state' t2 in
      if ty1 != ty2 then
        input_error "the two arguments of a disequality test should have the same type" e;
      QNeq(t1', t2')
  | PGFunApp(("=", _), [t1; t2]) ->
      let state' = { state with q_choice_message = Some "Equalities in queries, lemmas, and axioms should not contain choice." } in
      let (t1', ty1) = check_query_term state' t1 in
      let (t2', ty2) = check_query_term state' t2 in
      if ty1 != ty2 then
        input_error "the two arguments of an equality test should have the same type" e;
      QEq(t1', t2')
  | PGFunApp((">=",_), [t1;t2]) ->
      let state' = { state with q_choice_message = Some "Inequalities in queries, lemmas, and axioms should not contain choice." } in
      let (t1', ty1) = check_query_term state' t1 in
      let (t2', ty2) = check_query_term state' t2 in
      if ty1 != Param.nat_type || ty2 != Param.nat_type then
        input_error "the two arguments of an inequality test should have the nat type" e;
      QGeq(t1', t2')
  | PGFunApp((">",_), [t1;t2]) ->
      let state' = { state with q_choice_message = Some "Inequalities in queries, lemmas, and axioms should not contain choice." } in
      let (t1', ty1) = check_query_term state' t1 in
      let (t2', ty2) = check_query_term state' t2 in
      if ty1 != Param.nat_type || ty2 != Param.nat_type then
        input_error "the two arguments of an inequality test should have the nat type" e;
      QGeq(t1', Terms.sum_nat_term t2' 1)
  | PGFunApp(("<=",_), [t1;t2]) ->
      let state' = { state with q_choice_message = Some "Inequalities in queries, lemmas, and axioms should not contain choice." } in
      let (t1', ty1) = check_query_term state' t1 in
      let (t2', ty2) = check_query_term state' t2 in
      if ty1 != Param.nat_type || ty2 != Param.nat_type then
        input_error "the two arguments of an inequality test should have the nat type" e;
      QGeq(t2', t1')
  | PGFunApp(("<",_), [t1;t2]) ->
      let state' = { state with q_choice_message = Some "Inequalities in queries, lemmas, and axioms should not contain choice." } in
      let (t1', ty1) = check_query_term state' t1 in
      let (t2', ty2) = check_query_term state' t2 in
      if ty1 != Param.nat_type || ty2 != Param.nat_type then
        input_error "the two arguments of an inequality test should have the nat type" e;
      QGeq(t2', Terms.sum_nat_term t1' 1)
  | PGFunApp(("is_nat",_), [t]) ->
      let state' = { state with q_choice_message = Some "Predicates is_nat in queries, lemmas, and axioms should not contain choice." } in
      let (t', ty) = check_query_term state' t in
      if ty != Param.nat_type then
        input_error "the two arguments of an inequality test should have the nat type" e;
      QIsNat(t')
  | PGFunApp(("event",e'),tl0) ->
      let (f,tl) = match tl0 with
        | [PGFunApp(f, tl),_] -> (f,tl)
        | [PGIdent f,_] -> (f,[])
        | _ -> input_error "predicate event should have one argument, which is a function application" e'
      in
      let (tl', tyl') = List.split (List.map (check_query_term state) tl) in
      if !Param.key_compromise == 0 then
        QSEvent(None,[],None,FunApp((get_event_fun state.q_env f tyl'), tl'))
      else
        QSEvent(None,[],None,FunApp((get_event_fun state.q_env f (Param.sid_type :: tyl')),(Terms.new_var_def_term Param.sid_type)::tl'))
  | PGFunApp(("inj-event",e'),tl0) ->
      let (f,tl) = match tl0 with
        | [PGFunApp(f, tl),_] -> (f,tl)
        | [PGIdent f,_] -> (f,[])
        | _ -> input_error "predicate inj-event should have one argument, which is a function application" e'
      in
      let (tl', tyl') = List.split (List.map (check_query_term state) tl) in
      if !Param.key_compromise == 0 then
        QSEvent(Some (Param.fresh_injective_index ()),[],None,FunApp((get_event_fun state.q_env f tyl'), tl'))
      else
        QSEvent(Some (Param.fresh_injective_index ()),[],None,FunApp((get_event_fun state.q_env f (Param.sid_type :: tyl')), (Terms.new_var_def_term Param.sid_type)::tl'))
  | PGFunApp(("attacker",_), tl) ->
      check_attacker state e tl (-1)
  | PGFunApp(("mess",_), tl) ->
      check_mess state e tl (-1)
  | PGFunApp(("table",_), tl) ->
      check_table state e tl (-1)
  | PGFunApp((s, ext) as p, tl) ->
      if List.mem s ["||"; "&&"; "not"; "==>"; ">"; "<"; ">="; "<="; "is_nat"] then
        input_error (s ^ " unexpected in events") ext;
      let (tl', tyl) = List.split (List.map (check_query_term state) tl) in
      QFact(get_pred state.q_env p tyl,[],tl')
  | PGPhase((s, ext), tl, n) ->
      begin
        match s with
          | "mess" -> check_mess state e tl n
          | "attacker" -> check_attacker state e tl n
          | "table" -> check_table state e tl n
          | _ -> input_error "phases can be used only with attacker, mess, or table" ext
      end
  | PGIdent p ->
      QFact(get_pred state.q_env p [],[],[])
  | PGLet(id,t,t') -> check_event (add_binding state (id,t)) t'
  | _ -> input_error "an event should be a predicate application" e

let rec check_ev_list state = function
  | PGFunApp(("&&", _), [e1;e2]), _ ->
      (check_ev_list state e1) @ (check_ev_list state e2)
  | ev ->
      let ev' = check_event state ev in
      let ev'' =
	match ev' with
	| QNeq _ | QEq _ | QGeq _ | QIsNat _ ->
	    input_error "Inequalities, disequalities, equalities or is_nat cannot occur before ==> in queries" (snd ev)
        | QFact(p,_,_) ->
	    if state.q_is_lemma then
	      begin
		match p.p_info with
		| [Attacker _] | [Mess _] | [Table _]-> ()
		| _ -> Parsing_helper.input_error "Declared lemmas and axioms should only contain attacker predicates, message predicates, table predicates, or events in their premises." (snd ev)
	      end;
	    ev'
	| QSEvent(Some _,_,_, _) when state.q_is_lemma ->
	    input_error "Declared lemmas and axioms should not contain injective events in their premise." (snd ev)
        | QSEvent _ when !Param.key_compromise == 0 -> ev'
        | QSEvent(inj, ord_fun,None,FunApp(f, sid::l)) -> QSEvent(inj, ord_fun,None,FunApp(f, non_compromised_session::l))
        | QSEvent _
        | QSEvent2 _ ->
            internal_error "Bad format for events in queries"
      in
      [ev'']

let rec check_hyp state = function
    (* FunApp: ==>, ||, && allowed, or what is allowed in events *)
    PGFunApp(("==>", _), [evl; hypll]), ext ->
      let evl' = check_ev_list state evl in
      List.iter (function
        | QNeq _ | QEq _ | QFact _-> input_error "Inequalities, equalities and facts cannot occur before ==> in nested queries" (snd evl)
        | _ -> ()
      ) evl';
      let hypll' = check_hyp state hypll in
      if state.q_is_lemma then
	Parsing_helper.input_error "Declared lemmas and axioms should not contain nested queries." ext;
      NestedQuery(Before(evl', hypll'))
  | PGFunApp(("||", _), [he1;he2]), _ ->
      QOr(check_hyp state he1,check_hyp state he2)
  | PGFunApp(("&&", _), [he1;he2]), _ ->
      QAnd(check_hyp state he1,check_hyp state he2)
  | PGIdent("false", _), _ -> QFalse
  | PGIdent("true", _), _ -> QTrue
  | PGLet(id,t,t'), _ -> check_hyp (add_binding state (id,t)) t'
  | ev ->
      let ev' = check_event state ev in
      if state.q_is_lemma then
	begin
	  match ev' with
	  | QSEvent(Some _,_,_,_) -> Parsing_helper.input_error "Declared lemmas and axioms should not contain injective events." (snd ev)
	  | QFact(pred,_,_) ->
	      begin
		match pred.p_info with
		| [] | [PolymPred _] ->
		    if pred.p_prop land Param.pred_BLOCKING == 0
		    then Parsing_helper.input_error "Declared lemmas and axioms can only use blocking predicates in their conclusion." (snd ev)
		| _ -> Parsing_helper.input_error "Declared lemmas and axioms can only use blocking predicates in their conclusion." (snd ev)
	      end
	  | _ -> ()
	end;
      QEvent(ev')

let rec check_real_query_top state = function
    PGFunApp(("==>", _), [evl; hypll]), _ ->
      (* FunApp: ==> allowed, or what is allowed in events (case below) *)
      let evl' = check_ev_list state evl in
      let hypll' = check_hyp state hypll in
      Before(evl', hypll')
  | PGLet(id,t,t'), _ -> check_real_query_top (add_binding state (id,t)) t'
  | evl ->
      let evl' = check_ev_list state evl in
      Before(evl', QFalse)

let check_query state = function
  | PRealQuery (q, pub_vars) ->
      let q' = check_real_query_top state q in
      let pub_vars' = List.concat (List.map (find_all_var_name_in_glob_table state) pub_vars) in
      RealQuery(q', pub_vars')
  | PQSecret(v, pub_vars, opt) ->
      if state.q_is_lemma then
        input_error "Lemmas should be correspondence queries." (snd v);
      let v' = find_all_var_name_in_glob_table state v in
      let pub_vars' = List.concat (List.map (find_all_var_name_in_glob_table state) pub_vars) in
      let opt' = ref Reachability in
      List.iter (fun (s,ext) ->
        if s = "reachability" || s = "pv_reachability" then
          opt' := Reachability
        else if s = "real_or_random" || s = "pv_real_or_random" then
          opt' := RealOrRandom
        else if Terms.starts_with s "cv_" then
          ()
        else
          input_error "The allowed options for query secret are reachability, pv_reachability, real_or_random, pv_real_or_random, and for compatibility with CryptoVerif, all options starting with cv_" ext
      ) (no_param_option_list opt);
      QSecret(v',pub_vars', !opt')
  | PPutBegin(i, l) ->
      if state.q_is_lemma then
	begin
	  match l with
	  | (_,ext)::_ -> input_error "Lemmas should be correspondence queries." ext;
	  | [] -> internal_error "put_begin with empty list"
	end;
      let l' =
        List.map (fun (s,e) ->
                try
                  match StringMap.find s state.q_env with
                    EEvent r -> r
                  | _ -> input_error (s ^ " should be an event") e
                with Not_found ->
                  input_error ("unknown event " ^s) e
        ) l
      in
      PutBegin(i,l')

let check_lemma state (q,ror_opt,pub_vars) =
  let state' =
    if not state.q_is_equivalence_query && ror_opt = None
    then { state with q_choice_message = Some "choice can only be used in lemmas when the main query is an equivalence of (bi)processes,\nor if they have been specified for a query secret with the option real_or_random or pv_real_or_random." }
    else state
  in
  let q' = check_real_query_top state' q in
  let pub_vars' = List.concat (List.map (find_all_var_name_in_glob_table state') pub_vars) in
  let ror_opt' = match ror_opt with
    | None -> None
    | Some (v,(s,ext)) ->
        if s <> "real_or_random" && s <> "pv_real_or_random"
        then input_error "A lemma can only be specified to a query secret with the option real_or_random or pv_real_or_random." ext;

        let v' = find_all_var_name_in_glob_table state' v in
        Some v'
  in
  (RealQuery(q',pub_vars'), ror_opt')

let rec map_opt f = function
    [] -> []
  | a::l ->
      match f a with
        None -> map_opt f l
      | Some a' -> a' :: (map_opt f l)

let handle_bad_bound_names state action e =
  let message, message_compl, ext =
    match e with
    | BadBoundName (s, ext, []) -> (s ^ " should be a bound name"), "", ext
    | BadBoundName (s, ext, _) ->
       (s ^ " cannot be used in queries, not, or nounif. Its definition is ambiguous"),
       (" (For example, several restrictions might define " ^ s ^ ".)"),
       ext
    | MissingNameArg(s, s', ext) ->
       ("variable " ^ s' ^ " not defined at restriction " ^ s), "", ext
    | _ -> "unknown error", "", Parsing_helper.dummy_ext
  in
  if state.q_name_args_exact then
    input_error (message ^ "." ^ message_compl) ext
  else
    begin
      input_warning (message ^ " after process transformation." ^ message_compl ^ " " ^ action) ext;
      None
    end

let check_query_list state l =
  map_opt (fun q ->
    try
      Some (check_query state q)
    with
    | (MissingNameArg _ | BadBoundName _) as e ->
       handle_bad_bound_names state "Cannot test this query." e
    ) l

let check_lemma_list state l =
  List.map (fun q ->
    try
      Some (check_lemma state q)
    with
      | (MissingNameArg _ | BadBoundName _) as e -> handle_bad_bound_names state "Cannot test this query." e
  ) l

let transl_option_lemma_query is_lemma is_axiom options =
  let sat_app = ref !Param.sat_application in
  let verif_app = ref !Param.verif_application in
  let max_subset = ref (not is_lemma) in
  let induction = ref (
    if is_lemma
    then !Param.induction_lemmas
    else !Param.induction_queries)
  in

  let sat_option = ref false in
  let verif_option = ref false in
  let max_subset_option = ref false in
  let induction_option = ref false in
  let keep = ref false in

  List.iter (fun (str,ext) -> match str with
    | "maxSubset" ->
        if is_axiom
        then input_error "An axiom cannot have the option maxSubset. Only lemmas can." ext;
        if not is_lemma
        then input_error "A query cannot have the option maxSubset. Only lemmas can." ext;
        if !max_subset_option
        then input_error "The option maxSubset was already declared." ext;
        max_subset_option := true;
        max_subset := true
    | "proveAll" ->
        if is_axiom
        then input_error "An axiom cannot have the option proveAll. Only queries can." ext;
        if is_lemma
        then input_error "A lemma cannot have the option proveAll. Only queries can." ext;
        if !max_subset_option
        then input_error "The option proveAll was already declared." ext;
        max_subset_option := true;
        max_subset := false
    | "noneSat" ->
        if !sat_option
        then input_error "An option for the application of this lemma during the saturation procedure as already been declared." ext;
        sat_app := LANone;
        sat_option := true
    | "noneVerif" ->
        if !verif_option
        then input_error "An option for the application of this lemma during the verification procedure as already been declared." ext;
        verif_app := LANone;
        verif_option := true
    | "discardSat" ->
        if !sat_option
        then input_error "An option for the application of this lemma during the saturation procedure as already been declared." ext;
        sat_app := LAOnlyWhenRemove;
        sat_option := true
    | "discardVerif" ->
        if !verif_option
        then input_error "An option for the application of this lemma during the verification procedure as already been declared." ext;
        verif_app := LAOnlyWhenRemove;
        verif_option := true
    | "fullSat" ->
        if !sat_option
        then input_error "An option for the application of this lemma during the saturation procedure as already been declared." ext;
        sat_app := LAFull;
        sat_option := true
    | "fullVerif" ->
        if !verif_option
        then input_error "An option for the application of this lemma during the verification procedure as already been declared." ext;
        verif_app := LAFull;
        verif_option := true
    | "instantiateSat" ->
        if !sat_option
        then input_error "An option for the application of this lemma during the saturation procedure as already been declared." ext;
        sat_app := LAOnlyWhenInstantiate;
        sat_option := true
    | "instantiateVerif" ->
        if !verif_option
        then input_error "An option for the application of this lemma during the verification procedure as already been declared." ext;
        verif_app := LAOnlyWhenInstantiate;
        verif_option := true
    | "induction" ->
        if !induction_option
        then input_error "The option induction or noInduction has already been declared." ext;
        induction := true;
        induction_option := true
    | "noInduction" ->
        if !induction_option
        then input_error "The option induction or noInduction has already been declared." ext;
        induction := false;
        induction_option := true
    | "keep" ->
        if not is_axiom || not is_lemma
        then input_error "Only axioms can have the option 'keep'." ext;
	if !keep
	then input_error "The option keep has already been declared." ext;
        keep := true
    | _ -> input_error "Unknown option" ext
  ) options;

  (!max_subset,!induction,!sat_app,!verif_app,!keep)

let transl_query (env,q,options) pi_state =
  let q_state = build_q_state false pi_state in
  let q_state =
    { q_state with q_env = add_env true q_state.q_env env;
      q_choice_message = Some "choice cannot be used in queries" }
  in
  let q' = check_query_list q_state q in

  let (max_subset,induction,sat_app,verif_app,_) = transl_option_lemma_query false false options in

  let solve_status =
    {
      s_max_subset = max_subset;
      s_ind_sat_app = (if induction then sat_app else LANone);
      s_ind_verif_app = (if induction then verif_app else LANone);
      s_induction = induction
    }
  in

  CorrespQuery(List.map Reduction_helper.check_inj_coherent q', solve_status)

(* Translation lemmas and axioms *)

let transl_lemma axiom (env,q,options) pi_state =
  let q_state = build_q_state false pi_state in

  let is_equivalence_query = match pi_state.pi_process_query with
    | Equivalence _ -> true
    | SingleProcessSingleQuery(_,ChoiceQuery) -> true
    | _ -> false
  in

  let q_state =
    { q_state with q_env = add_env true q_state.q_env env;
      q_is_lemma = true;
      q_is_equivalence_query = is_equivalence_query }
  in

  let q' = check_lemma_list q_state q in

  List.iter2 (fun q1 q1' ->
    match q1, q1' with
    | ((_, ext), _, _), Some (RealQuery(_,pub_vars), ror_opt) ->
	if is_equivalence_query then
	  begin
	    if (pub_vars != [] || ror_opt != None) then
	      input_error "Lemma not used because there is no matching query" ext
	  end
	else
	  begin
	    let queryl =
	      match pi_state.pi_process_query with
	      | Equivalence _ -> internal_error "Should be handled before"
	      | SingleProcessSingleQuery(_,query) -> [query]
	      | SingleProcess(_,queryl) -> queryl
	    in
	    if not (List.exists (function
	      | QueryToTranslate _ -> internal_error "transl_lemma: Queries should have been translated"
	      | CorrespQEnc _ | ChoiceQEnc _ -> internal_error "transl_lemma: Queries should not have been encoded"
	      | ChoiceQuery | NonInterfQuery _ | WeakSecret _ ->
		  pub_vars == [] && ror_opt == None
	      | CorrespQuery(ql, _) ->
		  List.exists (function
		    | PutBegin _ -> false
		    | RealQuery(_, pub_vars')
		    | QSecret(_, pub_vars', Reachability) ->
			(Terms.same_term_lists pub_vars pub_vars') && (ror_opt == None)
		    | QSecret(ror', pub_vars', RealOrRandom) ->
			(Terms.same_term_lists pub_vars pub_vars') &&
			(match ror_opt with
			| None -> false
			| Some ror -> Terms.same_term_lists ror ror')
		      ) ql
	      ) queryl)
	    then
	      input_error "Lemma not used because there is no matching query" ext
	  end
    | _, None -> ()
    | _ -> internal_error "[pitsyntax.ml >> transl_lemma] Lemmas should be encoded as RealQuery."
    ) q q';

  let (max_subset,induction,sat_app,verif_app,keep) = transl_option_lemma_query true axiom options in

  let lemma_list =
    map_opt (function
      | Some((RealQuery _ as q), ror_opt) ->
          Some {
            ql_query = q;
            ql_real_or_random = ror_opt;
            ql_original_query = None;
            ql_index_query_for_induction = None;
            ql_application_side = AllSide
        }
      | None -> None
      | _ -> internal_error "[pitsyntax.ml >> transl_lemma] Lemmas should be encoded as RealQuery."
    ) q'
  in

  let lemma_state =
    {
      lemmas = lemma_list;
      is_axiom = axiom;
      max_subset = max_subset;
      sat_app = sat_app;
      verif_app = verif_app;
      induction = induction;
      keep_axiom = keep
    }
  in

  Lemma(lemma_state)

(* Not declarations *)

let get_not not_list pi_state =
  let q_state = build_q_state true pi_state in
  map_opt (fun (env, no) ->
    try
      Some (check_event { q_state with q_env = add_env true q_state.q_env env } no)
    with
    | (MissingNameArg _ | BadBoundName _) as e ->
       handle_bad_bound_names q_state "Ignoring this not declaration." e
    ) not_list

(* For Nounif. Very similar to queries, except that *v is allowed
   and events are not allowed *)

let fget_ident_any state (s, ext) =
   try
     match StringMap.find s state.q_env with
         EVar b ->
           begin
             match b.link with
               FLink t -> (t, b.btype)
             | NoLink -> (FVar b, b.btype)
             | _ -> internal_error "unexpected link in fget_ident_any"
           end
       | EName r ->
           (FFunApp(r, []), snd r.f_type)
       | EFun f ->
           begin
             match f.f_cat with
               Eq _ | Tuple -> ()
             | _ ->  input_error ("function " ^ s ^ " is defined by \"reduc\". Such a function should not be used in a \"nounif\" declaration") ext
           end;
           if fst f.f_type == [] then
             (FFunApp(f,[]), snd f.f_type)
           else
             input_error ("function " ^ s ^ " expects " ^
                          (string_of_int (List.length (fst f.f_type))) ^
                          " arguments but is used without arguments") ext
       | _ ->
           input_error ("identifier " ^ s ^ " should be a variable, a function, or a name") ext
   with Not_found ->
     input_error ("identifier " ^ s ^ " not defined") ext



let rec check_gformat state (term, ext0) =
  match term with
    PFGIdent i -> fget_ident_any state i
  | PFGFunApp((s,ext),l) ->
      (* FunApp: only constructors allowed *)
      let (l', tl') = List.split (List.map (check_gformat state) l) in
      let (f, result_type) = get_fun state.q_env (s,ext) tl' in
      begin
        match f.f_cat with
          Eq _ | Tuple | Choice -> ()
        | _ ->  input_error ("function " ^ s ^ " is defined by \"reduc\". Such a function should not be used in a \"nounif\" declaration") ext
      end;
      if (f.f_options land Param.fun_TYPECONVERTER != 0) && (Param.get_ignore_types()) then
        match l' with
          [t] -> (t, result_type)
        | _ -> internal_error "type converter functions should always be unary"
      else
        (FFunApp(f, l'), result_type)
  | PFGTuple l ->
      let (l', tl') = List.split (List.map (check_gformat state) l) in
      (FFunApp(Terms.get_tuple_fun tl', l'), Param.bitstring_type)
  | PFGAny (s,ext) ->
      begin
        try
          match StringMap.find s state.q_env with
            EVar b ->
              begin
                match b.link with
                  NoLink -> (FAny b, b.btype)
                | FLink _ -> input_error "variables preceded by * must not be defined by a binding" ext
                | _ -> internal_error "unexpected link in check_gformat"
              end
          | _ -> input_error (s ^ " should be a variable") ext
        with Not_found ->
          input_error ("variable " ^ s ^ " is not defined") ext
      end
  | PFGName ((s,ext) as id,bl) ->
      let r = find_name_in_glob_table state id in
      if fst r.f_type == Param.tmp_type then
        Parsing_helper.input_error ("You are referring to name " ^ s ^ " in this nounif declaration, but this name will never be generated") ext
      else
        begin
          match r.f_cat with
            Name { prev_inputs_meaning = sl } ->
              List.iter (fun ((s',ext'),_) ->
                if not (List.exists (fun m -> Reduction_helper.meaning_encode m = s') sl) then
                  raise (MissingNameArg(s,s',ext))
                           ) bl;
              let p = List.map2 (fun m ty ->
                fbinding_find state (Reduction_helper.meaning_encode m) ty bl) sl (fst r.f_type)
              in
              (FFunApp(r, p), snd r.f_type)
          | _ -> internal_error "name expected here"
        end
  | PFGLet(id,t,t') -> check_gformat (add_fbinding state (id,t)) t'

and fbinding_find state s ty = function
    [] -> FAny (Terms.new_var_def ty)
  | ((s',ext),t)::l ->
      if s' = s then
        begin
          let (t', ty') = check_gformat state t in
          if ty' != ty then
            input_error ("this variable is of type " ^ ty.tname ^ " but is given a value of type " ^ ty'.tname) ext;
          if (s <> "") && (s.[0] = '!') then
            begin
              match t' with
                FVar _ | FAny _ -> ()
              | _ -> input_error "session identifiers should be variables" ext
            end;
          t'
        end
      else
        fbinding_find state s ty l

and add_fbinding state ((i,ext),t) =
  begin
    try
      match StringMap.find i state.q_env with
        EVar _ -> input_error ("variable " ^ i ^ " already defined") ext
      | _ -> ()
    with Not_found -> ()
  end;
  let (t', ty') = check_gformat state t in
  let v = Terms.new_var i ty' in
  v.link <- FLink t';
  { state with q_env = StringMap.add i (EVar v) state.q_env }

let rec check_table_gformat state (term, ext0) =
  match term with
  | PFGFunApp((s,ext),l) ->
      (* FunApp: only tables allowed *)
      let (l', tl') = List.split (List.map (check_gformat state) l) in
      let f = get_table_fun state.q_env (s,ext) tl' in
      FFunApp(f, l')
  | _ -> input_error "Table term expected" ext0

let check_event_gformat state (term, ext0) =
  match term with
  | PFGFunApp((s,ext),l) ->
      (* FunApp: only event allowed *)
      let (l', tl') = List.split (List.map (check_gformat state) l) in
      let f = get_event_fun state.q_env (s,ext) tl' in
      FFunApp(f, l')
  | _ -> input_error "Event term expected" ext0

let check_gfact_format state concl_opt ((s, ext), tl, n) =
  match s with
    "attacker" ->
      begin
        match tl with
          [t1] ->
            let (t1', ty1) = check_gformat state t1 in
            let att_n = Param.get_pred (Attacker((if n = -1 then state.q_max_phase else n), ty1))
            in
            (att_n, [t1'])
        | _ ->
            input_error "arity of predicate attacker should be 1" ext
      end
  | "mess" ->
      begin
        match tl with
          [t1;t2] ->
            let (t1', ty1) = check_gformat state t1 in
            let (t2', ty2) = check_gformat state t2 in
            if ty1 != Param.channel_type then
              input_error ("First argument of mess is of type " ^ ty1.tname ^ " and should be of type channel") ext;
            let mess_n = Param.get_pred (Mess((if n = -1 then state.q_max_phase else n), ty2))
            in
            (mess_n, [t1';t2'])
        | _ ->
            input_error "arity of predicate mess should be 2" ext
      end
  | "table" ->
      begin
        match tl with
          [t1] ->
            let t1' = check_table_gformat state t1 in
            let table_n = Param.get_pred (Table((if n = -1 then state.q_max_phase else n)))
            in
            (table_n, [t1'])
        | _ ->
            input_error "arity of predicate table should be 1" ext
      end
  | "event" ->
      let is_concl = ref false in
      let is_induction_sat = ref false in
      List.iter (function
        | Conclusion -> is_concl := true
        | InductionSat _ -> is_induction_sat := true
        | _ -> ()
      ) concl_opt;
      if not (!is_concl || !is_induction_sat)
      then input_error "Nounif declaration on an event must have the option 'conclusion' or 'inductionOn'" ext;

      if !is_concl && !is_induction_sat
      then input_error "Nounif declaration on an event cannot have both the options 'conclusion' and 'inductionOn'. Make two separate declarations." ext;

      begin
        match tl with
          [t1] ->
            let t1' = check_event_gformat state t1 in
            let p = if !is_concl then Param.end_pred else Param.begin_pred in
            (p, [t1'])
        | _ ->
            input_error "arity of predicate event should be 1" ext
      end
  | s ->
      let (tl', tyl) = List.split (List.map (check_gformat state) tl) in
      (get_pred state.q_env (s,ext) tyl, tl')

(* [check_induction_format vl f] is [true] if and only if the variables in [vl]
   do not occur in a FAny in [f]. *)
let rec check_induction_format vl = function
  | FFunApp(_,args) -> List.iter (check_induction_format vl) args
  | FAny v' ->
      List.iter (fun (v,(s,ext)) ->
        if v == v'
        then input_error ("The variable " ^ s ^ " declared for induction should not be used with * in the fact.") ext;
      ) vl
  | _ -> ()

(* In [handle_nounif state nounif_op has_concl test_var], the function [test_var]
    verifies that the variables declared with the option [inductionOn] do not
    occur in a FAny position. *)
let rec handle_nounif state nounif_op  test_var = function
    BFLet(id,t,nounif) -> handle_nounif (add_fbinding state (id,t)) nounif_op test_var nounif
  | BFNoUnif(fact,n) ->
      let format = check_gfact_format state nounif_op fact in
      test_var format;
      (format, -n,nounif_op)

let check_nounif_options pi_state opt =
  if opt = []
  then [Hypothesis], (fun _ -> ())
  else
    begin
      let hyp_op_decl = ref false in
      let hyp_op = ref false in
      let concl_op = ref false in
      let induc_verif_op = ref false in
      let induc_sat_op = ref None in

      List.iter (fun (i,arg) -> match i with
        | "hypothesis", ext ->
            if !hyp_op_decl
            then input_warning "The option hypothesis has already been declared" ext;
            check_no_param_option (i,arg);
	    hyp_op_decl := true;
            hyp_op := true
        | "conclusion", ext ->
            if !concl_op
            then input_warning "The option conclusion has already been declared" ext;
            check_no_param_option (i,arg);
            concl_op := true
        | "ignoreOnce",ext ->
            if !induc_verif_op
            then input_warning "The option ignoreOnce has already been declared" ext;
            check_no_param_option (i,arg);
            induc_verif_op := true;
            hyp_op := true
        | "inductionOn",ext ->
            if !induc_sat_op != None
            then input_warning "The option inductionOn has already been declared" ext;
            induc_sat_op := Some (get_param_option (i,arg));
            hyp_op := true
        | _, ext -> input_error "The only options available for nounif declaration are: hypothesis, conclusion, ignoreOnce and inductionOn. The option inductionOn takes a variable as parameter." ext
      ) opt;

      let op_acc = ref [] in
      if !hyp_op then op_acc := Hypothesis :: !op_acc;
      if !concl_op then op_acc := Conclusion :: !op_acc;
      if !induc_verif_op then op_acc := InductionVerif :: !op_acc;

      match !induc_sat_op with
        | None -> !op_acc, (fun _ -> ())
        | Some bl ->
            let bl_ext =
              List.map (fun (s,ext) ->
                match StringMap.find s pi_state.q_env with
                  | EVar b ->
                      if b.btype != Param.nat_type
                      then input_error ("variable " ^ s ^ " used for inductions should be of type nat but is here of type " ^ b.btype.tname) ext;
                      b, (s,ext)
                 | _ -> input_error (s ^ " should be a variable") ext
              ) bl
            in
            (InductionSat (List.map (fun (b,_) -> b) bl_ext)) :: !op_acc,
	    (fun (_,args) ->
	      List.iter (check_induction_format bl_ext) args;
	      List.iter (fun (b,(s,ext)) ->
		if not (List.exists (Terms.occurs_var_format b) args) then
		  input_error ("The variable " ^ s ^ " declared for induction should occur in the fact.") ext
		    ) bl_ext
		)
    end

let get_nounif nounif_list pi_state =
  let q_state = build_q_state true pi_state in
  map_opt (fun (env, nounif,nounif_op) ->
    try
      let q_state1 = { q_state with q_env = add_env true q_state.q_env env } in

      let (nounif_op',test_var) = check_nounif_options q_state1 nounif_op in
      Some (handle_nounif q_state1 nounif_op'  test_var nounif)
    with
    | (MissingNameArg _ | BadBoundName _) as e ->
       handle_bad_bound_names q_state "Ignoring this nounif declaration." e
    ) nounif_list

(********************************************
 Local state of the main parsing function
*********************************************)

let equations = ref []
let disequations = ref []
let destructors_check_deterministic = ref []
let ids_with_global_refs = ref []

let corresp_query_list = ref ([] : (envdecl * tquery list) list)
let query_list = ref ([] : t_query list)
let not_list = ref ([] : (envdecl * gterm_e) list)
let input_clauses = ref ([] : (fact list * fact * constraints * label) list)
let elimtrue = ref ([] : fact list)
let equiv_list = ref ([] : (fact list * fact * int) list)
let nounif_list = ref ([] : (envdecl * nounif_t * options list) list)

let lemma_list = ref ([] : t_lemmas list)

let global_env = ref (StringMap.empty : envElement StringMap.t)

(*********************************************
                Parsing files
**********************************************)

let parse filename =
  try
    let ic = open_in filename in
    let lexbuf = Lexing.from_channel ic in
    lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with
                                  Lexing.pos_fname = filename };
    let ptree =
      try
        Pitparser.all Pitlexer.token lexbuf
      with Parsing.Parse_error ->
        input_error "Syntax error" (extent lexbuf)
    in
    close_in ic;
    ptree
  with Sys_error s ->
    user_error ("File error: " ^ s)

let parse_lib filename =
  let filename =
    if Terms.ends_with filename ".pvl" then
      filename
    else
      filename ^ ".pvl"
  in
  try
    let ic = open_in filename in
    let lexbuf = Lexing.from_channel ic in
    lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with
                                  Lexing.pos_fname = filename };
    let ptree =
      try
        Pitparser.lib Pitlexer.token lexbuf
      with Parsing.Parse_error ->
        input_error "Syntax error" (extent lexbuf)
    in
    close_in ic;
    ptree
  with Sys_error s ->
    user_error ("File error: " ^ s)

let parse_with_lib filename =
  let l1 =
    if (!Param.lib_name) <> "" then
      parse_lib (!Param.lib_name)
    else
      []
  in
  let (l,p,second_p) = parse filename in
  (l1 @ l, p,second_p)

(*******************************************
Get identifiers with global references, to
make sure that we keep them when they appear
as arguments of processes or letfun.
******************************************)

let add_id accu (s,ext) =
  if not (List.mem s (!accu)) then
    accu := s :: (!accu)

let get_ids_with_global_refs_query accu = function
    PPutBegin _ -> ()
  | PRealQuery(_,pub_vars) -> List.iter (add_id accu) pub_vars
  | PQSecret(s,pub_vars,_) -> add_id accu s; List.iter (add_id accu) pub_vars

let get_ids_with_global_refs_decl accu = function
    TQuery(_, ql,_) ->
      List.iter (get_ids_with_global_refs_query accu) ql
  | _ -> ()


(********* Types ***********
This section is composed of two main functions :
- [get_type : Ptree.ident -> Types.typet]
        [get_type (s,_)] returns the type associated to [s] in [global_env] if [s] isn't the pre-defined type ["sid"] and ["any_type"]
- [check_type_decl : Ptree.ident -> unit]
        [check_type_decl (s,_)] first checks if [s] is not ["any_type"], ["sid"], or already defined.
If not, then the type is added into [global_env]
****************************)

let get_type_polym polym sid_allowed id =
  get_type_polym (!global_env) polym sid_allowed id

let get_type ty = get_type_polym false false ty

(** [check_type_decl (s,ext)] first checks if [s] is not ["any_type"], ["sid"], or already defined.
If not, then the type is added into [global_env] *)
let check_type_decl (s, ext) =
  if s = "any_type" then
    input_error "type any_type reserved for polymorphism" ext;
  if s = "sid" then
    input_error "type sid reserved for session identifiers" ext;
  if StringMap.mem s (!global_env) then
    input_error ("identifier " ^ s ^ " already defined (as a free name, a function, a predicate, or a type)") ext;
  let r = { tname = s } in
  global_env := StringMap.add s (EType r) (!global_env)

(*********************************************
          Functions For Environment
**********************************************)

let initialize_env () =
  (* Initial functions and constant *)
  Display.record_id "true" dummy_ext;
  global_env := StringMap.add "true" (EFun Terms.true_cst) (!global_env);

  Display.record_id "false" dummy_ext;
  global_env := StringMap.add "false" (EFun Terms.false_cst) (!global_env);

  Display.record_id "not" dummy_ext;
  global_env := StringMap.add "not" (EFun (Terms.not_fun())) (!global_env);

  Display.record_id "&&" dummy_ext;
  global_env := StringMap.add "&&" (EFun (Terms.and_fun())) (!global_env);

  Display.record_id "||" dummy_ext;
  global_env := StringMap.add "||" (EFun (Terms.or_fun())) (!global_env);

  Display.record_id "0" dummy_ext;
  global_env := StringMap.add "0" (EFun Terms.zero_cst) (!global_env);

  Display.record_id "+" dummy_ext;
  global_env := StringMap.add "+" (EFun Terms.succ_fun) (!global_env);

  Display.record_id ">" dummy_ext;
  global_env := StringMap.add ">" (EFun (Terms.greater_fun ())) (!global_env);

  Display.record_id ">=" dummy_ext;
  global_env := StringMap.add ">=" (EFun (Terms.geq_fun ())) (!global_env);

  Display.record_id "<" dummy_ext;
  global_env := StringMap.add "<" (EFun (Terms.less_fun ())) (!global_env);

  Display.record_id "<=" dummy_ext;
  global_env := StringMap.add "<=" (EFun (Terms.leq_fun ())) (!global_env);

  Display.record_id "is_nat" dummy_ext;
  global_env := StringMap.add "is_nat" (EFun (Terms.is_nat_fun ())) (!global_env);

  List.iter (fun t ->
    Display.record_id t.tname dummy_ext;
    global_env := StringMap.add t.tname (EType t) (!global_env)
         ) Param.types_initial

let get_var env (s,ext) =
  try
    match StringMap.find s env with
      EVar v -> v
    | _ -> input_error (s ^ " should be a variable") ext
  with Not_found ->
    input_error ("variable " ^ s ^ " not declared") ext

(* environment *)

let create_env l =
  add_env false (!global_env) l

(* May-fail environment *)

let add_env_may_fail sid_allowed env l =
  let env_ref = ref env in
  List.iter (fun ((s,ext),ty,can_fail) ->
    let t = get_type_polym false sid_allowed ty in
    begin
      try
        match StringMap.find s (!env_ref) with
            | EVar v when v.unfailing && can_fail -> input_error ("variable " ^ s ^ " already defined") ext
            | EVar _ when can_fail -> input_error ("variable "^s^" was already defined as a may fail variable") ext
            | EVar _ -> input_error ("variable "^s^" was already defined as a message variable") ext
            | _ -> input_warning ("identifier " ^ s ^ " rebound") ext
      with Not_found -> ()
    end;

    let var = Terms.new_var ~may_fail:can_fail s t in
    env_ref := StringMap.add s (EVar var) (!env_ref)
  ) l;
  !env_ref

let create_may_fail_env l =
  add_env_may_fail false (!global_env) l

(*********************************************
        Check constructor declaration
**********************************************)

let check_fun_decl (name, ext) argtypes restype options =
  let tyarg = List.map get_type argtypes in
  let tyres = get_type restype in
  if StringMap.mem name (!global_env) then
    input_error ("identifier " ^ name ^ " already defined (as a free name, a function, a predicate, or a type)") ext;
  if  tyres == Param.nat_type
  then input_error ("The function " ^ name ^ " cannot be declared with 'nat' as a return type") ext;
  let is_tuple = ref false in
  let is_private = ref false in
  let opt = ref 0 in
  List.iter (function
        ("data",_) -> is_tuple := true
      | ("projection" | "uniform"),_ -> () (* ignored, for compatibility with CryptoVerif *)
      |       ("private",_) -> is_private := true
      | ("typeConverter",_) ->
          if List.length tyarg != 1 then
            input_error "only unary functions can be declared \"typeConverter\"" ext;
          is_tuple := true;
          opt := (!opt) lor Param.fun_TYPECONVERTER
      | (_,ext) ->
        input_error "for functions, the only allowed options are data, private, typeConverter, and projection and uniform, which are ignored, for compatibility with CryptoVerif" ext) options;
  if (!is_tuple) && (!is_private) then
    input_error "a function cannot be declared both data or typeConverter and private" ext;
  let cat = if !is_tuple (* || ((arity == 0) && (not is_private)) *) then Tuple else Eq [] in
  let r = { f_name = Fixed name;
            f_type = tyarg, tyres;
            f_cat = cat;
            f_initial_cat = cat;
            f_private = !is_private;
            f_options = !opt }
  in
  global_env := StringMap.add name (EFun r) (!global_env)

(*********************************************
         Check destructor declaration
**********************************************)

(* Destructor to check *)

let f_eq_tuple f s ext =
  match f.f_cat with
    Eq _ | Tuple -> ()
  | Name _ -> input_error (s ^ " is a name; it should not appear in equations or rewrite rules") ext
  | Red _ -> input_error (s ^ " is a function defined by rewrite rules; it should not appear in equations or rewrite rules") ext
  | _ -> input_error (s ^ " should not appear in equations or rewrite rules") ext

let f_any f s ext =
  match f.f_cat with
    Choice -> input_error "function choice should not appear in clauses or elimtrue" ext
  | Name _ -> input_error "names should not appear in clauses or elimtrue" ext
  | _ -> ()

let f_eq_tuple_name f s ext =
  match f.f_cat with
    Eq _ | Tuple | Name _ -> ()
  | Red _ -> input_error (s ^ " is a function defined by rewrite rules. It should not appear in non-interference queries") ext
  | _ -> input_error (s ^ " should not appear in non-interference queries") ext


(* Check messages *)

let rec check_eq_term f_allowed fail_allowed_top fail_allowed_all env (term,ext) =
  match term with
    | PFail -> input_error "The constant fail should not appear in this term" ext
    | (PIdent (s,ext)) ->
      let t =
        try
          match StringMap.find s env with
            | EVar v when (not (fail_allowed_top || fail_allowed_all)) && v.unfailing ->
                input_error ("The may-fail variable " ^ s ^ " cannot be used in this term.") ext
            | EVar v -> Var v
            | EFun f ->
                if fst f.f_type <> [] then
                input_error ("function " ^ s ^ " expects " ^
                  (string_of_int (List.length (fst f.f_type))) ^
                  " arguments but is used without arguments") ext;

                f_allowed f s ext;
                FunApp(f, [])
            | EName r ->
                f_allowed r s ext;
                FunApp (r, [])
            | _ -> input_error ("identifier " ^ s ^ " should be a function, a variable, or a name") ext
        with Not_found ->
          input_error ("identifier " ^ s ^ " not defined") ext
      in
      (t, Terms.get_term_type t)
    | (PFunApp ((f,ext), tlist)) ->
      (* FunApp: the allowed functions depend on f_allowed
         Three values of f_allowed are used:
         - f_eq_tuple: allow constructors only (for equations and definitions of destructors)
         - f_any: allow all functions except choice and names (for clauses and elimtrue)
         - f_eq_tuple_name: allow constructors and names (for non-interference queries)
         Predicates are never allowed. *)
      let (tl', tyl) = List.split (List.map (check_eq_term f_allowed false fail_allowed_all env) tlist) in
      let (f', result_type) = get_fun env (f,ext) tyl in
      f_allowed f' f ext;
      if (f'.f_options land Param.fun_TYPECONVERTER != 0) && (Param.get_ignore_types()) then
        match tl' with
          [t] -> (t, result_type)
        | _ -> internal_error "type converter functions should always be unary"
      else
        (FunApp(f', tl'), result_type)

  | (PTuple tlist) ->
      let (tl', tyl) = List.split (List.map (check_eq_term f_allowed false fail_allowed_all env) tlist) in
      (FunApp (Terms.get_tuple_fun tyl, tl'), Param.bitstring_type)

  | PProj _ ->
      input_error "projections not allowed here" ext

(* Check may-fail message *)

let check_may_fail_term env type_term (mterm,ext) = match mterm with
  | PFail ->
      Terms.get_fail_term type_term
  | _ ->
      let t, type_t = check_eq_term f_eq_tuple true false env (mterm,ext) in
      if type_t != type_term then
        input_error ("the term is of type "^type_t.tname^" but the type "^type_term.tname^" was expected") ext;
      t

(* Equations *)

let check_equation (env, t1, t2) =
  let var_env = create_env env in
  let (t1', ty1) = check_eq_term f_eq_tuple false false var_env t1 in
  let (t2', ty2) = check_eq_term f_eq_tuple false false var_env t2 in
  if ty1 != ty2 then
    begin
      let ext = merge_ext (snd t1) (snd t2) in
      input_error "the two members of an equation should have the same type" ext
    end;
  (t1', t2')

let check_equation_one_term (env, t1) =
  let var_env = create_env env in
  let (t1', ty1) = check_eq_term f_eq_tuple false false var_env t1 in
  if ty1 != Param.bool_type then
    input_error "when an equation declaration is just a term, it should have type bool" (snd t1);
  (t1', Terms.true_term)

let check_equations l eqinfo =
  let eqinfo' = match eqinfo with
    [] -> EqNoInfo
  | ["convergent",ext] -> EqConvergent
  | ["linear",ext] -> EqLinear
  | (_,ext)::_ -> Parsing_helper.input_error "for equations, the only allowed options are either convergent or linear" ext
  in
  let l' = map_opt (fun (env, t) ->
    match t with
      PFunApp(("=",_), [t1;t2]),_ ->
        Some (check_equation (env, t1, t2))
    | PFunApp(("<>",_), [t1;t2]), ext ->
        if eqinfo' != EqNoInfo then
          Parsing_helper.input_error "disequations should not have options [convergent] or [linear]" ext;
        disequations := (check_equation (env, t1, t2)) :: (!disequations);
        None
    | t1 ->
        Some (check_equation_one_term (env, t1))
          ) l
  in
  if l' <> [] then
    equations := (l', eqinfo') :: (!equations)

(* Definition of destructors using Otherwise. *)

let check_red_may_fail (f,ext) type_arg type_res tlist options =
  let ty_arg = List.map get_type type_arg in
  let ty_res = get_type type_res in

  if StringMap.mem f (!global_env) then
    input_error ("identifier " ^ f ^ " already defined (as a free name, a function, a predicate, or a type)") ext;

  if List.mem f special_functions then
    input_error (f ^ " not allowed here") ext;

  let rec generate_rules prev_args red_list = match red_list with
     | [] -> [],prev_args
     | (var_def,(PFunApp((f',ext'),l1),_), t2)::q ->
         if f <> f' then
           input_error ("In \"reduc\", all rewrite rules should begin with the same function " ^ f) ext';

         if List.length ty_arg != List.length l1 then
           input_error ("Function " ^ f ^ " expects " ^
                        (string_of_int (List.length ty_arg)) ^
                        " argument(s) but is here given " ^
                        (string_of_int (List.length l1)) ^ " argument(s)") ext';

         let env = create_may_fail_env var_def in

         let lhs = List.map2 (check_may_fail_term env) ty_arg l1
         and rhs = check_may_fail_term env ty_res t2 in

         (* Generate the destructors from side condition *)

         if lhs = []
         then ([[],rhs,Terms.true_constraints], [])
         else
           begin try
             let destructors = Terms.generate_destructor_with_side_cond prev_args lhs rhs ext' in
             let next_destructors,all_args = generate_rules (lhs::prev_args) q in

             (destructors @ next_destructors), all_args
           with Terms.False_inequality ->
             (* This otherwise and all the next ones are not satisfiable anymore (we should raise a warning probably) *)
             ([],prev_args)
           end
     | (_,(_, ext1), _)::_ -> input_error ("In \"reduc\", all rewrite rules should begin with function application") ext1

  in

  let red_list,all_args = generate_rules [] tlist in

  (* Generate the failing case *)
  let may_fail_vars = List.map (Terms.new_var_def_term ~may_fail:true) ty_arg
  and fail_term = Terms.get_fail_term ty_res in

  let complete_red_list =
    if may_fail_vars = []
    then red_list
    else
      begin try
        red_list @ (Terms.generate_destructor_with_side_cond all_args may_fail_vars fail_term Parsing_helper.dummy_ext)
      with
        Terms.False_inequality -> red_list
      end
  in

  assert (complete_red_list != []);

  let cat = Red complete_red_list in
  let is_private = ref false in

  List.iter (function
    | ("private",_) -> is_private := true
    | (_,ext) -> input_error "for functions defined by rewrite rules, the only allowed option is private" ext
  ) options;

  let fsymb =
    {
      f_name = Fixed f;
      f_type = ty_arg, ty_res;
      f_private = !is_private;
      f_options = 0;
      f_cat = cat;
      f_initial_cat = cat
    } in

  (* Adding the destructor in environment *)

  (*Display.Text.display_red fsymb complete_red_list;*)
  global_env := StringMap.add f (EFun fsymb) (!global_env)

(* Old definition of destructors, without otherwise *)

let check_red tlist options =
  match tlist with
    | (_,(PFunApp((f,ext),_),_),_)::_ ->
        begin
          if List.mem f special_functions then
            input_error (f ^ " not allowed here") ext;

          if StringMap.mem f (!global_env) then
            input_error ("identifier " ^ f ^ " already defined (as a free name, a function, a predicate, or a type)") ext;

          let red_list, ty_red_list = List.split (
            List.map (function
              | (var_def,(PFunApp((f',ext'),l1),_), t2) ->
                  if f <> f' then
                    input_error ("In \"reduc\", all rewrite rules should begin with the same function " ^ f) ext';

                  let env = create_env var_def in

                  let (lhs, tylhs), (rhs, tyrhs) = (List.split (List.map (check_eq_term f_eq_tuple false false env) l1), check_eq_term f_eq_tuple false false env t2) in
                  let var_list_rhs = ref [] in
                  Terms.get_vars var_list_rhs rhs;

                  if not (List.for_all (fun v -> List.exists (Terms.occurs_var v) lhs) (!var_list_rhs)) then
                    Parsing_helper.input_error "All variables of the right-hand side of a \"reduc\" definition\nshould also occur in the left-hand side." ext';

                  (lhs, rhs, Terms.true_constraints), (tylhs, tyrhs)
              | _,(_, ext1), _-> input_error ("In \"reduc\", all rewrite rules should begin with function application") ext1
            ) tlist
          ) in

          match ty_red_list with
            | [] -> internal_error "reduction with empty list"
            | (tylhs,tyrhs)::r ->
                List.iter (fun (tylhs',tyrhs') ->
                  if not (Terms.eq_lists tylhs tylhs') then
                    input_error ("the arguments of function " ^ f ^ " do not have the same type in all rewrite rules") ext;

                  if not (tyrhs == tyrhs') then
                    input_error ("the result of function " ^ f ^ " does not have the same type in all rewrite rules") ext
                ) r;

                let red_list' =
                  begin
                    let var_list = List.map (fun ty -> Terms.new_var_def_term ty) tylhs
                    and fail = Terms.get_fail_term tyrhs
                    and tuple_symb = Terms.get_tuple_fun tylhs in

                    let tuple = FunApp(tuple_symb, var_list) in

                    assert (!Terms.current_bound_vars == []);

                    let side_cond_neq =
                      List.map (fun (arg_list,_,_) ->
                        [tuple,FunApp(tuple_symb, List.map (Terms.generalize_vars_not_in []) arg_list)]
                      ) red_list in
                    let side_cond = { neq = side_cond_neq; geq = []; is_nat = []; is_not_nat = []} in

                    Terms.cleanup ();

                    red_list @ ((var_list,fail,side_cond)::(Terms.complete_semantics_constructors tylhs tyrhs))
                  end in

                let cat = Red red_list' in
                let is_private = ref false in

                List.iter (function
                  | ("private",_) -> is_private := true
                  | (_,ext) ->
                    input_error "for functions defined by rewrite rules, the only allowed option is private" ext
                ) options;

                let fsymb = {
                    f_name = Fixed f;
                    f_type = tylhs, tyrhs;
                    f_private = !is_private;
                    f_options = 0;
                    f_cat = cat;
                    f_initial_cat = cat
                  } in

                (* Adding the destructor for checking *)

                destructors_check_deterministic := fsymb::(!destructors_check_deterministic);

                (*Display.Text.display_red fsymb red_list';*)

                global_env := StringMap.add f (EFun fsymb) (!global_env)
      end
  | (_,(_, ext1), _) :: l ->
      input_error ("In \"reduc\", all rewrite rules should begin with function application") ext1
  | [] -> internal_error "reduction with empty list"

(* Check clauses *)

let rec interpret_info tyl prop = function
    ("memberOptim", ext) ->
      if List.length tyl != 2 then
        input_error "memberOptim makes sense only for predicates of arity 2" ext;
      prop lor Param.pred_ELEM
  | ("block",_) -> prop lor Param.pred_BLOCKING
          (* add other qualifiers here *)
  | (s,ext) -> input_error ("unknown predicate qualifier " ^ s) ext

let check_pred (c,ext) tl info =
  if c = "attacker" || c = "mess" || c = "event" || c = "inj-event" then
    input_error ("predicate name " ^ c ^ " is reserved. You cannot declare it") ext;
  if StringMap.mem c (!global_env) then
    input_error ("identifier " ^ c ^ " already defined (as a free name, a function, a predicate, or a type)") ext;
  let tyl = List.map (get_type_polym true false) tl in
  let prop = List.fold_left (interpret_info tyl) 0 info in
  let r = { p_name = c; p_type = tyl; p_prop = prop;
            p_info =
            if List.exists (fun t -> t == Param.any_type) tyl then
              [PolymPred(c, prop, tyl)]
            else
              [] }
  in
  global_env := StringMap.add c (EPred r) (!global_env)


let add_rule hyp concl constra tag =
  input_clauses := (hyp, concl, constra, tag) :: (!input_clauses)


let equal_fact t1 t2 =
  Pred(Param.get_pred (Equal(Terms.get_term_type t1)), [t1;t2])

let check_cterm env (p,t) =
  let (tl, tyl) = List.split (List.map (check_eq_term f_any false true env) t) in
  (get_pred env p tyl, tl)

let rec check_hyp is_simple (hyp_accu,constra_accu) env (fact, ext) =
  match fact with
  | PFail -> input_error "The constant fail should not appear in this fact" ext
  | PIdent p ->
      let (p',l') = check_cterm env (p,[]) in
      (Pred(p',l')::hyp_accu, constra_accu)
  | PTuple _ -> input_error "tuples not allowed here" ext
  | PProj _ -> input_error "projections not allowed here" ext
  | PFunApp((f,fext) as p, l) ->
      (* FunApp: two cases:
         If is_simple, allow && and predicates
         If not is_simple, allow &&, <>, =, and predicates
         NOTE: in the latter case, I could allow all functions and predicates (except choice),
         for functions other than &&, they should return type boolean, and
         the term t would be encoded as equal:t, true.
         In that case, I should also modify the case PIdent to allow boolean constants. *)
      match f,l with
        "<>", [t1;t2] ->
          if is_simple then
            input_error (f ^ " not allowed here") ext;
          let (t1', ty1) = check_eq_term f_any false true env t1 in
          let (t2', ty2) = check_eq_term f_any false true env t2 in
          if ty1 != ty2 then
            input_error "the two arguments of an inequality test should have the same type" ext;
          (hyp_accu, { constra_accu with neq = [(t1', t2')] :: constra_accu.neq})
      | "=", [t1;t2] ->
          if is_simple then
            input_error (f ^ " not allowed here") ext;
          let (t1', ty1) = check_eq_term f_any false true env t1 in
          let (t2', ty2) = check_eq_term f_any false true env t2 in
          if ty1 != ty2 then
            input_error "the two arguments of an equality test should have the same type" ext;
          ((equal_fact t1' t2')::hyp_accu, constra_accu)
      | "&&", [h1;h2] ->
          check_hyp is_simple (check_hyp is_simple (hyp_accu,constra_accu) env h1) env h2
      | ("<>" | "=" | "&&"), _ -> internal_error ("Bad arity for special function " ^ f)
      | _ ->
          let (p',l') = check_cterm env (p,l) in
          (Pred(p',l')::hyp_accu, constra_accu)

let check_simple_fact env (fact, ext) =
  match fact with
  | PFail -> input_error "The constant fail should not appear in this fact" ext
  | PIdent p ->
      let (p',l') = check_cterm env (p,[]) in
      Pred(p',l')
  | PTuple _ -> input_error "tuples not allowed here" ext
  | PProj _ -> input_error "projections not allowed here" ext
  | PFunApp((f,fext) as p,l) ->
      (* FunApp: only predicates allowed *)
      let (p',l') = check_cterm env (p,l) in
      Pred(p',l')

let check_clause = function
  | (env, PFact(c)) ->
     let env = create_may_fail_env env in
     let concl = check_simple_fact env c in
     add_rule [] concl Terms.true_constraints LblClause
  | (env, PClause(i,c)) ->
     let env = create_may_fail_env env in
     let (hyp, constra) = check_hyp false ([],Terms.true_constraints) env i in
     let concl = check_simple_fact env c in
     add_rule hyp concl constra LblClause
  | (env, PEquiv(i,c,select)) ->
      let env = create_may_fail_env env in
      let (hyp, constra) = check_hyp true ([],Terms.true_constraints) env i in
      if not (Terms.is_true_constraints constra) then
        Parsing_helper.internal_error "Inequality constraints not allowed in equivalences, should be eliminated by check_hyp true\n";
      let concl = check_simple_fact env c in
      add_rule hyp concl Terms.true_constraints LblEquiv;
      List.iter (fun h -> add_rule [concl] h Terms.true_constraints LblEquiv) hyp;
      equiv_list := (hyp, concl, -1)::(!equiv_list); (* TO DO should give a real rule number, but that's not easy... *)
      if not select then Terms.add_unsel concl


(* List of the free names of the process *)

let add_free_name (s,ext) t options =
  let is_private = ref false in
  List.iter (function
    | ("private",_) -> is_private := true
    | (_,ext) ->
        input_error "for free names, the only allowed option is private" ext) options;
  let ty = get_type t in
  if StringMap.mem s (!global_env) then
    input_error ("identifier " ^ s ^ " already declared (as a free name, a function, a predicate, or a type)") ext;
  if  ty == Param.nat_type
  then input_error ("The name " ^ s ^ " cannot be declared with the type 'nat'") ext;
  let r = Terms.create_name ~allow_rename:false s ([],ty) (!is_private) in
  global_env := StringMap.add s (EName r) (!global_env)


(* Check non-interference terms *)

let get_non_interf_name env (s,ext) =
   try
     match StringMap.find s env  with
       EName r ->
         if not r.f_private then
           input_error ("Non-interference is certainly false on public values, such as " ^ s) ext
         else
           r
     | _ ->
         input_error ("Non-interference can only be tested on private free names") ext
   with Not_found ->
     input_error ("Name " ^ s ^ " is not declared") ext

let get_non_interf env (id, lopt) =
  let n = get_non_interf_name (create_env env) id in
  (n,
   match lopt with
     None -> None
   | Some l ->
       Some (List.map (fun t ->
         let (t', ty) = check_eq_term f_eq_tuple_name false false (create_env env) t in
         if ty != snd n.f_type then
           input_error ("this term has type " ^ ty.tname ^ " but should have type " ^ (snd n.f_type).tname) (snd t);
         t'
             ) l))

(*********************************************
           Preliminary functions
**********************************************)

(* Term from identifier *)

let get_term_from_ident env (s, ext) =
   try
     match StringMap.find s env with
       EVar b ->
         (fun proc_context -> proc_context
           begin
             match b.link with
             | NoLink -> Var(b)
             | TLink t -> t
             | _ -> internal_error "Bad link in the environment [pit_syntax_equivalence > get_term_from_ident]"
           end
             ), b.btype
     | EName r ->
         (fun proc_context -> proc_context (FunApp (r,[]))), snd r.f_type
     | EFun f ->
         if fst f.f_type = [] then
           (fun proc_context -> proc_context (FunApp(f,[]))), snd f.f_type
         else
           input_error ("function " ^ s ^ " expects " ^
                        (string_of_int (List.length (fst f.f_type))) ^
                        " arguments but is used without arguments") ext
     | ELetFun(func_proc_layer, arg_type_list, result_type) ->
         if arg_type_list != [] then
             input_error ("letfun function " ^ s ^ " expects " ^
                        (args_to_string arg_type_list) ^
                        " but is used without arguments") ext;
         (func_proc_layer []), result_type
     | EPred p ->
         if p.p_type != [] then
           input_error ("predicate " ^ s ^ " expects " ^
                        (args_to_string p.p_type) ^
                        " but is used without arguments") ext;
         (fun proc_context ->
           LetFilter([], Pred(p, []),
                   proc_context Terms.true_term,
                   proc_context Terms.false_term,
                   Terms.new_occurrence ()
                     )), Param.bool_type
     | _ -> input_error ("identifier " ^ s ^ " should be a variable, a function, a name, or a predicate") ext
   with Not_found ->
     input_error ("Variable, function, name, or predicate " ^ s ^ " not declared") ext

(*********************************************
              Checking Event
**********************************************)

let check_event (name, ext) argtypes =
  let tyarg = List.map get_type argtypes in
  let tyarg = if !Param.key_compromise = 0 then tyarg else Param.sid_type :: tyarg in
  if StringMap.mem name (!global_env) then
    input_error ("identifier " ^ name ^ " already defined (as a free name, a function, a predicate, or a type)") ext;
  let r = { f_name = Fixed name;
            f_type = tyarg, Param.event_type;
            f_cat = Eq[];
            f_initial_cat = Eq[];
            f_private = true;
            f_options = 0 }
  in
  global_env := StringMap.add name (EEvent r) (!global_env)

(*********************************************
              Checking Table
**********************************************)

let check_table (name, ext) argtypes =
  let tyarg = List.map get_type argtypes in
  if StringMap.mem name (!global_env) then
    input_error ("identifier " ^ name ^ " already defined (as a free name, a function, a predicate, or a type)") ext;
  let r = { f_name = Fixed name;
            f_type = tyarg, Param.table_type;
            f_cat = Tuple;
            f_initial_cat = Tuple;
            f_private = true;
            f_options = 0 }
  in
  global_env := StringMap.add name (ETable r) (!global_env)

(*********************************************
               Checking Term
**********************************************)

let rec get_restr_arg env = function
    [] -> []
  | (s,ext)::l ->
      if List.exists (fun (s',_) -> s' = s) l then
        get_restr_arg env l
      else
        try
          match StringMap.find s env with
            EVar b -> b::(get_restr_arg env l)
          | _ ->
              Parsing_helper.input_error (s ^ " should be a variable") ext
        with Not_found ->
          Parsing_helper.input_error ("variable " ^ s ^ " not defined") ext

let get_restr_arg_opt env = function
    None -> None
  | Some l -> Some (get_restr_arg env l)

let check_no_global_ref (s,ext) =
  if List.mem s (!ids_with_global_refs) then
    input_error ("Variable or name "^s^" defined in a term and referenced in a query. This is not allowed because in general the expansion of terms may not allow "^s^" to be defined exactly when it is in the initial process") ext

let rec check_no_global_ref_pat = function
    PPatVar (id,_) -> check_no_global_ref id
  | PPatTuple(l) | PPatFunApp(_,l) ->
      List.iter check_no_global_ref_pat l
  | PPatEqual _ -> ()

let check_no_ref ext vlist proc_layer =
  let proc_layer_Nil = proc_layer (fun _ -> Nil) in
  if List.exists (fun v -> Reduction_helper.occurs_var_proc v proc_layer_Nil) vlist then
    input_error "Cannot expand term because a variable in the expanded part would be referenced before being defined" ext

(** [check_term : Types.envElement -> Pitptree.pterm_e -> ((Types.term -> Types.process) -> Types.process) * Types.typet].
In [check_term env pterm],
-- [env] is the environment that stores the meaning of the elements currently in scope
-- [pterm] is the term that will be checked

The function returns the translated process obtain from [proc_func] once [pterm] is translated, and the type of the term. *)
let rec check_term env (term, ext) =
  match term with
  | PPIdent(id) ->
      get_term_from_ident env id

  | PPTuple(term_list) ->
      let proc_layer_list, type_list = check_term_list env term_list in
      let tuple_symb = Terms.get_tuple_fun type_list in
      let proc_layer_tuple proc_context =
        proc_layer_list (fun l -> proc_context (FunApp(tuple_symb,l)))
      in
      (proc_layer_tuple, Param.bitstring_type)

  | PPRestr((s,ext),args,tyid,t) ->
      check_no_global_ref (s,ext);
      let ty = get_type tyid in
      if (StringMap.mem s env) then
        input_warning ("identifier " ^ s ^ " rebound") ext;
      if  ty == Param.nat_type
       then input_error ("The name " ^ s ^ " cannot be declared with the type 'nat'") ext;
      let r = Terms.create_name s (Param.tmp_type, ty) true in
      let env' = StringMap.add s (EName r) env in
      let (proc_layer, type_t) = check_term env' t in
      let args_opt = get_restr_arg_opt env args in
      let rec get_lets_args = function
          [] -> ([],[])
        | b::l ->
            let (lets,l') = get_lets_args l in
            match b.link with
              NoLink -> (lets, b::l')
            | TLink (Var b') ->
                (lets, b'::l')
            | TLink t ->
                let b' = Terms.copy_var b in
                let glet_symb =  Terms.glet_fun b.btype in
                ((b', FunApp(glet_symb, [t]))::lets, b'::l')
            | _ -> Parsing_helper.internal_error "unexpected link in Pitsyntax.check_term"
      in
      let get_lets_args_opt = function
          None -> ([], None)
        | Some l ->
            let lets, l' = get_lets_args l in
            (lets, Some l')
      in
      let rec put_lets p = function
          [] -> p
        | (v,t)::l -> put_lets (Let(PatVar v,t,p,Nil,Terms.new_occurrence())) l
      in
      let proc_layer_restr proc_context =
        let (lets, args_opt') = get_lets_args_opt args_opt in
        put_lets
          (Restr(r, (args_opt', env), proc_layer proc_context, Terms.new_occurrence())) lets
      in
      (proc_layer_restr, type_t)

  | PPFunApp((s,ext),list_arg) ->
        (* FunApp: all functions (including choice), predicates, and letfun allowed. *)
      begin
        let (proc_layer_list, type_list) = check_term_list env list_arg in
        match get_apply_symb env (s,ext) type_list with
          (EFun f, result_type) ->
            if (f.f_options land Param.fun_TYPECONVERTER != 0) && (Param.get_ignore_types()) then
              (* For a type converter function, the result is directly given : no FunApp.
                 Furthermore, the number of argument should be 1 *)
              let proc_layer proc_context =
                proc_layer_list (fun l ->
                  match l with
                  | [t] -> proc_context t
                  | _ -> internal_error "Type converter functions should always be unary")
              in
              (proc_layer, result_type)
            else
              let proc_layer proc_context =
                proc_layer_list (fun l -> proc_context (FunApp(f,l)))
              in
              (proc_layer, result_type)

        | (ELetFun(func_proc_layer, arg_type_list, result_type), _) ->
            let proc_layer proc_context =
              proc_layer_list (fun l ->
                func_proc_layer l proc_context
                  )
            in
            (proc_layer, result_type)

        | (EPred p, result_type) ->
            (* allow predicates, encoded by LetFilter([], p(M1...Mn), true, false *)
            let proc_layer context =
              proc_layer_list (fun t_list ->
                LetFilter([], Pred(p, t_list),
                          context Terms.true_term,
                          context Terms.false_term,
                          Terms.new_occurrence ()
                            )
                  )
            in
            (proc_layer, result_type)

        | _ -> input_error (s ^ " should be a function or a predicate") ext
      end

  | PPTest(cond,term_then,term_else_opt) ->
        (* PPTest can be transformed into an application of the destructor gtest *)

        let (proc_layer_cond, type_cond) = check_term env cond in
        let (proc_layer_then, type_then) = check_term env term_then in
        let (proc_layer_else, type_else) =
          match term_else_opt with
            Some term_else -> check_term env term_else
          | None ->
              let fail = Terms.get_fail_term type_then in
              ((fun proc_context -> proc_context fail), type_then)
        in

        if type_cond != Param.bool_type then
          input_error ("The type of the condition in the test is " ^
                       type_cond.tname ^ " but a boolean is expected.") ext;
        if type_then != type_else then
          input_error
            (Printf.sprintf "The then and else branches of the test should have the same type, but the then branch is of type %s and the else branch is of type %s."
               type_then.tname type_else.tname)
            ext;

        if !Param.expand_if_terms_to_terms then

          let proc_layer proc_context =
            proc_layer_cond (fun c ->
              proc_layer_then (fun tthen ->
                proc_layer_else (fun telse ->
                  let gtest_symb = Terms.gtest_fun type_then in
                  proc_context (FunApp(gtest_symb,[c;tthen;telse]))
            )))
          in
          (proc_layer, type_then)
        else
          begin
            match term_else_opt with
              Some term_else ->
                let fail = Terms.get_fail_term type_then in
                let b = Terms.new_var_def Param.bool_type in
                let proc_layer proc_context =
                  proc_layer_cond (fun c ->
                  Let(PatVar b, c,
                      Test(Var b, proc_layer_then proc_context,
                            proc_layer_else proc_context,
                           Terms.new_occurrence()),
                      proc_context fail,
                      Terms.new_occurrence()))
                in
                (proc_layer, type_then)

            | None ->
                let fail = Terms.get_fail_term type_then in
                let proc_layer proc_context =
                  proc_layer_cond (fun c ->
                    Let(PatEqual (Terms.true_term), c,
                        proc_layer_then proc_context,
                        proc_context fail,
                        Terms.new_occurrence()))
                in
                (proc_layer, type_then)
          end

  | PPLet(pat,term,term_then, term_else_opt) ->
      check_no_global_ref_pat pat;
        (* This case will be transformed into a process Let which will never fail,
           and then use the destructor gletresult to get the correct message.*)

        let (proc_layer_term, type_term) = check_term env term in
        let (proc_layer_pattern, env',_) = check_pattern_into_one_var ext env (Some type_term) pat in

        let (proc_layer_then, type_then) = check_term env' term_then in
        let (proc_layer_else, type_else) =
          match term_else_opt with
            Some term_else -> check_term env term_else
          | None ->
              let fail = Terms.get_fail_term type_then in
              ((fun proc_context -> proc_context fail), type_then)
        in

        if type_then != type_else
        then input_error "the in and else branches should have the same type" ext;

        let proc_layer proc_context  =
          proc_layer_term (fun term_eval ->
            proc_layer_pattern (fun pattern -> fun opt_test_pattern ->
              let glet_symb =  Terms.glet_fun type_term in

              let var = Terms.term_of_pattern_variable pattern in

              match opt_test_pattern with
                |None ->
                   Let(pattern, FunApp(glet_symb,[term_eval]),
                     proc_layer_then (fun t_then ->
                       proc_layer_else (fun t_else ->
                         proc_context (FunApp(Terms.gtest_fun type_then, [FunApp(Terms.not_caught_fail_fun type_term, [var]); t_then; t_else]))
                       )
                     )
                     ,Nil,
                     Terms.new_occurrence()
                   )
                |Some(test) ->
                   Let(pattern, FunApp(glet_symb,[term_eval]),
                       proc_layer_then (fun t_then ->
                         proc_layer_else (fun t_else ->
                           proc_context (FunApp(Terms.gtest_fun type_then,
                                                [ FunApp(Terms.and_fun(),
                                                         [ FunApp(Terms.not_caught_fail_fun type_term, [var]);
                                                           FunApp(Terms.success_fun Param.bool_type, [FunApp(Terms.is_true_fun(), [test])]) ]);
                                                  t_then; t_else ]))
                         )
                       ),
                       Nil,
                       Terms.new_occurrence()
                   )

            )
          ) in

        (proc_layer, type_then)

  | PPLetFilter(identlist,(fact,ext),term_then,term_else_opt) ->
      List.iter (fun (id,_) -> check_no_global_ref id) identlist;
        let (env', vlist) =
          List.fold_left (fun (env, vlist) ((s,e),t) ->
            if (StringMap.mem s env) then
              input_warning ("identifier " ^ s ^ " rebound") e;

            let ty = get_type t in
            let v = Terms.new_var s ty in
            (StringMap.add s (EVar v) env, v:: vlist)
          ) (env,[]) identlist in

        let vlist = List.rev vlist in

        let layer_fact = check_fact env' (fact,ext) in
        (* Verify that the expanded part of layer_fact does not reference
           the variables of vlist *)
        check_no_ref ext vlist layer_fact;

        let (layer_then, type_then) = check_term env' term_then in
        let (layer_else, type_else) =
          match term_else_opt with
            Some term_else -> check_term env term_else
          | None ->
              let fail = Terms.get_fail_term type_then in
              ((fun proc_context -> proc_context fail), type_then)
        in

        if type_then != type_else then
          input_error "the in and else branches should have the same type" ext;

        let layer_proc context =
          layer_fact (fun fact' ->
            LetFilter(vlist,fact',
              layer_then context,
              layer_else context,
              Terms.new_occurrence ()
            )
          ) in

        (layer_proc, type_then)

    | PPEvent(id,l, env_args, term_cont) ->
        let (layer_list, type_list) = check_term_list env l in
        let env_args' = (get_restr_arg_opt env env_args, env) in
        if !Param.key_compromise == 0 then
          let f = get_event_fun env id type_list in
          let (proc_layer_cont, type_cont) = check_term env term_cont in
          let proc_layer proc_context =
            layer_list (fun l' ->
              Event(FunApp(f, l'), env_args',
                    proc_layer_cont proc_context,
                    Terms.new_occurrence()))
          in
          (proc_layer, type_cont)
        else
          let f = get_event_fun env id (Param.sid_type :: type_list) in
          let (proc_layer_cont, type_cont) = check_term env term_cont in
          let proc_layer proc_context =
            layer_list (fun l' ->
              Event(FunApp(f, (Terms.new_var_def_term Param.sid_type) :: l'),
                    env_args',
                    proc_layer_cont proc_context,
                    Terms.new_occurrence()))
          in
          (proc_layer, type_cont)

    | PPInsert(id,l,term_cont) ->
        let (layer_list, type_list) = check_term_list env l in
        let f = get_table_fun env id type_list in
        let (proc_layer_cont, type_cont) = check_term env term_cont in
        let proc_layer proc_context =
          layer_list (fun l' ->
            Insert(FunApp(f,l'),
                   proc_layer_cont proc_context,
                   Terms.new_occurrence()))
        in
        (proc_layer, type_cont)

    | PPGet((i,ext),pat_list,cond_opt,term_then,term_else_opt) ->
        List.iter check_no_global_ref_pat pat_list;
        try
          match StringMap.find i env with
          | ETable f ->
              (* By checking the terms in the patterns in the initial environment env,
                 we make sure that layer_pat cannot reference variables bound in the
                 patterns *)
              if List.length (fst f.f_type) != List.length pat_list then
                input_error ("Table " ^ i ^ " expects " ^
                             (string_of_int (List.length (fst f.f_type))) ^
                             " argument(s) but is here given " ^
                             (string_of_int (List.length pat_list)) ^ " argument(s)") ext;
               let (layer_pat, env', type_pat) = check_pattern_list ext env (List.map (fun t -> Some t) (fst f.f_type)) pat_list env in

               let layer_cond =
                 match cond_opt with
                 | Some t ->
                     let (layer_cond,type_cond) = check_term env' t in
                     if type_cond != Param.bool_type then
                       input_error ("this term has type " ^ type_cond.tname ^ " but should have type bool") (snd t);

                     (* Verify that the expanded part of layer_cond does not reference
                        the variables of bound in the patterns *)
                     let vlist = ref [] in
                     let _ = layer_pat (fun pat_list ->
                       (* The goal of this function is to get all variables bound by the pattern
                          by storing them in vlist *)
                       vlist := List.fold_left Reduction_helper.get_pat_vars (!vlist) pat_list;
                       Nil)
                     in
                     check_no_ref (snd t) (!vlist) layer_cond;
                     layer_cond
                 | None ->
                     (fun cond_context -> cond_context Terms.true_term)
               in
               let (proc_layer_then, type_then) = check_term env' term_then in
               let (proc_layer_else, type_else) =
                 match term_else_opt with
                   Some term_else -> check_term env term_else
                 | None ->
                     let fail = Terms.get_fail_term type_then in
                     ((fun proc_context -> proc_context fail), type_then)
               in
               if type_then != type_else then
                 input_error
                   (Printf.sprintf "The then and else branches of get should have the same type, but the then branch is of type %s and the else branch is of type %s."
                      type_then.tname type_else.tname)
                   ext;

               let proc_layer proc_context =
                 layer_pat (fun pat_list ->
                   layer_cond (fun cond ->
                     Get(PatTuple(f,pat_list), cond,
                         proc_layer_then proc_context,
                         proc_layer_else proc_context, Terms.new_occurrence ())
                       )
                     )
               in
               (proc_layer, type_then)
          | _ -> input_error (i ^ " should be a table") ext
        with Not_found ->
          input_error ("table " ^ i ^ " not defined") ext

(** [check_term_list : Types.envElement -> Pitptree.pterm_e list -> ((Types.term list -> Types.process) -> Types.process) * Types.typet].
*)
and check_term_list env term_list = (match term_list with
  | [] ->
      (* It corresponds to when no term needs to be checked hence the context is in fact a process *)
      ((fun proc_context -> proc_context []), [])
  | term::q ->
      let (proc_layer_q,ty_list_q) = check_term_list env q
      and (proc_layer_t,ty_term) = check_term env term in

      let proc_layer_list proc_context =
        proc_layer_t (fun t -> proc_layer_q (fun l -> proc_context (t::l))) in

      (proc_layer_list, (ty_term::ty_list_q)):((Types.term list -> Types.process) -> Types.process)*(Types.typet list))


(*********************************************
               Checking Pattern
**********************************************)


(** [check_pattern :
       Types.envElement ->
       Types.typet option ->
       Pitptree.tpattern ->
       ((Types.pattern -> Types.term -> Types.process) -> Types.process) * Types.envElement].
*)
and check_pattern environment type_pat_opt pat new_env =
  match pat with
  | PPatVar ((s,e), ty_opt) ->
      let ty =
        match ty_opt, type_pat_opt with
          | None, None -> input_error ("variable " ^ s ^ " should be declared with a type") e
          | Some (t,e), None -> get_type (t,e)
          | None, Some ty -> ty
          | Some (t,e), Some ty ->
              let ty' = get_type (t,e) in
              if ty != ty' then
                input_error ("variable " ^ s ^ " is declared of type " ^ t ^ " but should be of type " ^ ty.tname) e;
              ty
      in

      if (StringMap.mem s new_env) then
        input_warning ("identifier " ^ s ^ " rebound") e;

      let v = Terms.new_var s ty in

      (* DEBUG *)

      (*Printf.printf "\nType of Pattern %s is %s\n" (v.sname) (v.btype.tname);*)

      let layer_proc context = context (PatVar v) in

      (layer_proc, StringMap.add s (EVar v) new_env, ty)

  | PPatTuple list_pat ->
      begin
        match type_pat_opt with
          |None -> ()
          |Some(ty) when ty != Param.bitstring_type -> input_error ("pattern is of type " ^ Param.bitstring_type.tname ^ " but should be of type " ^ ty.tname) dummy_ext
          |_ -> ()
      end;

     let (layer_proc_list,env', ty_list) = check_pattern_list dummy_ext environment (List.map (fun _ -> None) list_pat) list_pat new_env in

     let tuple_symb = Terms.get_tuple_fun ty_list in

     let layer_proc context =
       layer_proc_list (fun l_pat ->
         context (PatTuple(tuple_symb, l_pat))
       )
     in
     (layer_proc, env', Param.bitstring_type)

  | PPatEqual term ->
      (* By checking the term in the initial environment before
         adding variables bound by the pattern, we make sure that
         layer_proc_t does not reference variables bound in the pattern *)
      let (layer_proc_t, type_t) = check_term environment term in

      begin
        match type_pat_opt with
        | None -> ()
        | Some(ty) ->
            if ty != type_t then
              input_error ("pattern is of type " ^ type_t.tname ^ " but should be of type " ^ ty.tname) (snd term);
      end;

      let layer_proc context =
        layer_proc_t (fun t -> context (PatEqual t)) in

      (layer_proc, new_env, type_t)

  | PPatFunApp((s,ext),l) ->
      (* PatFunApp: only data constructors allowed *)
      try
        begin match StringMap.find s environment with
          | EFun f ->
              begin match type_pat_opt with
                | None -> ()
                | Some ty ->
                    if ty != snd f.f_type then
                      input_error ("pattern is of type " ^ (snd f.f_type).tname ^ " but should be of type " ^ ty.tname) ext;
              end;

              if List.length (fst f.f_type) != List.length l then
                input_error ("Function " ^ s ^ " expects " ^
                             (string_of_int (List.length (fst f.f_type))) ^
                             " argument(s) but is here given " ^
                             (string_of_int (List.length l)) ^ " argument(s)") ext;

              let (layer_list, env', type_list) = check_pattern_list ext environment (List.map (fun t -> Some t) (fst f.f_type)) l new_env in

              if f.f_cat <> Tuple then
                input_error ("only data functions are allowed in patterns, not " ^ s) ext;

              if (f.f_options land Param.fun_TYPECONVERTER != 0) && (Param.get_ignore_types())
              then
                let layer_proc context =
                  layer_list (fun l -> match l with
                    | [t] -> context t
                    | _ -> internal_error "type converter functions should always be unary"
                  ) in

                (layer_proc, env', snd f.f_type)
              else
                let layer_proc context =
                  layer_list (fun l -> context (PatTuple(f,l))) in

                (layer_proc, env', snd f.f_type)
          | _ -> input_error ("only functions can be applied, not " ^ s) ext
        end
      with Not_found ->
        input_error ("function " ^ s ^ " not defined") ext


and check_pattern_list ext environment type_pat_list_opt pat_list env = match pat_list,type_pat_list_opt with
  | [],[] -> (fun context -> context []),env, []
  | pat::pat_l, ty_pat::ty_pat_l ->
      let (layer_proc_pat, env', type_t) = check_pattern environment ty_pat pat env in
      let (layer_proc_pat_l, env'', type_tl) = check_pattern_list ext environment ty_pat_l pat_l env' in

      let layer_proc context =
        layer_proc_pat (fun pattern ->
          layer_proc_pat_l (fun pattern_list ->
            context (pattern::pattern_list)
          )
        ) in

      (layer_proc, env'',type_t::type_tl)
  |_,_ -> internal_error "[check_pattern_list] Size of pattern list and type list should be the same"

(*********************************************
        Checking and Transform Pattern
**********************************************)


(** [check_pattern :
       Types.envElement ->
       Types.typet option ->
       Pitptree.tpattern ->
       ((Types.pattern -> Types.term -> Types.process) -> Types.process) * Types.envElement].
*)
and check_pattern_into_one_var ext environment type_pat_opt pat =

  let rec sub_check_pattern  env cor_ty_opt pattern = match pattern with
    | PPatVar ((s,e), ty_opt) ->
        let ty =
          match ty_opt, cor_ty_opt with
            | None, None -> input_error ("variable " ^ s ^ " should be declared with a type") e
            | Some (t,e), None -> get_type (t,e)
            | None, Some ty -> ty
            | Some (t,e), Some ty ->
                let ty' = get_type (t,e) in
                if ty != ty' then
                  input_error ("variable " ^ s ^ " is declared of type " ^ t ^ " but should be of type " ^ ty.tname) e;
                ty
        in

        if (StringMap.mem s env) then
          input_warning ("identifier " ^ s ^ " rebound") e;

        let v = Terms.new_var s ty in

        let layer_proc final_pat cor_term context =
          v.link <- (TLink cor_term);
          let p = context final_pat None in
          p
        in

        (layer_proc, StringMap.add s (EVar v) env, ty)

    | PPatTuple [] ->
        let equal_symb = Terms.equal_fun Param.bitstring_type in
        let tuple_symb = Terms.get_tuple_fun [] in

        let layer_proc final_pat cor_term context =
          context final_pat (Some (FunApp(equal_symb,[FunApp(tuple_symb,[]);cor_term]))) in

        (layer_proc, env, Param.bitstring_type)

    | PPatTuple list_pat ->
        begin
          match cor_ty_opt with
          | None -> ()
          | Some(ty) when ty != Param.bitstring_type -> input_error ("pattern is of type " ^ Param.bitstring_type.tname ^ " but should be of type " ^ ty.tname) ext;
          |_ -> ()
        end;

        let (layer_proc_list,env', ty_list) = sub_check_pattern_list env (List.map (fun _ -> None) list_pat) list_pat in

        let layer_proc final_pat cor_term context =
          let cor_term_list = List.map (fun f -> FunApp(f,[cor_term])) (Terms.get_all_projection_fun (Terms.get_tuple_fun ty_list)) in

         layer_proc_list final_pat cor_term_list
           (fun f_pat -> fun opt_test ->
             let fst_elt = List.hd cor_term_list
             and success_symb = Terms.success_fun (List.hd ty_list) in
             let test_proper_tuple = FunApp(success_symb,[fst_elt]) in
             match opt_test with
             | None -> context f_pat (Some test_proper_tuple)
             | Some(test) -> context f_pat (Some (FunApp(Terms.and_fun(),[test;test_proper_tuple])))
           )
       in

       (layer_proc, env', Param.bitstring_type)

    | PPatEqual term ->
        let (layer_proc_t, type_t) = check_term environment term in

        begin
          match cor_ty_opt with
          | None -> ()
          | Some(ty) when ty != type_t -> input_error ("pattern is of type " ^ type_t.tname ^ " but should be of type " ^ ty.tname) (snd term);
          |_ -> ()
        end;

        let equal_symb = Terms.equal_fun type_t in

        let layer_proc final_pat cor_term context =
          layer_proc_t (fun t -> context final_pat (Some (FunApp(equal_symb,[t;cor_term])))) in

        (layer_proc, env, type_t)

    | PPatFunApp((s,ext),l) ->
        (* PatFunApp: only data constructors allowed *)
        begin
          try
            match StringMap.find s env with
            | EFun f when fst f.f_type = [] ->
                if l != [] then
                  input_error ("Function " ^ s ^
                               " expects no argument but is here given " ^
                               (string_of_int (List.length l)) ^ " argument(s)") ext;
                let equal_symb = Terms.equal_fun (snd f.f_type) in

                let layer_proc final_pat cor_term context =
                  context final_pat (Some (FunApp(equal_symb,[FunApp(f,[]);cor_term]))) in

                (layer_proc, env, snd f.f_type)
            | EFun f->
                begin
                  match cor_ty_opt with
                  | None -> ()
                  | Some ty ->
                      if ty != snd f.f_type then
                        input_error ("pattern is of type " ^ (snd f.f_type).tname ^ " but should be of type " ^ ty.tname) ext;
                end;

                if List.length (fst f.f_type) != List.length l then
                  input_error ("Function " ^ s ^ " expects " ^
                               (string_of_int (List.length (fst f.f_type))) ^
                               " argument(s) but is here given " ^
                               (string_of_int (List.length l)) ^ " argument(s)") ext;
                let (layer_list, env', type_list) = sub_check_pattern_list env (List.map (fun t -> Some t) (fst f.f_type)) l in

                if f.f_cat <> Tuple then
                  input_error ("only data functions are allowed in patterns, not " ^ s) ext;

                if (f.f_options land Param.fun_TYPECONVERTER != 0) && (Param.get_ignore_types())
                then
                  let layer_proc final_pat cor_term context =
                    layer_list final_pat ([cor_term]) context in
                  (layer_proc, env', snd f.f_type)
                else
                  let layer_proc final_pat cor_term context =
                    let cor_term_list = List.map (fun f -> FunApp(f,[cor_term])) (Terms.get_all_projection_fun f) in

                    layer_list final_pat cor_term_list
                      (fun f_pat -> fun opt_test ->
                         let fst_elt = List.hd cor_term_list
                         and success_symb = Terms.success_fun (List.hd type_list) in
                         let test_proper_tuple = FunApp(success_symb,[fst_elt]) in
                         match opt_test with
                           | None -> context f_pat (Some test_proper_tuple)
                           | Some(test) -> context f_pat (Some (FunApp(Terms.and_fun(),[test;test_proper_tuple])))
                      )
                  in

                  (layer_proc, env', snd f.f_type)
            | _ -> input_error ("only functions can be applied, not " ^ s) ext
          with Not_found ->
            input_error ("function " ^ s ^ " not defined") ext
        end

  and sub_check_pattern_list env cor_ty_list_opt pattern_list = match pattern_list,cor_ty_list_opt with
    | [],[] -> (fun final_pat -> fun _ -> fun context -> context final_pat None),env, []
    | pat::pat_l, ty_pat::ty_pat_l ->
       let (layer_proc_pat, env', type_t) = sub_check_pattern env ty_pat pat in
       let (layer_proc_pat_l, env'', type_tl) = sub_check_pattern_list env' ty_pat_l pat_l in

       let layer_proc final_pat cor_term_list context =
          layer_proc_pat final_pat (List.hd cor_term_list)
            (fun f_pat -> fun opt_test ->
              layer_proc_pat_l f_pat (List.tl cor_term_list)
                (fun  f_pat' -> fun opt_test' ->
                   match opt_test, opt_test' with
                     |None,None -> context f_pat' None
                     |None,Some(_) -> context f_pat' opt_test'
                     |Some(_),None -> context f_pat' opt_test
                     |Some(test),Some(test') -> context f_pat' (Some (FunApp(Terms.and_fun(),[test; test'])))
                )
            ) in

       (layer_proc, env'',type_t::type_tl)
    | _,_ -> internal_error "[sub_check_pattern_list] The two list should have the same size" in

  let (layer_proc, env, type_pat) = sub_check_pattern environment type_pat_opt pat in

  let x = Terms.new_var_def type_pat in

  (layer_proc (PatVar x) (Var x), env, type_pat)

(*********************************************
              Checking Fact
**********************************************)

and check_fact env (fact, ext) = match fact with
  | PPIdent p ->
      (fun context -> context (Pred(get_pred env p [],[])))

  | PPTuple _ -> input_error "tuples not allowed here" ext
  | PPRestr _ | PPTest _ | PPLet _ | PPLetFilter _
  | PPEvent _ | PPInsert _ | PPGet _ ->
      input_error "new, if, let allowed in terms, but not at this position in conditions" ext
  | PPFunApp((f,fext) as p,l) ->
      (* FunApp: = and predicates allowed
         NOTE: in fact, t = true allows to encode any boolean term,
         should I rather allow any boolean term? *)

      match f, l with
        "=", [t1;t2] ->
          let (layer_1, type_1) = check_term env t1
          and (layer_2, type_2) = check_term env t2 in

          if type_1 != type_2 then
            input_error "the two arguments of an equality test should have the same type" ext;

          fun context ->
            layer_1 (fun term_1 ->
              layer_2 (fun term_2 ->
                context (equal_fact term_1 term_2)
              )
            )

      | "=", _ -> internal_error ("Bad arity for special function " ^ f)
      | _ ->
          let (layer_list, type_l) = check_term_list env l in
          let pred = get_pred env p type_l in
          fun context ->
            layer_list (fun t_list -> context (Pred(pred,t_list)))


(*********************************************
              Checking Process
**********************************************)

(* [term_may_fail t] returns [true] when [t] may fail
   and [false] when [t] for sure does not fail. *)

let rec term_may_fail = function
    Var v -> v.unfailing
  | FunApp(f,l) ->
      (match f.f_cat with
       Eq _ | Tuple | Choice | Name _ -> false
      | _ -> true) || (List.exists term_may_fail l)

let rec used_in_restr b = function
    Nil -> false
  | NamedProcess(_, _, p) -> used_in_restr b p
  | Test(_,p1,p2,_) | Get(_,_,p1,p2,_) | Let(_,_,p1,p2,_)
  | LetFilter(_,_,p1,p2,_) | Par(p1,p2) ->
      (used_in_restr b p1) || (used_in_restr b p2)
  | Input(_,_,p,_) | Output(_,_,p,_) | Event(_,_,p,_) | Insert(_,p,_)
  | Phase(_,p,_) | Repl(p,_) | Barrier(_,_,p,_) | AnnBarrier(_,_,_,_,_,p,_) ->
      used_in_restr b p
  | Restr(f,(args,env),p,_) ->
      (match args with
        None -> false
      | Some l -> List.memq b l) || (used_in_restr b p)

let get_precise_option = function
  | [] -> false
  | [("precise",_),None] -> true
  | ((_,ext),_)::q -> Parsing_helper.input_error "Process input, get, let suchthat can only have \"precise\" as option." ext

let rec check_process cur_phase env (process, ext0) = match process with
  | PNil -> Nil
  | PPar(p1,p2) -> Par(check_process cur_phase env p1, check_process cur_phase env p2)
  | PRepl p -> Repl(check_process cur_phase env p, Terms.new_occurrence ())
  | PTest(cond,p1,p2) ->
      let layer_proc_cond, type_cond = check_term env cond in

      if type_cond != Param.bool_type then
        input_error "The condition on the test should be of type boolean" (snd cond);

      layer_proc_cond (fun t ->
        if !Param.expand_simplify_if_cst then
          begin
            if Terms.equal_terms t Terms.true_term then
              check_process cur_phase env p1
            else if Terms.equal_terms t Terms.false_term then
              check_process cur_phase env p2
            else
              Test(t,check_process cur_phase env p1, check_process cur_phase env p2, Terms.new_occurrence ())
          end
        else
          Test(t,check_process cur_phase env p1, check_process cur_phase env p2, Terms.new_occurrence ())
      )

  | PLetDef((s,ext), args) ->
      let proc_layer_list, type_list = check_term_list env args in
      begin
        try
          match StringMap.find s env with
            EProcess(param, p') ->
              let p' = NamedProcess(s, (List.map (fun b -> Var b) param), p') in
              let ptype = List.map (fun b -> b.btype) param in
              if not (Terms.eq_lists ptype type_list) then
                input_error ("process " ^ s ^ " expects " ^
                             (args_to_string ptype) ^
                             " but is here given " ^
                             (args_to_string type_list)) ext;

              assert (!Terms.current_bound_vars == []);

              proc_layer_list (fun l ->
                let p = ref p' in
                List.iter2 (fun t v ->
                  (* [keep_v] is true when a [let] must be introduced
                     because the variable [v] is used in queries *)
                  let keep_v = List.mem v.vname.orig_name (!ids_with_global_refs) in
                  if keep_v && v.unfailing then
                    input_error ("This process has a parameter " ^ v.vname.orig_name ^ " of type ... or fail; this argument cannot be used in query secret or in public_vars") ext;

                  (* We never introduce a [let] when the type of the argument is [... or fail]
                     In this case, [v.unfailing = true]. *)
                  if (not v.unfailing) &&
                  (* We must introduce a [let] when the term [t] may fail and the type
                     of the argument is not [... or fail]: the process must not execute
                     at all in this case. *)
                    (term_may_fail t || keep_v ||
                (* Simplify.copy_process supports linking a variable
                   that occurs in the argument of a Restr to a non-variable
                   term only by introducing a [let] itself. If possible,
                   we rather introduce it here.
                   Hence we introduce a Let to keep a variable in this case *)
                  (used_in_restr v (!p) && not (Terms.is_var t))) then
                    p := Let(PatVar v, t, (!p), Nil, Terms.new_occurrence())
                  else
                    Terms.link v (TLink t)) l param;

                let p'' = Simplify.copy_process (!p) in
                Terms.cleanup ();
		let min_phase = Reduction_helper.get_min_used_phase p'' in
		if min_phase <= cur_phase then
		  input_error ("process " ^ s ^ " called in phase " ^
			       (string_of_int cur_phase) ^ " and uses phase " ^
			       (string_of_int min_phase) ^ ": phases should be in increasing order") ext;
                p''
                  )
          | _ ->
              input_error (s ^ " should be a process") ext
        with Not_found ->
          input_error ("process " ^ s ^ " not defined") ext
      end

  | PRestr((s,ext),args,t,p) ->
      let ty = get_type t in
      if (StringMap.mem s env) then
        input_warning ("identifier " ^ s ^ " rebound") ext;
      if  ty == Param.nat_type
      then input_error ("The name " ^ s ^ " cannot be declared with the type 'nat'") ext;
      let r = Terms.create_name s (Param.tmp_type, ty) true in
      Restr(r, (get_restr_arg_opt env args, env), check_process cur_phase (StringMap.add s (EName r) env) p, Terms.new_occurrence())

  | PInput(ch_term,pat,p,opts) ->
      let precise = get_precise_option opts in
      let layer_channel, type_ch = check_term env ch_term in
      if type_ch != Param.channel_type then
        input_error ("this term has type " ^ type_ch.tname ^ " but should have type channel") (snd ch_term);
      let layer_pattern, env', type_pat = check_pattern env None pat env in
      layer_channel (fun ch ->
        layer_pattern (fun pattern ->
          Input(ch, pattern, check_process cur_phase env' p, Terms.new_occurrence ~precise:precise ())
        )
      )

      (*
      layer_channel (fun ch ->
        layer_pattern (fun pattern -> fun opt_test_pattern ->
          match opt_test_pattern with
            | None -> Input(ch, pattern, check_process cur_phase env' p, new occurrence())
            | Some(test) ->
                let x = new_var_def_term Param.boolean_type in
                Input(ch, pattern,
                  Let(PatVar x, FunApp(Terms.is_true_fun(), [test]),check_process cur_phase env' p, Nil, new occurrence ()),
                  new_occurrence ())
        )
      )
      *)

   | POutput(ch_term,term, p) ->
       let layer_channel, type_ch = check_term env ch_term in
       if type_ch != Param.channel_type then
        input_error ("this term has type " ^ type_ch.tname ^ " but should have type channel") (snd ch_term);
       let layer_term, ty_term = check_term env term in
       layer_term (fun t ->
         layer_channel (fun ch ->
           Output(ch, t, check_process cur_phase env p, Terms.new_occurrence ())
         )
       )

   | PLet(pat, t, p, p') ->
       let layer_term, type_t = check_term env t in

       let layer_pattern, env', _ = check_pattern env (Some type_t) pat env in

       layer_term (fun term ->
         layer_pattern (fun pattern ->
           Let(pattern, term, check_process cur_phase env' p, check_process cur_phase env p', Terms.new_occurrence ())
         )
       )

   | PLetFilter(identlist,(fact,ext),p,q,opts) ->
       let precise = get_precise_option opts in
       let (env', vlist) = List.fold_left (fun (env, vlist) ((s,e),t) ->
         if (StringMap.mem s env) then
           input_warning ("identifier " ^ s ^ " rebound") e;
         let ty = get_type t in
         let v = Terms.new_var s ty in
         (StringMap.add s (EVar v) env, v:: vlist)) (env,[]) identlist
       in

       let vlist = List.rev vlist in
       let layer_fact = check_fact env' (fact,ext) in
       (* Verify that the expanded part of layer_fact does not reference
          the variables of vlist *)
       check_no_ref ext vlist layer_fact;

       layer_fact (fun fact' ->
         LetFilter(vlist,fact', check_process cur_phase env' p, check_process cur_phase env q, Terms.new_occurrence ~precise:precise ())
       )

   | PEvent(id,l,env_args,p) ->
       let layer_list,type_list = check_term_list env l in
       let env_args' = (get_restr_arg_opt env env_args, env) in

       if !Param.key_compromise == 0 then
         let f = get_event_fun env id type_list in

         layer_list (fun l' -> Event(FunApp(f, l'), env_args', check_process cur_phase env p, Terms.new_occurrence()))
       else
         let f = get_event_fun env id (Param.sid_type :: type_list) in

         layer_list (fun l' ->
           Event(FunApp(f, (Terms.new_var_def_term Param.sid_type) :: l'), env_args',
             check_process cur_phase env p,
             Terms.new_occurrence()
           )
         )

   | PInsert(id,l,p) ->
       let layer_list, type_list = check_term_list env l in

       let f = get_table_fun env id type_list in

       layer_list (fun l' ->
         Insert(FunApp(f, l'), check_process cur_phase env p, Terms.new_occurrence()))

   | PGet((i,ext),pat_list,cond_opt,p,elsep,opts) ->
       let precise = get_precise_option opts in
       begin try
         begin match StringMap.find i env with
           | ETable f ->
               (* By checking the terms in the patterns in the initial environment env,
                  we make sure that layer_pat cannot reference variables bound in the
                  patterns *)
               if List.length (fst f.f_type) != List.length pat_list then
                 input_error ("Table " ^ i ^ " expects " ^
                              (string_of_int (List.length (fst f.f_type))) ^
                              " argument(s) but is here given " ^
                              (string_of_int (List.length pat_list)) ^ " argument(s)") ext;

               let (layer_pat, env', type_pat) = check_pattern_list ext env (List.map (fun t -> Some t) (fst f.f_type)) pat_list env in

               begin
                 match cond_opt with
                 | Some t ->
                     let (layer_cond,type_cond) = check_term env' t in
                     if type_cond != Param.bool_type then
                       input_error ("this term has type " ^ type_cond.tname ^ " but should have type bool") (snd t);

                     (* Verify that the expanded part of layer_cond does not reference
                        the variables of bound in the patterns *)
                     let vlist = ref [] in
                     let _ = layer_pat (fun pat_list ->
                       (* The goal of this function is to get all variables bound by the pattern
                          by storing them in vlist *)
                       vlist := List.fold_left Reduction_helper.get_pat_vars (!vlist) pat_list;
                       Nil)
                     in
                     check_no_ref (snd t) (!vlist) layer_cond;

                     layer_pat (fun pat_list ->
                       layer_cond (fun cond ->
                         Get(PatTuple(f,pat_list), cond, check_process cur_phase env' p, check_process cur_phase env elsep, Terms.new_occurrence ~precise:precise ())
                       )
                     )
                  | None ->
                      layer_pat (fun pat_list ->
                        Get(PatTuple(f, pat_list), Terms.true_term, check_process cur_phase env' p, check_process cur_phase env elsep, Terms.new_occurrence ~precise:precise ())
                      )
               end
           | _ -> input_error (i ^ " should be a table") ext
         end
       with Not_found ->
         input_error ("table " ^ i ^ " not defined") ext
       end

   | PPhase(n,p) ->
       if cur_phase >= n then
	 input_error "phases should be in increasing order" ext0;
       Phase(n, check_process n env p, Terms.new_occurrence())

   | PBarrier(n,tag, p) ->
       let tag' =
         match tag with
           None -> None
         | Some (s,_) -> Some s
       in
       Barrier(n, tag', check_process cur_phase env p, Terms.new_occurrence())

(*********************************************
               Other Checking
**********************************************)

(* Macro expansion *)

let macrotable = ref StringMap.empty

let rename_table = ref StringMap.empty

let expansion_number = ref 0

let rename_ident i =
  match i with
    "=" | "<>" | "not" | "&&" | "||" | "event" | "inj-event" | "==>" | "choice" | ">" | ">=" | "<=" | "<" -> i
  | _ -> if i.[0] = '!' then i else
  try
    StringMap.find i (!rename_table)
  with Not_found ->
    let r = "@" ^ (string_of_int (!expansion_number)) ^ "_" ^ i in
    rename_table := StringMap.add i r (!rename_table);
    r

let rename_ie (i,ext) = (rename_ident i, ext)

let rec rename_term (t,ext) =
  let t' = match t with
  | PFail -> PFail
  | PIdent i -> PIdent (rename_ie i)
  | PFunApp(f,l) -> PFunApp(rename_ie f, List.map rename_term l)
  | PTuple l -> PTuple(List.map rename_term l)
  | PProj _ -> input_error "projections not allowed here" ext
  in
  (t',ext)

let rec rename_format = function
    PFIdent i -> PFIdent (rename_ie i)
  | PFFunApp(f,l) -> PFFunApp(rename_ie f, List.map rename_format l)
  | PFTuple l -> PFTuple(List.map rename_format l)
  | PFName _ -> internal_error "Names not allowed in formats with -in pi"
  | PFAny i -> PFAny (rename_ie i)

let rename_format_fact (i,l) = (rename_ie i, List.map rename_format l)

let rec rename_gformat (t,ext) =
  let t' = match t with
    PFGIdent i -> PFGIdent (rename_ie i)
  | PFGFunApp(f,l) -> PFGFunApp(rename_ie f, List.map rename_gformat l)
  | PFGTuple l -> PFGTuple(List.map rename_gformat l)
  | PFGName(i,l) ->  PFGName(rename_ie i, List.map (fun (i,t) -> (rename_ie i, rename_gformat t)) l)
  | PFGAny i -> PFGAny (rename_ie i)
  | PFGLet(i,t,t') -> PFGLet(rename_ie i, rename_gformat t, rename_gformat t')
  in
  (t',ext)

let rec rename_nounif = function
    BFLet(i,f,t) -> BFLet(rename_ie i, rename_gformat f, rename_nounif t)
  | BFNoUnif((i,l,n'),n) -> BFNoUnif((rename_ie i, List.map rename_gformat l, n'), n)

let rec rename_gterm (t,ext) =
  let t' = match t with
    PGIdent i -> PGIdent (rename_ie i)
  | PGFunApp(f,l) -> PGFunApp(rename_ie f, List.map rename_gterm l)
  | PGPhase(i,l,n) -> PGPhase(rename_ie i, List.map rename_gterm l, n)
  | PGTuple l -> PGTuple(List.map rename_gterm l)
  | PGName(i,l) -> PGName(rename_ie i, List.map (fun (i,t) -> (rename_ie i, rename_gterm t)) l)
  | PGLet(i,t,t') -> PGLet(rename_ie i, rename_gterm t, rename_gterm t')
  in
  (t',ext)

let rename_query = function
    PPutBegin(b,l) -> PPutBegin(b, List.map rename_ie l)
  | PRealQuery (t,l) -> PRealQuery(rename_gterm t, List.map rename_ie l)
  | PQSecret(v,l,opt) -> PQSecret(rename_ie v, List.map rename_ie l, opt)

let rename_lemma (t,opt_ror,pubvars) =
  let opt_ror' = match opt_ror with
    | None -> None
    | Some (x,opt) -> Some (rename_ie x, opt)
  in
  (rename_gterm t, opt_ror', List.map rename_ie pubvars)

let rename_clause = function
    PClause(t,t') -> PClause(rename_term t, rename_term t')
  | PFact t -> PFact(rename_term t)
  | PEquiv(t,t',b) -> PEquiv(rename_term t, rename_term t', b)

let rec rename_pterm (t,ext) =
  let t' = match t with
    PPIdent i -> PPIdent (rename_ie i)
  | PPFunApp(f,l) -> PPFunApp(rename_ie f, List.map rename_pterm l)
  | PPTuple(l) -> PPTuple(List.map rename_pterm l)
  | PPRestr(i,args,ty,t) ->
      let args' =
        match args with
          None -> None
        | Some l-> Some (List.map rename_ie l)
      in
      PPRestr(rename_ie i, args', rename_ie ty, rename_pterm t)
  | PPTest(t1,t2,t3opt) -> PPTest(rename_pterm t1, rename_pterm t2, rename_pterm_opt t3opt)
  | PPLet(pat, t1, t2, t3opt) -> PPLet(rename_pat pat, rename_pterm t1, rename_pterm t2, rename_pterm_opt t3opt)
  | PPLetFilter(l, t1, t2, t3opt) -> PPLetFilter(List.map(fun (i,ty) -> (rename_ie i, rename_ie ty)) l, rename_pterm t1, rename_pterm t2, rename_pterm_opt t3opt)
  | PPEvent(i,l,lidopt,t) ->
      PPEvent(rename_ie i, List.map rename_pterm l,
              (match lidopt with
                None -> None
              | Some lid -> Some (List.map rename_ie lid)),
              rename_pterm t)
  | PPInsert(i,l,t) ->
      PPInsert(rename_ie i, List.map rename_pterm l, rename_pterm t)
  | PPGet(i,lpat,topt,t1,t2opt) ->
      PPGet(rename_ie i, List.map rename_pat lpat, rename_pterm_opt topt,
            rename_pterm t1, rename_pterm_opt t2opt)
  in
  (t',ext)

and rename_pterm_opt = function
    None -> None
  | Some t3 -> Some (rename_pterm t3)

and rename_pat = function
    PPatVar(i,tyopt) -> PPatVar(rename_ie i, match tyopt with
      None -> None
    | Some ty -> Some (rename_ie ty))
  | PPatTuple l -> PPatTuple(List.map rename_pat l)
  | PPatFunApp(f,l) -> PPatFunApp(rename_ie f, List.map rename_pat l)
  | PPatEqual t -> PPatEqual (rename_pterm t)

let rec rename_process (process, ext0) =
  let process' = match process with
    PNil -> PNil
  | PPar(p1,p2) -> PPar(rename_process p1, rename_process p2)
  | PRepl(p) -> PRepl(rename_process p)
  | PRestr(i,args,ty,p) ->
      let args' =
        match args with
          None -> None
        | Some l -> Some (List.map rename_ie l)
      in
      PRestr(rename_ie i, args', rename_ie ty, rename_process p)
  | PLetDef(i,l) -> PLetDef(rename_ie i, List.map rename_pterm l)
  | PTest(t,p1,p2) -> PTest(rename_pterm t, rename_process p1, rename_process p2)
  | PInput(t,pat,p,opts) -> PInput(rename_pterm t, rename_pat pat, rename_process p,opts)
  | POutput(t1,t2,p) -> POutput(rename_pterm t1, rename_pterm t2, rename_process p)
  | PLet(pat, t, p1, p2) -> PLet(rename_pat pat, rename_pterm t, rename_process p1, rename_process p2)
  | PLetFilter(l, t, p1, p2,opts) -> PLetFilter(List.map (fun (i,ty) -> (rename_ie i, rename_ie ty)) l, rename_pterm t, rename_process p1, rename_process p2,opts)
  | PEvent(i,l,env_args,p) ->
      let env_args' =
        match env_args with
          None -> None
        | Some l -> Some (List.map rename_ie l)
      in
      PEvent(rename_ie i ,List.map rename_pterm l, env_args', rename_process p)
  | PInsert(i,l,p) -> PInsert(rename_ie i ,List.map rename_pterm l, rename_process p)
  | PGet(i,patl,topt,p,elsep,opts) -> PGet(rename_ie i ,List.map rename_pat patl, rename_pterm_opt topt, rename_process p, rename_process elsep,opts)
  | PPhase(n,p) -> PPhase(n, rename_process p)
  | PBarrier(n,tag,p) -> PBarrier(n, tag, rename_process p)
  in
  (process', ext0)

let rename_env env = List.map (fun (i,ty) -> (rename_ie i, rename_ie ty)) env

let rename_may_fail_env env = List.map (fun (i,ty,can_fail) -> (rename_ie i, rename_ie ty, can_fail)) env

let rec rename_side_condition side_c = match side_c with
        |[] -> []
        |(env,t1,t2)::q -> (rename_env env, rename_term t1, rename_term t2)::(rename_side_condition q)

let rename_decl = function
    TTypeDecl i -> TTypeDecl (rename_ie i)
  | TFunDecl(i,l,ty,opt) -> TFunDecl(rename_ie i, List.map rename_ie l, rename_ie ty, opt)
  | TEventDecl(i,l) -> TEventDecl(rename_ie i, List.map rename_ie l)
  | TTableDecl(i,l) -> TTableDecl(rename_ie i, List.map rename_ie l)
  | TConstDecl(i,ty,opt) -> TConstDecl(rename_ie i, rename_ie ty, opt)
  | TReduc(l,opt) -> TReduc(List.map (fun (env,t1,t2) -> (rename_env env,rename_term t1, rename_term t2)) l, opt)
  | TReducFail(f, ty_arg,ty_res,l,opt) -> TReducFail(rename_ie f, List.map rename_ie ty_arg, rename_ie ty_res, List.map (fun (env,t1,t2) -> (rename_may_fail_env env,rename_term t1, rename_term t2)) l, opt)
  | TEquation(l, eqinfo) -> TEquation(List.map (fun (env, t1) -> (rename_env env, rename_term t1)) l, eqinfo)
  | TPredDecl(i,l,opt) -> TPredDecl(rename_ie i, List.map rename_ie l, opt)
  | TSet ((_,ext),_) ->
      input_error "set is not allowed inside macro definitions" ext
  | TPDef(i,env,p) -> TPDef(rename_ie i, rename_may_fail_env env, rename_process p)
  | TQuery(env, l,opt) -> TQuery(rename_env env, List.map rename_query l,opt)
  | TLemma(b,env,l,opt) -> TLemma(b,rename_env env, List.map rename_lemma l,opt)
  | TNoninterf(env, l) -> TNoninterf(rename_env env, List.map (fun (i,tlopt) ->
      (rename_ie i, match tlopt with
        None -> None
      | Some tl -> Some (List.map rename_term tl))) l)
  | TWeaksecret i -> TWeaksecret (rename_ie i)
  | TNoUnif(env, nounif,opt) -> TNoUnif(rename_env env, rename_nounif nounif,opt)
  | TNot(env, t) -> TNot(rename_env env, rename_gterm t)
  | TElimtrue(env, f) -> TElimtrue(rename_may_fail_env env, rename_term f)
  | TFree(i,ty, opt) -> TFree(rename_ie i, rename_ie ty, opt)
  | TClauses l -> TClauses (List.map (fun (env, cl) -> (rename_may_fail_env env, rename_clause cl)) l)
  | TDefine((s1,ext1),argl,def) ->
      input_error "macro definitions are not allowed inside macro definitions" ext1
  | TExpand(s1,argl) ->
      TExpand(s1, List.map rename_ie argl)
  | TLetFun(i,env,t) -> TLetFun(rename_ie i, rename_may_fail_env env, rename_pterm t)

let apply argl paraml already_def def =
  rename_table := StringMap.empty;
  incr expansion_number;
  List.iter (fun s ->
    rename_table := StringMap.add s s (!rename_table)) already_def;
  List.iter2 (fun (a,_) (p,_) ->
    rename_table := StringMap.add p a (!rename_table)) argl paraml;
  let def' = List.map rename_decl def in
  rename_table := StringMap.empty;
  def'


let declares = function
    TTypeDecl(i)
  | TFunDecl(i,_,_,_)
  | TConstDecl(i,_,_)
  | TReduc((_,(PFunApp(i,_),_),_)::_,_)
  | TReducFail(i,_,_,_,_)
  | TPredDecl (i,_,_)
  | TEventDecl (i,_)
  | TTableDecl (i,_)
  | TFree(i,_,_)
  | TPDef (i, _, _)
  | TLetFun(i,_,_) ->
      Some i
  | _ -> None

(* [add_already_def expanded_macro already_def] adds to [already_def]
   the identifiers defined in [expanded_macro].
   Since we use @ in identifiers in the expanded macro, we do not
   need to restrict ourselves to identifiers that appear in arguments. *)

let rec add_already_def expanded_macro already_def =
  List.fold_left (fun already_def a ->
    match declares a with
    | Some (s,_) -> s::already_def
    | None -> already_def
          ) already_def expanded_macro


let rec check_no_dup = function
    [] -> ()
  | (arg,ext)::l ->
      List.iter (fun (arg',ext') ->
        if arg = arg' then
          input_error ("Macro contains twice the argument " ^ arg) ext'
            ) l;
      check_no_dup l

type macro_elem =
    Macro of Pitptree.ident list * Pitptree.tdecl list * string list * macro_elem Stringmap.StringMap.t

let rec expand_macros macro_table already_def = function
    [] -> []
  | a::l ->
      match a with
      | TDefine((s1,ext1),argl,def) ->
          if StringMap.mem s1 macro_table then
            input_error ("Macro " ^ s1 ^ " already defined.") ext1
          else
            check_no_dup argl;
            let macro_table' = StringMap.add s1 (Macro(argl, def, already_def, macro_table)) macro_table in
            expand_macros macro_table' already_def l
      | TExpand((s1,ext1),argl) ->
          begin
            try
              let Macro(paraml, def, old_already_def, old_macro_table) = StringMap.find s1 macro_table in
              if List.length argl != List.length paraml then
                input_error ("Macro " ^ s1 ^ " expects " ^ (string_of_int (List.length paraml)) ^
                             " arguments, but is here given " ^ (string_of_int (List.length argl)) ^ " arguments.") ext1;
              let applied_macro = apply argl paraml old_already_def def in
              let expanded_macro = expand_macros old_macro_table old_already_def applied_macro in
              let already_def_after_macro = add_already_def expanded_macro already_def in
              expanded_macro @ (expand_macros macro_table already_def_after_macro l)
            with Not_found ->
              input_error ("Macro " ^ s1 ^ " not defined.") ext1
          end
      | _ ->
          let already_def' =
            match declares a with
              Some(s,_) -> s::already_def
            | None -> already_def
          in
          a::(expand_macros macro_table already_def' l)

(* Fix query options: there is a shift/reduce conflict in the parsing
of query options:
query ... secret x ... [options_secret] [options_query]
where both [options_secret] and [options_query] are optional.
As a consequence, when only one set of options is present,
the parser assumes that it is [options_secret].
This function fixes the parsing in case these options are actually
[options_query].
*)

let is_query_option ((id, ext), args) =
  (args = None) && List.mem id ["maxSubset"; "proveAll"; "noneSat"; "noneVerif"; "discardSat"; "discardVerif"; "fullSat"; "fullVerif"; "instantiateSat"; "instantiateVerif"; "induction"; "noInduction"; "keep" ]

let fix_query_options (env, q, opt) =
  if opt = [] then
    let rec aux = function
      | [PQSecret(sec_var, pub_vars, options)] as q ->
	  if List.for_all is_query_option options then
	    [PQSecret(sec_var, pub_vars, [])], options
	  else
	    q, []
      | q1::qrest ->
	  let qrest', opt' = aux qrest in
	  q1::qrest', opt'
      | [] -> [], []
    in
    let q', opt' = aux q in
    env, q', opt'
  else
    env, q, opt

(* Handle all declarations *)

let rec check_one = function
    TTypeDecl(i) -> check_type_decl i
  | TFunDecl(f,argt,rest,i) -> check_fun_decl f argt rest (no_param_option_list i)
  | TConstDecl(f,rest,i) -> check_fun_decl f [] rest (no_param_option_list i)
  | TEquation(l,eqinfo) -> check_equations l (no_param_option_list eqinfo)
  | TReduc (r,i) -> check_red r (no_param_option_list i)
  | TReducFail (f,ty_arg,ty_res,r,i) -> check_red_may_fail f ty_arg ty_res r (no_param_option_list i)
  | TPredDecl (p, argt, info) -> check_pred p argt (no_param_option_list info)
  | TEventDecl(i, args) -> check_event i args
  | TTableDecl(i, args) -> check_table i args
  | TPDef ((s,ext), args, p) ->
      let env = ref (!global_env) in
      let arglist = List.map (fun ((s',ext'),ty,may_fail) ->
        let t = get_type ty in
        begin
          try
            match StringMap.find s' (!env) with
              EVar _ -> input_error ("variable " ^ s' ^ " already defined") ext'
            | _ -> ()
          with Not_found ->
            ()
        end;
        let v = Terms.new_var ~may_fail:may_fail s' t in
        env := StringMap.add s' (EVar v) (!env);
        v
               ) args
      in
      let p' = check_process 0 (!env) p in
      global_env := StringMap.add s (EProcess(arglist, p')) (!global_env)
  | TQuery (env,q,opt) ->
      let (env,q,opt) = fix_query_options (env,q,opt) in
      query_list := (QueryToTranslate(transl_query (env, q,(no_param_option_list opt)))) :: (!query_list);
      corresp_query_list := (env,q) :: (!corresp_query_list)
  | TLemma(b,env,q,opt) ->
      lemma_list := (LemmaToTranslate(transl_lemma (not b) (env,q,(no_param_option_list opt)))):: !lemma_list;
      let q' = List.map (fun (t,_,pubvars) -> PRealQuery(t,pubvars)) q in
      corresp_query_list := (env,q') :: (!corresp_query_list)
  | TNoninterf (env, lnoninterf) ->
      let non_interf_query = List.map (get_non_interf env) lnoninterf in
      query_list := (NonInterfQuery non_interf_query) :: (!query_list);
  | TWeaksecret i ->
      let w = get_non_interf_name (!global_env) i in
      query_list := (WeakSecret w) :: (!query_list)
  | TNoUnif (env, nounif,opt) -> nounif_list := (env,nounif,opt) :: !nounif_list
  | TElimtrue(env, fact) ->
      let env = create_may_fail_env env in
      elimtrue := (check_simple_fact env fact) :: (!elimtrue)
  | TNot (env, no) ->
      not_list := (env, no) :: (!not_list)
  | TFree (name,ty,i) ->
      add_free_name name ty (no_param_option_list i)
  | TClauses c ->
      List.iter check_clause c
  | TLetFun ((s,ext), args, p) ->
      if StringMap.mem s (!global_env) then
        input_error ("identifier " ^ s ^ " already defined (as a free name, a function, a predicate, or a type)") ext;

      let initial_env = !global_env in
      let env = ref (!global_env) in

      let type_arg_list = List.map (fun ((s',ext'),ty,may_fail) ->
        let t = get_type ty in
        begin
          try
            match StringMap.find s' (!env) with
              EVar _ -> input_error ("variable " ^ s' ^ " already defined") ext'
              | _ -> ()
          with Not_found ->
            ()
        end;

        let v = Terms.new_var s' t in
        env := StringMap.add s' (EVar v) (!env);
        t
      ) args in

      let _, type_result = check_term (!env) p in

      let func_proc_layer list_term_arg proc_context =
        let env = ref initial_env in
        let ok_args = ref [] in
        let rec link_the_variables args_list term_args_list = match args_list,term_args_list with
          | [],[] -> ()
          | [],_ | _,[] -> internal_error "Should have the same size"
          | ((s',ext'),ty,may_fail)::q,term::q_term ->
              let t = get_type ty in
              let v = Terms.new_var ~may_fail:may_fail s' t in
              v.link <- TLink term;
              env := StringMap.add s' (EVar v) (!env);
              if (not may_fail) && (term_may_fail term) then
                ok_args := (FunApp(Terms.success_fun t, [term])) :: (!ok_args);
              link_the_variables q q_term in

        link_the_variables args list_term_arg;

        let (proc_layer, _) = check_term (!env) p in

        proc_layer (fun tthen ->
          if (!ok_args) = [] then proc_context tthen else
          (* The arguments that are not marked "or fail" must not fail.
             If they fail, the result of the "letfun" is fail as well *)
          let gtest_symb = Terms.gtest_fun type_result in
          let fail = Terms.get_fail_term type_result in
          let cond = Terms.and_list (!ok_args) in
          proc_context (FunApp(gtest_symb, [cond; tthen; fail]))
            )
      in

      global_env := StringMap.add s (ELetFun(func_proc_layer, type_arg_list, type_result)) (!global_env)

  | TDefine _ | TExpand _ ->
      internal_error "macros should have been expanded"

  | TSet _ -> internal_error "set declaration should have been handled before"

(* Maximum phase for queries, not, nounif *)

let max_phase_event max_phase_process (f,e) =
  match f with
  | PGPhase((s, ext), tl, n) ->
      begin
        match s with
          "mess" | "attacker" | "table" ->
            if n > max_phase_process then
              input_warning "phase greater than the maximum phase used in the process.\nIs that really what you want?" e;
            n
        | _ -> input_error "phases can be used only with attacker, mess, or table" ext
      end
  | _ -> 0

let rec max_phase_query max_phase_process = function
  | PGFunApp((("==>" | "||" | "&&"), _), [he1;he2]), _ ->
      max (max_phase_query max_phase_process he1)
        (max_phase_query max_phase_process he2)
  | PGLet(id,t,t'), _ ->
      max_phase_query max_phase_process t'
  | ev ->
      max_phase_event max_phase_process ev

let max_phase_corresp_secret_putbegin_query max_phase_process = function
  | PRealQuery (q, _) ->
      max_phase_query max_phase_process q
  | PQSecret _ | PPutBegin _ -> 0

let max_phase_format max_phase_process ((s, ext), _, n) =
  match s with
    "attacker" | "mess" | "table" ->
      if n > max_phase_process then
        input_warning "nounif declaration for a phase greater than used" ext;
      n
  | s ->
      if n <> -1 then
        input_error "declared predicates do not depend on phases, so no phase should be specified in such facts in queries" ext;
      0

let rec max_phase_nounif max_phase_process = function
    BFLet(_,_,nounif) -> max_phase_nounif max_phase_process nounif
  | BFNoUnif(fact,_) -> max_phase_format max_phase_process fact

(* Reset the local state of this module *)

let reset() =
  equations := [];
  destructors_check_deterministic := [];
  ids_with_global_refs := [];
  corresp_query_list := [];
  query_list := [];
  not_list := [];
  input_clauses := [];
  elimtrue := [];
  equiv_list := [];
  nounif_list := [];
  lemma_list := [];
  global_env := StringMap.empty;
  macrotable := StringMap.empty;
  rename_table := StringMap.empty;
  expansion_number := 0


(* Final parsing function *)

let parse_file s =
  (* Reinitialize the state *)
  Param.reset_param();
  Display.init_used_ids();
  reset();
  let (decl, proc, second_proc) = parse_with_lib s in
  (* ignoreTypes must be set before doing the rest of the work
     Setting all parameters beforehand does not hurt.
     Furthermore, we record identifiers that we want to keep unchanged *)
  List.iter (function
    | TSet((p,ext),v) ->
        begin
          match (p,v) with
            "attacker", S ("passive",_) -> Param.active_attacker := false
          | "attacker", S ("active",_) -> Param.active_attacker := true
          | "preciseActions", _ -> Param.boolean_param Param.precise_actions p ext v
	  | "privateCommOnPublicFreeNames", _ -> Param.boolean_param Param.allow_private_comm_on_public_free_names p ext v
          | "keyCompromise", S ("strict",_) -> Param.key_compromise := 2
          | "keyCompromise", S ("approx",_) -> Param.key_compromise := 1
          | "keyCompromise", S ("none",_) -> Param.key_compromise := 0
          | "movenew", _ -> Param.boolean_param Param.move_new p ext v
          | "inductionLemmas", _ -> Param.boolean_param Param.induction_lemmas p ext v
          | "inductionQueries", _ -> Param.boolean_param Param.induction_queries p ext v
          | "verboseLemmas", _ -> Param.boolean_param Param.verbose_lemmas p ext v
          | "nounifIgnoreOnce", S ("none",_) -> Param.nounif_ignore_once:= Param.NIO_None
          | "nounifIgnoreOnce", S ("all",_) -> Param.nounif_ignore_once:= Param.NIO_All
          | "nounifIgnoreOnce", S ("auto",_) -> Param.nounif_ignore_once:= Param.NIO_Auto
          | "removeEventsForLemma", _ -> Param.boolean_param Param.event_lemma_simplification p ext v
          | "saturationApplication", S ("none",_) -> Param.sat_application:= LANone
          | "saturationApplication", S ("full",_) -> Param.sat_application:= LAFull
          | "saturationApplication", S ("discard",_) -> Param.sat_application:= LAOnlyWhenRemove
          | "saturationApplication", S ("instantiate",_) -> Param.sat_application:= LAOnlyWhenInstantiate
          | "verificationApplication", S ("none",_) -> Param.verif_application:= LANone
          | "verificationApplication", S ("full",_) -> Param.verif_application:= LAFull
          | "verificationApplication", S ("discard",_) -> Param.verif_application:= LAOnlyWhenRemove
          | "verificationApplication", S ("instantiate",_) -> Param.verif_application:= LAOnlyWhenInstantiate
          | "verboseClauses", S ("explained",_) -> Param.verbose_explain_clauses := Param.ExplainedClauses
          | "verboseClauses", S ("short",_) -> Param.verbose_explain_clauses := Param.Clauses
          | "verboseClauses", S ("none",_) -> Param.verbose_explain_clauses := Param.NoClauses
          | "explainDerivation", _ -> Param.boolean_param Param.explain_derivation p ext v
          | "removeUselessClausesBeforeDisplay", _ -> Param.boolean_param Param.remove_subsumed_clauses_before_display p ext v
          | "predicatesImplementable", S("check",_) -> Param.check_pred_calls := true
          | "predicatesImplementable", S("nocheck",_) -> Param.check_pred_calls := false
          | "eqInNames", _ -> Param.boolean_param Param.eq_in_names p ext v
          | "reconstructTrace", _ -> Param.boolean_param Param.reconstruct_trace p ext v
          | "traceBacktracking", _ -> Param.boolean_param Param.trace_backtracking p ext v
          | "unifyDerivation", _ -> Param.boolean_param Param.unify_derivation p ext v
          | "traceDisplay", S ("none",_) -> Param.trace_display := Param.NoDisplay
          | "traceDisplay", S ("short",_) -> Param.trace_display := Param.ShortDisplay
          | "traceDisplay", S ("long",_) -> Param.trace_display := Param.LongDisplay
          | "ignoreTypes", S (("all" | "true" | "yes"), _) -> Param.set_ignore_types true
          | "ignoreTypes", S (("none" | "attacker" | "false" | "no"), _) -> Param.set_ignore_types false
          | "simplifyProcess", S (("true" | "yes"), _) -> Param.simplify_process := 1
          | "simplifyProcess", S (("false" | "no"), _) -> Param.simplify_process := 0
          | "simplifyProcess", S ("interactive", _) -> Param.simplify_process := 2
          | "rejectChoiceTrueFalse", _ -> Param.boolean_param Param.reject_choice_true_false p ext v
                | "rejectNoSimplif", _ -> Param.boolean_param Param.reject_no_simplif p ext v
          | "expandIfTermsToTerms", _ -> Param.boolean_param Param.expand_if_terms_to_terms p ext v
          | "expandSimplifyIfCst", _ -> Param.boolean_param Param.expand_simplify_if_cst p ext v
          | "interactiveSwapping", _ -> Param.boolean_param Param.interactive_swapping p ext v
          | "swapping", S sext -> Param.set_swapping := Some sext
          | _,_ -> Param.common_parameters p ext v
        end
    | one_decl ->
        match declares one_decl with
        | Some (s,ext) -> Display.record_id s ext
        | None -> ()
              ) decl;
  Param.default_set_ignore_types();
  initialize_env();

  (* Expand macros [def] / [expand] *)
  let already_def = StringMap.fold (fun s _ already_def -> s :: already_def) (!global_env) [] in
  let decl = expand_macros StringMap.empty already_def decl in

  (* Set [ids_with_global_refs] to make sure that
     we keep them when we expand processes and [letfun] *)
  List.iter (get_ids_with_global_refs_decl ids_with_global_refs) decl;

  (* *)

  List.iter (function
      TSet _ -> ()
    | x -> check_one x) decl;

  let p = Terms.auto_cleanup (fun () ->
    check_process 0 (!global_env) proc)
  in

  let second_p = match second_proc with
    | None -> None
    | Some(proc2) ->
        let p2 = Terms.auto_cleanup (fun () ->
          check_process 0 (!global_env) proc2)
        in
        if (!Param.key_compromise != 0) then
          Parsing_helper.user_error "Key compromise is incompatible with equivalence";
        Some p2
  in

  (* Compute process_query *)
  let process_query = match second_p with
    | Some p2 ->
        if !Param.has_choice then
          Parsing_helper.user_error "Equivalence is incompatible with choice";
        if (!query_list) != [] then
          Parsing_helper.user_error "Queries are incompatible with equivalence";
        Equivalence({ proc = p; bi_pro = false; display_num = None; construction = Initial_process1 },
		    { proc = p2; bi_pro = false; display_num = None; construction = Initial_process2 })
    | None ->
        if !Param.has_choice then
          begin
            if (!query_list) != [] then
              Parsing_helper.user_error "Queries are incompatible with choice";
            SingleProcessSingleQuery({ proc = p; bi_pro = true; display_num = None; construction = Initial_process }, ChoiceQuery)
          end
        else
          SingleProcess({ proc = p; bi_pro = false; display_num = None; construction = Initial_process }, List.rev (!query_list))
  in

  (* Compute maximum phase *)
  let max_phase_process =
    if !Param.key_compromise = 2 then
      1
    else
      max (Reduction_helper.get_max_used_phase p)
        (match second_p with
          None -> 0
        | Some p2 -> Reduction_helper.get_max_used_phase p2)
  in
  let max_phase =
    List.fold_left (fun accu (env, ql) ->
      List.fold_left (fun accu q ->
        max accu (max_phase_corresp_secret_putbegin_query max_phase_process q)
          ) accu ql
        ) max_phase_process (!corresp_query_list)
  in
  let max_phase =
    List.fold_left (fun accu (env, no_decl) ->
      max accu (max_phase_event max_phase_process no_decl)
        ) max_phase (!not_list)
  in
  let max_phase =
    List.fold_left (fun accu (env, nounif,opt) ->
      max accu (max_phase_nounif max_phase_process nounif)
        ) max_phase (!nounif_list)
  in

  let pi_state =
    { pi_process_query = process_query;
      pi_global_env = Set (!global_env);
      pi_glob_table = Unset;
      pi_glob_table_var_name = Unset;
      pi_types = StringMap.fold (fun _ v accu ->
               match v with
               | EType t -> t::accu
               | _ -> accu) (!global_env) [];
      pi_funs = StringMap.fold (fun _ v accu ->
               match v with
               | EFun f -> f::accu
               | _ -> accu) (!global_env) [];
      pi_freenames = StringMap.fold (fun _ v accu ->
               match v with
               | EName n -> n::accu
               | _ -> accu) (!global_env) [];
      pi_events = StringMap.fold (fun _ v accu ->
               match v with
               | EEvent e -> e::accu
               | _ -> accu) (!global_env) [];
      pi_equations = !equations;
      pi_max_used_phase = max_phase;
      pi_input_clauses = !input_clauses;
      pi_elimtrue = !elimtrue;
      pi_equivalence_clauses = !equiv_list;
      pi_destructors_check_deterministic = !destructors_check_deterministic;
      pi_disequations = !disequations;
      pi_event_status_table = Unset;
      pi_get_not = get_not (!not_list);
      pi_get_nounif = get_nounif (!nounif_list);
      pi_terms_to_add_in_name_params = Unset;
      pi_min_choice_phase = Unset;
      pi_need_vars_in_names = Function (get_need_vars_in_names (!corresp_query_list) (!not_list) (!nounif_list));
      pi_name_args_exact = true;
      pi_lemma = List.rev !lemma_list;
      pi_original_axioms = [];
      pi_precise_actions = []
    }
  in
  reset();
  pi_state
