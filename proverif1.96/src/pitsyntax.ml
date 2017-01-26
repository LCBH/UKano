(*************************************************************
 *                                                           *
 *  Cryptographic protocol verifier                          *
 *                                                           *
 *  Bruno Blanchet, Vincent Cheval, and Marc Sylvestre       *
 *                                                           *
 *  Copyright (C) INRIA, CNRS 2000-2016                      *
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
    user_error ("File error: " ^ s ^ "\n")

let parse_lib filename =
  let filename = filename ^ ".pvl" in
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
    user_error ("File error: " ^ s ^ "\n")

let parse_with_lib filename =
  let l1 = 
    if (!Param.lib_name) <> "" then
      parse_lib (!Param.lib_name) 
    else
      []
  in
  let (l,p,second_p) = parse filename in
  (l1 @ l, p,second_p)


(********* Types ***********
This section is composed of two main functions :
- [get_type : Ptree.ident -> Types.typet]
	[get_type (s,_)] returns the type associated to [s] in [Param.all_types] if [s] isn't the pre-defined type ["sid"] and ["any_type"]
- [check_type : Ptree.ident -> unit] 
	[check_type_decl (s,_)] first checks if [s] is not ["any_type"], ["sid"], or already defined.
If not, then the type is added into [Param.all_types] and [global_env] 
****************************)

let global_env = ref (StringMap.empty : envElement StringMap.t)

let get_type_polym polym sid_allowed (s, ext) =
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
    List.find (fun t -> t.tname = s) (!Param.all_types)
  with Not_found -> 
    input_error ("type " ^ s ^ " not declared") ext

let get_type ty = get_type_polym false false ty

(** [check_type_decl (s,ext)] first checks if [s] is not ["any_type"], ["sid"], or already defined.
If not, then the type is added into [Param.all_types] and [global_env] *)
let check_type_decl (s, ext) =
  if s = "any_type" then
    input_error "type any_type reserved for polymorphism" ext;
  if s = "sid" then
    input_error "type sid reserved for session identifiers" ext;
  if StringMap.mem s (!global_env) then
    input_error ("identifier " ^ s ^ " already defined (as a free name, a function, a predicate, or a type)") ext;
  let r = { tname = s } in 
  Param.all_types := r :: (!Param.all_types);
  global_env := StringMap.add s (EType r) (!global_env)

(* Table of bound names of the process *)

let glob_table = Simplify.glob_table

let check_single ext s =
  let vals = Hashtbl.find_all glob_table s in
  match vals with
    _::_::_ -> input_error (s ^ " cannot be used in queries, not, or nounif. Its definition is ambiguous. (For example, several restrictions might define " ^ s ^ ".)") ext
  | _ -> ()
  
  
(*********************************************
          Functions For Environment
**********************************************)  

let fun_decls = Param.fun_decls

let initialize_env_and_fun_decl () =
  (* Initial functions and constant *)
  Hashtbl.add fun_decls "true" Terms.true_cst;
  Terms.record_id "true" dummy_ext;
  global_env := StringMap.add "true" (EFun Terms.true_cst) (!global_env);
  
  Hashtbl.add fun_decls "false" Terms.false_cst;
  Terms.record_id "false" dummy_ext;
  global_env := StringMap.add "false" (EFun Terms.false_cst) (!global_env);
  
  Hashtbl.add fun_decls "not" (Terms.not_fun());
  Terms.record_id "not" dummy_ext;
  global_env := StringMap.add "not" (EFun (Terms.not_fun())) (!global_env);
  
  Hashtbl.add fun_decls "&&" (Terms.and_fun());
  Terms.record_id "&&" dummy_ext;
  global_env := StringMap.add "&&" (EFun (Terms.and_fun())) (!global_env);
  
  Hashtbl.add fun_decls "||" (Terms.or_fun());
  Terms.record_id "||" dummy_ext;
  global_env := StringMap.add "||" (EFun (Terms.or_fun())) (!global_env);
  
  List.iter (fun t -> 
    Terms.record_id t.tname dummy_ext;
    global_env := StringMap.add t.tname (EType t) (!global_env)
	 ) (!Param.all_types)

let special_functions = ["choice"; "||"; "&&"; "="; "<>"]

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
  | _ ->
  try
    match StringMap.find s env with
      (EFun r) as x -> 
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

let get_var env (s,ext) =
  try 
    match StringMap.find s env with
      EVar v -> v
    | _ -> input_error (s ^ " should be a variable") ext
  with Not_found -> 
    input_error ("variable " ^ s ^ " not declared") ext

(* environment *)    
    
let add_env sid_allowed env l =
  let env_ref = ref env in
  List.iter (fun ((s,ext),ty) ->
      let t = get_type_polym false sid_allowed ty in
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
    
    let var = 
      if can_fail
      then Terms.new_unfailing_var s t
      else Terms.new_var s t 
    in
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
  let is_tuple = ref false in
  let is_private = ref false in
  let opt = ref 0 in
  List.iter (function 
	("data",_) -> is_tuple := true
      |	("private",_) -> is_private := true
      |	("typeConverter",_) -> 
	  if List.length tyarg != 1 then
	    input_error "only unary functions can be declared \"typeConverter\"" ext;
	  is_tuple := true;
	  opt := (!opt) lor Param.fun_TYPECONVERTER
      |	(_,ext) ->
	input_error "for functions, the only allowed options are data, private, and typeConverter" ext) options;
  if (!is_tuple) && (!is_private) then
    input_error "a function cannot be declared both data or typeConverter and private" ext;
  let cat = if !is_tuple (* || ((arity == 0) && (not is_private)) *) then Tuple else Eq [] in
  let r = { f_name = name;
	    f_type = tyarg, tyres;
	    f_cat = cat;
	    f_initial_cat = cat;
	    f_private = !is_private;
	    f_options = !opt }
  in
  Hashtbl.add fun_decls name r;
  global_env := StringMap.add name (EFun r) (!global_env)
  
(*********************************************
         Check destructor declaration
**********************************************)

(* Destructor to check *)

let destructors_check_deterministic = ref []

let f_eq_tuple f ext =
  match f.f_cat with
    Eq _ | Tuple -> ()
  | Name _ -> input_error (f.f_name ^ " is a name; it should not appear in equations or rewrite rules") ext
  | Red _ -> input_error (f.f_name ^ " is a function defined by rewrite rules; it should not appear in equations or rewrite rules") ext
  | _ -> input_error (f.f_name ^ " should not appear in equations or rewrite rules") ext

let f_any f ext = 
  match f.f_cat with
    Choice -> input_error "function choice should not appear in clauses or elimtrue" ext
  | Name _ -> input_error "names should not appear in clauses or elimtrue" ext
  | _ -> ()

let f_eq_tuple_name f ext =
  match f.f_cat with
    Eq _ | Tuple | Name _ -> ()
  | Red _ -> input_error (f.f_name ^ " is a function defined by rewrite rules. It should not appear in non-interference queries") ext
  | _ -> input_error (f.f_name ^ " should not appear in non-interference queries") ext


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
							
		f_allowed f ext;
		FunApp(f, [])
	    | EName r -> 
		f_allowed r ext;
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
      f_allowed f' ext;
      if (f'.f_options land Param.fun_TYPECONVERTER != 0) && (Param.get_ignore_types()) then
	match tl' with
	  [t] -> (t, result_type)
	| _ -> internal_error "type converter functions should always be unary"
      else
      	(FunApp(f', tl'), result_type)

  | (PTuple tlist) ->
      let (tl', tyl) = List.split (List.map (check_eq_term f_allowed false fail_allowed_all env) tlist) in
      (FunApp (Terms.get_tuple_fun tyl, tl'), Param.bitstring_type)
      
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

let check_equation l eqinfo =
  let l' = List.map (fun (env, t1, t2) ->
    let var_env = create_env env in
    let (t1', ty1) = check_eq_term f_eq_tuple false false var_env t1 in
    let (t2', ty2) = check_eq_term f_eq_tuple false false var_env t2 in
    if ty1 != ty2 then
      begin
	let ext = merge_ext (snd t1) (snd t2) in
	input_error "the two members of an equation should have the same type" ext
      end;
    (t1', t2')) l 
  in
  let eqinfo' = match eqinfo with
    [] -> EqNoInfo
  | ["convergent",ext] -> EqConvergent
  | ["linear",ext] -> EqLinear
  | (_,ext)::_ -> Parsing_helper.input_error "for equations, the only allowed options are either convergent or linear" ext
  in
  TermsEq.register_equation eqinfo' l'

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
         then ([[],rhs,[]], [])
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
  let may_fail_vars = List.map Terms.new_unfailing_var_def ty_arg
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
      f_name = f;
      f_type = ty_arg, ty_res;
      f_private = !is_private;
      f_options = 0;
      f_cat = cat;
      f_initial_cat = cat
    } in
	
  (* Adding the destructor in environment *)
    
  (*Display.Text.display_red fsymb complete_red_list;*)
	        
  Hashtbl.add fun_decls f fsymb;
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
                  
                  (lhs, rhs, []), (tylhs, tyrhs)
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
	            let var_list = List.map (fun ty -> Terms.new_var_def ty) tylhs
	            and fail = Terms.get_fail_term tyrhs
	            and tuple_symb = Terms.get_tuple_fun tylhs in
	              
	            let tuple = FunApp(tuple_symb, var_list) in
	            
	            assert (!Terms.current_bound_vars == []);
	                
	            let side_cond = 
	              List.map (fun (arg_list,_,_) -> 
	                tuple,FunApp(tuple_symb, List.map (Terms.generalize_vars_not_in []) arg_list)
	              ) red_list in
	              
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
		  f_name = f;
		  f_type = tylhs, tyrhs;
		  f_private = !is_private;
		  f_options = 0;
		  f_cat = cat;
		  f_initial_cat = cat
		} in
		
		(* Adding the destructor for checking *)
  
		destructors_check_deterministic := fsymb::(!destructors_check_deterministic);
		
	        (*Display.Text.display_red fsymb red_list';*)
	        
	        Hashtbl.add fun_decls f fsymb;
	        global_env := StringMap.add f (EFun fsymb) (!global_env)
      end
  | (_,(_, ext1), _) :: l -> 
      input_error ("In \"reduc\", all rewrite rules should begin with function application") ext1
  | [] -> internal_error "reduction with empty list"
  

  
(* Check clauses *)
	
let pred_env = Param.pred_env

let rec interpret_info ty r = function
    ("memberOptim", ext) -> 
      if List.length ty != 2 then
	input_error "memberOptim makes sense only for predicates of arity 2" ext;
      r.p_prop <- r.p_prop lor Param.pred_ELEM
  | ("block",_) -> r.p_prop <- r.p_prop lor Param.pred_BLOCKING
	  (* add other qualifiers here *)
  | (s,ext) -> input_error ("unknown predicate qualifier " ^ s) ext

let check_pred (c,ext) tl info =
  if c = "attacker" || c = "mess" || c = "event" || c = "inj-event" then
    input_error ("predicate name " ^ c ^ " is reserved. You cannot declare it") ext;
  if StringMap.mem c (!global_env) then
    input_error ("identifier " ^ c ^ " already defined (as a free name, a function, a predicate, or a type)") ext;
  let tyl = List.map (get_type_polym true false) tl in
  let r = { p_name = c; p_type = tyl; p_prop = 0; p_info = [] } in
  List.iter (interpret_info tyl r) info;
  if List.exists (fun t -> t == Param.any_type) tyl then
    r.p_info <- [PolymPred(c, r.p_prop, tyl)];
  Hashtbl.add pred_env c r;
  global_env := StringMap.add c (EPred r) (!global_env) 


let add_rule hyp concl constra tag =
  Param.red_rules := (hyp, concl, constra, tag) :: (!Param.red_rules)


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
	  (hyp_accu, [Neq(t1', t2')] :: constra_accu)
      | "=", [t1;t2] ->
	  if is_simple then
	    input_error (f ^ " not allowed here") ext;
	  let (t1', ty1) = check_eq_term f_any false true env t1 in
	  let (t2', ty2) = check_eq_term f_any false true env t2 in
	  if ty1 != ty2 then
	    input_error "the two arguments of an equality test should have the same type" ext;
	  ((equal_fact t1' t2')::hyp_accu, constra_accu)
      |	"&&", [h1;h2] ->
	  check_hyp is_simple (check_hyp is_simple (hyp_accu,constra_accu) env h1) env h2
      |	("<>" | "=" | "&&"), _ -> internal_error ("Bad arity for special function " ^ f)
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
  | PFunApp((f,fext) as p,l) ->
      (* FunApp: only predicates allowed *)
      let (p',l') = check_cterm env (p,l) in
      Pred(p',l')

let check_clause = function
    (env, PFact(c)) ->
      begin
	let env = create_may_fail_env env in
	let concl = check_simple_fact env c in
	add_rule [] concl [] LblClause
      end
  | (env, PClause(i,c)) ->
      begin
      try 
	let env = create_may_fail_env env in
	let (hyp, constra) = check_hyp false ([],[]) env i in
	let concl = check_simple_fact env c in
	add_rule hyp concl
	  (TermsEq.simplify_constra_list (concl :: hyp) constra) LblClause
      with TermsEq.FalseConstraint -> ()
      end
  | (env, PEquiv(i,c,select)) ->
      let env = create_may_fail_env env in
      let (hyp, constra) = check_hyp true ([],[]) env i in
      if constra != [] then 
	Parsing_helper.internal_error "Inequality constraints not allowed in equivalences, should be eliminated by check_hyp true\n";
      let concl = check_simple_fact env c in
      add_rule hyp concl [] LblEquiv;
      List.iter (fun h -> add_rule [concl] h [] LblEquiv) hyp;
      Rules.add_equiv (hyp, concl, -1); (* TO DO should give a real rule number, but that's not easy... *)
      if not select then Terms.add_unsel concl

      
(* List of the free names of the process *)

let freenames = Param.freenames

let add_free_name (s,ext) t options =
  let is_private = ref false in
  List.iter (function 
    | ("private",_) -> is_private := true
    | (_,ext) ->
	input_error "for free names, the only allowed option is private" ext) options;
  let ty = get_type t in
  if StringMap.mem s (!global_env) then
    input_error ("identifier " ^ s ^ " already declared (as a free name, a function, a predicate, or a type)") ext;
  let r = Terms.create_name s ([],ty) (!is_private) in 
  global_env := StringMap.add s (EName r) (!global_env);
  freenames := r :: !freenames


(* Check non-interference terms *)

let get_non_interf_name env (s,ext) =
   try
     match StringMap.find s env  with
       EName r -> 
	 check_single ext s;
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

(* Table of processes defined by "let" *)

let pdeftbl = (Hashtbl.create 7 : (string, binder list * process) Hashtbl.t)

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
      let ty = get_type tyid in
      if (StringMap.mem s env) then
	input_warning ("identifier " ^ s ^ " rebound") ext;
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
		let b' = Terms.new_var_noren b.sname b.btype in
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
	        let b = Terms.new_var Param.def_var_name Param.bool_type in
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
        let (env', vlist) = 
          List.fold_left (fun (env, vlist) ((s,e),t) ->
	    if (StringMap.mem s env) then
	      input_warning ("identifier " ^ s ^ " rebound") e;
	  
	    let ty = get_type t in
	    let v = Terms.new_var_noren s ty in
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
	
      let v = Terms.new_var_noren s ty in
	
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
		input_error ("Function " ^ f.f_name ^ " expects " ^ 
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
	
	let v = Terms.new_var_noren s ty in
	
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
		  input_error ("Function " ^ f.f_name ^ 
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
		  input_error ("Function " ^ f.f_name ^ " expects " ^ 
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
  
  let x = Terms.new_var Param.def_var_name type_pat in
  
  (layer_proc (PatVar x) (Var x), env, type_pat)
 
(*********************************************
              Checking Fact
**********************************************)	
  
and check_fact env (fact, ext) = match fact with
  | PPIdent p -> 
      (fun context -> context (Pred(get_pred env p [],[])))
      
  | PPTuple _ -> input_error "tuples not allowed here" ext
  | PPRestr _ | PPTest _ | PPLet _ | PPLetFilter _ -> 
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
              Checking Event
**********************************************)	

let event_fun_table = Hashtbl.create 7

let check_event (name, ext) argtypes =
  let tyarg = List.map get_type argtypes in
  let tyarg = if !Param.key_compromise = 0 then tyarg else Param.sid_type :: tyarg in
  if StringMap.mem name (!global_env) then
    input_error ("identifier " ^ name ^ " already defined (as a free name, a function, a predicate, or a type)") ext;
  let r = { f_name = name;
	    f_type = tyarg, Param.event_type;
	    f_cat = Eq[];
	    f_initial_cat = Eq[];
	    f_private = true;
	    f_options = 0 }
  in
  Hashtbl.add event_fun_table name r;
  global_env := StringMap.add name (EEvent r) (!global_env)


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
      
  
(*********************************************
              Checking Table
**********************************************)	

let check_table (name, ext) argtypes =
  let tyarg = List.map get_type argtypes in
  if StringMap.mem name (!global_env) then
    input_error ("identifier " ^ name ^ " already defined (as a free name, a function, a predicate, or a type)") ext;
  let r = { f_name = name;
	    f_type = tyarg, Param.table_type;
	    f_cat = Tuple;
	    f_initial_cat = Tuple;
	    f_private = true;
	    f_options = 0 }
  in
  global_env := StringMap.add name (ETable r) (!global_env)

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
      |        _ -> true) || (List.exists term_may_fail l)

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

let rec check_process env process = match process with
  | PNil -> Nil
  | PPar(p1,p2) -> Par(check_process env p1, check_process env p2)
  | PRepl p -> Repl(check_process env p, Terms.new_occurrence ())
  | PTest(cond,p1,p2) ->
      let layer_proc_cond, type_cond = check_term env cond in
       
      if type_cond != Param.bool_type then
        input_error "The condition on the test should be of type boolean" (snd cond);
       
      layer_proc_cond (fun t ->
	if !Param.expand_simplify_if_cst then
	  begin
	    if Terms.equal_terms t Terms.true_term then
	      check_process env p1
	    else if Terms.equal_terms t Terms.false_term then
	      check_process env p2
	    else
              Test(t,check_process env p1, check_process env p2, Terms.new_occurrence ())
	  end
	else
	  Test(t,check_process env p1, check_process env p2, Terms.new_occurrence ())
      )
        
  | PLetDef((s,ext), args) -> 
      let proc_layer_list, type_list = check_term_list env args in
      begin
	try
          let (param, p') = Hashtbl.find pdeftbl s in
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
	      if (not v.unfailing) && (term_may_fail t || 
		(* Simplify.copy_process does not support linking a variable
		   that occurs in the argument of a Restr to a non-variable
		   term (because arguments of Restr are always variables,
		   and it would need to replace that variable with a 
		   non-variable term).
		   Hence we introduce a Let to keep a variable in this case *)
	         (used_in_restr v (!p) && not (Terms.is_var t))) then 
		p := Let(PatVar v, t, (!p), Nil, Terms.new_occurrence())
	      else
		Terms.link v (TLink t)) l param;
            
            let p'' = Simplify.copy_process false (!p) in
            Terms.cleanup ();
            p''
          )
        with Not_found ->
          input_error ("process " ^ s ^ " not defined") ext
      end
  
  | PRestr((s,ext),args,t,p) ->
      let ty = get_type t in
      if (StringMap.mem s env) then
	input_warning ("identifier " ^ s ^ " rebound") ext;
      let r = Terms.create_name s (Param.tmp_type, ty) true in
      Restr(r, (get_restr_arg_opt env args, env), check_process (StringMap.add s (EName r) env) p, Terms.new_occurrence())
      
  | PInput(ch_term,pat,p) ->
      let layer_channel, type_ch = check_term env ch_term in
      if type_ch != Param.channel_type then
        input_error ("this term has type " ^ type_ch.tname ^ " but should have type channel") (snd ch_term);
      let layer_pattern, env', type_pat = check_pattern env None pat env in
      layer_channel (fun ch ->
        layer_pattern (fun pattern -> 
          Input(ch, pattern, check_process env' p, Terms.new_occurrence())
        )
      )
      
      (*
      layer_channel (fun ch -> 
        layer_pattern (fun pattern -> fun opt_test_pattern ->
          match opt_test_pattern with
            | None -> Input(ch, pattern, check_process env' p, new occurrence())
            | Some(test) -> 
                let x = new_var_def Param.boolean_type in
                Input(ch, pattern,
                  Let(PatVar x, FunApp(Terms.is_true_fun(), [test]),check_process env' p, Nil, new occurence ()),
                  new_occurence ())
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
           Output(ch, t, check_process env p, Terms.new_occurrence ())
         )
       )
       
   | PLet(pat, t, p, p') -> 
       let layer_term, type_t = check_term env t in
       
       let layer_pattern, env', _ = check_pattern env (Some type_t) pat env in
       
       layer_term (fun term ->
         layer_pattern (fun pattern ->
           Let(pattern, term, check_process env' p, check_process env p', Terms.new_occurrence ())
         )
       )
       
   | PLetFilter(identlist,(fact,ext),p,q) ->
       let (env', vlist) = List.fold_left (fun (env, vlist) ((s,e),t) ->
         if (StringMap.mem s env) then
	   input_warning ("identifier " ^ s ^ " rebound") e;
	 let ty = get_type t in
	 let v = Terms.new_var_noren s ty in
	 (StringMap.add s (EVar v) env, v:: vlist)) (env,[]) identlist 
       in
	 
       let vlist = List.rev vlist in
       let layer_fact = check_fact env' (fact,ext) in
       (* Verify that the expanded part of layer_fact does not reference 
	  the variables of vlist *)
       check_no_ref ext vlist layer_fact;
       
       layer_fact (fun fact' ->
         LetFilter(vlist,fact', check_process env' p, check_process env q, Terms.new_occurrence ())
       )
   
   | PEvent((i,ext),l,env_args,p) -> 
       let layer_list,type_list = check_term_list env l in
       let env_args' = (get_restr_arg_opt env env_args, env) in

       if !Param.key_compromise == 0 then
         let f = get_event_fun env (i,ext) type_list in
         
         layer_list (fun l' -> Event(FunApp(f, l'), env_args', check_process env p, Terms.new_occurrence()))
       else
	 let f = get_event_fun env (i,ext) (Param.sid_type :: type_list) in
	
	 layer_list (fun l' -> 
	   Event(FunApp(f, (Terms.new_var_def Param.sid_type) :: l'), env_args', 
	     check_process env p, 
	     Terms.new_occurrence()
	   )
	 )
   
   | PInsert((i,ext),l,p) -> 
       let layer_list, type_list = check_term_list env l in
       
       let f = get_table_fun env (i,ext) type_list in
      
       layer_list (fun l' ->
         Insert(FunApp(f, l'), check_process env p, Terms.new_occurrence()))
   
   | PGet((i,ext),pat_list,cond_opt,p,elsep) ->
       begin try
         begin match StringMap.find i env with
           | ETable f ->
	       (* By checking the terms in the patterns in the initial environment env,
		  we make sure that layer_pat cannot reference variables bound in the
		  patterns *)
	       if List.length (fst f.f_type) != List.length pat_list then
		 input_error ("Table " ^ f.f_name ^ " expects " ^ 
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
                         Get(PatTuple(f,pat_list), cond, check_process env' p, check_process env elsep, Terms.new_occurrence ())
                       )
                     )
                  | None -> 
                      layer_pat (fun pat_list ->
                        Get(PatTuple(f, pat_list), Terms.true_term, check_process env' p, check_process env elsep, Terms.new_occurrence ())
                      )
               end 
           | _ -> input_error (i ^ " should be a table") ext
         end
       with Not_found ->
	 input_error ("table " ^ i ^ " not defined") ext
       end
   
   | PPhase(n,p) -> Phase(n, check_process env p, Terms.new_occurrence())

   | PBarrier(n,tag, p) -> 
       let tag' = 
	 match tag with
	   None -> None
	 | Some (s,_) -> Some s
       in
       Barrier(n, tag', check_process env p, Terms.new_occurrence())
   
(*********************************************
               Other Checking
**********************************************)	 
   
let query_list = ref ([] : (envdecl * tquery list) list)
let need_vars_in_names = Reduction_helper.need_vars_in_names
let noninterf_list = ref ([] : (funsymb * term list option) list list)
let not_list = ref ([] : (envdecl * gterm_e) list)
let nounif_list = ref ([] : (envdecl * nounif_t) list)
let weaksecret_list = ref ([] : funsymb list)

(* Compute need_vars_in_names: the list of pairs (restriction, variable name)
   such that the variable "variable name" must occur as argument in the
   pattern that models names created by "restriction", because the
   structure "restriction[... variable name = ... ]" is used in the input 
   file. *)

let rec nvn_t (term, ext0) =
  match term with
    PGIdent _ -> ()
  | PGFunApp(_,l) -> List.iter nvn_t l
  | PGPhase(_,l, _) -> List.iter nvn_t l
  | PGTuple l -> List.iter nvn_t l
  | PGName ((s,ext),bl) ->
      List.iter (fun ((s',ext'),t) -> 
	(* The replication indices do not need to be added in 
	   need_vars_in_names, because they are always included as
	   arguments of names, whether or not they occur in 
	   the input file. 
	   They must not be added to need_vars_in_names, because 
	   they are not correctly computed by trace reconstruction,
	   so adding them would cause bugs in trace reconstruction. *)
	if (s' <> "") && (s'.[0] != '!') then
	  begin
	    try 
	      let r = Hashtbl.find glob_table s in
	      (* print_string ("Need " ^ s' ^ " in " ^ r.f_name ^ "\n");  *)
	      need_vars_in_names := (r.f_name, s',ext') :: (!need_vars_in_names)
	    with Not_found ->
	      ()
	  end;
	nvn_t t
						) bl
  | PGLet(_,t,t') -> nvn_t t; nvn_t t'

let nvn_q  = function
    PRealQuery q -> nvn_t q
  | PPutBegin(i, l) -> ()

let rec nvn_f (f,ext0) = 
  match f with
    PFGIdent (s,ext) -> ()
  | PFGFunApp((s,ext),l) -> List.iter nvn_f l
  | PFGTuple l -> List.iter nvn_f l
  | PFGName ((s,ext),bl) ->
      List.iter (fun ((s',ext'),t) -> 
	(* The replication indices do not need to be added in 
	   need_vars_in_names, because they are always included as
	   arguments of names, whether or not they occur in 
	   the input file. 
	   They must not be added to need_vars_in_names, because 
	   they are not correctly computed by trace reconstruction,
	   so adding them would cause bugs in trace reconstruction. *)
	if (s' <> "") && (s'.[0] != '!') then
	  begin
	    try 
	      let r = Hashtbl.find glob_table s in
	      (* print_string ("Need " ^ s' ^ " in " ^ r.f_name ^ "\n");  *)
	      need_vars_in_names := (r.f_name, s',ext') :: (!need_vars_in_names)
	    with Not_found ->
	      ()
	  end;
	nvn_f t
						) bl
  | PFGAny (s,ext) -> ()
  | PFGLet(_,t,t') -> nvn_f t; nvn_f t'

let rec nvn_nounif = function
    BFLet(_,t,nounif) ->  nvn_f t; nvn_nounif nounif
  | BFNoUnif((id,fl,n),_) -> List.iter nvn_f fl

let set_need_vars_in_names() =
  List.iter (fun (_, q) -> List.iter nvn_q q) (!query_list);
  List.iter (fun (_, no) -> nvn_t no) (!not_list);
  List.iter (fun (_, nounif) -> nvn_nounif nounif) (!nounif_list)

let rec has_nvn_t (term, ext0) =
  match term with
    PGIdent _ -> false
  | PGFunApp(_,l) | PGPhase(_,l, _) | PGTuple l -> List.exists has_nvn_t l
  | PGName ((s,ext),bl) -> bl != []
  | PGLet(_,t,t') -> (has_nvn_t t) || (has_nvn_t t')

let rec has_nvn_f (f,ext0) = 
  match f with
    PFGIdent _ | PFGAny _ -> false
  | PFGFunApp(_,l) | PFGTuple l -> List.exists has_nvn_f l
  | PFGName ((s,ext),bl) -> bl != []
  | PFGLet(_,t,t') -> (has_nvn_f t) || (has_nvn_f t')

let rec has_nvn_nounif = function
    BFLet(_,t,nounif) ->  (has_nvn_f t) || (has_nvn_nounif nounif)
  | BFNoUnif((id,fl,n),_) -> List.exists has_nvn_f fl

let reset_need_vars_in_names() =
  (* Since simplification does not support specifying new a[x = ...],
     I remove the secrecy assumptions and nounif declaration that need that. *)
  need_vars_in_names := [];
  let secrecy_assumption_removed = ref false in
  not_list := List.filter (fun (_, no) -> 
    if has_nvn_t no then
      begin
	secrecy_assumption_removed := true;
	false
      end
    else
      true) (!not_list);
  if !secrecy_assumption_removed then
    print_string "Warning! Removed one or several several not declarations that used a construct of the form new a[x = ...].\n";
  let nounif_removed = ref false in
  nounif_list := List.filter (fun (_, nounif) -> 
    if has_nvn_nounif nounif then
      begin
	nounif_removed := true;
	false
      end
    else
      true) (!nounif_list);
  if !nounif_removed then
    print_string "Warning! Removed one or several several nounif declarations that used a construct of the form new a[x = ...].\n"

(* Macro expansion *)

let macrotable = ref StringMap.empty

let rename_table = ref StringMap.empty

let expansion_number = ref 0

let rename_ident i = 
  match i with
    "=" | "<>" | "not" | "&&" | "||" | "event" | "inj-event" | "==>" | "choice" -> i
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
  | PRealQuery t -> PRealQuery(rename_gterm t)

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

let rec rename_process = function
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
  | PInput(t,pat,p) -> PInput(rename_pterm t, rename_pat pat, rename_process p)
  | POutput(t1,t2,p) -> POutput(rename_pterm t1, rename_pterm t2, rename_process p)
  | PLet(pat, t, p1, p2) -> PLet(rename_pat pat, rename_pterm t, rename_process p1, rename_process p2)
  | PLetFilter(l, t, p1, p2) -> PLetFilter(List.map (fun (i,ty) -> (rename_ie i, rename_ie ty)) l, rename_pterm t, rename_process p1, rename_process p2)
  | PEvent(i,l,env_args,p) -> 
      let env_args' = 
	match env_args with
	  None -> None
	| Some l -> Some (List.map rename_ie l)
      in
      PEvent(rename_ie i ,List.map rename_pterm l, env_args', rename_process p)
  | PInsert(i,l,p) -> PInsert(rename_ie i ,List.map rename_pterm l, rename_process p)
  | PGet(i,patl,topt,p,elsep) -> PGet(rename_ie i ,List.map rename_pat patl, rename_pterm_opt topt, rename_process p, rename_process elsep)
  | PPhase(n,p) -> PPhase(n, rename_process p)
  | PBarrier(n,tag,p) -> PBarrier(n, tag, rename_process p)
	
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
  | TEquation(l, eqinfo) -> TEquation(List.map (fun (env, t1, t2) -> (rename_env env, rename_term t1, rename_term t2)) l, eqinfo)
  | TPredDecl(i,l,opt) -> TPredDecl(rename_ie i, List.map rename_ie l, opt)
  | TSet ((_,ext),_) ->
      input_error "set is not allowed inside macro definitions" ext
  | TPDef(i,env,p) -> TPDef(rename_ie i, rename_may_fail_env env, rename_process p)
  | TQuery(env, l) -> TQuery(rename_env env, List.map rename_query l)
  | TNoninterf(env, l) -> TNoninterf(rename_env env, List.map (fun (i,tlopt) ->
      (rename_ie i, match tlopt with
	None -> None
      |	Some tl -> Some (List.map rename_term tl))) l)
  | TWeaksecret i -> TWeaksecret (rename_ie i)
  | TNoUnif(env, nounif) -> TNoUnif(rename_env env, rename_nounif nounif)
  | TNot(env, t) -> TNot(rename_env env, rename_gterm t)
  | TElimtrue(env, f) -> TElimtrue(rename_may_fail_env env, rename_term f)
  | TFree(i,ty, opt) -> TFree(rename_ie i, rename_ie ty, opt)
  | TClauses l -> TClauses (List.map (fun (env, cl) -> (rename_may_fail_env env, rename_clause cl)) l)
  | TDefine((s1,ext1),argl,def) ->
      input_error "macro definitions are not allowed inside macro definitions" ext1
  | TExpand((s1,ext1),argl) ->
      internal_error "macro-expansion inside a macro should have been expanded at macro definition point" 
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


(* Handle all declarations *)

let rec check_one = function
    TTypeDecl(i) -> check_type_decl i
  | TFunDecl(f,argt,rest,i) -> check_fun_decl f argt rest i
  | TConstDecl(f,rest,i) -> check_fun_decl f [] rest i
  | TEquation(l,eqinfo) -> check_equation l eqinfo
  | TReduc (r,i) -> check_red r i
  | TReducFail (f,ty_arg,ty_res,r,i) -> check_red_may_fail f ty_arg ty_res r i
  | TPredDecl (p, argt, info) -> check_pred p argt info
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
	let v = Terms.new_var_noren_with_fail s' t may_fail in
	env := StringMap.add s' (EVar v) (!env);
	v
	       ) args
      in
      let p' = check_process (!env) p in
      Hashtbl.add pdeftbl s (arglist, p')
  | TQuery (env,q) -> 
      query_list := (env,q) :: (!query_list)
  | TNoninterf (env, lnoninterf) -> 
      noninterf_list := (List.map (get_non_interf env) lnoninterf) :: (!noninterf_list); 
  | TWeaksecret i ->
      weaksecret_list := (get_non_interf_name (!global_env) i) ::(!weaksecret_list)
  | TNoUnif (env, nounif) ->
      nounif_list := (env, nounif) :: (!nounif_list)
  | TElimtrue(env, fact) ->
      let env = create_may_fail_env env in
      Param.elim_true := (check_simple_fact env fact) :: (!Param.elim_true)
  | TNot (env, no) -> 
      not_list := (env, no) :: (!not_list)
  | TFree (name,ty,i) -> 
      add_free_name name ty i
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
	  
        let v = Terms.new_var_noren s' t in
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
              let v = Terms.new_var_noren_with_fail s' t may_fail in
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

  | TDefine((s1,ext1),argl,def) ->
      if StringMap.mem s1 (!macrotable) then
	input_error ("Macro " ^ s1 ^ " already defined.") ext1
      else
	(* Expand macro calls inside macro definitions
	   Because this is done at macro definition point, this requires that
	   the macros used inside the definition be defined before, which
	   is a safe requirement. (It prevents recursive macros, in particular.) *)
	let rec expand_inside_macro = function 
	    TDefine((s,ext),_,_)::l -> 
	      input_error "macro definitions are not allowed inside macro definitions" ext
	  | TExpand((s2,ext2), argl2)::l ->
	      begin
		try 
		  let (paraml2, def2, already_def2) = StringMap.find s2 (!macrotable) in
		  if List.length argl2 != List.length paraml2 then
		    input_error ("Macro " ^ s2 ^ " expects " ^ (string_of_int (List.length paraml2)) ^
				 " arguments, but is here given " ^ (string_of_int (List.length argl2)) ^ " arguments.") ext2;
		  (apply argl2 paraml2 already_def2 def2) @ (expand_inside_macro l)
		with Not_found ->
		  input_error ("Macro " ^ s2 ^ " not defined.") ext2
	      end
	  | a::l -> a::(expand_inside_macro l)
	  | [] -> []
	in
	let def = expand_inside_macro def in
	let already_def = ref [] in
	StringMap.iter (fun s _ -> already_def := s :: (!already_def)) (!global_env);
	macrotable := StringMap.add s1 (argl, def, !already_def) (!macrotable)
  | TExpand((s1,ext1),argl) ->
      begin
	try 
	  let (paraml, def, already_def ) = StringMap.find s1 (!macrotable) in
	  if List.length argl != List.length paraml then
	    input_error ("Macro " ^ s1 ^ " expects " ^ (string_of_int (List.length paraml)) ^
			 " arguments, but is here given " ^ (string_of_int (List.length argl)) ^ " arguments.") ext1;
	  List.iter check_one (apply argl paraml already_def def)
	with Not_found ->
	  input_error ("Macro " ^ s1 ^ " not defined.") ext1
      end 
  | TSet _ -> internal_error "set declaration should have been handled before"

(* Get the maximum phase number *)

let rec set_max_used_phase = function
    Nil -> ()
  | Par(p1,p2) -> set_max_used_phase p1; set_max_used_phase p2
  | Repl (p,_) ->  set_max_used_phase p
  | Restr(n,_,p,_) -> set_max_used_phase p
  | Test(_,p1,p2,_) -> set_max_used_phase p1; set_max_used_phase p2
  | Input(_,_, p,_) -> set_max_used_phase p
  | Output(_,_,p,_) -> set_max_used_phase p
  | Let(_,_,p1, p2,_) -> set_max_used_phase p1; set_max_used_phase p2
  | LetFilter(_,_,p,q,_) -> set_max_used_phase p; set_max_used_phase q
  | Event(_,_,p,_) -> set_max_used_phase p
  | Insert(_,p,_) -> set_max_used_phase p
  | NamedProcess(_, _, p) -> set_max_used_phase p
  | Get(_,_,p,q,_) -> set_max_used_phase p; set_max_used_phase q
  | Phase(n,p,_) ->
      if n > !Param.max_used_phase then
	Param.max_used_phase := n;
      set_max_used_phase p
  | Barrier(_,_,p,_) ->
      set_max_used_phase p
  | AnnBarrier _ ->
      Parsing_helper.internal_error "Annotated barriers should not occur in the initial process"

      
let parse_file s = 
  let (decl, proc, second_proc) = parse_with_lib s in
  (* ignoreTypes must be set before doing the rest of the work
     Setting all parameters beforehand does not hurt. 
     Furthermore, we record identifiers that we want to keep unchanged *)
  List.iter (function
      TTypeDecl(s,ext) -> Terms.record_id s ext
    | TFunDecl((s,ext),_,_,_) -> Terms.record_id s ext
    | TConstDecl((s,ext),_,_) -> Terms.record_id s ext
    | TReduc((_,(PFunApp((s,ext),_),_),_)::_,_) -> Terms.record_id s ext
    | TReducFail((s,ext),_,_,_,_) -> Terms.record_id s ext
    | TPredDecl((s,ext),_,_) -> Terms.record_id s ext
    | TFree((s,ext),_,_) -> Terms.record_id s ext
    | TEventDecl((s,ext),_) -> Terms.record_id s ext
    | TTableDecl((s,ext),_) -> Terms.record_id s ext
    | TLetFun((s,ext),_,_) -> Terms.record_id s ext
    | TSet((p,ext),v) -> 
	begin
	  match (p,v) with
	    "attacker", S ("passive",_) -> Param.active_attacker := false
	  | "attacker", S ("active",_) -> Param.active_attacker := true
	  | "keyCompromise", S ("strict",_) -> Param.key_compromise := 2
	  | "keyCompromise", S ("approx",_) -> Param.key_compromise := 1
	  | "keyCompromise", S ("none",_) -> Param.key_compromise := 0
	  | "movenew", _ -> Param.boolean_param Param.move_new p ext v
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
    | _ -> ()) decl;
  Param.default_set_ignore_types();
  initialize_env_and_fun_decl();
  
  (* *)

  List.iter (function
      TSet _ -> ()
    | x -> check_one x) decl;
  
  let p = Terms.auto_cleanup (fun () ->
    check_process (!global_env) proc)
  in  
    
  match second_proc with
    | None -> 
        if !Param.key_compromise = 2 then
          Param.max_used_phase := 1
        else
          set_max_used_phase p;
        
        p,None
    | Some(proc2) ->
        let p2 = Terms.auto_cleanup (fun () ->
          check_process (!global_env) proc2)
	in
	
	if (!Param.key_compromise != 0) then
	  Parsing_helper.user_error "Key compromise is incompatible with equivalence\n";
	  
	set_max_used_phase p;
	set_max_used_phase p2;
	
	p,Some p2

let display () =
   print_string "Functions ";
   Hashtbl.iter (fun _ fsymb -> 
     print_string (fsymb.f_name ^ "(" ^ (Terms.tl_to_string ", " (fst fsymb.f_type)) 
		   ^ "):" ^ (snd fsymb.f_type).tname ^ ". ")
       ) fun_decls;
   print_string "\n"

(* queries *)

let non_compromised_session = FunApp(Param.session1, [])


(* Note: when check_query, get_queries are applied before the
   translation of the process into Horn clauses has been done, 
   the arity of names may not be correctly initialized. In this case,
   update_type_names should be called after the translation of the
   process to update it.  *)

let get_ident_any env (s, ext) =
   try
     match StringMap.find s env with
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
	   if fst f.f_type == [] then 
	     FunApp(f,[]) 
	   else
	     input_error ("function " ^ s ^ " has expects " ^ 
			  (string_of_int (List.length (fst f.f_type))) ^
			  " arguments but is used without arguments") ext
       | _ -> input_error ("identifier " ^ s ^ " should be a variable, a free name, or a function") ext
   with Not_found ->
     input_error ("identifier " ^ s ^ " not defined") ext

let rec check_query_term names_must_be_encoded env (term, ext0) =
  match term with
    PGIdent i -> 
      let t = get_ident_any env i in
      (t, Terms.get_term_type t)
  | PGPhase _ -> input_error ("phase unexpected in query terms") ext0
  | PGFunApp((s,ext),l) -> 
      (* FunApp: only constructors allowed *)
      if List.mem s ["="; "<>"; "==>"; "&&"; "||"; "event"; "inj-event"; "table"] then
	input_error (s ^ " unexpected in query terms") ext;
      let (l', tl') = List.split (List.map (check_query_term names_must_be_encoded env) l) in
      let (f, result_type) = get_fun env (s,ext) tl' in
      begin
        match f.f_cat with
          Eq _ | Tuple -> ()
	| Choice -> 
	    (* Choice is useful only for "not" declarations when using biprocesses *)
	    if not ((!Param.has_choice) || (!Param.equivalence)) then
	      input_error "choice cannot be used in queries or not declarations, except for not declarations when proving equivalences" ext
        | _ ->  input_error ("function " ^ s ^ " is defined by \"reduc\". Such a function should not be used in a query") ext
      end;
      if (f.f_options land Param.fun_TYPECONVERTER != 0) && (Param.get_ignore_types()) then
	match l' with
	  [t] -> (t, result_type)
	| _ -> internal_error "type converter functions should always be unary"
      else
	(FunApp(f, l'), result_type)
  | PGTuple l -> 
      let (l', tl') = List.split (List.map (check_query_term names_must_be_encoded env) l) in
      (FunApp(Terms.get_tuple_fun tl', l'), Param.bitstring_type)
  | PGName ((s,ext),bl) -> 
      begin
	try
	  let r = Hashtbl.find glob_table s in
	  check_single ext s;
	  if fst r.f_type == Param.tmp_type then
	    begin
	      if names_must_be_encoded then
		Parsing_helper.input_error ("You are referring to name " ^ s ^ " in this query or secrecy assumption, but this name will never be generated") ext
	      else
		begin
		  let v = Terms.new_var Param.def_var_name (snd r.f_type) in
		  v.link <- PGLink (fun () -> fst (check_query_term true env (term,ext0)));
		  (Var v, snd r.f_type)
		end
	    end
	  else
	    begin
	      match r.f_cat with 
		Name { prev_inputs_meaning = sl } ->
		  List.iter (fun ((s',ext'),_) -> 
		    if not (List.exists (fun m -> Reduction_helper.meaning_encode m = s') sl) then
		      input_error ("variable " ^ s' ^ " not defined at restriction " ^ s) ext') bl;
		  let p = List.map2 (fun m ty ->
		    match m with
		      MCompSid -> non_compromised_session 
                    | _ -> binding_find names_must_be_encoded env (Reduction_helper.meaning_encode m) ty bl) sl (fst r.f_type)
		  in
		  (FunApp(r, p), snd r.f_type)
	      | _ -> internal_error "name expected here"
	    end
	with Not_found ->
	  input_error (s ^ " should be a name") ext
      end
  | PGLet(id,t,t') -> check_query_term names_must_be_encoded (add_binding names_must_be_encoded env (id,t)) t'

and binding_find names_must_be_encoded env s ty = function
    [] -> Terms.new_var_def ty
  | ((s',ext),t)::l ->
      if s' = s then
	begin
	  let (t', ty') = check_query_term names_must_be_encoded env t in
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
	binding_find names_must_be_encoded env s ty l

and add_binding names_must_be_encoded env ((i,ext),t) =
  begin
    try
      match StringMap.find i env with
	EVar _ -> input_error ("variable " ^ i ^ " already defined") ext
      | _ -> ()
    with Not_found -> ()
  end;
  let (t', ty') = check_query_term names_must_be_encoded env t in
  let v = Terms.new_var i ty' in
  v.link <- TLink t';
  StringMap.add i (EVar v) env

let check_mess names_must_be_encoded env e tl n =
  match tl with
    [t1;t2] ->
      if n > !Param.max_used_phase then
	begin
	  input_warning "phase greater than the maximum phase used in the process.\nIs that really what you want?" e;
	  Param.max_used_phase := n;
	end;
      let (t1', ty1) = check_query_term names_must_be_encoded env t1 in
      let (t2', ty2) = check_query_term names_must_be_encoded env t2 in
      if ty1 != Param.channel_type then
	input_error ("First argument of mess is of type " ^ ty1.tname ^ " and should be of type channel") e;
      let mess_n = Param.get_pred (Mess((if n = -1 then (!Param.max_used_phase) else n),
					ty2))
      in
      QFact(mess_n, [t1';t2'])
  | _ -> 
      input_error "arity of predicate mess should be 2" e

let check_attacker names_must_be_encoded env e tl n =
  match tl with
    [t1] ->
      if n > !Param.max_used_phase then
	begin
	  input_warning "phase greater than the maximum phase used in the process.\nIs that really what you want?" e;
	  Param.max_used_phase := n;
	end;
      let (t1', ty1) = check_query_term names_must_be_encoded env t1 in
      let att_n = Param.get_pred (Attacker((if n = -1 then (!Param.max_used_phase) else n),
	                                   ty1)) 
      in
      QFact(att_n, [t1'])
  | _ -> 
      input_error "arity of predicate attacker should be 1" e

let rec check_table_term names_must_be_encoded env (term, ext0) =
  match term with
  | PGFunApp((s,ext),l) -> 
      (* FunApp: only tables allowed *)
      if List.mem s ["="; "<>"; "==>"; "&&"; "||"; "event"; "inj-event"; "table"] then
	input_error (s ^ " unexpected in query terms") ext;
      let (l', tl') = List.split (List.map (check_query_term names_must_be_encoded env) l) in
      let f = get_table_fun env (s,ext) tl' in
      FunApp(f, l')
  | _ -> input_error "Table term expected" ext0

let check_table names_must_be_encoded env e tl n =
  match tl with
    [t1] ->
      if n > !Param.max_used_phase then
	begin
	  input_warning "phase greater than the maximum phase used in the process.\nIs that really what you want?" e;
	  Param.max_used_phase := n;
	end;
      let t1' = check_table_term names_must_be_encoded env t1 in
      let table_n = Param.get_pred (Table(if n = -1 then (!Param.max_used_phase) else n)) in
      QFact(table_n, [t1'])
  | _ -> 
      input_error "arity of predicate table should be 1" e

let rec check_event names_must_be_encoded env (f,e) =
  match f with
    (* FunApp: predicates, =, <>, event, inj-event, attacker, mess, table allowed *)
    PGFunApp(("<>", _), [t1; t2]) ->
      let (t1', ty1) = check_query_term names_must_be_encoded env t1 in
      let (t2', ty2) = check_query_term names_must_be_encoded env t2 in
      if ty1 != ty2 then
	input_error "the two arguments of an inequality test should have the same type" e;      
      QNeq(t1', t2')
  | PGFunApp(("=", _), [t1; t2]) ->
      let (t1', ty1) = check_query_term names_must_be_encoded env t1 in
      let (t2', ty2) = check_query_term names_must_be_encoded env t2 in
      if ty1 != ty2 then
	input_error "the two arguments of an equality test should have the same type" e;      
      QEq(t1', t2')
  | PGFunApp(("event",e'),tl0) ->
      let (f,tl) = 
	match tl0 with
	  [PGFunApp(f, tl),_] -> (f,tl)
	| [PGIdent f,_] -> (f,[])
	| _ -> input_error "predicate event should have one argument, which is a function application" e'
      in
      let (tl', tyl') = List.split (List.map (check_query_term names_must_be_encoded env) tl) in
      if !Param.key_compromise == 0 then
	QSEvent(false, FunApp((get_event_fun env f tyl'), tl'))
      else
	QSEvent(false, FunApp((get_event_fun env f (Param.sid_type :: tyl')),
			      (Terms.new_var_def Param.sid_type)::tl'))
  | PGFunApp(("inj-event",e'),tl0) ->
      let (f,tl) = 
	match tl0 with
	  [PGFunApp(f, tl),_] -> (f,tl)
	| [PGIdent f,_] -> (f,[])
	| _ -> input_error "predicate inj-event should have one argument, which is a function application" e'
      in
      let (tl', tyl') = List.split (List.map (check_query_term names_must_be_encoded env) tl) in
      if !Param.key_compromise == 0 then
	QSEvent(true, FunApp((get_event_fun env f tyl'), tl'))
      else
	QSEvent(true, FunApp((get_event_fun env f (Param.sid_type :: tyl')),
			     (Terms.new_var_def Param.sid_type)::tl'))
  | PGFunApp(("attacker",_), tl) ->
      check_attacker names_must_be_encoded env e tl (-1)
  | PGFunApp(("mess",_), tl) ->
      check_mess names_must_be_encoded env e tl (-1)
  | PGFunApp(("table",_), tl) ->
      check_table names_must_be_encoded env e tl (-1)
  | PGFunApp((s, ext) as p, tl) ->
      if List.mem s ["||"; "&&"; "not"; "==>"] then
	input_error (s ^ " unexpected in events") ext;
      let (tl', tyl) = List.split (List.map (check_query_term names_must_be_encoded env) tl) in
      QFact(get_pred env p tyl, tl')
  | PGPhase((s, ext), tl, n) ->
      begin
	match s with
	  "mess" -> check_mess names_must_be_encoded env e tl n
	| "attacker" -> check_attacker names_must_be_encoded env e tl n
	| "table" -> check_table names_must_be_encoded env e tl n
	| _ -> input_error "phases can be used only with attacker, mess, or table" ext
      end
  | PGIdent p -> 
      QFact(get_pred env p [], [])
  | PGLet(id,t,t') -> check_event names_must_be_encoded (add_binding false env (id,t)) t'
  | _ -> input_error "an event should be a predicate application" e
      
let rec check_hyp env = function
    (* FunApp: ==>, ||, && allowed, or what is allowed in events *)
    PGFunApp(("==>", _), [ev; hypll]), _ ->
      let ev' = check_event false env ev in
      (
       match ev' with
	 QNeq _ | QEq _ -> input_error "Inequalities or equalities cannot occur before ==> in queries" (snd ev)
       | _ -> ()
      );
      let hypll' = check_hyp env hypll in
      [[NestedQuery(Before(ev', hypll'))]]
  | PGFunApp(("||", _), [he1;he2]), _ -> 
      (check_hyp env he1) @ (check_hyp env he2)
  | PGFunApp(("&&", _), [he1;he2]), _ ->
      let he1' = check_hyp env he1 in
      let he2' = check_hyp env he2 in
      List.concat (List.map (fun e1 -> List.map (fun e2 -> e1 @ e2) he2') he1')
  | PGLet(id,t,t'), _ -> check_hyp (add_binding false env (id,t)) t'
  | ev -> [[QEvent(check_event false env ev)]]

let rec check_real_query_top env = function
    PGFunApp(("==>", _), [ev; hypll]), _ ->
      (* FunApp: ==> allowed, or what is allowed in events (case below) *)
      let ev' = check_event false env ev in
      let ev'' = 
	match ev' with
	  QNeq _ | QEq _ -> user_error "Inequalities or equalities cannot occur before ==> in queries\n"
	| QFact _ -> ev'
	| QSEvent _ when !Param.key_compromise == 0 -> ev'
	| QSEvent(inj, FunApp(f, sid::l)) ->
	    QSEvent(inj, FunApp(f, non_compromised_session::l))
	| QSEvent(_,_) ->
	    internal_error "Bad format for events in queries"
      in
      let hypll' = check_hyp env hypll in
      Before(ev'', hypll')
  | PGLet(id,t,t'), _ -> check_real_query_top (add_binding false env (id,t)) t'
  | ev ->
      let ev' = check_event false env ev in
      let ev'' = 
	match ev' with
	  QNeq _ | QEq _ -> user_error "Inequalities or equalities cannot occur alone queries\n"
	| QFact _ -> ev'
	| QSEvent _ when !Param.key_compromise == 0 -> ev'
	| QSEvent(inj, FunApp(f, sid::l)) ->
	    QSEvent(inj, FunApp(f, non_compromised_session::l))
	| QSEvent(_,_) ->
	    internal_error "Bad format for events in queries"
      in
      Before(ev'', [])

let rec check_query_list env = function
    [] -> []
  | (PRealQuery q)::lq -> 
      (RealQuery(check_real_query_top env q))::(check_query_list env lq)
  | (PPutBegin(i, l))::lq ->
      let l' = List.map (fun (s,e) ->
	try
	  match StringMap.find s env with
	    EEvent r -> r
	  | _ -> input_error (s ^ " should be an event") e
	with Not_found ->
	  input_error ("unknown event " ^s) e) l
      in
      (PutBegin(i,l'))::(check_query_list env lq)

let rec has_inj = function
    Before(_,ll) ->
      List.exists (List.exists (function
	  NestedQuery q -> has_inj q
	| QEvent (QSEvent (i,_)) -> i
	| QEvent (_) -> false)) ll

let rec check_inj_coherent_r q = 
  if has_inj q then
    match q with 
      Before(e,ll) ->
	let e' = 
	match e with
	  QFact _ | QNeq _ | QEq _ -> user_error "In a query e ==> h, if h contains an injective event, then e must be an event or better inj-event\n"
	| QSEvent(_,t) -> QSEvent(true, t) (* set the event injective *)
	in
	Before(e', List.map (List.map (function 
	    QEvent e -> QEvent e
	  | NestedQuery q' -> NestedQuery (check_inj_coherent_r q'))) ll)
  else q

let check_inj_coherent = function
    (PutBegin(_,_) as q) -> q
  | RealQuery q -> RealQuery (check_inj_coherent_r q)


let transl_query (env,q) =
  let q' = check_query_list (add_env true (!global_env) env) q in
  let q'' = List.map check_inj_coherent q' in
  Pievent.init_event_status_table event_fun_table;
  List.iter Pievent.set_event_status q'';
  q''

(* Give the fact to query from the detailed query
   This is used only to create a resembling specification for SPASS
 *)

let query_to_facts q =
  let facts = ref [] in
  List.iter (function
      PutBegin(_) -> ()
    | RealQuery(Before(e,_)) -> match e with
	QSEvent(_,(FunApp(f,l) as param)) -> 
	  facts := 
	    (if (Pievent.get_event_status f).end_status = Inj then
	      Pred(Param.end_pred_inj, [Var(Terms.new_var "endsid" Param.sid_type);param])
	    else
	      Pred(Param.end_pred, [param])) :: (!facts)
      | QSEvent(_, _) ->
	  user_error ("Events should be function applications\n")
      | QFact(p,l) ->
	  facts := (Pred(p,l)) :: (!facts)
      | QNeq _ | QEq _ -> internal_error "no Neq/Eq queries"
	    ) q;
  !facts

(* Noninterf queries *)

let get_noninterf_queries () =
  !noninterf_list

(* Weaksecret queries *)

let get_weaksecret_queries () =
  !weaksecret_list

(* Not declarations *)

let get_not() =
  List.map (fun (env, no) -> 
    check_event true (add_env true (!global_env) env) no) (!not_list)

(* For Nounif. Very similar to queries, except that *v is allowed
   and events are not allowed *)

let fget_ident_any env (s, ext) =
   try
     match StringMap.find s env with
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



let rec check_gformat env (term, ext0) =
  match term with
    PFGIdent i -> fget_ident_any env i
  | PFGFunApp((s,ext),l) -> 
      (* FunApp: only constructors allowed *)
      let (l', tl') = List.split (List.map (check_gformat env) l) in
      let (f, result_type) = get_fun env (s,ext) tl' in
      begin
        match f.f_cat with
          Eq _ | Tuple -> ()
	| Choice -> 
	    if not ((!Param.has_choice) || (!Param.equivalence)) then
	      input_error "choice can be used in nounif declarations only when proving equivalences" ext
        | _ ->  input_error ("function " ^ s ^ " is defined by \"reduc\". Such a function should not be used in a \"nounif\" declaration") ext
      end;
      if (f.f_options land Param.fun_TYPECONVERTER != 0) && (Param.get_ignore_types()) then
	match l' with
	  [t] -> (t, result_type)
	| _ -> internal_error "type converter functions should always be unary"
      else
	(FFunApp(f, l'), result_type)
  | PFGTuple l -> 
      let (l', tl') = List.split (List.map (check_gformat env) l) in
      (FFunApp(Terms.get_tuple_fun tl', l'), Param.bitstring_type)
  | PFGAny (s,ext) -> 
      begin
	try
	  match StringMap.find s env with
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
  | PFGName ((s,ext),bl) -> 
      begin
	try
	  let r = Hashtbl.find glob_table s in
	  check_single ext s;
	  if fst r.f_type == Param.tmp_type then
	    Parsing_helper.input_error ("You are referring to name " ^ s ^ " in this nounif declaration, but this name will never be generated") ext
	  else
	    begin
	      match r.f_cat with 
		Name { prev_inputs_meaning = sl } ->
		  List.iter (fun ((s',ext'),_) -> 
		    if not (List.exists (fun m -> Reduction_helper.meaning_encode m = s') sl) then
		      input_error ("variable " ^ s' ^ " not defined at restriction " ^ s) ext') bl;
		  let p = List.map2 (fun m ty ->
		    fbinding_find env (Reduction_helper.meaning_encode m) ty bl) sl (fst r.f_type) 
		  in
		  (FFunApp(r, p), snd r.f_type)
	      | _ -> internal_error "name expected here"
	    end
	with Not_found ->
	  input_error (s ^ " should be a name") ext
      end
  | PFGLet(id,t,t') -> check_gformat (add_fbinding env (id,t)) t'

and fbinding_find env s ty = function
    [] -> FAny (Terms.new_var Param.def_var_name ty)
  | ((s',ext),t)::l ->
      if s' = s then
	begin
	  let (t', ty') = check_gformat env t in
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
	fbinding_find env s ty l

and add_fbinding env ((i,ext),t) =
  begin
    try
      match StringMap.find i env with
	EVar _ -> input_error ("variable " ^ i ^ " already defined") ext
      | _ -> ()
    with Not_found -> ()
  end;
  let (t', ty') = check_gformat env t in
  let v = Terms.new_var i ty' in
  v.link <- FLink t';
  StringMap.add i (EVar v) env


let rec check_table_gformat env (term, ext0) =
  match term with
  | PFGFunApp((s,ext),l) -> 
      (* FunApp: only tables allowed *)
      let (l', tl') = List.split (List.map (check_gformat env) l) in
      let f = get_table_fun env (s,ext) tl' in
      FFunApp(f, l')
  | _ -> input_error "Table term expected" ext0

let check_gfact_format env ((s, ext), tl, n) =
  match s with
    "attacker" ->
      begin
	match tl with
	  [t1] ->
	    if n > !Param.max_used_phase then
	      input_warning "nounif declaration for a phase greater than used" ext;
	    let (t1', ty1) = check_gformat env t1 in
	    let att_n = Param.get_pred (Attacker((if n = -1 then (!Param.max_used_phase) else n), ty1)) 
	    in
	    (att_n, [t1'])
	| _ -> 
	    input_error "arity of predicate attacker should be 1" ext
      end
  | "mess" ->
      begin
	match tl with
	  [t1;t2] ->
	    if n > !Param.max_used_phase then
	      input_warning "nounif declaration for a phase greater than used" ext;
	    let (t1', ty1) = check_gformat env t1 in
	    let (t2', ty2) = check_gformat env t2 in
	    if ty1 != Param.channel_type then
	      input_error ("First argument of mess is of type " ^ ty1.tname ^ " and should be of type channel") ext;
	    let mess_n = Param.get_pred (Mess((if n = -1 then (!Param.max_used_phase) else n), ty2)) 
	    in
	    (mess_n, [t1';t2'])
	| _ -> 
	    input_error "arity of predicate mess should be 2" ext
      end
  | "table" ->
      begin
        match tl with
          [t1] ->
            if n > !Param.max_used_phase then
              input_warning "nounif declaration for a phase greater than used" ext;
	    let t1' = check_table_gformat env t1 in
	    let table_n = Param.get_pred (Table((if n = -1 then (!Param.max_used_phase) else n))) 
	    in
	    (table_n, [t1'])
	| _ -> 
	    input_error "arity of predicate table should be 1" ext
      end
  | s ->
      if n != -1 then
	input_error "declared predicates do not depend on phases, so no phase should be specified in such facts in queries" ext;
      let (tl', tyl) = List.split (List.map (check_gformat env) tl) in
      (get_pred env (s,ext) tyl, tl')

let rec handle_nounif env = function
    BFLet(id,t,nounif) -> handle_nounif (add_fbinding env (id,t)) nounif
  | BFNoUnif(fact,n) -> (check_gfact_format env fact, -n)

let get_nounif() =
  List.map (fun (env, nounif) -> handle_nounif (add_env true (!global_env) env) nounif) (!nounif_list)
     
