(*************************************************************
 *                                                           *
 *  Cryptographic protocol verifier                          *
 *                                                           *
 *  Bruno Blanchet and Vincent Cheval                        *
 *                                                           *
 *  Copyright (C) INRIA, CNRS 2000-2015                      *
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
open Parsing_helper
open Terms

exception HistoryUnifyError

(* add a rule and return its history *)

let rule_hash = Hashtbl.create 7

let change_type_attacker p t =
  match p.p_info with
    [Attacker(n,_)] -> Param.get_pred (Attacker(n,t))
  | [AttackerBin(n,_)] -> Param.get_pred (AttackerBin(n,t))
  | [AttackerGuess _] -> Param.get_pred (AttackerGuess(t))
  | [Compromise _] -> Param.get_pred (Compromise(t))
  | [PolymPred(s,i,tl)] -> Param.get_pred (PolymPred(s,i,Terms.copy_n (List.length tl) t))
  | [] -> 
      if !Param.typed_frontend then
	Parsing_helper.internal_error "Non-polymorphic user-defined predicates should not be declared data in the typed front-end"
      else
	p
  | _ -> Parsing_helper.internal_error "Unexpected predicate in change_type_attacker"

let get_rule_hist descr =
  try
    Hashtbl.find rule_hash descr
  with Not_found ->
    let (hyp,concl,constra,hdescr) = 
      match descr with
        RElem(preds, ({ p_type = [t1;t2] } as p)) ->
	  let v = Terms.new_var_def t1 in
	  let v' = Terms.new_var_def t2 in
	  (List.map (fun p' -> Pred(change_type_attacker p' t1, [v])) preds, 
	   Pred(p, [v;v']), 
	   [], Elem(preds,p))
      | RApplyFunc(f,p) ->
	  let rec gen_vars n =
	    if n = 0 then
	      [] 
	    else
	      (FunApp(f, Terms.var_gen (fst f.f_type))) :: (gen_vars (n-1))
	  in
	  let concl = gen_vars (List.length p.p_type) in
	  let hypl = reorganize_fun_app f concl in
	  (List.map (fun h -> Pred((change_type_attacker p (Terms.get_term_type (List.hd h))), h)) hypl, 
	   Pred((change_type_attacker p (Terms.get_term_type (List.hd concl))), concl), [],
	   Apply(f,p))
      | RApplyProj(f,nproj,p) ->
	  let rec gen_vars n =
	    if n = 0 then
	      [] 
	    else
	      (FunApp(f, Terms.var_gen (fst f.f_type))) :: (gen_vars (n-1))
	  in
	  let hyp = gen_vars (List.length p.p_type) in
	  let concl = List.nth (reorganize_fun_app f hyp) nproj in
	  ([Pred((change_type_attacker p (Terms.get_term_type (List.hd hyp))),hyp)], 
	   Pred((change_type_attacker p (Terms.get_term_type (List.hd concl))), concl), [],
	   Apply(Terms.projection_fun(f,nproj+1), p))
      |	_ -> 
	  internal_error "unsupported get_rule_hist"
    in
    let hist = Rule(-1, hdescr, hyp, concl, constra) in
    Hashtbl.add rule_hash descr hist;
    hist

(* History simplification *)

(* We use a hash table that associates to each fact all trees that
   derive it. To avoid recomputing hashes, we store them together with
   the considered fact. *)

module HashFact =
  struct

    type t = 
	{ hash : int;
	  fact : fact }

    let equal a b = Termslinks.equal_facts_with_links a.fact b.fact

    type skel_term =
	SVar of int
      |	SFun of string * skel_term list

    type skel_fact =
	SPred of string * skel_term list
      |	SOut of skel_term

    let rec skeleton_term = function
	Var b -> 
	  begin
	    match b.link with
	      TLink t -> skeleton_term t
	    | NoLink -> SVar(b.vname)
	    | _ -> Parsing_helper.internal_error "unexpected link in skeleton_term"
	  end
      |	FunApp(f,l) -> 
	  match f.f_cat with
	    Name _ -> SFun(f.f_name,[])
	  | _ -> SFun(f.f_name, List.map skeleton_term l)

    let skeleton_fact = function
	Pred(p,l) -> SPred(p.p_name, List.map skeleton_term l)
      |	Out(t,_) -> SOut(skeleton_term t)

    let hash a = a.hash

    (* build a HashFact.t from a fact *)

    let build f = { hash = Hashtbl.hash(skeleton_fact f);
		    fact = f }

  end

module TreeHashtbl = Hashtbl.Make(HashFact)

let tree_hashtbl = TreeHashtbl.create 7

let seen_fact hf =
  if !Param.simplify_derivation_level = Param.AllFacts then
    TreeHashtbl.find tree_hashtbl hf
  else
  match hf.HashFact.fact with
    Pred(p,_) when p.p_prop land Param.pred_ATTACKER != 0 ->
      TreeHashtbl.find tree_hashtbl hf
  | _ -> raise Not_found 
               (* Remove proofs of the same fact only for attacker facts,
                  several proofs of the same fact may be useful for attack
		  reconstruction for other facts: for mess facts, in particular
		  several outputs of the same message on the same channel
		  may be needed for private channels. *)

let rec unroll_rwp t =
  match t.desc with 
    FRemovedWithProof t' -> unroll_rwp t'
  | _ -> t

let equal_son t t' =
  unroll_rwp t == unroll_rwp t'

let seen_tree hf t =
  if !Param.simplify_derivation_level != Param.AttackerSameTree then
    begin
      TreeHashtbl.add tree_hashtbl hf t;
      t
    end
  else
    match t.thefact with
      Pred(p,_) when p.p_prop land Param.pred_ATTACKER != 0 -> 
          (* If t was already proved, it would have been removed by seen_fact when it
	     concludes an attacker fact *)
	TreeHashtbl.add tree_hashtbl hf t;
	t
    | _ ->
	try
	  let r = TreeHashtbl.find_all tree_hashtbl hf in
	  let t' =
	    List.find (fun t' ->
	      (match t.desc, t'.desc with
		FHAny, FHAny -> true
	      | FEmpty, FEmpty -> true
	      | FRule(n, tags, constra, sons), FRule(n', tags', constra', sons') ->
		  (n == n') && (Termslinks.equal_tags tags tags') && (Termslinks.equal_constra constra constra') &&
		  (List.length sons == List.length sons') && (List.for_all2 equal_son sons sons')
	      | FEquation son, FEquation son' ->
		  equal_son son son'
	      | FRemovedWithProof _, _ -> internal_error "Unexpected FRemovedWithProof"
	      | _ -> false)
		) r
	  in
	  { t with desc = FRemovedWithProof t' }
        with Not_found ->
	  TreeHashtbl.add tree_hashtbl hf t;
	  t

let rec simplify_tree t =
  let hf = HashFact.build t.thefact in
  match t.desc with
    FRemovedWithProof t' -> 
      begin
	try
	  { t with desc = FRemovedWithProof (TreeHashtbl.find tree_hashtbl hf) }
	with Not_found ->
	  simplify_tree t'
      end
  | FHAny | FEmpty ->
      begin
	try   
	  { t with desc = FRemovedWithProof (seen_fact hf) }
        with Not_found ->
	  seen_tree hf t
      end
  | FRule(n, tags, constra, sons) -> 
      begin
	try   
	  { t with desc = FRemovedWithProof (seen_fact hf) }
        with Not_found ->
	  let sons' = List.rev_map simplify_tree (List.rev sons) in
	  seen_tree hf { t with desc = FRule(n, tags, constra, sons') } 
      end
  | FEquation son -> 
      begin
	try   
	  { t with desc = FRemovedWithProof (seen_fact hf) }
        with Not_found ->
	  let son' = simplify_tree son in
	  seen_tree hf { t with desc = FEquation son' }
      end

(* Find hypothesis number n in the history tree *)

type res = Success of fact_tree
         | Failure of int

let rec get_desc_rec t n = 
  match t.desc with
    FEmpty -> if n = 0 then Success(t) else Failure(n-1)
  | FHAny -> Failure(n)
  | FRemovedWithProof _ -> Failure(n)
  | FRule(_,_,_,l) -> get_desc_list_rec l n
  | FEquation h -> get_desc_rec h n

and get_desc_list_rec l n = 
  match l with
    [] -> Failure(n)
  | (a::l') ->
      match get_desc_rec a n with
	Success d -> Success d
      | Failure n' -> get_desc_list_rec l' n'


let get_desc s t n =
  match get_desc_rec t n with
    Success d -> d
  | Failure n' -> 
      print_string ("Hypothesis " ^ (string_of_int n) ^ " not found (" ^ s ^ ")\n");
      Display.Text.display_history_tree "" t;
      internal_error ("failed to find history hypothesis (" ^ s ^ ")")

(* Rebuild the derivation tree *)

let rec build_fact_tree = function
    Empty(f) -> 
      let tmp_bound_vars = !current_bound_vars in
      current_bound_vars := [];
      let f' = copy_fact2 f in
      cleanup();
      current_bound_vars := tmp_bound_vars;
      { desc = FEmpty;
        thefact = f' }
  | Any(n, h) ->
      let t = build_fact_tree h in
      let d = get_desc "any" t n in
      begin
	try
	  match d.thefact with
	    Pred(p, a::r) when p.p_prop land Param.pred_ANY_STRICT != 0
	      && p.p_prop land Param.pred_ANY == 0 ->
	      (* The arguments of "any" facts must all be equal *)
	      List.iter (fun b -> unify a b) r
	  | _ -> ()
	with Unify -> raise HistoryUnifyError
      end;
      d.desc <- FHAny;
      t
  | Removed(rem_count, dup_count, h) -> 
      let t = build_fact_tree h in
      let d1 = get_desc "removed" t rem_count in
      let d2 = get_desc "removed" t dup_count in
      begin
      try 
        unify_facts d1.thefact d2.thefact
      with Unify -> raise HistoryUnifyError
      end;      
      d1.desc <- FRemovedWithProof d2;
      t
  | HEquation(n,leq,req,h) ->
     let t = build_fact_tree h in
     (* Copy the facts *)
     let tmp_bound_vars = !current_bound_vars in
     current_bound_vars := [];
     let leq' = copy_fact2 leq in
     let req' = copy_fact2 req in
     cleanup();
     current_bound_vars := tmp_bound_vars;
     if n = -1 then 
       begin
        begin
          try 
            unify_facts req' t.thefact
          with Unify -> raise HistoryUnifyError
        end;
        { desc = FEquation(t);
          thefact = leq' }
       end
     else
       begin
         let d = get_desc "equation" t n in
         begin
           try 
             unify_facts leq' d.thefact
           with Unify -> raise HistoryUnifyError
         end;
         d.desc <- FEquation({ desc = FEmpty;
                               thefact = req' });
         t
       end
  | Rule(n,descr,hyp,concl,constra) -> 
      let tmp_bound = !current_bound_vars in
      current_bound_vars := [];
      let rhyp = List.map copy_fact hyp in
      let rconcl = copy_fact concl in
      let rconstra = List.map copy_constra constra in
      let rdescr = 
	match descr with
	  ProcessRule(hypspec,name_params) -> 
	    ProcessRule(hypspec,List.map copy_term name_params)
	| x -> x
      in
      cleanup();
      current_bound_vars := tmp_bound;
      { desc = FRule(n, rdescr, rconstra, List.map (fun f -> { desc = FEmpty; thefact = f }) rhyp);
	thefact = rconcl }
  | Resolution(h1, n, h2) ->
      let t1 = build_fact_tree h1 in
      let t2 = build_fact_tree h2 in
      let d = get_desc "resolution" t2 n in
      begin
	try 
          unify_facts t1.thefact d.thefact
	with Unify -> raise HistoryUnifyError
      end;
      d.desc <- t1.desc;
      t2
  | TestUnifTrue(n, h2) ->
      let t2 = build_fact_tree h2 in
      let d = get_desc "test_unif_true" t2 n in
      d.desc <- FRule(-1, TestUnif, [], []);
      t2

let build_history (subgoals, orig_fact, hist_done, constra) =
  assert (!current_bound_vars == []);
  if not (!Param.reconstruct_derivation) then 
    begin
      if !Param.typed_frontend then
	Display.Text.print_line "I do not reconstruct derivations.\nIf you want to reconstruct them, add\n   set reconstructDerivation = true. \nto your script."
      else
	Display.Text.print_line "I do not reconstruct derivations.\nIf you want to reconstruct them, add\n   param reconstructDerivation = true. \nto your script.";
      { desc = FEmpty; thefact = orig_fact }
    end
  else
  try 
    let new_tree0 = build_fact_tree hist_done in
    let new_tree1 =
      if !Param.simplify_derivation then
	begin
	  TreeHashtbl.clear tree_hashtbl;
	  let r = simplify_tree new_tree0 in
	  TreeHashtbl.clear tree_hashtbl;
	  r
	end
      else
	new_tree0
    in
    if !Param.html_output then
      begin
	incr Param.derivation_number;
	let qs = string_of_int (!Param.derivation_number) in
	if !Param.abbreviate_derivation then
	  begin
	    let (abbrev_table, new_tree2) = Display.abbreviate_derivation new_tree1 in
	    (* Display short derivation *)
	    Display.LangHtml.openfile ((!Param.html_dir) ^ "/derivation" ^ qs ^ ".html") ("ProVerif: derivation for query " ^ qs);
	    Display.Html.print_string "<H1>Derivation</H1>\n";
	    if abbrev_table != [] then Display.Html.display_abbrev_table abbrev_table;
	    Display.Html.display_history_tree "" new_tree2;
	    Display.LangHtml.close();
	    Display.Html.print_string ("<A HREF=\"derivation" ^ qs ^ ".html\">Derivation</A> ");
	    (* Display explained derivation *)
	    Display.LangHtml.openfile ((!Param.html_dir) ^ "/derivationexplained" ^ qs ^ ".html") ("ProVerif: derivation for query " ^ qs);
	    Display.Html.print_string "<H1>Explained derivation</H1>\n";
	    if abbrev_table != [] then Display.Html.display_abbrev_table abbrev_table;
	    Display.Html.explain_history_tree new_tree2;
	    Display.LangHtml.close();
	    Display.Html.print_string ("<A HREF=\"derivationexplained" ^ qs ^ ".html\">Explained derivation</A><br>\n")
	  end
	else
	  begin
	    (* Display short derivation *)
	    Display.LangHtml.openfile ((!Param.html_dir) ^ "/derivation" ^ qs ^ ".html") ("ProVerif: derivation for query " ^ qs);
	    Display.Html.print_string "<H1>Derivation</H1>\n";
	    Display.Html.display_history_tree "" new_tree1;
	    Display.LangHtml.close();
	    Display.Html.print_string ("<A HREF=\"derivation" ^ qs ^ ".html\">Derivation</A> ");
	    (* Display explained derivation *)
	    Display.LangHtml.openfile ((!Param.html_dir) ^ "/derivationexplained" ^ qs ^ ".html") ("ProVerif: derivation for query " ^ qs);
	    Display.Html.print_string "<H1>Explained derivation</H1>\n";
	    Display.Html.explain_history_tree new_tree1;
	    Display.LangHtml.close();
	    Display.Html.print_string ("<A HREF=\"derivationexplained" ^ qs ^ ".html\">Explained derivation</A><br>\n")
	  end
      end
    else if !Param.display_derivation then
      begin
	if !Param.abbreviate_derivation then
	  let (abbrev_table, new_tree2) = Display.abbreviate_derivation new_tree1 in
	  if abbrev_table != [] then Display.Text.display_abbrev_table abbrev_table;
	  if !Param.explain_derivation then
	    Display.Text.explain_history_tree new_tree2
	  else
	    Display.Text.display_history_tree "" new_tree2
	else
	  if !Param.explain_derivation then
	    Display.Text.explain_history_tree new_tree1
	  else
	    Display.Text.display_history_tree "" new_tree1;
	Display.Text.newline()
      end;
    new_tree1
  with HistoryUnifyError ->
      if ((!Param.max_hyp) >= 0) || ((!Param.max_depth) >= 0) then
      begin
        print_string "You have probably found a false attack due to the limitations\non depth of terms and/or number of hypotheses.\nI do not know if there is a real attack.\n";
	if !Param.html_output then
	  Display.Html.print_line "You have probably found a false attack due to the limitations\non depth of terms and/or number of hypotheses.\nI do not know if there is a real attack.";
        cleanup();
        { desc = FEmpty; thefact = orig_fact }
      end
      else
        internal_error "Unification failed in history rebuilding"

