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
open Terms

let debug_print s = ()
(* print_endline s *)

let max_proc_nb = 1024

let cur_proc_nb = ref 1

let get_proc_nb () = !cur_proc_nb

let up_proc_nb int = cur_proc_nb := int

let no_more_proc () = get_proc_nb () >= max_proc_nb

let choice_in_term = Terms.choice_in_term

let match_pat_all_mode = Menu_helper.match_pat_all_mode

let term_eval_match_pat_all_mode = Menu_helper.term_eval_match_pat_all_mode

let rec get_recipe_of_term question_text t t' set_tio in_or_out =
  let state = Menu_helper.get_state () in
  try
    auto_cleanup (fun () ->
        let recipe = Menu_helper.get_recipe "" question_text in
        let exp = Menu_helper.expand_recipe state.pub_vars state.public recipe in
        try
          let result = Menu_helper.evaluates_term_all_mode exp in
          begin
            try
              if Menu_helper.equal_terms_modulo_all_mode t' result then
                begin
		  let recipe_term_list = Menu_helper.decompose_term_all_mode (recipe, result) in
		  let state' = Menu_helper.add_public_list_dec_all_mode state recipe_term_list in
                  if state' == state then
                    let _ = Menu_helper.question_box  "Already in public" ["Ok"] ("Term " ^ (Display_interact.GtkInteract.display_term result) ^ " (or its components after decomposing data constructors) already in public") in
                    state
                  else
	            let (new_pub, pub_vars) = Menu_helper.get_new_vars state state'.public in
                    { state' with
                        pub_vars = pub_vars;
                        comment = RAddpub new_pub;
                        previous_state = Some state
                    }
                end
              else
                Parsing_helper.user_error ("The recipe you have given evaluates to " ^
		                             (Display_interact.GtkInteract.display_term result) ^
		                               " which is different from " ^
                                                 (Display_interact.GtkInteract.display_term t))
            with
              Reduction_bipro.FailOnlyOnSide i ->
              begin
                match set_tio with
                | I_O (_, n, _, _, p)
                | O_I (_, n, _, _, p) ->
                   raise (Menu_helper.Div (DChannel(in_or_out, i, t, t', recipe, result, n, p)))
                | Other -> assert false
              end
          end
        with
          Reduction_bipro.FailOnlyOnSide i ->
           raise (Menu_helper.Div (DFail(i, recipe, exp)));
        | Unify ->
           let _ = Menu_helper.question_box "Evaluation fails on both sides" ["Ok"]
                     ("The evaluation of the expansion "
                      ^ (Display_interact.GtkInteract.display_term exp)
                      ^ "\nof the given recipe fails on both sides. Please, enter a new recipe.");
           in
           get_recipe_of_term question_text t t' set_tio in_or_out
      )
  with
  | Unify -> Parsing_helper.user_error "The evaluation of the recipe fails"
  | Menu_helper.WarningsAsError -> get_recipe_of_term question_text t t' set_tio in_or_out
  (* | Menu_helper.WrongChoice -> state *)

let do_repl state n p =
  debug_print "Doing Repl";
  {
    state with
    subprocess = Reduction_helper.add_at n (Menu_helper.sub_of_proc p) state.subprocess;
    previous_state = (Some state);
    comment = (RRepl (n, 2 ))
  }

(* [do_public_input state n tin pat p proc] Adversary makes an input on channel [tin], *)
(* corresponding to [proc = in(tin, exp:pat); p]. *)
let rec do_public_input state n tin pat p proc (* already_public *) =
  let rec get_recipe_and_result state =
    auto_cleanup (fun () ->
        let r = Menu_helper.get_recipe ""
                  ("<b>Input a recipe</b>"
                   ^ "\nGive the recipe to input on channel:"
                   ^ "\n" ^ (Display_interact.GtkInteract.display_term tin)
                   ^ ".")
        in
        let exp = Menu_helper.expand_recipe state.pub_vars state.public r in
        try
          let t' = Menu_helper.evaluates_term_all_mode exp in
          (r, t')
        with
        | Reduction_bipro.FailOnlyOnSide i ->
           raise (Menu_helper.Div (DFail(i, r, exp)))
        | Unify ->
           Parsing_helper.user_error "The evaluation of the recipe fails"
      )
  in
  try
    let (recipe, result) =
      get_recipe_and_result state
    in
    begin
      try
        auto_cleanup (fun () ->
            match_pat_all_mode pat result;
            let p' = auto_cleanup (fun () -> Reduction_helper.copy_process p) in
            { state with
              subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p') state.subprocess;
              comment = RInput_Success(n, tin, pat, recipe, result);
              previous_state = Some state
          })
      with
        Reduction_bipro.FailOnlyOnSide i ->
         Menu_helper.display_div state (DInputPat(i, recipe, result, pat, n, proc))
      | Unify ->
         if not (Terms.equal_types (Terms.get_pat_type pat) (Terms.get_term_type result)) then
           ignore (Menu_helper.question_box "Input failed" ["OK"] "The input failed because the received message is not of the expected type." )
         else
           ignore (Menu_helper.question_box "Input failed" ["OK"] "The input failed because the pattern-matching failed.");
         { state with
           subprocess = Reduction_helper.remove_at n state.subprocess;
           comment = RInput_PatFails(n, tin, pat, recipe, result);
           previous_state = Some state
         }
    end
  with Menu_helper.Div exn ->
    Menu_helper.display_div state exn

(* [do_fail_input] performs an input in which the evaluation
   of the channel fails *)
let do_fail_input state n tc pat =
  { state with
    subprocess = Reduction_helper.remove_at n state.subprocess;
    comment = RInput_Remove(n, tc, pat, DestrFails);
    previous_state = Some state
  }

let do_auto_input state n tin pat proc =
  try
    let tin' = Menu_helper.evaluates_term_all_mode tin in
    ignore (Menu_helper.is_in_public_test_div state.public tin');
    (* Should never happen when input is auto reducible *)
    assert false
  with Unify ->
	do_fail_input state n tin pat
     | Reduction_bipro.FailOnlyOnSide i ->
        (* the [n]-th subprocess of the current state is an input process on [tc] *)
        (* such that when we evaluates [tc], *)
        (* only the evaluation of side [i] fails *)
        Menu_helper.display_div state (DEval("an input such that the evaluation of the channel", i, tin, n, proc))
     | Menu_helper.DivTermPub (i, channel, ca, pub) ->
        Menu_helper.display_div state (DChannel("input", i, tin, channel, ca, pub, n , proc))


(* [do_auto_or_public_output state n tc t p proc] [n]-th subprocess do an auto output
or a public output corresponding to a reduction step on [proc = out(tc, t); p] *)
let do_auto_or_public_output state n tc t p proc =
  debug_print "Doing Out";
  try
    auto_cleanup (fun () ->
        let (tc', t') = Menu_helper.evaluates_2terms_all_mode tc t in
        let ch_pub = Menu_helper.is_in_public_test_div state.public tc' in
        assert ch_pub;
	let (n_b, recipe_term_list) = Menu_helper.decompose_term_rev_all_mode t' in
        try
          let state' = Menu_helper.add_public_list_dec_all_mode state recipe_term_list in
          let (_, pub_vars) = Menu_helper.get_new_vars state state'.public in
          { state' with
            subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p) state.subprocess;
            comment = ROutput_Success(n, tc', n_b, t');
            pub_vars = pub_vars;
            previous_state = Some state
          }
        with
        | Menu_helper.Div div ->
           Menu_helper.display_div state (DOutputMess(t, t', n_b, n, proc, div))
      )
  with Unify ->
    { state with
      subprocess = Reduction_helper.remove_at n state.subprocess;
      comment = ROutput_Remove(n, tc, t, DestrFails);
      previous_state = Some state
    }
   | Menu_helper.DivTermPub (i, tc', ca, pub) ->
      Menu_helper.display_div state (DChannel ("output", i, tc, tc', ca, pub, n, proc))
   | Reduction_bipro.FailOnlyOnSide i ->
      Menu_helper.display_div state (DEvalOut (i, tc, t,  n, proc))


let do_insert state n t p proc =
  let rec insert_in acc t = function
      [] -> List.rev (t::acc)
    | (t'::tl) as tables ->
       let l_t = Menu_helper.get_table_name t in
       let l_t' = Menu_helper.get_table_name t' in
       if l_t' = l_t then
         if equal_terms t t' then
           List.rev_append acc tables
         else
           insert_in (t'::acc) t tl
       else
         if l_t > l_t' then
           insert_in (t::acc) t' tl
         else
           insert_in (t'::acc) t tl
  in
  try
    begin
      auto_cleanup
        (fun () ->
	  let t' = Menu_helper.evaluates_term_all_mode t in
	  { state with
            subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p) state.subprocess;
	    tables = insert_in []  t' state.tables;
	    comment = RInsert_Success(n, t', false);
	    previous_state = Some state }
        )
    end
  with
  | Reduction_bipro.FailOnlyOnSide i ->
     Menu_helper.display_div state (DEval("an insert such that the evaluation of", i, t, n, proc))
  | Unify ->
     debug_print "remove insert";
     { state with
       subprocess = Reduction_helper.remove_at n state.subprocess;
       comment = RInsert_Remove(n, t, DestrFails);
       previous_state = Some state }

let do_nil state n =
  { state with
    subprocess = Reduction_helper.remove_at n state.subprocess;
    comment = RNil(n);
    previous_state = Some state}

let do_par state p q n =
  debug_print "Doing Par";
  { state with
    subprocess = Reduction_helper.add_at n (Menu_helper.sub_of_proc p)
                   (Reduction_helper.replace_at n (Menu_helper.sub_of_proc q)
                      state.subprocess);
    comment = RPar(n);
    previous_state = Some state }

let do_restr state na env args p n =
  debug_print "Doing Restr";
  let na' = Terms.copy_name na [] in
  let n' = FunApp(na', []) in
  let p' = Reduction_helper.process_subst p na n' in
  { state with
    subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p') state.subprocess;
    comment = RRestr(n, na, n');
    previous_state = Some state }

let do_event state t n p proc =
  try
    auto_cleanup
      (fun () ->
        let t = Menu_helper.evaluates_term_all_mode t in
        { state with
          subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p) state.subprocess;
          comment = REvent_Success(n, t, false);
          previous_state = Some state;
          events = t::state.events
      })
  with
    Reduction_bipro.FailOnlyOnSide i ->
     Menu_helper.display_div state (DEval("an event such that the evaluation of", i, t, n, proc))
  | Unify ->
     { state with
       subprocess = Reduction_helper.remove_at n state.subprocess;
       comment = REvent_Remove(n, t, DestrFails);
       previous_state = Some state }

let do_let state pat t p q n proc =
  debug_print "Doing Let";
  auto_cleanup (fun () ->
      try
        (* evaluates and match in one time *)
        term_eval_match_pat_all_mode pat t;
        let p' = auto_cleanup (fun () -> Reduction_helper.copy_process p) in
        { state with
          subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p') state.subprocess;
          comment = RLet_In(n, pat, t);
          previous_state = Some state}
      with
        Reduction_bipro.FailOnlyOnSide i ->
         Menu_helper.display_div state (DEvalLet(i, t, pat, n, proc))
      | Unify ->
         (* Evaluation or pattern-matching failed on both sides *)
         { state with
           subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc q) state.subprocess;
           comment = RLet_Else(n, pat, t);
           previous_state = Some state}
    )


let do_test state t p q n proc =
  if q == Nil then
    begin
      try
        if Menu_helper.evaluates_term_to_true_all_mode t then
          { state with
            subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p) state.subprocess;
            comment = RTest_Then(n, t);
            previous_state = Some state;
          }
        else
          { state with
            subprocess = Reduction_helper.remove_at n state.subprocess;
            comment = RTest_Remove(n, t, TestFails);
            previous_state = Some state;
          }
      with
      | Reduction_bipro.FailOnlyOnSide i ->
         Menu_helper.display_div state (DTest(i, true, choice_in_term 1 t,  choice_in_term 2 t, t, n, proc))
    end
  else
    try
      let t' = Menu_helper.evaluates_term_all_mode t in
      try
        if Menu_helper.equal_terms_modulo_all_mode t' true_term then
          { state with
            subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p) state.subprocess;
            comment = RTest_Then(n, t);
            previous_state = Some state;
          }
        else
          { state with
            subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc q) state.subprocess;
            comment = RTest_Else(n, t);
            previous_state = Some state;
          }
      with Reduction_bipro.FailOnlyOnSide i ->
        Menu_helper.display_div state (DTest(i, false, choice_in_term 1 t,  choice_in_term 2 t, t, n, proc))
    with Unify ->
          { state with
            subprocess = Reduction_helper.remove_at n state.subprocess;
            comment = RTest_Remove(n, t, DestrFails);
            previous_state = Some state;
         }
       | Reduction_bipro.FailOnlyOnSide i ->
          Menu_helper.display_div state (DEval("a test such that the evaluation of the condition", i, t, n, proc))

let do_get state pat mess_term t n p proc =
  auto_cleanup(fun () ->
      match_pat_all_mode pat mess_term;
      let p' = auto_cleanup (fun () -> Reduction_helper.copy_process p) in
      { state with
        subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc p') state.subprocess;
        comment = RGet_In(n, pat, t, mess_term);
        previous_state = Some state
      }
    )

let do_rio t pat p q n_input n_output tin state =
  debug_print "do rio";
  Menu_helper.set_io_c Other;
  auto_cleanup (fun () ->
      (* The evaluation of the message [t] always succeeds
	 because when it fails (on at least one side), the output is automatically removed *)
      let t' =  Menu_helper.evaluates_term_all_mode t in
      try
        match_pat_all_mode pat t';
        let q'' = auto_cleanup (fun () -> Reduction_helper.copy_process q) in
        { state with
          subprocess = Reduction_helper.replace_at (n_input) (Menu_helper.sub_of_proc q'') (Reduction_helper.replace_at n_output (Menu_helper.sub_of_proc p) state.subprocess);
          comment = RIO(n_input, tin, pat, n_output, tin, None, t', false);
          previous_state = Some state }
      with
      | Reduction_bipro.FailOnlyOnSide i ->
         let proc_in = Menu_helper.get_proc state n_input in
         let proc_out = Menu_helper.get_proc state n_output in
         Menu_helper.display_div state (DIOPat(i, t, t', pat, n_input, proc_in, n_output, proc_out))
      | Unify ->
         debug_print "doing RIO_PatRemove";
         { state with
           subprocess = Reduction_helper.remove_at (n_input) (Reduction_helper.replace_at n_output (Menu_helper.sub_of_proc p) state.subprocess);
           comment = RIO_PatRemove(n_input, tin, pat, n_output, tin, None, t, false, true);
           previous_state = Some state }
    )

let do_phase state n =
  debug_print ("Doing Phase " ^(string_of_int n));
  if n <= state.current_phase then
    Parsing_helper.user_error "Phases should be in increasing order.";
  { state with
    subprocess = Evaluation_helper.extract_phase n state.subprocess;
    current_phase = n;
    comment = RPhase(n);
    previous_state = Some state
  }


(* [show_terms termsl] Display the terms in  termsl in a form of a store. It allows the user to click *)
(* on one term, and update [choice_term] with this term. *)
let show_terms termsl frz dfrz =
  let window = GWindow.dialog ~modal:true ~title:"Double-click on a term" ~width:300 ~height:300 ~border_width:0 () in
  window#misc#modify_bg [(`NORMAL, `WHITE)];
  let destroy_win () =
    window#destroy();
    GMain.Main.quit()
  in
  frz();
  window#set_position `CENTER;
  let choice_term = ref None in
  let cols = new GTree.column_list in
  let col = cols#add Gobject.Data.string in
  let create_model labl =
    let store = GTree.list_store cols in
    let fill l =
      let iter = store#append () in
      store#set ~row:iter ~column:col l
    in
    List.iter fill labl;
    store
  in
  (* Function called when a double click is made on a row *)
  let on_row_activated (view:GTree.view) path column =
    let row_nb = int_of_string (GTree.Path.to_string path) in
    choice_term := Some (List.nth termsl row_nb);
    window#destroy()
  in
  let create_view ~model ~packing =
    let view = GTree.view ~headers_visible:false  ~packing ~model  () in
    let col_v =  GTree.view_column ~renderer:(GTree.cell_renderer_text [], ["markup", col]) () in
    let _ = view#append_column col_v in
    let _ = view#connect#row_activated ~callback:(on_row_activated view) in
    view#coerce
  in
  let labl = List.map Display_interact.GtkInteract.display_term termsl in
  let _ =  window#connect#destroy ~callback:destroy_win in
  let scrolled_window = GBin.scrolled_window ~border_width:10
                          ~packing:window#vbox#add () in
  let main_vbox = GPack.vbox ~packing:scrolled_window#add_with_viewport () in
  let model = create_model labl in
  let _ = create_view ~model ~packing:main_vbox#pack in
  let cancel_b = GButton.button ~stock:`CANCEL  ~packing:window#action_area#add () in
  let _ = cancel_b#connect#clicked ~callback:destroy_win in
  window#show ();
  GMain.Main.main();
  !choice_term

let do_get_full state n pat t p q proc frz dfrz =
  try
  match Menu_helper.match_terms_lst state.tables pat t n p with
  | [] -> (* The else branch is taken: q is executed *)
     debug_print "Doing Get2";
     { state with
       subprocess = Reduction_helper.replace_at n (Menu_helper.sub_of_proc q) state.subprocess;
       comment = RGet_Else(n, pat, t);
       previous_state = Some state
     }
  | [mess_term] -> (* Only one choice, p\sigma is executed *)
     do_get state pat mess_term t n p proc;
  | termsl ->
     let t' = show_terms termsl frz dfrz in
     match t' with
       None -> state
     | Some mess_term -> do_get state pat mess_term t n p proc
  with Menu_helper.Div(div) ->
    Menu_helper.display_div state div

(* Do the reduction of the n-th process of state.subprocess which *)
(* is proc. This function doesn't treat the case LetFilter yet. NamedProcess reductions are done *)
(* automatically *)
let rec do_auto_reduction state n proc frz dfrz =
  let n_state =
    match proc with
    | Repl(p,occ) -> do_repl state n p
    | Insert(t,p,_) -> do_insert state n t p proc
    | Nil -> do_nil state n;
    | Par(p, q) -> do_par state p q n
    | Restr(na, (args, env), p, occ) -> do_restr state na env args p n
    | Let(pat, t, p, q, occ) -> do_let state pat t p q n proc
    | Test(t, p, q, occ) -> do_test state t p q n proc
    | Output(tc,t,p,occ) -> do_auto_or_public_output state n tc t p proc
    | Input(tc,pat,p,occ) -> do_auto_input state n tc pat proc
    | Event(t, _, p, _) -> do_event state t n p proc
    | Get(pat, t, p, q, occ) ->
            do_get_full state n pat t p q proc frz dfrz
    | _ -> raise Menu_helper.WrongChoice
  in
  Menu_helper.delete_NamedProcess n_state

(* Make a manual reduction of the nth process in state.subprocess (proc), *)
(* reduct renaming NamedProcess. Might raise Div(DIO..) *)
let do_manual_reduction state n proc frz dfrz =
  let quest_io io tin tin' set_tio func =
      let ans =  Menu_helper.question_box ("Private " ^ io) ["1) Channel is public"; "2) Private communication"; "Cancel"] ("Either: \n 1) The channel " ^ Display_interact.GtkInteract.display_term tin ^ " is in fact public. Give a recipe to prove that. \n 2) Make a communication on the private channel " ^ Display_interact.GtkInteract.display_term tin ^ ".\n      You will then choose the process to communicate with.")
      in
      begin
        match ans with
        | 1 ->
           begin
             try
               let n_state = get_recipe_of_term
                               ("Give a recipe for the channel:\n"
                                ^ Display_interact.GtkInteract.display_term tin)
                               tin tin' set_tio io
               in
               func n_state
             with
             | Menu_helper.WrongChoice -> state
	     | Menu_helper.Div div ->
		 Menu_helper.display_div state div
           end
        | 2 ->
           let data = Menu_helper.get_data () in
           begin
	     try
               (* We scan the whole list (we do not stop when we know that there is
                  at least one corresponding input/output).
                  This allows us to detect all diverge cases due to channels equal
                  on one side and different on the other at this point. *)
               if List.filter (fun (_,x) ->
                      Menu_helper.equal_io_oi x set_tio) data.titles != [] then
                 begin
                   Menu_helper.set_io_c set_tio;
	           state
                 end
               else
                 begin
                   let _ = Menu_helper.question_box "Error" ["OK"]
                             "No Reduction possible on this private channel"
                   in
                   state
                 end
             with
             | Menu_helper.Div(div) ->
                 Menu_helper.display_div state div
           end
        | _ ->  state
      end
  in
  let n_state = match Menu_helper.get_io_c () with
    | Other ->
       begin
         match proc with
         | Repl(p,occ) -> do_repl state n p
         | Phase(n, p, _) -> do_phase state n
         | Input(tin, pat, p, _) ->
            begin
	      try
		let tin' = Menu_helper.evaluates_term_all_mode tin in
                if Menu_helper.is_in_public_test_div state.public tin' then
                  do_public_input state n tin' pat p proc
		else
                  let fun_1 n_state = do_public_input n_state n tin' pat p proc in
                  quest_io "input" tin tin' (I_O (tin, n, pat, p, proc)) fun_1
	      with
	      | Unify -> (* should not happen because it is an auto-reduction *)
		  do_fail_input state n tin pat
              | Reduction_bipro.FailOnlyOnSide i ->
              (* the [n]-th subprocess of the current state is an input process on [tc] *)
              (* such that when we evaluates [tc], *)
              (* only the evaluation of side [i] fails *)
                  Menu_helper.display_div state (DEval("an input such that the evaluation of the channel", i, tin, n, p))
              | Menu_helper.DivTermPub (i, tin', ca, pub) ->
                  Menu_helper.display_div state (DChannel("input", i, tin, tin', ca, pub, n, p))
            end
         | Output(tc, t, p, occ) ->
            let fun_1 state = do_auto_or_public_output state n tc t p proc in
            let tc' = Menu_helper.evaluates_term_all_mode tc in
            quest_io "output" tc tc' (O_I (tc, n, t, p, proc)) fun_1
         | Insert(t,p,_) ->
            do_insert state n t p proc
         | Get(pat, t, p, q, occ) ->
            (* 3 cases are possible: *)
            (* - There could be no term in [state.tables] that satisfying the pattern, *)
            (* in which case, q is executed. *)
            (* - There could be only one term that matches the pattern with a substitution \sigma, *)
            (* in which case p\sigma is executed *)
            (* - There could be several terms that matches the pattern. In this case, the possible terms are *)
            (* displayed using [show_terms], and the reduction is made. *)
            (* [match_terms_lst] contains all the terms in state.table that match the pattern with a substitution \sigma *)
            (* such that t\sigma is true will be on match_terms_lst *)
            do_get_full state n pat t p q proc frz dfrz

         | _ -> state
       end
    | I_O(tin, n_input, pat, q, _) -> (* Input on the private channel tin has been made *)
       begin
         match proc with
         | Output(_, t, p, _) ->
                do_rio t pat p q n_input (n) tin state
         | _ -> failwith "RIO"
       end
    | O_I(tc, n_output, t, p, _) -> (* Output on a the private channel tc has been made *)
       begin
         match proc with
         | Input(_, pat, q, _) ->
              do_rio t pat p q n n_output tc state
         | _ -> failwith "RIO"
       end
  in
  Menu_helper.delete_NamedProcess n_state

(* [do_one_reduction_step state n] Do one reduction step when clicking on the [n]-th columns *)
let rec do_one_reduction_step state n frz dfrz =
  Menu_helper.reset_forward_lst ();
  let proc = Menu_helper.get_proc state n in
  let aux state n proc =
    (* try *)
      if Menu_helper.has_div state then
        state
      else
        if Menu_helper.is_auto_reductible state proc n then
          do_auto_reduction state n proc frz dfrz
        else
          do_manual_reduction state n proc frz dfrz
  in
  match proc with
  | Repl(_, _) | Par(_, _) ->
     if no_more_proc () then
       let _ = GToolbox.message_box ~title:"Error" "Too many processes to do this reduction" in
       state
     else
       aux state n proc
  | _ -> aux state n proc

(* [do_all_auto_reduction state] Do all auto-reductions on state *)
let do_all_auto_reduction state frz dfrz =
  Menu_helper.reset_forward_lst ();
  let proc_nb = ref (List.length state.subprocess) in
  let rec aux state  = function
    | n when n = !proc_nb -> state
    | n ->
       if Menu_helper.has_div state then
         state
       else
         let proc = Menu_helper.get_proc state n in
         if Menu_helper.is_auto_reductible state proc n then
           begin
	     let state' = do_auto_reduction state n proc frz dfrz in
	     proc_nb := List.length state'.subprocess;
             aux state' n
	   end
         else
           aux state (n + 1)
  in
  aux state 0
