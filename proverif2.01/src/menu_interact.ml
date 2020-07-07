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
open Pitypes
open Types
open Terms

let debug_print s = ()
  (* print_endline s *)

let inc_proc_nb () = Reduction_interact.up_proc_nb
                       (Reduction_interact.get_proc_nb () + 1)

let dec_proc_nb () = Reduction_interact.up_proc_nb
                       (Reduction_interact.get_proc_nb ()- 1)

let model_build = ref false

(* TreeView *)

let _ = GtkMain.Main.init ()

(* [window_p] Main Window of the interactive mode *)
let window_p = GWindow.window
                 ~position:`CENTER
                 ~width:1000
                 ~height:680
                 ~title:"Proverif Interact"
                 ~allow_shrink:true ()

let _ = window_p#misc#modify_bg [(`NORMAL,`WHITE)]
(* For displaying traces *)
(* Main window to display trace *)
let win_trace = ref (GWindow.window ~title:"Trace" ())

let file_names = ref None

let get_file_names() =
  match !file_names with
    None ->
      let dot_file_name = Filename.temp_file "trace" ".dot" in
      let png_file_name = Filename.temp_file "trace" ".png" in
      file_names := Some (dot_file_name, png_file_name);
      (dot_file_name, png_file_name)
  | Some (dot_file_name, png_file_name) ->
      (dot_file_name, png_file_name)

(* The vertical box for the main widows. It will contain the menu *)
(* bar, the buttons, and the view representing the data *)
let main_vbox = GPack.vbox ~packing:window_p#add ()

(* [view] The treeview used to represent the data. It contains a column list *)
let view = GTree.view ~enable_search:false ()

let cols = new GTree.column_list

let col_lst =
  let rec create_n_cols acc = function
    | 0 -> List.rev acc
    | n ->
       let col = cols#add Gobject.Data.string in create_n_cols (col::acc) (n - 1)
  in
  create_n_cols [] (Reduction_interact.max_proc_nb + 3)

(* Menu *)
(* Callbacks are defined in menu_interact for some items *)
let menu_bar = GMenu.menu_bar ~packing:(main_vbox#pack) ()
let factory = new GMenu.factory menu_bar
let accel_group = factory#accel_group
let _ = window_p#add_accel_group accel_group

let file_menu = factory#add_submenu "File"
let factory_file = new GMenu.factory file_menu ~accel_group
let file_select_item = factory_file#add_item "Load File" ~key:_L
let quit_item = factory_file#add_item "Quit"

let reduct_menu = factory#add_submenu "Reduction"
let factory_reduct = new GMenu.factory reduct_menu ~accel_group
let next_auto_item = factory_reduct#add_item "Next auto-step" ~key:_N
let all_auto_item = factory_reduct#add_item "All auto-steps" ~key:_A
let step_back_item = factory_reduct#add_item "Backward" ~key:_B
let step_forw_item = factory_reduct#add_item "Forward" ~key:_F
let create_nonce_item = factory_reduct#add_item "New nonce" ~key:_C
let create_public_item = factory_reduct#add_item "Add a term to public" ~key:_P

let show_menu = factory#add_submenu "Show"
let factory_show = new GMenu.factory show_menu ~accel_group
let display_trace_item = factory_show#add_item "Display trace" ~key:_D
let show_tables_item = factory_show#add_item "Show/hide tables" ~key:_T
let show_events_item = factory_show#add_item "Show/hide events" ~key:_E

(* [some_items] Items that might need to be freeze *)
let some_items = [file_select_item; next_auto_item;
                  all_auto_item; step_back_item;
                  step_forw_item;
                  create_nonce_item;
                  create_public_item]

(* Button [b_all_auto] allows to make all auto-reduction *)
let b_all_auto = GButton.button ~label:"All auto-steps" ()
(* Button [b_bstep] allows to go a step Backward *)
let b_bstep = GButton.button ~label:"Backward" ()
(* Button [b_bstep] allows to go a step forward *)
let b_fstep = GButton.button ~label:"Forward" ()
(* Button [b_step_auto] allows to make the first auto-step *)
let b_step_auto = GButton.button ~label:"Next auto-step" ()
(* Button [b_new_name] allows to create a new name and add it into state.public *)
let b_new_nonce = GButton.button ~label:"New nonce" ()
(* Button [b_new_public] Allow to create a new public term and add it into state.public *)
let b_new_public = GButton.button ~label:"Add a term to public" ()
let all_buttons = [b_step_auto; b_all_auto; b_bstep; b_fstep;
                   b_new_nonce; b_new_public]

(* [diff_widgets] Widgets to freeze when processes with [choice] are *)
(* distinguishable (diff mode) *)
let div_widgets = [next_auto_item#coerce; all_auto_item#coerce;
                   create_nonce_item#coerce; create_public_item#coerce;
                   b_step_auto#coerce; b_all_auto#coerce; b_new_nonce#coerce;
                   b_new_public#coerce]

(* [sets_obj obj b] Set the sensitivity of [obj] according to [b] *)
let sets_obj obj b =
  ignore(obj#misc#set_sensitive b)

let sets_obj_lst b lst = List.iter (fun obj -> sets_obj obj b) lst

let label_box = GPack.hbox ~border_width:8 ()

let label_exn = GMisc.label ~markup:"" ~justify:`LEFT ()

(* |sets_b_bool b] Set the sensitivity for the main window according *)
(* to [b] and the current state *)
let sets_b_bool b =
  (* use to set the sensitivity of the widgets according to b *)
  let set_aux () =
    label_box#misc#hide();
    sets_obj_lst b some_items;
    sets_obj_lst b all_buttons;
    if not (Menu_helper.exists_auto ()) then
      sets_obj_lst false
          [b_all_auto#coerce; all_auto_item#coerce;
           b_step_auto#coerce; next_auto_item#coerce];
    if Menu_helper.is_first_step () then
      sets_obj_lst false
        [b_bstep#coerce; step_back_item#coerce];
    if !Param.trace_win_open = true then
      sets_obj display_trace_item false;
    if not (Menu_helper.exists_forward ()) then
        sets_obj_lst false
          [step_forw_item#coerce; b_fstep#coerce];
    if Menu_helper.exists_div () then (* Processes are not diff-equivalent *)
      begin
        label_box#misc#show();
        sets_obj_lst false div_widgets;
      end
    else
      match Menu_helper.get_io_c () with
	Other -> ()
      | I_O _ | O_I _ ->
	  label_box#misc#show();
	  label_exn#set_label "Please select the process with which you want to perform the communication:"
  in
  set_aux ();
  let sets_columns data =
    let mark_process n title click =
      let col = view#get_column n in
      col#set_clickable click;
      let l1 = GMisc.label ~markup:title () in
      col#set_widget (Some l1#coerce)
    in
    match  (Menu_helper.get_state()).comment with
    | RDiverges div ->
       begin
         let mess, proc1, proc2 = Menu_helper.show_div div in
         label_exn#set_label ("<b>The processes are not diff-equivalent:</b>\n" ^ mess);
        List.iteri (fun n (title, _) ->
            mark_process n title false) data.titles;
        match proc1, proc2 with
        | Some m', None  | None, Some m' ->
           mark_process (m' + 3) "<b>Divergence</b>" false
        (* + 3 since there is the first three columns *)
        | Some m', Some m'' ->
           mark_process (m' + 3) "<b>Divergence</b>" false;
           mark_process (m'' + 3) "<b>Divergence</b>" false
        | None, None -> ()
      end
    | _ ->
      List.iteri (fun n (title, t2) ->
          if n < 3 then
            mark_process n title false
          else
            mark_process n title b
        ) data.titles
  in
  if !model_build then
    sets_columns (Menu_helper.get_data())

(* [frz ()] Freeze the necessaries elements in the main window *)
let frz () = sets_b_bool false
(* [dfrz ()] De-freeze the necessaries elements in the main window *)
let dfrz () = sets_b_bool true

(* [delete_trace_files ()] Delete the files associated to the trace if it's open *)
let delete_trace_files () =
  match !file_names with
    None -> ()
  | Some (dot_file_name, png_file_name) ->
      Unix.unlink(dot_file_name);
      Unix.unlink(png_file_name);
      file_names := None

(* [destroy_win_trace ()] Callback function to destroy trace window. *)
let destroy_win_trace () =
  if !Param.trace_win_open then
    begin
      delete_trace_files ();
      !win_trace#destroy();
      sets_obj display_trace_item true;
      Param.trace_win_open := false
    end

let state_destroyed = ref false

(* [check_supported p] verifies that all needed features are supported by the simulator *)
let rec check_supported = function
    | Nil -> ()
    | Par(p, q)
    | Let(_, _, p, q, _)
    | Get(_, _, p, q, _)
    | Test(_, p, q, _) -> check_supported p; check_supported q
    | Restr(_,_,p, _)
    | Repl(p, _)
    | Input(_, _, p, _)
    | Event(_,_, p, _)
    | Insert(_, p, _)
    | Phase(_, p, _)
    | NamedProcess(_, _, p)
    | Output(_, _, p, _) -> check_supported p
    | LetFilter _ -> Parsing_helper.user_error "let...suchthat not supported by the simulator"
    | Barrier _ | AnnBarrier _ -> Parsing_helper.user_error "sync not supported by the simulator"

(* [public_build l] Initial attacker knowledge *)
let rec public_build l =
  match l with
  | [] -> []
  | h::l' ->
    if not h.f_private then
      let t = (FunApp(h,[])) in
        (t, t)::(public_build l')
    else
      public_build l'

(* [reduc_state_of_proc proc] Return the term Pitypes.reduc_state build from [proc] *)
let reduc_state_of_proc proc =
  let public = public_build (!Param.current_state).pi_freenames in
  {goal = NoGoal;
   subprocess = [Menu_helper.sub_of_proc proc];
   public = public;
   pub_vars = List.map fst public;
   tables = [];
   prepared_attacker_rule = [];
   io_rule = [];
   previous_state = None; hyp_not_matched = [];
   assumed_false = [];
   current_phase = 0;
   comment = RInit;
   events = [];
   barriers = []
  }

(* [anal_file s] Parse the file of path [s]. Update the current state with the *)
(* result of this parsing. Show a dialog box with an error message if there  *)
(* is a problem during the parsing, and raise [Menu_helper.WrongChoice]. *)
(* If there is the symbol [choice] present  *)
(* in the input file, a window pop-up first to ask the user if he wants to simulate the *)
(* left side of the process, the right side, or the biprocess. *)
let rec anal_file s0 =
  Menu_helper.reset_env();
  state_destroyed := true;
  let build_state_from p =
    check_supported p;
    let p1 =
      if !Param.has_choice then
	begin
	  let i_choice =
            Menu_helper.question_box
              "Choice/diff present in your process"
              ["Left"; "Right"; "Biprocess"]
              ("Would your like to:"
               ^ "\n - Simulate a component of choice/diff (Left or Right)?"
               ^ "\n - Simulate the biprocess (biprocess)?")
               in
	  if i_choice = 0 then
	    raise Menu_helper.WrongChoice
          else if i_choice <= 2 then
	    Terms.choice_in_proc i_choice p
          else
            begin
              Param.bipro_i_mode := true;
              p
            end
	end
      else
	p
    in
    Menu_helper.update_cur_state (Menu_helper.delete_NamedProcess (reduc_state_of_proc p1))
  in
  try
    let s =
      (* Preprocess .pcv files with m4 *)
      let s_up = String.uppercase_ascii s0 in
      if Terms.ends_with s_up ".PCV" then
	let s' = Filename.temp_file "pv" ".pv" in
	let res = Unix.system("m4 -DProVerif " ^ s0 ^ " > " ^ s') in
	match res with
          Unix.WEXITED 0 -> s'
	| _ -> Parsing_helper.user_error ("Preprocessing of " ^ s0 ^ " by m4 failed.")
      else
	s0
    in
    Param.typed_frontend := true;
    let pi_state = Pitsyntax.parse_file s in
    let pi_state1 = Simplify.prepare_process pi_state in
    TermsEq.record_eqs_with_destr pi_state1;
    Destructor.check_deterministic pi_state1.pi_destructors_check_deterministic;
    Param.current_state := pi_state1;
    (* Delete trailling [-1] in binders *)
    (* Allow the user to choose which process simulates in case second_p0 is not Null *)
    (* (i.e. when equivalence between process is made *)
    let warnings = Parsing_helper.get_warning_list() in
    if warnings != [] then
      begin
	let messages = String.concat "" (List.map (fun (mess, ext) ->
	  (Parsing_helper.get_mess_from true "Warning: " mess ext) ^ "\n") warnings) in
	ignore (Menu_helper.question_box "Warnings" ["OK"] messages)
      end;
    begin
      match pi_state1.pi_process_query with
      | SingleProcess(p,_) | SingleProcessSingleQuery(p,_) ->
	  build_state_from p.proc
      | Equivalence(p1, p2) ->
         begin
           match  Menu_helper.question_box "Choose a process to simulate" ["First"; "Second"] "Simulate first or second process ?" with
           | 1 -> build_state_from p1.proc;
           | 2 -> build_state_from p2.proc;
           | _ -> raise Menu_helper.WrongChoice
         end
    end;
    (* Remove the preprocessed temporary file when everything went well *)
    if s0 <> s then
       Unix.unlink s;
    state_destroyed := false
  with
  | Parsing_helper.InputError (mess, ext) ->
     Menu_helper.input_error_box true mess ext;
     Menu_helper.reset_env();
     raise Menu_helper.WrongChoice

(* [do_all_auto_reduction ()] Do all possible auto reductions on the current state. *)
(* Return the modified state *)
let rec do_all_auto_reduction () =
  let state = Menu_helper.get_state () in
  let n_state = Reduction_interact.do_all_auto_reduction state frz dfrz in
  Menu_helper.update_cur_state n_state

(* [create_model ()] Create the list_store from the current state and fill it. *)
(* Return [(data, store)], where [data] contains the data associated to  *)
(* the current state and [store] is the [GTree.list_store] used to display *)
(* these data *)
let create_model () =
  model_build := true;
  let data = Menu_helper.get_data () in
  if not (Menu_helper.exists_auto()) then
      sets_obj_lst false
        [b_all_auto#coerce; all_auto_item#coerce;
         b_step_auto#coerce; next_auto_item#coerce];
  if Menu_helper.is_first_step () then
      sets_obj_lst false [b_bstep#coerce; step_back_item#coerce];
  if not (Menu_helper.exists_forward ()) then
      sets_obj_lst false [b_fstep#coerce; step_forw_item#coerce];
  let store = GTree.list_store cols in
  let iter = ref (store#append ()) in
  let all_empty = ref true in
  let rec fill_store acc n lls =
    match lls with
      [] ->
        begin
          match acc with
            [] -> ()
          | acc -> if !all_empty then () else
              begin
                all_empty:= true;
                iter := store#append ();
                fill_store [] 0 (List.rev acc)
              end
        end
    | ls::tl_lls ->
       begin
         match ls with
           [] ->
           store#set ~row:!iter ~column:(List.nth col_lst n) "";
           fill_store ([]::acc) (n + 1) tl_lls
         | s::tl_s ->
            begin
              all_empty:= false;
              store#set ~row:!iter ~column:(List.nth col_lst n) s;
              fill_store (tl_s::acc) (n + 1) tl_lls
            end
       end
  in
  let lls = data.tables_lst::data.events_lst::data.public_lst::data.proc_llst in
  fill_store [] 0 lls;
  (data, store)

(* [do_one_reduction_step n ()] Do one reduction step on the [n]-th subprocess of the current state. *)
(* Modify the current state *)
let do_one_reduction_step n () =
  let state = Menu_helper.get_state () in
  try
    let n_state = Reduction_interact.do_one_reduction_step state n frz dfrz in
    Menu_helper.update_cur_state (n_state)
  with
    Menu_helper.WrongChoice -> ()
  | Parsing_helper.InputError(mess, extent) -> Menu_helper.input_error_box false mess extent

(* [next_auto_step ()] Callback function to make the first next auto reduction step. *)
(* Modify the current state *)
let next_auto_step () =
  let state = Menu_helper.get_state () in
  let rec aux state n = function
      [] -> assert false
    | sub::tl ->
       let p = Menu_helper.proc_of_sub sub in
       if Menu_helper.is_auto_reductible state p n then
         do_one_reduction_step n ()
       else
         aux state (n + 1) tl
  in
  aux state 0 state.subprocess

(* [dialog_box title string ()] Create a dialog box with title *)
(* [title], displaying [string]. *)
(* Return the string entered by the user, *)
(* raise WrongChoice if no string is entered. *)
let dialog_box title string () =
  let db = GToolbox.input_string ~title ~text:"" string in
  match db  with
    Some s -> s
  | None -> raise Menu_helper.WrongChoice

(* [create_new_nonce ()] Callback function to create a nonce and add it to the current state. *)
(* Modify the current state *)
let create_new_nonce () =
  let state = Menu_helper.get_state () in
  let return state ty =
    let n = Terms.create_name ~orig:false "n" ([], ty) false in
    let t = FunApp(n, []) in
    Menu_helper.reset_forward_lst ();
    Menu_helper.update_cur_state
      { state with
        public = (t, t)::state.public;
        pub_vars = t::state.pub_vars;
        previous_state = Some(state);
        comment = RRestrAtt(t)}
  in
  try
    if not (Param.get_ignore_types ()) then
      let t =
        dialog_box "Enter the type" "Enter the type of the new nonce" ()
      in
      let ty = List.find (fun {tname = t'} -> t = t') (!Param.current_state).pi_types in
      return state ty
    else
      return state Param.any_type
  with
    Not_found ->
     let _ =  Menu_helper.question_box "Error" ["Ok"] "Type not defined"  in
     ()
  | Menu_helper.WrongChoice -> ()

let create_new_public () =
  let state = Menu_helper.get_state () in
  try
    Terms.auto_cleanup (fun () ->
        let r = Menu_helper.get_recipe "" "Give a recipe to add to the public\nelements of the current state" in
        let exp = Menu_helper.expand_recipe state.pub_vars state.public r in
        try
          let t = Menu_helper.evaluates_term_all_mode exp in
	  let recipe_term_list = Menu_helper.decompose_term_all_mode (r, t) in
	  let state' = Menu_helper.add_public_list_dec_all_mode state recipe_term_list in
          if state' == state then
            ignore (Menu_helper.question_box "Error" ["Ok"] "Term (or its components after decomposing data constructors) already in the public elements of the current state")
          else
	    let (new_pub, pub_vars) = Menu_helper.get_new_vars state state'.public in
            Menu_helper.reset_forward_lst ();
            let n_state =
              { state' with
                   pub_vars = pub_vars;
                   previous_state = Some state;
                   comment = RAddpub new_pub
              }
            in
            Menu_helper.update_cur_state n_state
        with
        | Terms.Unify ->
	    (* raised by [evaluates_term_all_mode] *)
	    ignore(Menu_helper.question_box "Error" ["Ok"] "The evaluation of the recipe fails")
        | Reduction_bipro.FailOnlyOnSide i ->
	    (* raised by [evaluates_term_all_mode] *)
            let n_state = Menu_helper.display_div state (DFail(i, r, exp)) in
            Menu_helper.update_cur_state n_state
        | Menu_helper.Div div ->
	    (* raised by [add_public_list_dec_all_mode] *)
	    let n_state = Menu_helper.display_div state div in
	    Menu_helper.update_cur_state n_state
      )
  with
    Menu_helper.WrongChoice -> ()

(* [one_step_backward ()] Callback function to make one backward reduction step .*)
(* Modify the current state. *)
let rec one_step_backward () =
  Menu_helper.set_io_c Other;
  let state = Menu_helper.get_state () in
  match state.previous_state, state.comment with
  | None, _ -> ()
     (* Menu_helper.update_cur_state state *)
  | Some state', RNamedProcess(_, _, _) ->
     (* If the current state is a NamedProcess step, we call the function on the previous state *)
     Menu_helper.update_cur_state state';
     one_step_backward ()
  | Some state', _ ->
     Menu_helper.add_to_forwards_lst state;
     Menu_helper.update_cur_state state'

let show_tables_bool = ref false

let show_events_bool = ref false

let click_on_show bool n =
  let col = view#get_column n in
  col#set_visible (not bool);
  not bool

(* [update_titles data] Update titles of the view according to data. *)
(* RIO reductions are made in two steps. First the user click on a column containing a private *)
(* input (respectively output). [Menu_helper.get_io_c ()] is then equal to [I_O(tou, _, _, _)], *)
(* (resp. [O_I(tin, _, _, _)]) and the call to [update_titles view data] will only show  *)
(* the output processes on [tou] (resp. input on [tin]). *)
(* In the case of a biprocess simulation, the calls to *)
(*  [equal_io_oi] might raise exceptions *)
(* if there are processes that diverge (diff case) *)
let update_titles data =
  let t1 = Menu_helper.get_io_c () in
  let aux n title t2 =
   let col = view#get_column n in
    col#set_title title;
    if (t1 = Other) || (Menu_helper.equal_io_oi t1 t2) then
      begin
        if n = 0 then
          col#set_visible !show_tables_bool
        else
          if n = 1 then
            col#set_visible !show_events_bool
          else
              col#set_visible true
      end
    else
      col#set_visible false
  in
  try
    List.iteri (fun n (title, t2) ->
        aux n title t2) data.titles;
  with Menu_helper.Div(exn) ->
    (* Should never happen: all such divergence cases should be detected
       in Reduction_interact.do_manual_reduction
       (subfunction quest_io, case 2) *)
    assert false

(* [ends_with s sub] Return true if [sub] if a suffix of [s]. *)
let ends_with s sub =
  let l_s = String.length s in
  let l_sub = String.length sub in
  (l_s >= l_sub) && (String.sub s (l_s - l_sub) l_sub = sub)

let _ = window_p#connect#destroy ~callback:(fun () ->
            if !Param.trace_win_open then
              delete_trace_files ();
            exit 0)
(* let _ = window_p#set_default_size ~width:1000 ~height:480 *)

(* [img] Image to put inside the trace box (the vbox inside the trace window). *)
let img = ref (GMisc.image ())

let width = 400
let heigth = 800

let png_width = ref width
let png_heigth = ref heigth

let b_incr = ref (GButton.button ~label:"+" ())
let b_decr = ref (GButton.button ~label:"-" ())

let reset_png_size () =
  png_width := width;
  png_heigth := heigth

let refresh_img () =
  let state = Menu_helper.get_state () in
  if !Param.trace_win_open = true then
    begin
      let (dot_file_name, png_file_name) = get_file_names() in
      let state_conv = Convert_repl.convert_repl state in
      Display.AttGraph.write_state_to_dot_file dot_file_name Display.term_to_term Reduction_bipro.noninterftest_to_string state_conv (Menu_helper.has_div state);
      match Sys.command ("dot -Tpng " ^ dot_file_name ^ " -o " ^ png_file_name) with
        0 ->
         begin
           let pixbuf = GdkPixbuf.from_file_at_size png_file_name !png_width !png_heigth in
           !img#set_pixbuf pixbuf;
         end
      | _ ->
          let _ =  Menu_helper.question_box "Error" ["Ok"] "The call to Graphviz failed. Please check that Graphviz is correctly installed.\n(The program \"dot\" must be in the PATH.)" in
          Param.trace_win_open := false
    end

(* Generate functions to increase or decrease the size of the png *) (* image of the trace *)
let aux_png b_incr b_decr op comp i ()  =
  let d = int_of_float ((float_of_int !png_width)  *. 0.25) in
  let c = op !png_width d in
  if comp c i
  then
    begin
      sets_obj b_decr true;
      sets_obj b_incr true;
      png_width := op !png_width d;
      png_heigth := op !png_heigth d;
      if not (comp (op c d) i) then
        sets_obj b_decr false
    end
  else
    begin
      sets_obj b_incr true;
      sets_obj b_decr false
    end;
  refresh_img ()

let incr_png b_incr b_decr = aux_png b_incr b_decr (+) (<) 3200

let decr_png b_incr b_decr = aux_png b_incr b_decr (-) (>) 100

let filter string =
  let patterns = "*." ^ string in
  GFile.filter ~name:patterns ~patterns:[patterns] ()

let dir = ref (Sys.getcwd ())

let update_dir = function
  | None -> ()
  | Some s -> dir := s


(* [display_trace refresh_img ()] Callback function to display graph trace. *)
let display_trace refresh_img () =
  reset_png_size ();
  Param.trace_win_open := true;
  let (dot_file_name, png_file_name) = get_file_names() in
  (* [callback_save()] Callback dialog function to save the trace file in .png. *)
  let rec callback_save () =
    let ok_cb dialog  () =
      match dialog#filename with
        None ->
          let _ =  Menu_helper.question_box "Error" ["Ok"] "Please use .png, .pdf, .jpg, or .eps format to save the file." in
          dialog#destroy ();
          callback_save()
      | Some s ->
         begin
           update_dir (dialog#current_folder);
           let s_up = String.uppercase_ascii s in
           if (ends_with s_up ".PNG") || (ends_with s_up ".PDF") || (ends_with s_up ".JPG") || (ends_with s_up ".EPS") then
             begin
	       let last_3 = String.lowercase_ascii (String.sub s (String.length s - 3) 3) in
               match Sys.command ((!Param.interactive_dot_command) ^ " -T" ^ last_3
                                  ^ " " ^ dot_file_name ^ " -o "
                                  ^ s)
               with
                 0 -> dialog#destroy ();
               | _ ->
		   let _ =  Menu_helper.question_box "Error" ["Ok"] ("The call to " ^ (!Param.interactive_dot_command) ^ " failed. Please check that it is correctly installed.\n(The program \"" ^ (!Param.interactive_dot_command) ^ "\" must be in the PATH.)") in
                   dialog#destroy ()
             end
           else
             let _ =  Menu_helper.question_box "Error" ["Ok"] "Please use .png, .pdf, .jpg, or .eps format to save the file." in
             dialog#destroy();
             update_dir (dialog#current_folder );
             callback_save ()
         end
    in
    let dialog = GWindow.file_chooser_dialog ~action:`SAVE  ~title:"Save trace. Please specify the extension (.png, .pdf, .jpg, or .eps) in the file name" () in
    frz();
    update_dir (dialog#current_folder);
    let _ = dialog#set_current_folder (!dir) in
    dialog#add_button_stock `CANCEL `CANCEL;
    dialog#add_select_button_stock `SAVE `SAVE;
    List.iter (fun t -> dialog#add_filter (filter t))
      ["png"; "pdf"; "jpg"; "eps"];
    begin
      match dialog#run () with
      | `SAVE ->
         begin
           match dialog#filename with
           | None -> ()
           | Some s ->
              ok_cb dialog ();
         end
    | `DELETE_EVENT | `CANCEL -> dialog#destroy ()
    end;
    dfrz()
  in
  let create_shortcuts win_trace =
     ignore(win_trace#event#connect#key_press ~callback:
      begin
        fun ev ->
        let key = GdkEvent.Key.keyval ev  in
        if key = GdkKeysyms._KP_Add || key = Char.code('+') then
          incr_png !b_incr !b_decr ();
        if key = GdkKeysyms._KP_Subtract || key = Char.code ('-') then
          decr_png !b_incr !b_decr ();
        if GdkEvent.Key.keyval ev = GdkKeysyms._Escape then
          win_trace#destroy();
        false
      end);
  in
  (* [create_button ()] Used for adding buttons in the trace window *)
  let create_button () =
    b_incr := GButton.button ~label:"+" ();
    b_decr := GButton.button ~label:"-" ();
    let bbox = GPack.button_box `HORIZONTAL  ~border_width:5 ~layout:`START
                 ~child_height:5 ~child_width:5  ~spacing:5 () in
    bbox#add !b_incr#coerce;
    bbox#add !b_decr#coerce;
    let _ = !b_incr#connect#clicked ~callback:(incr_png !b_incr !b_decr) in
    let _ = !b_decr#connect#clicked ~callback:(decr_png !b_incr !b_decr) in
    create_shortcuts !win_trace;
    bbox#coerce
  in
  (* [create_win_trace ()] Create the main window trace, return [trace_box], the vbox *)
  (* inside the window trace which contains the image of the trace *)
  let create_win_trace () =
    Param.trace_win_open := true;
    (* Set the sensitivity of display trace item to false *)
    let t = display_trace_item in
    sets_obj t false;
    win_trace := GWindow.window ~title:"Trace" ();
    let _ = !win_trace#connect#destroy ~callback:destroy_win_trace in
    !win_trace#set_default_size ~width:800 ~height:480;
    let trace_box = GPack.vbox ~packing:(!win_trace#add)  () in
    img := GMisc.image ();
    let menu_bar = GMenu.menu_bar ~packing:trace_box#pack () in
    let factory = new GMenu.factory menu_bar in
    let accel_group = factory#accel_group in
    let _ = !win_trace#add_accel_group accel_group in
    let save_menu = factory#add_submenu "Save" in
    let factory_save = new GMenu.factory save_menu ~accel_group in
    let _ = factory_save#add_item "Save File" ~key:_S ~callback:callback_save in
    trace_box
  in
  (* [create_trace state trace_box] Create the trace from cur_state, insert it in trace_box, *)
  (* display the trace window. If graphviz is not installed, display an error dialog box. *)
  let create_trace (trace_box:GPack.box) =
    let state = Menu_helper.get_state () in
    let state_conv = Convert_repl.convert_repl state in
    Display.AttGraph.write_state_to_dot_file dot_file_name Display.term_to_term Reduction_bipro.noninterftest_to_string state_conv (Menu_helper.has_div state);
    match Sys.command ((!Param.interactive_dot_command) ^ " -Tpng " ^ dot_file_name ^ " -o " ^ png_file_name) with
      0 ->
	let pixbuf = GdkPixbuf.from_file_at_size png_file_name !png_width !png_heigth in
        !img#set_pixbuf pixbuf;
        trace_box#pack (create_button ());
        let win_scrolled_trace = GBin.scrolled_window ~packing:(trace_box#pack ~expand:true)  () in
        win_scrolled_trace#add_with_viewport !img#coerce;
        (* trace_box#pack !img#coerce; *)
        !win_trace#show ()
    | _ ->
       let _ =  Menu_helper.question_box "Error" ["Ok"] ("The call to " ^ (!Param.interactive_dot_command) ^ " failed. Please check that it is correctly installed.\n(The program \"" ^ (!Param.interactive_dot_command) ^ "\" must be in the PATH.)") in
       ()
  in
  let trace_box = create_win_trace () in
  create_trace (trace_box)

(* [update update_view up_fun ()] Update the current state applying *)
(* [update_cur_state (up_fun ())]. Update the view according to the new state *)
(* using [update_view]. Create the new model, and associate it with view. *)
(* Refresh the trace is the trace window is open. *)
let update update_view up_fun () =
  let proc_nb_cur state = List.length state.subprocess in
  frz();
  let old_state = Menu_helper.get_state () in
  up_fun ();
  let n_state = Menu_helper.get_state () in
  let diff = proc_nb_cur n_state - proc_nb_cur old_state in
  update_view diff;
  let (data, n_model) = create_model () in
  update_titles data;
  view#set_model None;
  let _ = view#set_model (Some(n_model#coerce)) in
  refresh_img ();
  dfrz();
  ()

(* [update_view diff] Add or suppress [diff] columns to the view. *)
let rec update_view diff  =
  (* [add_column_at n] Add a column at position n *)
  let add_column_at n =
    (* [markup] attribute means that we use Pango markup language in the cell, instead *)
    (* of a simple string. Used to color keywords when displaying processes *)
    let col = GTree.view_column ~renderer:(GTree.cell_renderer_text [], ["markup", List.nth col_lst n]) () in
    col#set_clickable true;
    let _ = col#connect#clicked
             ~callback:(update update_view (do_one_reduction_step (n- 3))) in
    let _ = view#append_column col in
    col#set_resizable true;
  in
  (* [add_n_columns n] Add n columns at the end of the view. *)
  (* Update the current number of processes *)
  let rec add_n_columns n  = match n with
    | 0 -> ()
    | n ->
       begin
         inc_proc_nb();
         add_column_at (Reduction_interact.get_proc_nb () + 2);
         add_n_columns (n - 1)
       end
  in
  (* [remove_n_columns n] Remove n columns at the end of the view. *)
  (* Update the current number of processes *)
  let rec remove_n_columns n = match n with
    | 0 -> ()
    | n ->
       begin
         let _ = view#remove_column (view#get_column (Reduction_interact.get_proc_nb () + 2 )) in
         dec_proc_nb ();
         remove_n_columns (n - 1)
       end
  in
  match diff with
  | n when n < 0  ->
     remove_n_columns (-diff)
  | _ ->
     add_n_columns diff

(* The function use to refresh the view *)
let update_refresh = update update_view

(* [callback_when_view_exists filew ()] Callback function used by  *)
(* [file_selection_window callback ()] to create a new model and associated to *)
(* to the existing view.  *)
let rec callback_when_view_exists filew () =
  Menu_helper.set_io_c Other;
  anal_file filew;
  let nop = Reduction_interact.get_proc_nb () in
  let nnop = 1 in
  let diff = nnop - nop in
  update_view diff;
  let (data, n_model) = create_model () in
  update_titles data;
  view#set_model None;
  ignore(view#set_model (Some(n_model#coerce)))

(* [callback_create_view create_view filew ()] Callback function used by  *)
(* [file_selection_window callback ()] to create the first view and the model associated to *)
(* it after the parsing of the input file. *)
let rec callback_create_view create_view filew () =
  model_build := true;
  try
    anal_file filew;
    let (data, model) = create_model () in
    let _ = create_view data model in
    ()
   with
   | exc -> model_build := false; raise exc

(* [file_selection_window callback ()] Open a file selection *)
(* dialog window. The [callback] function *)
(* is instanced either by [callback_create_view create_view] *)
(* to create the view, or by *)
(* [callback_when_view_exists] if the view already exists. *)
let rec file_selection_window callback () =
  frz();
  (* Close trace windows if it's open *)
  if !Param.trace_win_open then
    begin
      !win_trace#destroy ();
      Param.trace_win_open := false
    end;
  let dialog = GWindow.file_chooser_dialog ~action:`OPEN ~title:"Open File" () in
  dialog#add_button_stock `CANCEL `CANCEL;
  dialog#add_select_button_stock `OPEN `OPEN;
  let _ = dialog#set_current_folder (!dir) in
  List.iter (fun t -> dialog#add_filter (filter t))
      ["pv"; "pcv"];
  begin
    match dialog#run () with
    | `OPEN ->
       begin
         match dialog#filename with
         | None -> ()
         | Some s ->
            update_dir (dialog#current_folder);
            dialog#destroy();
           begin
             try
               callback s ();
             with
             | _ ->
                dialog#destroy ();
                file_selection_window callback ()
           end;
       end
    | `DELETE_EVENT | `CANCEL ->
       if !state_destroyed then
	  window_p#destroy ()
	else
	  dialog#destroy ()
  end;
  dfrz()

(* [create_button_box ()] Used for adding buttons in the main window. *)
let create_button_box () =
  (* [ibox] used to control the expansion of the buttons, best way ? *)
  let ibox = GPack.hbox () in
  let bbox = GPack.button_box `HORIZONTAL
      ~spacing:3 ~packing:(ibox#pack ~padding:3 ~expand:false) () in
  List.iter (fun t -> bbox#pack ~fill:false t) [b_step_auto#coerce; b_all_auto#coerce; b_bstep#coerce; b_fstep#coerce; b_new_nonce#coerce; b_new_public#coerce];
  (* add callbacks to buttons. *)
  List.iter (fun (b, c) -> ignore(b#connect#clicked ~callback:c))
    [(b_all_auto, update_refresh (do_all_auto_reduction));
     (b_bstep, update_refresh one_step_backward);
     (b_fstep, update_refresh Menu_helper.one_step_forward);
     (b_step_auto, update_refresh (next_auto_step));
     (b_new_nonce, update_refresh create_new_nonce);
     (b_new_public, update_refresh create_new_public)];
  ibox#coerce

(* [click_on_tables view ()] Callback function for Show/hide tables item *)
let click_on_tables view () =
  show_tables_bool := click_on_show !show_tables_bool 0

(* [click_on_events view ()] Callback function for Show/hide events item *)
let click_on_events view () =
  show_events_bool := click_on_show !show_events_bool 1

let set_menu_items () =
  (* Connect callbacks to menu items *)
  List.iter (fun (i, c) -> ignore(i#connect#activate ~callback:c))
    [(file_select_item, file_selection_window (callback_when_view_exists));
     (next_auto_item, update_refresh (next_auto_step));
     (quit_item, window_p#destroy);
     (all_auto_item, update_refresh (do_all_auto_reduction));
     (step_back_item, update_refresh one_step_backward);
     (step_forw_item, update_refresh Menu_helper.one_step_forward);
     (create_nonce_item, update_refresh create_new_nonce);
     (create_public_item, update_refresh create_new_public);
     (display_trace_item, display_trace refresh_img);
     (show_tables_item, click_on_tables view);
     (show_events_item, click_on_events view)]

(* [window_menu ()] Add buttons, menu, and view in the main vbox. *)
let window_menu () =
  set_menu_items ();
  let main_s = GBin.scrolled_window () in
  let buttons = create_button_box () in
  main_vbox#set_homogeneous false;
  main_vbox#pack  ~expand:false buttons#coerce;
  main_vbox#pack ~expand:false label_box#coerce;
  label_box#pack ~expand:false label_exn#coerce;
  main_vbox#pack ~expand:true main_s#coerce;
  main_s#add view#coerce

(* Return the view correctly filled with respect to the data and  *)
(* model *)
let rec create_view data model =
  view#set_model (Some model#coerce);
  let _ = window_menu () in
  (* Create the view columns. "markup" is used for Pango language. *)
  ignore(List.iteri (fun n d ->
    let col = GTree.view_column ~title:d ~renderer:(GTree.cell_renderer_text [], ["markup", List.nth col_lst n]) () in
    if n <= 2 then
      begin
        (* Tables, events, and public columns are not clickable *)
        col#set_clickable false;
        if n <= 1 then
          (* By default, events and public columns are not visible *)
          col#set_visible false
      end
    else
      begin
        col#set_clickable true;
        (* The callback reduction step is done on n - 3 since *)
        (* there is the columns public, events, and tables. *)
        ignore(col#connect#clicked ~callback:(update_refresh (do_one_reduction_step (n - 3))));
      end;
    ignore (view#append_column col);
    col#set_resizable true;
  ) (List.map fst data.titles));
  window_p#show();
  dfrz();
  GMain.Main.main ();
  view

(* [main_window fileopt] If [fileopt = None] launch the file *)
(* dialog box which allows the user to choose the *)
(* file containing the process to emulate. *)
(* Otherwise [fileopt = Some s], and the emulator starts *)
(* emulating the process represented in file of path [s]. *)
(* If [s] does not exists, or the parsing went wrong, acts *)
(* like in the case [fileopt = None] *)
let main_window fileopt =
  Param.allow_tilde := true;
  Parsing_helper.interactive_mode := true;
  match fileopt with
    None ->
      let _ = file_selection_window (callback_create_view create_view) () in
      ()
  | Some file ->
     try
       update_dir (Some(Filename.dirname file));
       callback_create_view create_view file ()
     with
     | _ -> file_selection_window (callback_create_view create_view) ()
