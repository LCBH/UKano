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
open Display
open GMain
(* This module writes everything in a buffer, on a Pango markup text form. *)
(* The next [module Gtk = LangDisp(LangGtk)] is giving displaying fonctions *)
(* "for free". The last [module ListOfProc] includes Gtk. It contains *)
(* the function [display_process proc] which returns a list of "Pango strings" *)
(* representing the process, and display_cpl_lst cpl_lst which is used to display *)
(* the public elements during the protocol interactive reduction. *)
module LangGtk =
  struct
    let buff = Buffer.create 1024

    let lst_ref = ref []

    let indentstring = "    "

    let add_buffer s = Buffer.add_string buff s

    let clear_buff () = Buffer.clear buff

    let newline() =
      match Buffer.length buff with
      | 0 -> ()
      | n ->
      lst_ref := (Buffer.contents buff)::(!lst_ref);
      clear_buff ()

    (* For the functor *)
    let wrap_if_necessary () = ()

    (* [print_string_from s pos0] adds the suffix of [s] starting from position [pos0] *)
    (*   to the buffer [buff], wrapping at spaces if necessary *)
    let rec print_string_from s pos0 =
      try
	let pos = (String.index_from s pos0 ' ') - pos0 in
	Buffer.add_substring buff s pos0 pos;
	Buffer.add_char buff ' ';
	print_string_from s (pos0 + pos + 1);
      with Not_found ->
	let s_len = (String.length s) - pos0 in
	Buffer.add_substring buff s pos0 s_len

    let print_string s =
      print_string_from s 0
      (* newline () *)

    (* We use Pango markup language for colors *)

    let start_color s = add_buffer "<span foreground=\""; add_buffer s; add_buffer "\">"

    let reset_color() = add_buffer "</span>"

    let start_bold() =
      add_buffer "<span font_weight=\"bold\">"

    let end_bold() =
      add_buffer "</span>"

    let display_occ n =
      start_color "green";
      print_string ("{" ^ (string_of_int n.Types.occ) ^ "}");
      reset_color()

    let display_occ_ref = display_occ

    let display_clause_link n =
      add_buffer ("clause " ^ (string_of_int n) ^ " ")

    let display_step_link n =
      add_buffer (string_of_int n)

    let start_cl = function
      | CFun | CName | CVar | CPred | CType | CQuery | CResult -> ()
      | CExplain -> start_color "magenta"
      | CKeyword -> start_color "blue"
      | CConn -> start_bold()
      | CProcess | CQTrue -> start_color "green"
      | CQFalse -> start_color "red"
      | CQDontKnow -> start_color "orange"
	    
    let end_cl = function
      | CFun | CName | CVar | CPred | CType | CQuery | CResult -> ()
      | CConn -> end_bold()
      | _ -> reset_color()

    let esc_s s = Glib.Markup.escape_text s

    let and_connective() =
      if !Param.typed_frontend then esc_s "&&" else esc_s "&"
    let or_connective() =
      if !Param.typed_frontend then esc_s "||" else esc_s "|"

    let impl_connective = esc_s "->"
    let red_connective = esc_s "=>"
    let before_connective = esc_s"==>"
    let diff_connective = esc_s "≠"
    let equal_connective = "="
    let eq1_connective = esc_s "<->"
    let eq2_connective = esc_s "<=>"
    let geq_connective = esc_s ">="
    let greater_connective = esc_s ">"
    let hline = "--------------------------------------------------------------\n"

    let convert_funname = function
      | "<>" -> esc_s "≠"
      | ">=" -> esc_s "≥"
      | "<=" -> esc_s "≤"
      | s -> esc_s s

    let convert_funname s = esc_s s

    let start_numbered_list() = ()
    let end_numbered_list() = newline ()
    let start_list() = ()
    let end_list() = newline()

    let clause_item n =
      let ns = string_of_int n in
      newline();
      add_buffer ("Clause " ^ ns ^ ": ")

    let lemma_item n =
      let ns = string_of_int n in
      newline();
      add_buffer ("Lemma " ^ ns ^ ": ")

    let history_item n =
      newline();
      add_buffer ((string_of_int n) ^ ". ")

    let basic_item () =
      newline()

    let dash_item () =
      newline();
      print_string " - "
	
    let process_link proc_name n =
      proc_name ^ " " ^(string_of_int n)
  end

module Gtk = LangDisp(LangGtk)

module GtkInteract =
  struct
    include Gtk
    open LangGtk

    (* Returns a string list representing the proc *)
    let display_process proc =
      display_process "  " proc;
      let s = !lst_ref in
      lst_ref := [];
      clear_buff();
      List.rev s
    (* returns a list of "Pango strings" representing proc *)
    (* let display_process proc = *)
    (*   List.rev (String.split_on_char '\n' (display_process2 proc)) *)

    let display_term term =
      display_term2 term;
      let s = Buffer.contents buff in
      clear_buff ();
      s

    let display_fact fact =
      display_fact2 fact;
      let s = Buffer.contents buff in
      clear_buff ();
      s

    let display_pattern pat =
      display_pattern pat;
      let s = Buffer.contents buff in
      clear_buff ();
      s

    let rec display_public public pub_vars =
      let rec aux acc public pub_vars =
        match public, pub_vars with
          [], [] -> List.rev acc
        | (recipe, mess)::tlp, var::tlv ->
           display_term2 var;
           if not (Terms.equal_terms recipe var) then
             begin
               print_string " = ";
               display_term2 recipe;
             end;
            if not
		(if !Param.bipro_i_mode then
		  (Terms.equal_terms recipe (Terms.choice_in_term 1 mess)) &&
		  (Terms.equal_terms recipe (Terms.choice_in_term 2 mess))
		else
		  Terms.equal_terms recipe mess) then
             begin
               print_string " = ";
               display_term2 mess
             end;
           let s = Buffer.contents buff in
           clear_buff ();
           aux (s::acc) tlp tlv
        | _ -> assert false
      in
      (* We reverse the list to execute the display of the tail of the list *)
      (* first so that the variables numbers are in increasing order *)
      aux [] (List.rev public) (List.rev pub_vars)
  end
