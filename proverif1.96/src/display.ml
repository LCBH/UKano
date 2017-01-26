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
open Types
open Pitypes


(* Helper function to make the display more readable: we abbreviate names with
   just a constant symbol. *)

let find_abbrev abbrev_table t =
  let rec find_abbrev_rec = function
  [] ->
    begin
      match t with
	FunApp(f,l) ->
	  let f_base_name =
	    try
	      let pos = String.rindex f.f_name '_' in
	      String.sub f.f_name 0 pos
	    with Not_found -> f.f_name
	  in
	  let t'' = Var (Terms.new_var f_base_name (snd f.f_type)) in
	  abbrev_table := (t'',t) :: (!abbrev_table);
	  t''
      | _ -> Parsing_helper.internal_error "Function application expected in find_abbrev"
    end
    | (t'',t')::l ->
       if Terms.equal_terms t t' then
	 t''
       else
	 find_abbrev_rec l
  in
  find_abbrev_rec (!abbrev_table)

let rec abbrev_term abbrev_table = function
Var { link = TLink t } -> abbrev_term abbrev_table t
  | Var { link = VLink v } -> (Var v)
  | Var v -> Var v
  | FunApp(f,l) ->
     let l' = List.map (abbrev_term abbrev_table) l in
     match f.f_cat, l with
       (Name _), (_::_) ->
	  (* Abbreviate names with arguments *)
	 find_abbrev abbrev_table (FunApp(f,l'))
     | _ -> FunApp(f,l')

let abbrev_fact abbrev_table = function
Pred(p,l) -> Pred(p, List.map (abbrev_term abbrev_table) l)
  | Out(t,l) -> Out(abbrev_term abbrev_table t,
		    List.map (fun (v,t) -> (v, abbrev_term abbrev_table t)) l)

let abbrev_constra abbrev_table = List.map (List.map (function
Neq(t1,t2) -> Neq(abbrev_term abbrev_table t1, abbrev_term abbrev_table t2)))

(* Return a new rule and an association table where the names are abbreviated *)

let abbreviate_rule ((hyp, concl, hist, constra)) =
  let abbrev_table = ref [] in
  let rule' = (List.map (abbrev_fact abbrev_table) hyp, abbrev_fact abbrev_table concl,
	       hist, abbrev_constra abbrev_table constra)  in
  (!abbrev_table,rule')

(* Return an abbreviated derivation and an association table where the names are abbreviated *)

let abbreviate_derivation tree =
  let abbrev_table = ref [] in
  let rec abbrev_tree tree =
    { desc =
        begin
	  match tree.desc with
	    (FEmpty | FHAny | FRemovedWithProof _) as x -> x
	  |	FRule(n, descr, constra, hl) ->
	     FRule(n, descr, abbrev_constra abbrev_table constra, List.map abbrev_tree hl)
	  |	FEquation h -> FEquation (abbrev_tree h)
        end;
      thefact = abbrev_fact abbrev_table tree.thefact
    }
  in
  let tree' = abbrev_tree tree in
  (!abbrev_table, tree')

type cl = CFun | CName | CVar | CPred | CType | CExplain | CKeyword | CConn

module type LangSig =
sig
  val indentstring : string
  val print_string : string -> unit
  val display_occ : int -> unit
  val display_occ_ref : int -> unit
  val display_clause_link : int -> unit
  val display_step_link : int -> unit
  val start_cl : cl -> unit
  val end_cl : cl -> unit
  val convert_funname : string -> string
  val and_connective : unit -> string
  val or_connective : unit -> string
  val impl_connective : string
  val red_connective : string
  val before_connective : string
  val diff_connective : string
  val equal_connective : string
  val eq1_connective : string
  val eq2_connective : string
  val hline : string
  val start_numbered_list : string
  val end_numbered_list : string
  val start_list : string
  val end_list : string
  val clause_item : int -> unit
  val history_item : int -> unit
  val basic_item : unit -> unit
  val newline : unit -> unit
end

module LangText : LangSig =
struct

  let indentstring = "    "

  let print_string = Pervasives.print_string

  let color_black = 30
  let color_red = 31
  let color_green = 32
  let color_yellow = 33
  let color_blue = 34
  let color_magenta = 35
  let color_cyan = 36
  let color_white = 37

  let bold = 1

  let color_stack = ref []

  let emit_color n =
    print_string "\027[";
    print_int n;
    print_string "m"

  let start_color n =
    if !Param.ansi_color then
      begin
        emit_color n;
        color_stack := n :: (!color_stack)
      end

  let reset_color() =
    if !Param.ansi_color then
      begin
        match !color_stack with
	  [] -> Parsing_helper.internal_error "Popping more colors than pushed"
        |	[n] -> emit_color 0; color_stack := []
        |	_::n::r -> emit_color n; color_stack := n::r
      end

  let display_occ n =
    start_color color_green;
    print_string ("{" ^ (string_of_int n) ^ "}");
    reset_color()

  let display_occ_ref = display_occ

  let display_clause_link n =
    print_string ("clause " ^ (string_of_int n) ^ " ")

  let display_step_link n =
    print_string (string_of_int n)

  let start_cl = function
  CFun | CName | CVar | CPred | CType -> ()
    | CExplain -> start_color color_magenta
    | CKeyword -> start_color color_blue
    | CConn -> start_color bold

  let end_cl = function
  CFun | CName | CVar | CPred | CType -> ()
    | _ -> reset_color()

  let convert_funname s = s

  let and_connective() =
    if !Param.typed_frontend then "&&" else "&"
  let or_connective() =
    if !Param.typed_frontend then "||" else "|"
  let impl_connective = "->"
  let red_connective = "=>"
  let before_connective = "==>"
  let diff_connective = "<>"
  let equal_connective = "="
  let eq1_connective = "<->"
  let eq2_connective = "<=>"

  let hline = "--------------------------------------------------------------\n"

  let start_numbered_list = ""
  let end_numbered_list = "\n"
  let start_list = ""
  let end_list = "\n"

  let clause_item n =
    let ns = string_of_int n in
    print_string ("\nClause " ^ ns ^ ": ")

  let history_item n =
    print_string ("\n" ^ (string_of_int n) ^ ". ")

  let basic_item() =
    print_string "\n"

  let newline() =
    print_newline()

end


module LangHtml =
struct
(*
  Characters not to use in HTML
  & -> &amp;
  < -> &lt;
  > -> &gt;
  quotes -> &quot;
*)

  let indentstring = "&nbsp;&nbsp;&nbsp;&nbsp;"

  let proverifurl = ref "" (* currently, you need to copy the CSS file into your html directory. TO DO? improve that? *)

  let previousf = ref []

  let f = ref stdout

  let print_string s =
    if (!previousf) == [] then
      Parsing_helper.internal_error "html output with no open html file.\n";
    output_string (!f) s

  let openfile fname title =
    previousf := (!f) :: (!previousf);
    begin
      try
        f := open_out fname
      with Sys_error _ ->
        Parsing_helper.user_error ("Error: could not open html file. The html directory that you specified, " ^ (!Param.html_dir) ^ ", probably does not exist.\n")
    end;
    print_string ("<!DOCTYPE html PUBLIC \"-//W3C//DTD HTML 4.01//EN\">
<html>
<head>
  <title>" ^ title ^ "</title>
  <link rel=\"stylesheet\" href=\"" ^ (!proverifurl) ^ "cssproverif.css\">
</head>
<body>
")

  let close() =
    match !previousf with
      [] -> Parsing_helper.internal_error "No html file to close"
    | (f'::r) ->
       print_string "</body>\n</html>\n";
      close_out (!f);
      f := f';
      previousf := r

  let display_occ n =
    let ns = string_of_int n in
    print_string ("<a href=\"process_"^(string_of_int !Param.process_number)^".html#occ" ^ ns ^ "\" target=\"process\" class=\"occ\">{" ^ ns ^ "}</a>")

  let display_occ_ref n =
    let ns = string_of_int n in
    print_string ("<a name=occ" ^ ns ^ " class=\"occ\">{" ^ ns ^ "}</a> ")

  let display_clause_link n =
    let ns = string_of_int n in
    print_string ("<a href=\"clauses" ^
		     (string_of_int (!Param.current_query_number)) ^
		     ".html#clause" ^ ns ^ "\" target=\"clauses\">clause " ^ ns ^ "</a> ")

  let display_step_link n =
    let ns = string_of_int n in
    print_string ("<a href=\"#step" ^ ns ^ "\">" ^ ns ^ "</a>")


  let start_cl cl =
    let cls = match cl with
        CFun -> "fun"
      | CName -> "name"
      | CVar -> "var"
      | CPred -> "pred"
      | CType -> "type"
      | CExplain -> "explain"
      | CKeyword -> "keyword"
      | CConn -> "conn"
    in
    print_string ("<span class=\"" ^ cls ^ "\">")

  let end_cl cl = print_string "</span>"

  let convert_funname s =
    match s with
      "&&" -> "&amp;&amp;"
    | "<>" -> "&lt;&gt;"
    | _ -> s

  let and_connective() =
    if !Param.typed_frontend then "&amp;&amp;" else "&amp;"
  let or_connective() =
    if !Param.typed_frontend then "||" else "|"
  let impl_connective = "-&gt;"
  let red_connective = "=&gt;"
  let before_connective = "==&gt;"
  let diff_connective = "&lt;&gt;"
  let equal_connective = "="
  let eq1_connective = "&lt;-&gt;"
  let eq2_connective = "&lt;=&gt;"

  let hline = "<HR>\n"

  let start_numbered_list = "\n<ol>\n"
  let end_numbered_list = "\n</ol>\n"
  let start_list = "\n<ul>\n"
  let end_list = "\n</ul>\n"

  let clause_item n =
    let ns = string_of_int n in
    print_string ("\n<li><a name=clause" ^ ns ^ ">Clause " ^ ns ^ ":</a> ")

  let history_item n =
    print_string ("\n<li><a name=step" ^ (string_of_int n) ^ ">")

  let basic_item() =
    print_string "\n<li>"

  let newline() =
    print_string "<br>\n"

end


module LangDisp = functor (Lang : LangSig) ->
struct

(* The rest is independent of the output language *)

  let print_string = Lang.print_string
  let newline = Lang.newline
  let display_occ = Lang.display_occ

  let print_line s =
    print_string s;
    newline()

  let display_idcl cl s =
    Lang.start_cl cl;
    print_string s;
    Lang.end_cl cl

  let display_connective s =
    print_string " ";
    display_idcl CConn s;
    print_string " "

  let display_keyword s =
    display_idcl CKeyword s

  let varname v =
    if v.vname == -1 then
    (*Parsing_helper.internal_error "Variables created by new_var_noren should never be displayed"
      They may be displayed for debugging in Simplify.display_norm_* *)
      v.sname ^ "[-1]"
    else if v.vname != 0 then
      v.sname ^ "_" ^ (string_of_int v.vname)
    else
      v.sname

  let meaning = function
  MUnknown -> ""
    | MSid n -> "!" ^ (string_of_int n)
    | MCompSid -> "!comp"
    | MAttSid -> "!att"
    | MVar (b,_) -> varname b

  let rec display_list f sep = function
  [] -> ()
    | [a] -> f a
    | (a::l) -> f a;
      print_string sep;
      display_list f sep l

  let rec display_list_and f = function
  [] -> ()
    | [a] -> f a
    | (a::l) -> f a;
      display_connective (Lang.and_connective());
      display_list_and f l

  let display_item_list f l =
    print_string Lang.start_list;
    List.iter (fun x ->
      Lang.basic_item(); f x) l;
    print_string Lang.end_list

  let display_phase p =
    match p.p_info with
      [Attacker (n,_)] | [AttackerBin (n,_)] | [Mess (n,_)] | [MessBin (n,_)]
    | [InputP n] | [InputPBin n] | [OutputP n] | [OutputPBin n] | [Table n]
    | [TableBin n] ->
       if n > 0 then
	 print_string (" in phase " ^ (string_of_int n))
    | [AttackerGuess _] -> print_string " in off-line phase"
    | _ -> ()

  let display_function_name f =
    display_idcl CFun (Terms.get_function_name f)

  module DisplayFun =
    functor (Link : sig
      val follow : bool
    end) ->
  struct

    let rec term = function
    FunApp(f,l) ->
      begin
	match f.f_name with
	  "=" | "&&" | "||" | "<>" ->
		  (* Infix functions *)
	    begin
	      match l with
		[t1;t2] ->
		  print_string "(";
		  term t1;
		  print_string " ";
		  display_idcl CFun (Lang.convert_funname f.f_name);
		  print_string " ";
		  term t2;
		  print_string ")"
	      | _ -> Parsing_helper.internal_error "infix operators should have 2 arguments"
	    end
	|	"if-then-else" ->
	   begin
	     match l with
	       [t1;t2;t3] ->
		 print_string "(";
		 display_idcl CKeyword "if";
		 print_string " ";
		 term t1;
		 print_string " ";
		 display_idcl CKeyword "then";
		 print_string " ";
		 term t2;
		 print_string " ";
		 display_idcl CKeyword "else";
		 print_string " ";
		 term t3;
		 print_string ")"
	     | _ -> Parsing_helper.internal_error "if-then-else should have 3 arguments"
	   end
	|	_ ->
           match f.f_cat with
             Name { prev_inputs_meaning = sl } ->
	       display_idcl CName f.f_name;
	       print_string "[";
	       if (sl = []) || (!Param.tulafale = 1) then term_list l else name_list l sl;
               print_string "]"
	   | Choice ->
	      display_idcl CKeyword f.f_name;
             print_string "[";
             term_list l;
             print_string "]"
	   | General_var | General_mayfail_var ->
	      display_idcl CFun f.f_name
           | _ ->
	      display_idcl CFun f.f_name;
	     if (l != []) || (f.f_name = "") || not (!Param.typed_frontend) then
	       begin
                 print_string "(";
                 term_list l;
                 print_string ")"
	       end
      end
      | Var v ->
	 if Link.follow then
	   match v.link with
	     TLink t -> term t
	   | VLink b -> display_idcl CVar (varname b)
	   | NoLink -> display_idcl CVar (varname v)
	   | _ -> Parsing_helper.internal_error "unexpected link in display_term_with_links"
	 else
	   display_idcl CVar (varname v)
      (* to see links
         ;
         match v.link with
         NoLink -> print_string "nl"
         | TLink t -> print_string "tl"
         | VLink v -> print_string "vl"
         | PGLink t -> print_string "pgl"
      *)

    and term_list l = display_list term "," l

    and name_list l sl = match (l,sl) with
	[],[] -> ()
      | [a],[sa] ->
	 if sa <> MUnknown then
	   begin
	     print_string (meaning sa); print_string " = "
	   end;
	term a
      | (a::l),(sa::sl) ->
	 if sa <> MUnknown then
	   begin
	     print_string (meaning sa); print_string " = "
	   end;
	term a;
        print_string ",";
        name_list l sl
      |	_ ->
         Printf.printf "\nPrev meaning:\n";
        display_list (fun s -> print_string (meaning s)) "; " sl;
        Printf.printf "\nArgument:\n";
        display_list term "; " l;
        Parsing_helper.internal_error "prev_inputs_meaning should have the same length as the arguments of the name 2"

    let fact = function
    Pred(chann,t) ->
      display_idcl CPred chann.p_name;
      if not (!Param.typed_frontend) then print_string ":";
      if t != [] then
	begin
	  if !Param.typed_frontend then print_string "(";
	  term_list t;
	  if !Param.typed_frontend then print_string ")"
	end
      | Out(t,l) ->
         display_idcl CPred "begin";
        if !Param.typed_frontend then print_string "(" else print_string ":";
        term t;
        List.iter (fun (v,t) ->
	  print_string (", " ^ (varname v) ^ " = ");
	  term t) l;
        if !Param.typed_frontend then print_string ")"

(* Collect existential variables in a term, in order to display it *)

    let simple_constra = function
    Neq(t1,t2) ->
      term t1;
      display_connective Lang.diff_connective;
      term t2

    let rec constra_rec = function
    [] -> print_string "F"
      | [a] -> simple_constra a
      | (a::l) ->
         simple_constra a;
        print_string " | ";
        constra_rec l

(* Collect general variables in a term, in order to display it *)

    let rec collect_gen_vars accu = function
    FunApp(f, []) when f.f_cat == General_var || f.f_cat == General_mayfail_var ->
      if not (List.memq f (!accu)) then
	accu := f :: (!accu)
      | FunApp(f,l) -> List.iter (collect_gen_vars accu) l
      | Var _ -> ()

    let collect_gen_vars_constra accu constra =
      List.iter (function Neq(t1,t2) ->
        collect_gen_vars accu t1;
        collect_gen_vars accu t2) constra

    let constra a =
      let gen_vars = ref [] in
      collect_gen_vars_constra gen_vars a;
      if (!gen_vars <> []) then
        begin
          print_string "(forall ";
          display_list (fun f -> display_idcl CFun f.f_name) "," (!gen_vars);
          print_string ", "
        end;
      if List.length a > 1 then
        begin
          print_string "(";
          constra_rec a;
          print_string ")"
        end
      else
        constra_rec a;
      if (!gen_vars <> []) then
        print_string ")"

    let constra_list c = display_list_and constra c

    let concl upper concl tag =
      match tag with
        OutputTag occ :: _ ->
          print_string (if upper then "The message " else "the message ");
          begin
	    match concl with
	      Pred({p_info = [Attacker(n,_)]} as p, [v]) ->
	        term v;
	        print_string " may be sent to the attacker";
	        display_phase p
	    | Pred({p_info = [Mess(n,_)]} as p, [vc;v]) ->
	       term v;
	      print_string " may be sent on channel ";
	      term vc;
	      display_phase p
	    | Pred({p_info = [AttackerBin(n,_)]} as p, [v;v']) ->
	       term v;
	      print_string " (resp. ";
	      term v';
	      print_string ") may be sent to the attacker";
	      display_phase p
	    | Pred({p_info = [MessBin(n,_)]} as p, [vc;v;vc';v']) ->
	       term v;
	      print_string " may be sent on channel ";
	      term vc;
              print_string " (resp. message ";
	      term v';
	      print_string " on channel ";
	      term vc';
 	      print_string ")";
	      display_phase p
	    | _ -> Parsing_helper.internal_error "Unexpected conclusion for OutputTag"
          end;
          print_string " at output ";
          Lang.display_occ occ
      | TestUnifTag occ :: _ | TestUnifTag2 occ :: _ ->
         begin
	   print_string (if upper then "The attacker can make a distinguishing test at " else "the attacker can make a distinguishing test at ");
	   Lang.display_occ occ
         end
      | BeginFact :: BeginEvent(occ) :: _ | BeginEvent(occ) :: _ ->
         print_string (if upper then "Event " else "event ");
        begin
	  match concl with
	    Pred(_, [e]) ->
	      term e;
	      print_string " may be executed at ";
	      Lang.display_occ occ
	  | Pred(_, [e';e]) ->
	     term e;
	    print_string " may be executed at ";
	    Lang.display_occ occ;
	    print_string " in session ";
	    term e'
	  | _ -> Parsing_helper.internal_error "Unexpected conclusion for BeginEvent"
        end
      | InputPTag(occ) :: _ ->
         print_string (if upper then "An input on channel " else "an input on channel ");
        begin
	  match concl with
	    Pred({p_info = [InputP(n)]} as p, [e]) ->
	      term e;
	      print_string " may be triggered at ";
	      Lang.display_occ occ;
	      display_phase p
	  | Pred({p_info = [InputPBin(n)]} as p, [e;e']) ->
	     term e;
	    print_string " (resp. ";
	    term e';
	    print_string ") may be triggered at ";
	    Lang.display_occ occ;
	    display_phase p
	  | _ -> Parsing_helper.internal_error "Unexpected conclusion"
        end
      | OutputPTag(occ) :: _ ->
         print_string (if upper then "An output on channel " else "an output on channel ");
        begin
	  match concl with
	  | Pred({p_info = [OutputP(n)]} as p, [e]) ->
	     term e;
	    print_string " may be triggered at ";
	    Lang.display_occ occ;
	    display_phase p
	  |  Pred({p_info = [OutputPBin(n)]} as p, [e;e']) ->
	     term e;
	    print_string " (resp. ";
	    term e';
	    print_string ") may be triggered at ";
	    Lang.display_occ occ;
	    display_phase p
	  | _ -> Parsing_helper.internal_error "Unexpected conclusion"
        end
      | InsertTag occ :: _ ->
         print_string (if upper then "The entry " else "the entry ");
        begin
	  match concl with
	    Pred({p_info = [Table(n)]} as p, [v]) ->
	      term v;
	      print_string " may be inserted in a table";
	      display_phase p
	  | Pred({p_info = [TableBin(n)]} as p, [v;v']) ->
	     term v;
	    print_string " (resp. ";
	    term v';
	    print_string ") may be inserted in a table";
	    display_phase p
	  | _ -> Parsing_helper.internal_error "Unexpected conclusion for InsertTag"
        end;
        print_string " at insert ";
        Lang.display_occ occ
      | _ -> Parsing_helper.internal_error "There should be at least one tag"

  end


  module Std = DisplayFun(struct
    let follow = false
  end)

  module WithLinks = DisplayFun(struct
    let follow = true
  end)

  let display_term = Std.term
  let display_term_list = Std.term_list
  let display_fact = Std.fact
  let display_constra = Std.constra

  let rec display_format = function
  FFunApp(f,l) ->
    begin
      match f.f_cat with
        Name { prev_inputs_meaning = sl } ->
	  display_idcl CName f.f_name;
          print_string "[";
          if (sl = []) || (!Param.tulafale = 1) then display_format_list l else display_name_list l sl;
          print_string "]"
      | Choice ->
	 display_idcl CKeyword f.f_name;
        print_string "[";
        display_format_list l;
        print_string "]"
      | _ ->
	 display_idcl CFun f.f_name;
	if (l != []) || (f.f_name = "") || not (!Param.typed_frontend) then
	  begin
            print_string "(";
            display_format_list l;
            print_string ")"
	  end
    end
    | FVar v -> display_idcl CVar (varname v)
    | FAny v -> display_idcl CVar ("*" ^ (varname v))

  and display_format_list l = display_list display_format "," l

  and display_name_list l sl = match (l,sl) with
      [],[] -> ()
    | [a],[sa] ->
       if sa <> MUnknown then
	 begin
	   print_string (meaning sa); print_string " = "
	 end;
      display_format a
    | (a::l),(sa::sl) ->
       if sa <> MUnknown then
	 begin
	   print_string (meaning sa); print_string " = "
	 end;
      display_format a;
      print_string ",";
      display_name_list l sl
    |	_ -> Parsing_helper.internal_error "prev_inputs_meaning should have the same length as the arguments of the name (format)"


  let display_fact_format (chann,t) =
    display_idcl CPred chann.p_name;
    if not (!Param.typed_frontend) then print_string ":";
    if t != [] then
      begin
        if !Param.typed_frontend then print_string "(";
        display_format_list t;
        if !Param.typed_frontend then print_string ")"
      end

  let display_hyp h = display_list_and display_fact h

  let display_constra_list c = display_list_and display_constra c

  let display_rule_nonewline (hyp, concl, hist, constra) =
    display_constra_list constra;
    if (constra != []) && (hyp != []) then
      display_connective (Lang.and_connective());
    display_hyp hyp;
    if (constra != []) || (hyp != []) then
      display_connective Lang.impl_connective;
    display_fact concl

  let display_rule r =
    display_rule_nonewline r;
    newline()
(*
  TestUnifTag(occ): given only as first tag for clauses H /\ testunif(...) -> bad (for non_interference)
  TestUnifTag2(occ): given only as first tag for clauses H /\ M<>M' -> bad (for pitranslweak)
  TestTag(occ): test, associated to no hypothesis
  InputTag(occ): input, associated with one hypothesis mess:... or attacker:...
  ReplTag(occ,_): replication, associated with one hypothesis if non_interference and with two if
  non_interference and key_compromise == 1
  OutputTag(occ): output, used as first tag for clauses H -> mess:... or H -> attacker:...
  LetFilterFact: let suchthat, associated with one hypothesis [always followed by LetFilterTag(occ)]
  LetFilterTag(occ): let suchthat, associated with no hypothesis
  BeginEvent(occ): event, first tag for clauses H -> end:...
  tag associated with no hypothesis
  BeginFact: event, associated with one hypothesis begin:... [always followed by BeginEvent(occ)]
  LetTag(occ): let, associated with no hypothesis

  clauses H -> input:... and H -> output:... for non_interference currently
  have no tag for describing their conclusion
*)

  let rec display_hyp hyp tag =
    match (hyp, tag) with
      (_::h, TestUnifTag _ :: t) | (h, TestUnifTag2 _ :: t) | (h, TestTag _ :: t)
    | (h, LetTag _ :: t) | (h, InputPTag _ :: t) | (h, OutputPTag _ :: t)
    | (h, OutputTag _ :: t) | (h, InsertTag _ :: t) | (h, LetFilterTag _ :: t)
    | (h, BeginEvent _ :: t) ->
       display_hyp h t
    | (h, ReplTag _ :: t) ->
       if !Param.non_interference then
	 if !Param.key_compromise == 1 then
	   match h with
	     _::_::h' -> display_hyp h' t
	   | _ -> Parsing_helper.internal_error "2 hypotheses should be added for a replication for non_interference, key_compromise = 1"
	 else
	   match h with
	     _::h' -> display_hyp h' t
	   | _ -> Parsing_helper.internal_error "At least one hypothesis should be added for a replication for non_interference"
       else
	 display_hyp h t
    | (m::h,InputTag occ :: t) ->
       display_hyp h t;
      begin
	match m with
	  Pred({p_info = [Attacker(n,_)]} as p, [v]) ->
	    print_string "the message ";
	    display_term v;
	    print_string " is received from the attacker";
	    display_phase p;
	    print_string " at input ";
	    Lang.display_occ occ
	| Pred({p_info = [Mess(n,_)]} as p, [vc;v]) ->
	   print_string "the message ";
	  display_term v;
	  print_string " is received on channel ";
	  display_term vc;
	  display_phase p;
	  print_string " at input ";
	  Lang.display_occ occ
	| Pred({p_info = [AttackerBin(n,_)]} as p, [v;v']) ->
	   print_string "the message ";
	  display_term v;
	  print_string " (resp. ";
	  display_term v';
	  print_string ") is received from the attacker";
	  display_phase p;
	  print_string " at input ";
	  Lang.display_occ occ
	| Pred({p_info = [MessBin(n,_)]} as p, [vc;v;vc';v']) ->
	   print_string "the message ";
	  display_term v;
	  print_string " is received on channel ";
	  display_term vc;
          print_string " (resp. message ";
	  display_term v';
	  print_string " on channel ";
	  display_term vc';
 	  print_string ")";
	  display_phase p;
	  print_string " at input ";
	  Lang.display_occ occ
	| _ -> Parsing_helper.internal_error "Unexpected hypothesis for InputTag"
      end;
      print_string ",";
      newline()
    | (m::h, LetFilterFact :: LetFilterTag(occ) :: t) ->
       display_hyp h t;
      display_fact m;
      print_string " is true at ";
      Lang.display_occ occ;
      print_string ",";
      newline()
    | (Out(e,_) ::h, BeginFact :: BeginEvent(occ) :: t) ->
       display_hyp h t;
      print_string "event ";
      display_term e;
      print_string " is executed at ";
      Lang.display_occ occ;
      print_string ",";
      newline()
    | (m::h,GetTag occ :: t) ->
       display_hyp h t;
      begin
	match m with
	  Pred({p_info = [Table(n)]} as p, [v]) ->
	    print_string "the entry ";
	    display_term v;
	    print_string " is in a table";
	    display_phase p;
	    print_string " at get ";
	    Lang.display_occ occ
	| Pred({p_info = [TableBin(n)]} as p, [v;v']) ->
	   print_string "the entry ";
	  display_term v;
	  print_string " (resp. ";
	  display_term v';
	  print_string ") is in a table";
	  display_phase p;
	  print_string " at get ";
	  Lang.display_occ occ
	| _ -> Parsing_helper.internal_error "Unexpected hypothesis for GetTag"
      end;
      print_string ",";
      newline()
    | (h, GetTagElse occ :: t) ->
       display_hyp h t
    | ([],[]) -> ()
    | _ -> Parsing_helper.internal_error "Unexpected hypothesis"

  let rec empty_hyp hyp tags =
    match hyp, tags with
      (_::h, TestUnifTag _ :: t) | (h, TestUnifTag2 _ :: t) | (h, TestTag _ :: t)
    | (h, LetTag _ :: t) | (h, InputPTag _ :: t) | (h, OutputPTag _ :: t)
    | (h, OutputTag _ :: t) | (h, LetFilterTag _ :: t) | (h, InsertTag _ :: t)
    | (h, BeginEvent _ :: t) -> empty_hyp h t
    | (h, ReplTag _ :: t) ->
       if !Param.non_interference then
	 if !Param.key_compromise == 1 then
	   match h with
	     _::_::h' -> empty_hyp h' t
	   | _ -> Parsing_helper.internal_error "2 hypotheses should be added for a replication for non_interference, key_compromise = 1"
	 else
	   match h with
	     _::h' -> empty_hyp h' t
	   | _ -> Parsing_helper.internal_error "At least one hypothesis should be added for a replication for non_interference"
       else
	 empty_hyp h t
    | [], _ -> true
    | _ -> false


  let display_rule_num ((hyp,concl,hist,constra) as rule) =
    match hist with
      Rule (n,lbl,_,_,_) ->
        Lang.clause_item n;
        display_rule_nonewline rule;
        if !Param.verbose_explain_clauses = Param.ExplainedClauses then
	  begin
	    newline();
	    Lang.start_cl CExplain;
	    begin
	      match lbl with
	        Rn _ -> print_string "(The attacker can create new names.)"
	      | Init -> print_string "(Initial knowledge of the attacker.)"
	      | PhaseChange -> print_string "(Knowledge is communicated from one phase to the next.)"
	      | TblPhaseChange -> print_string "(Tables are communicated from one phase to the next.)"
	      | TestDeterministic(f) ->
	         print_string ("(The destructor ");
	        display_function_name f;
	        print_string " is not deterministic)"
	      | TestTotal(f) ->
	         print_string ("(The destructor ");
	        display_function_name f;
	        print_string " is not total)"
	      | Apply(f,p) ->
	         print_string "(The attacker applies function ";
	        display_function_name f;
	        display_phase p;
	        print_string ".)"
	      | TestApply(f,p) ->
	         print_string "(The attacker tests whether ";
	        display_function_name f;
	        print_string " is applicable";
	        display_phase p;
	        print_string ".)"
	      | TestEq(p) ->
	         print_string "(The attacker tests equality";
	        display_phase p;
	        print_string ".)"
	      | Rl(p,p') ->
	         print_string "(The attacker can listen on all channels it has";
	        display_phase p;
	        print_string ".)"
	      | Rs(p,p') ->
	         print_string "(The attacker can send messages it has on all channels it has";
	        display_phase p;
	        print_string ".)"
	      | Ri(p,p') ->
	         print_string "(The attacker can input on all channels it has";
	        display_phase p;
	        print_string ".)"
	      | Ro(p,p') ->
	         print_string "(The attacker can output on all channels it has";
	        display_phase p;
	        print_string ".)"
	      | Rfail(p) ->
	         print_string "(The attacker can test the failure of a term)";
	        display_phase p;
	        print_string ".)"
	      | TestComm(p,p') ->
	         print_string "(If an input and an output are done";
	        display_phase p;
	        print_string ", then the attacker may know whether the communication succeeds.)"
	      | InputSecr p ->
	         print_string "(If an input on the secret is done";
	        display_phase p;
	        print_string ", then the attacker may know whether the secret is a name.)"
	      | OutputSecr p ->
	         print_string "(If an output on the secret is done";
	        display_phase p;
	        print_string ", then the attacker may know whether the secret is a name.)"
	      | WeakSecr ->
	         print_string "(The attacker has the weak secret in the first component, a guess in the second.)"
	      | Elem(pl,p) -> ()
	      | TestUnif ->
	         print_string "(The attacker can test whether these terms unify.)"
	      | ProcessRule(tags, _) ->
	         if empty_hyp hyp tags && constra == [] then
		   begin
		     print_string "(";
		     Std.concl true concl tags;
		     print_string ".)"
		   end
	         else
		   begin
		     print_string "(If ";
		     display_hyp hyp tags;
		     if constra != [] then
		       begin
		         display_constra_list constra;
		         newline()
		       end;
		     print_string "then ";
		     Std.concl false concl tags;
		     print_string ".)";
		   end
	      | LblEquiv ->
	         print_string "(This clause comes from a";
	        display_connective Lang.eq1_connective;
	        print_string "or";
	        display_connective Lang.eq2_connective;
	        print_string "declaration in the input file.)"
	      | LblClause ->
	         print_string "(This clause is given in the input file.)"
	      | LblEq ->
	         print_string "(Definition of equal.)"
	      | LblComp ->
	         print_string "(The attacker has all names created in the compromised sessions.)"
	      | LblNone -> ()
	    end;
	    Lang.end_cl CExplain
	  end
    | _ -> Lang.basic_item(); display_rule_nonewline rule

  let display_eq (leq, req) =
    display_term leq;
    display_connective "=";
    display_term req

  let display_abbrev_table l =
    print_string "Abbreviations:";
    display_item_list display_eq (List.rev l)

  let display_rule_num_abbrev rule =
    if !Param.abbreviate_clauses then
      begin
        let abbrev_table,rule' = abbreviate_rule rule in
        display_rule_num rule';
        newline();
        if abbrev_table != [] then
	  display_abbrev_table abbrev_table
      end
    else
      begin
        display_rule_num rule;
      (* If a clause may be displayed on several lines, leave an empty line
         between clauses *)
        if !Param.verbose_explain_clauses = Param.ExplainedClauses then
	  newline()
      end

  let display_initial_clauses l =
    print_string Lang.start_list;
    List.iter display_rule_num_abbrev l;
    print_string Lang.end_list



  let display_red f l =
    let collect = Std.collect_gen_vars in

    let display_diseq (t1,t2) =
      let gen_vars = ref [] in
      collect gen_vars t1;
      collect gen_vars t2;

      if (!gen_vars <> []) then
        begin
      	  print_string "(forall ";
	  display_list (fun f -> display_idcl CFun f.f_name) "," (!gen_vars);
	  print_string ". "
        end;

      display_term t1;
      display_connective Lang.diff_connective;
      display_term t2;

      if (!gen_vars <> []) then print_string ")"

    in

    List.iter (fun (leq, req,side) ->
      display_term (FunApp(f,leq));
      display_connective Lang.red_connective;
      display_term req;
      if List.length side <> 0
      then
    	begin
    	  print_string " if ";
    	  display_list_and display_diseq side
    	end;
      newline()) l

(* Display functions *)

  let rec display_term2 = function
  FunApp(f,l) ->
    begin
      match f.f_cat with
        Name _ -> display_idcl CName f.f_name
      | Choice ->
	 begin
	   match l with
	     [t1;t2] ->
	       if Terms.equal_terms t1 t2 then
		 display_term2 t1
	       else
		 begin
		   display_idcl CKeyword "choice";
		   print_string "[";
		   display_term_list2 l;
		   print_string "]"
		 end
	   | _ -> Parsing_helper.internal_error "Choice expects 2 arguments"
	 end

      | _ ->
	 match f.f_name with
	   "=" | "&&" | "||" | "<>" ->
		(* Infix functions *)
	     begin
	       match l with
		 [t1;t2] ->
		   print_string "(";
		   display_term2 t1;
		   print_string " ";
		   display_idcl CFun (Lang.convert_funname f.f_name);
		   print_string " ";
		   display_term2 t2;
		   print_string ")"
	       | _ -> Parsing_helper.internal_error "infix operators should have 2 arguments"
	     end
	 |	"if-then-else" ->
	    begin
	      match l with
		[t1;t2;t3] ->
		  print_string "(";
		  display_idcl CKeyword "if";
		  print_string " ";
		  display_term2 t1;
		  print_string " ";
		  display_idcl CKeyword "then";
		  print_string " ";
		  display_term2 t2;
		  print_string " ";
		  display_idcl CKeyword "else";
		  print_string " ";
		  display_term2 t3;
		  print_string ")"
	      | _ -> Parsing_helper.internal_error "if-then-else should have 3 arguments"
	    end
	 | _ ->
	    display_idcl CFun f.f_name;
	   if (l != []) || (f.f_name = "") || not (!Param.typed_frontend) then
	     begin
	       print_string "(";
	       display_term_list2 l;
	       print_string ")"
	     end
    end
    | Var v -> display_idcl CVar (varname v)

  and display_term_list2 l = display_list display_term2 "," l


  let rec display_pattern = function
    | PatVar b ->
       display_idcl CVar (varname b);
      if !Param.typed_frontend then
	begin
	  print_string ": ";
	  display_idcl CType b.btype.tname
	end
    | PatTuple (f,l) ->
       display_idcl CFun f.f_name;
      if (l != []) || (f.f_name = "") || not (!Param.typed_frontend) then
	begin
	  print_string "(";
	  display_pattern_list l;
	  print_string ")"
	end
    | PatEqual t ->
       print_string "=";
      display_term2 t

  and display_pattern_list = function
    | [] -> ()
    | [h] -> display_pattern h
    | h::t ->
       display_pattern h;
      print_string ",";
      display_pattern_list t

  let display_fact2 = function
  Pred(chann,t) ->
    display_idcl CPred chann.p_name;
    if not (!Param.typed_frontend) then print_string ":";
    if t != [] then
      begin
	if !Param.typed_frontend then print_string "(";
	display_term_list2 t;
	if !Param.typed_frontend then print_string ")"
      end
    | Out(t,l) ->
       display_idcl CPred "begin";
      if !Param.typed_frontend then print_string "(" else print_string ":";
      display_term2 t;
      List.iter (fun (v,t) ->
	print_string (", " ^ (varname v) ^ " = ");
	display_term2 t
      ) l;
      if !Param.typed_frontend then print_string ")"

  let rec may_have_else = function
  Nil | Par _ -> false (* Par always introduces parentheses; whatever
	                  there is inside will be surrounded by these parentheses so does not
	                  need further parentheses *)
    | Repl(p,_) -> may_have_else p
    | Test _ | Let _ | LetFilter _ | Get _ -> true
    | Restr(_,_,p,_) | Event(_,_,p,_) | Output(_,_,p,_) | Input(_,_,p,_) | Insert(_,p,_)
    | Phase(_,p,_) | NamedProcess(_, _, p) | Barrier(_,_,p,_)
    | AnnBarrier(_,_,_,_,_,p,_) -> may_have_else p

  let rec is_nil = function
      Nil -> true
    | NamedProcess(_,_,p) -> is_nil p
    | _ -> false
	  
  let display_proc show_occ align proc =
    let display_occ occ =
      if show_occ then Lang.display_occ_ref occ
    in
    let rec display_process align proc =
      match proc with
      | Nil ->
	 print_string align;
	display_idcl CKeyword "0";
	newline()
      | Par _ ->
	 let rec dec_par = function
	     Par(p,p') -> (dec_par p) @ (dec_par p')
	   | NamedProcess(_,_,p) -> dec_par p
	   | p -> [p]
	 in
	 let l = dec_par proc in
	 print_string (align^"(");
	 newline();
	 let rec display_par_list = function
	 [] -> Parsing_helper.internal_error "empty list of parallel processes"
	   | [p] ->
	      display_process (align^Lang.indentstring) p;
	     print_string (align^")");
	     newline()
	   | p::l ->
	      display_process (align^Lang.indentstring) p;
	     print_string (align^") | (");
	     newline();
	     display_par_list l
	 in
	 display_par_list l
      | Repl (p,occ) ->
	 print_string align;
	display_occ occ;
	display_idcl CKeyword "!";
	newline();
	display_process align p
      | Restr (f, (args,_), p, occ) ->
	 print_string align;
	display_occ occ;
	display_idcl CKeyword "new";
	print_string " ";
	display_idcl CName f.f_name;
	begin
	  match args with
	    None -> ()
	  | Some l ->
	     print_string "[";
	    display_list (fun b -> display_idcl CVar (varname b)) "," l;
	    print_string "]";
	end;
	if !Param.typed_frontend then
	  begin
	    print_string ": ";
	    display_idcl CType (snd f.f_type).tname
	  end;
	display_opt_process align p
      | Test (t, p, p',occ) ->
	 print_string align;
	display_occ occ;
	display_idcl CKeyword "if";
	print_string " ";
	display_term2 t;
	print_string " ";
        display_idcl CKeyword "then";
	newline();
	if not (is_nil p') then
	  begin
	    display_process_paren align p;
	    print_string align;
	    display_idcl CKeyword "else";
	    newline();
	    display_process (align^Lang.indentstring) p'
	  end
	else
	  display_process align p;
      | Input (t, pat, p,occ) ->
	 print_string align;
	display_occ occ;
	display_idcl CKeyword "in";
	print_string "(";
	display_term2 t;
	print_string ", ";
	display_pattern pat;
	print_string ")";
	display_opt_process align p
      | Output (t, t', p, occ) ->
	 print_string align;
	display_occ occ;
	display_idcl CKeyword "out";
	print_string "(";
	display_term2 t;
	print_string ", ";
	display_term2 t';
	print_string ")";
	display_opt_process align p
      | Let (pat, t, p, p', occ) ->
	 print_string align;
	display_occ occ;
	display_idcl CKeyword "let";
	print_string " ";
	display_pattern pat;
	print_string " = ";
	display_term2 t;
	print_string " ";
	display_idcl CKeyword "in";
	newline();
	if is_nil p' then
	  display_process align p
	else
	  begin
	    display_process_paren align p;
	    print_string align;
	    display_idcl CKeyword "else";
	    newline();
	    display_process (align^Lang.indentstring) p'
	  end
      | Event (f,(env_args,_),p,occ) ->
	 print_string align;
	display_occ occ;
	display_idcl CKeyword "event";
	print_string " ";
	display_term2 f;
	begin
	  match env_args with
	    None -> ()
	  | Some l ->
	     print_string "[";
	    display_list (fun b -> display_idcl CVar (varname b)) "," l;
	    print_string "]";
	end;
	display_opt_process align p
      | Insert (f,p,occ) ->
	 print_string align;
	display_occ occ;
	display_idcl CKeyword "insert";
	print_string " ";
	display_term2 f;
	display_opt_process align p
      | Get(pat,t,p,elsep,occ) ->
	 print_string align;
	display_occ occ;
	display_idcl CKeyword "get";
	print_string " ";
	display_pattern pat;
	begin
	  match t with
	    FunApp(f,[]) when f == Terms.true_cst -> ()
	  | _ ->
	     print_string " "; display_idcl CKeyword "suchthat"; print_string " ";
	    display_term2 t;
	end;
	print_string " ";
	display_idcl CKeyword "in";
	newline();
	if is_nil elsep then
	  display_process align p
	else
	  begin
	    display_process_paren align p;
	    print_string align;
	    display_idcl CKeyword "else";
	    newline();
	    display_process (align^Lang.indentstring) elsep
	  end
      | Phase(n,p,occ) ->
	 print_string align;
	display_occ occ;
	display_idcl CKeyword "phase";
	print_string (" " ^ (string_of_int n) ^ ";");
	newline();
	display_process align p
      | Barrier(n,tag,p,occ) ->
	 print_string align;
	display_occ occ;
	display_idcl CKeyword "sync";
	print_string (" " ^ (string_of_int n) ^
	                 (match tag with
	                   None -> ";"
	                 | Some t -> " [" ^ t ^ "];"));
	newline();
	display_process align p
      | AnnBarrier(n,tag,a,c,subst,p,occ) ->
	 print_string align;
	display_occ occ;
	display_idcl CKeyword "sync";
	print_string (" " ^ (string_of_int n) ^ "[" ^ tag ^ ", ");
	display_idcl CName a.f_name;
	print_string ", ";
	display_idcl CName c.f_name;
	print_string ", (";
	display_list (fun (b,t) -> display_term2 t; print_string "/"; display_idcl CVar (varname b)) "," subst;
	print_string ")];";
	newline();
	display_process align p
      | LetFilter(lb,f,p,q,occ) ->
	 print_string align;
	display_occ occ;
	if lb != [] then
	  begin
	    display_idcl CKeyword "let";
	    print_string " ";
	    let first = ref true in
	    List.iter (fun b ->
	      if !first then
		first := false
	      else
		print_string ", ";
	      print_string (varname b);
	      if !Param.typed_frontend then
		print_string (": " ^ b.btype.tname)
	    ) lb;
	    print_string " ";
	    display_idcl CKeyword "suchthat";
	    print_string " ";
	    display_fact2 f;
	    print_string " ";
	    display_idcl CKeyword "in"
	  end
	else
	  begin
	    display_idcl CKeyword "if";
	    print_string " ";
	    display_fact2 f;
	    print_string " ";
	    display_idcl CKeyword "then"
	  end;
	newline();
	if not (is_nil q) then
	  begin
	    display_process_paren align p;
	    print_string align;
	    display_idcl CKeyword "else";
	    newline();
	    display_process (align^Lang.indentstring) q
	  end
	else
	  display_process align p
      | NamedProcess(name, tl, p) ->
        (*print_string align;
          print_string "Beginning of process ";
          print_string (name ^ "(");
          let first = ref true in
          List.iter (fun t ->
          if !first then
	  first := false
	  else
	  print_string ", ";
          display_term2 t) tl;*)
          display_process align p

    and display_opt_process align p =
      if is_nil p then
	newline()
      else
	begin
	  print_string ";";
	  newline();
	  display_process align p
	end
	  
    and display_process_paren align p =
      if may_have_else p then
        begin
	  print_string align;
	  print_string "(";
	  newline();
	  display_process (align^Lang.indentstring) p;
	  print_string align;
	  print_string ")";
	  newline()
        end
      else
        display_process (align^Lang.indentstring) p
    in
    display_process align proc

  let display_process align proc =
    display_proc false align proc

  let display_process_occ align proc =
    display_proc true align proc

(* Display a query *)

  let display_event = function
  QSEvent(b, t) ->
    if !Param.typed_frontend then
      print_string (if b then "inj-event(" else "event(")
    else
      print_string (if b then "evinj:" else "ev:");
    display_term t;
    if !Param.typed_frontend then print_string ")"
    | QFact(p, tl) ->
       display_idcl CPred p.p_name;
      if not (!Param.typed_frontend) then print_string ":";
      if tl != [] then
	begin
	  if !Param.typed_frontend then print_string "(";
	  display_term_list tl;
	  if !Param.typed_frontend then print_string ")"
	end
    | QNeq(t1,t2) ->
       display_term t1;
      display_connective Lang.diff_connective;
      display_term t2
    | QEq(t1,t2) ->
       display_term t1;
      display_connective "=";
      display_term t2

  let rec display_corresp_query = function
  Before(e, []) ->
    display_idcl CKeyword "not ";
    display_event e
    | Before(e, a::l) ->
       display_event e;
      display_connective Lang.before_connective;
      display_hyp_and a;
      List.iter (fun b ->
	display_connective (Lang.or_connective());
	display_hyp_and b) l

  and display_hyp_and = function
  [] -> display_idcl CFun "true"
    | (a::l) ->
       if l != [] then print_string "(";
      display_hyp_elem a;
      List.iter (fun b ->
	display_connective (Lang.and_connective());
	display_hyp_elem b) l;
      if l != [] then print_string ")"

  and display_hyp_elem = function
  QEvent e -> display_event e
    | NestedQuery q -> print_string "("; display_corresp_query q; print_string ")"

  let display_corresp_putbegin_query = function
  PutBegin(b, l) ->
    display_idcl CKeyword "putbegin"; print_string " ";
    if !Param.typed_frontend then
      print_string (if b then "inj-event:" else "event:")
    else
      print_string (if b then "evinj:" else "ev:");
    display_list (fun f -> display_idcl CFun f.f_name) "," l
    | RealQuery q -> display_corresp_query q


  let display_eq_query = function
    | DestructorQuery -> print_string "Deterministic and total destructors"
    | ChoiceQuery -> print_string "Observational equivalence"
    | NonInterfQuery l ->
       print_string "Non-interference ";
      display_list (fun (f, tset) ->
	display_idcl CFun f.f_name;
	match tset with
	  None -> ()
	| Some s ->
	   print_string " among (";
	  display_list display_term ", " s;
	  print_string ")"
      ) ", " l
    | WeakSecret f ->
       print_string "Weak secret ";
      display_idcl CFun f.f_name

(* History display *)

  let rec display_history_tree align ftree =
    begin
      match ftree.desc with
        FEmpty -> print_string (align ^ "hypothesis ");
      | FHAny -> print_string (align ^ "any ")
      | FRemovedWithProof _ -> print_string (align ^ "duplicate ")
      | FRule(n, descr, constra, hl) ->
	 print_string align;
	if n = -1 then
	  begin
	    begin
	      match descr with
		Elem(preds,p) ->
		  print_string "simplif "; display_idcl CPred p.p_name
	      | TestUnif ->
		 print_string "testunif"
	      | Apply(f,p) ->
		 print_string "apply ";
		display_function_name f
	      | _ ->
		 Parsing_helper.internal_error "unsupported get_rule_hist"
	    end;
	    print_string " "
	  end
	else
	  Lang.display_clause_link n
      | FEquation(h) -> print_string (align ^ "equation ")
    end;
    WithLinks.fact ftree.thefact;
    newline();
    begin
      match ftree.desc with
        FEmpty | FHAny | FRemovedWithProof _ -> ()
      | FRule(n, _, _, hl) -> List.iter (display_history_tree (align ^ Lang.indentstring)) hl
      | FEquation(h) -> display_history_tree (align ^ Lang.indentstring) h
    end

(* History display with explanations linking it to the process *)

  let display_step n =
    if n >= 0 then
      begin
        print_string "By ";
        Lang.display_step_link n;
        print_string ", "
      end

  let display_step_low n =
    if n >= 0 then
      begin
        print_string " by ";
        Lang.display_step_link n
      end

  let display_attacker_fact = function
  Pred({p_info = [Attacker(n,_)]}, [v]) ->
    WithLinks.term v;
    if n > 0 then
      print_string (" in phase " ^ (string_of_int n))
    | Pred({p_info = [AttackerBin(n,_)]}, [v;v']) ->
       WithLinks.term v;
      print_string " (resp. ";
      WithLinks.term v';
      print_string ")";
      if n > 0 then
	print_string (" in phase " ^ (string_of_int n))
    | Pred({p_info = [AttackerGuess _]}, [v;v']) ->
       WithLinks.term v;
      print_string " (resp. ";
      WithLinks.term v';
      print_string ") in off-line phase"
    | f ->
       print_string "Error: "; display_fact f;
      Parsing_helper.internal_error "Unexpected attacker fact in Display.display_attacker_fact"

  let display_tbl_fact = function
  Pred({p_info = [Table(n)]}, [v]) ->
    WithLinks.term v;
    if n > 0 then
      print_string (" in phase " ^ (string_of_int n))
    | Pred({p_info = [TableBin(n)]}, [v;v']) ->
       WithLinks.term v;
      print_string " (resp. ";
      WithLinks.term v';
      print_string ")";
      if n > 0 then
	print_string (" in phase " ^ (string_of_int n))
    | _ -> Parsing_helper.internal_error "Unexpected table fact"

  let display_input_fact = function
  Pred({p_info = [InputP(n)]}, [v]) ->
    WithLinks.term v;
    if n > 0 then
      print_string (" in phase " ^ (string_of_int n))
    | Pred({p_info = [InputPBin(n)]}, [v;v']) ->
       WithLinks.term v;
      print_string " (resp. ";
      WithLinks.term v';
      print_string ")";
      if n > 0 then
	print_string (" in phase " ^ (string_of_int n))
    | _ -> Parsing_helper.internal_error "Unexpected input fact"

  let display_output_fact = function
  Pred({p_info = [OutputP(n)]}, [v]) ->
    WithLinks.term v;
    if n > 0 then
      print_string (" in phase " ^ (string_of_int n))
    | Pred({p_info = [OutputPBin(n)]}, [v;v']) ->
       WithLinks.term v;
      print_string " (resp. ";
      WithLinks.term v';
      print_string ")";
      if n > 0 then
	print_string (" in phase " ^ (string_of_int n))
    | _ -> Parsing_helper.internal_error "Unexpected output fact"

  let display_attacker_hyp nl hl =
    List.iter2 (fun n h ->
      match h.thefact with
        Pred({ p_info = [TestUnifP _] }, [v;v']) ->
	  print_string "The terms ";
	  WithLinks.term v;
	  print_string " and ";
	  WithLinks.term v';
	  print_string" unify for some values of the secrets and not for others.";
	  newline()
      | _ ->
	 display_step n;
	print_string "the attacker may know ";
	display_attacker_fact h.thefact;
	print_string ".";
	newline()) nl hl

  let display_tbl_hyp nl hl =
    List.iter2 (fun n h ->
      display_step n;
      print_string "a table may contain the entry ";
      display_tbl_fact h.thefact;
      print_string ".";
      newline()) nl hl

  let display_hyp_basic nl hl =
    List.iter2 (fun n h ->
      display_step n;
      WithLinks.fact h.thefact;
      print_string ".";
      newline()) nl hl

  let display_hyp_spec = function
  ReplTag (o,_) -> print_string "!"; print_string (string_of_int o)
    | InputTag o -> print_string "i"; print_string (string_of_int o)
    | BeginEvent o -> print_string "b"; print_string (string_of_int o)
    | BeginFact -> print_string "bf"
    | LetFilterTag o -> print_string "s"; print_string (string_of_int o)
    | LetFilterFact -> print_string "sf"
    | OutputTag o -> print_string "o"; print_string (string_of_int o)
    | TestTag o -> print_string "t"; print_string (string_of_int o)
    | LetTag o -> print_string "l"; print_string (string_of_int o)
    | TestUnifTag o -> print_string "u"; print_string (string_of_int o)
    | TestUnifTag2 o -> print_string "ud"; print_string (string_of_int o)
    | InputPTag o -> print_string "ip"; print_string (string_of_int o)
    | OutputPTag o -> print_string "op"; print_string (string_of_int o)
    | InsertTag o ->  print_string "it"; print_string (string_of_int o)
    | GetTag o ->  print_string "gt"; print_string (string_of_int o)
    | GetTagElse o ->  print_string "gte"; print_string (string_of_int o)

  let rec display_hyp hyp hl tag =
    match (hyp, hl, tag) with
      (Pred(p,[v;v'])::h, _::hl', TestUnifTag _ :: t) ->
        display_hyp h hl' t;
        print_string "The terms ";
        WithLinks.term v;
        print_string " and ";
        WithLinks.term v';
        print_string" unify for some values of the secrets and not for others.";
        newline()
    | (h, hl, TestUnifTag2 _ :: t) | (h, hl, TestTag _ :: t)
    | (h, hl, LetTag _ :: t) | (h, hl, InputPTag _ :: t)
    | (h, hl, OutputPTag _ :: t) | (h, hl, BeginEvent _ :: t)
    | (h, hl, OutputTag _ :: t) | (h, hl, InsertTag _ :: t) ->
       display_hyp h hl t
    | (h, hl, ReplTag _ :: t) ->
       if !Param.non_interference then
	 if !Param.key_compromise == 1 then
	   match h, hl with
	     Pred(p, [v])::Pred(p', [v'])::h', s::s'::hl' ->
	       display_hyp h' hl' t;
	       display_step s;
	       print_string "the attacker may have the session identifier ";
	       WithLinks.term v;
	       display_phase p;
	       print_string ".";
	       newline();
	       display_step s';
	       print_string "the attacker may have the session identifier ";
	       WithLinks.term v';
	       display_phase p';
	       print_string ".";
	       newline()
	   | _ -> Parsing_helper.internal_error "2 hypotheses should be added for a replication for non_interference, key_compromise = 1"
	 else
	   match h, hl with
	     Pred(p, [v])::h', s::hl' ->
	       display_hyp h' hl' t;
	       display_step s;
	       print_string "the attacker may have the session identifier ";
	       WithLinks.term v;
	       display_phase p;
	       print_string ".";
	       newline()
	   | _ -> Parsing_helper.internal_error "At least one hypothesis should be added for a replication for non_interference"
       else
	 display_hyp h hl t
    | (m::h,s::hl,InputTag occ :: t) ->
       display_hyp h hl t;
      begin
	match m with
	  Pred({p_info = [Attacker(n,_)]} as p, [v]) ->
	    print_string "The message ";
	    WithLinks.term v;
	    print_string " that the attacker may have";
	    display_phase p;
	    display_step_low s;
	    print_string " may be received at input ";
	    Lang.display_occ occ
	| Pred({p_info = [Mess(n,_)]} as p, [vc;v]) ->
	   print_string "The message ";
	  WithLinks.term v;
	  print_string " that may be sent on channel ";
	  WithLinks.term vc;
	  display_phase p;
	  display_step_low s;
	  print_string " may be received at input ";
	  Lang.display_occ occ
	| Pred({p_info = [AttackerBin(n,_)]} as p, [v;v']) ->
	   print_string "The message ";
	  WithLinks.term v;
	  print_string " (resp. ";
	  WithLinks.term v';
	  print_string ") that the attacker may have";
	  display_phase p;
	  display_step_low s;
	  print_string " may be received at input ";
	  Lang.display_occ occ
	| Pred({p_info = [MessBin(n,_)]} as p, [vc;v;vc';v']) ->
	   print_string "The message ";
	  WithLinks.term v;
	  print_string " that may be sent on channel ";
	  WithLinks.term vc;
          print_string " (resp. message ";
	  WithLinks.term v';
	  print_string " on channel ";
	  WithLinks.term vc';
 	  print_string ")";
	  display_phase p;
	  display_step_low s;
	  print_string " may be received at input ";
	  Lang.display_occ occ
	| _ -> Parsing_helper.internal_error "Unexpected hypothesis for InputTag"
      end;
      print_string ".";
      newline()
    | (m::h, s::hl, LetFilterFact :: LetFilterTag(occ) :: t) ->
       display_hyp h hl t;
      display_step s;
      WithLinks.fact m;
      print_string " is true at ";
      Lang.display_occ occ;
      print_string ".";
      newline()
    | (h, hl, LetFilterTag(occ) :: t) ->
       display_hyp h hl t
    | (Out(e,l) ::h, s::hl, BeginFact :: BeginEvent(occ) :: t) ->
       display_hyp h hl t;
      print_string "The event ";
      WithLinks.term e;
      if l <> [] then
	begin
	  print_string " (with environment ";
	  display_list (fun (v,t) ->
	    print_string ((varname v) ^ " = ");
	    WithLinks.term t) ", " l;
	  print_string ")"
	end;
      print_string " may be executed at ";
      Lang.display_occ occ;
      print_string ".";
      newline()
    | (m::h,s::hl,GetTag occ :: t) ->
       display_hyp h hl t;
      begin
	match m with
	  Pred({p_info = [Table(n)]} as p, [v]) ->
	    print_string "The entry ";
	    WithLinks.term v;
	    print_string " that may be in a table";
	    display_phase p;
	    display_step_low s;
	    print_string " may be read at get ";
	    Lang.display_occ occ
	| Pred({p_info = [TableBin(n)]} as p, [v;v']) ->
	   print_string "The entry ";
	  WithLinks.term v;
	  print_string " (resp. ";
	  WithLinks.term v';
	  print_string ") that may be in a table";
	  display_phase p;
	  display_step_low s;
	  print_string " may be read at get ";
	  Lang.display_occ occ
	| _ -> Parsing_helper.internal_error "Unexpected hypothesis for GetTag"
      end;
      print_string ".";
      newline()
    | (h, l, GetTagElse occ :: t) ->
       display_hyp h hl t
    | ([],[],[]) -> ()
    | _ ->
       display_list WithLinks.fact " & " hyp;
      newline();
      display_list (fun n -> print_string (string_of_int n)) " " hl;
      newline();
      display_list display_hyp_spec " " tag;
      newline();
      Parsing_helper.internal_error "Unexpected hypothesis"

  let display_constra_list c =
    if c <> [] then
      begin
        print_string "We have ";
        display_list WithLinks.constra " & " c;
        print_string ".";
        newline()
      end


  let display_clause_explain n lbl hyp_num_list hl constra concl =
    match lbl with
      Rn _ ->
        print_string "The attacker creates the new name ";
        display_attacker_fact concl;
        print_string ".";
        newline()
    | Init ->
       print_string "The attacker initially knows ";
      display_attacker_fact concl;
      print_string ".";
      newline()
    | PhaseChange ->
       display_attacker_hyp hyp_num_list hl;
      print_string "So the attacker may know ";
      display_attacker_fact concl;
      print_string ".";
      newline()
    | TblPhaseChange ->
       display_tbl_hyp hyp_num_list hl;
      print_string "So a table may contain the entry ";
      display_tbl_fact concl;
      print_string ".";
      newline()
    | Apply(f,p) ->
       display_attacker_hyp hyp_num_list hl;
      print_string "Using the function ";
      display_function_name f;
      print_string " the attacker may obtain ";
      display_attacker_fact concl;
      print_string ".";
      newline()
    | TestDeterministic(f) ->
       display_attacker_hyp hyp_num_list hl;
      display_constra_list constra;
      print_string "Test whether ";
      display_function_name f;
      print_string " is deterministic.";
      newline()
    | TestTotal(f) ->
       display_attacker_hyp hyp_num_list hl;
      display_constra_list constra;
      print_string "Test whether ";
      display_function_name f;
      print_string " is total.";
      newline()
    | TestApply(f,p) ->
       display_attacker_hyp hyp_num_list hl;
      display_constra_list constra;
      print_string "The attacker tests whether ";
      display_function_name f;
      print_string " is applicable, which may allow it to distinguish cases.";
      newline()
    | TestEq(p) ->
       display_attacker_hyp hyp_num_list hl;
      display_constra_list constra;
      print_string "The attacker tests equality between the two terms he knows, which may allow it to distinguish cases.";
      newline()
    | Rl(p,p') ->
       begin
	 match (hyp_num_list, hl) with
	   [n1;n2], [h1;h2] ->
	     display_step n2;
	     print_string "the attacker may have the channel ";
	     display_attacker_fact h2.thefact;
	     print_string ".";
	     newline();
	     display_step n1;
	     print_string "the message ";
	     display_attacker_fact concl;
	     print_string " may be sent on this channel.";
	     newline();
	     print_string "So the attacker may obtain the message ";
	     display_attacker_fact concl;
	     print_string " by listening on this channel.";
	     newline()
	 | _ -> Parsing_helper.internal_error "Unexpected hypothesis for Rl"
       end
    | Rs(p,p') ->
       begin
	 match (hyp_num_list, hl) with
	   [n1;n2], [h1;h2] ->
	     display_step n1;
	     print_string "the attacker may have the channel ";
	     display_attacker_fact h1.thefact;
	     print_string ".";
	     newline();
	     display_step n2;
	     print_string "the attacker may have the message ";
	     display_attacker_fact h2.thefact;
	     print_string ".";
	     newline();
	     print_string "So the attacker may send this message on this channel.";
	     newline()
	 | _ -> Parsing_helper.internal_error "Unexpected hypothesis for Rs"
       end
    | Ri(p,p') ->
       display_attacker_hyp hyp_num_list hl;
      print_string "So the attacker may trigger an input on this channel.";
      newline()
    | Ro(p,p') ->
       display_attacker_hyp hyp_num_list hl;
      print_string "So the attacker may trigger an output on this channel.";
      newline()
    | Rfail(p)  ->
       display_attacker_hyp hyp_num_list hl;
      print_string "So the attacker may test the failure of this term, which may allow it to distinguish cases.";
      newline()
    | TestComm(p,p') ->
       begin
	 match (hyp_num_list, hl) with
	   n1::n2::_, h1::h2::r ->
	     display_step n1;
	     print_string "an input may be triggered on channel ";
	     display_input_fact h1.thefact;
	     print_string ".";
	     newline();
	     display_step n2;
	     print_string "an output may be triggered on channel ";
	     display_output_fact h2.thefact;
	     print_string ".";
	     newline();
	     begin
	       match r with
		 [] -> ()
	       |	[{thefact = Pred({ p_info = [TestUnifP _] }, [v;v'])}] ->
		  print_string "The terms ";
		 WithLinks.term v;
		 print_string " and ";
		 WithLinks.term v';
		 print_string" unify for some values of the secrets and not for others.";
		 newline()
	       |	_ -> Parsing_helper.internal_error "Unexpected hypothesis for TestComm (2)"
	     end;
	     display_constra_list constra;
	     print_string "So the attacker may know whether the communication succeeds, which may allow it to distinguish cases.";
	     newline()
	 | _ -> Parsing_helper.internal_error "Unexpected hypothesis for TestComm"
       end
    | InputSecr p ->
       begin
	 match (hyp_num_list, hl) with
	   [n],[h] ->
	     display_step n;
	     print_string "an input may be triggered on channel ";
	     display_input_fact h.thefact;
	     print_string ".";
	     newline();
	     print_string "Since this channel is secret, the attacker may know whether this secret is a name.";
	     newline()
	 | _ -> Parsing_helper.internal_error "Unexpected hypothesis for InputSecr"
       end
    | OutputSecr p ->
       begin
	 match (hyp_num_list, hl) with
	   [n],[h] ->
	     display_step n;
	     print_string "an output may be triggered on channel ";
	     display_output_fact h.thefact;
	     print_string ".";
	     newline();
	     print_string "Since this channel is secret, the attacker may know whether this secret is a name.";
	     newline()
	 | _ -> Parsing_helper.internal_error "Unexpected hypothesis for InputSecr"
       end
    | WeakSecr ->
       begin
	 match concl with
	   Pred(p, [v;v']) ->
	     print_string "The attacker has the weak secret ";
	     WithLinks.term v;
	     print_string " in the first component, a guess ";
	     WithLinks.term v';
	     print_string " in the second.";
	     newline()
	 | _ -> Parsing_helper.internal_error "Unexpected conclusion for WeakSecr"
       end
    | LblEquiv ->
       display_hyp_basic hyp_num_list hl;
      display_constra_list constra;
      print_string "Using a clause coming from a";
      display_connective Lang.eq1_connective;
      print_string "or";
      display_connective Lang.eq2_connective;
      print_string "declaration in the input file,";
      newline()
    | LblClause ->
       display_hyp_basic hyp_num_list hl;
      display_constra_list constra;
      print_string "Using a clause given in the input file,";
      newline()
    | LblEq ->
       print_string "By definition of equal,";
      newline()
    | Elem _ | TestUnif | LblComp ->
       Parsing_helper.internal_error "These tags should have been handled before"
    | ProcessRule(tags, _) ->
       if hl == [] && constra == [] then
	 WithLinks.concl true concl tags
       else
	 begin
	   display_hyp (List.map (fun t -> t.thefact) hl) hyp_num_list tags;
	   display_constra_list constra;
	   print_string "So ";
	   WithLinks.concl false concl tags
         end;
      print_string ".";
      newline()
    | LblNone ->
       display_hyp_basic hyp_num_list hl;
      display_constra_list constra;
      print_string ("Using the clause number " ^ (string_of_int n) ^ ",");
      newline()


  let explain_history_tree tree =
    let seen_list = ref [] in
    let rec find fact = function
    [] ->
      raise Not_found
      | ((c,f)::l) ->
	 if Termslinks.equal_facts_with_links f fact then c else
	   find fact l
    in
    let count = ref 0 in
    let rec display_history tree =
      match tree.desc with
        FEmpty ->
	  begin
	    match tree.thefact with
	      Out _ ->
	        seen_list := (-1, tree.thefact) :: (!seen_list);
	        -1 (* Do not display hypotheses "begin" *)
	    | _ ->
	       incr count;
	      seen_list := (!count, tree.thefact) :: (!seen_list);
	      (* print_string ((string_of_int (!count)) ^ ". We assume as hypothesis that"); *)
	      Lang.history_item (!count);
	      print_string "We assume as hypothesis that";
	      newline();
	      WithLinks.fact tree.thefact;
	      print_string ".";
	      newline();
	      (!count)
	  end
      | FHAny ->
	 incr count;
	seen_list := (!count, tree.thefact) :: (!seen_list);
	(*print_string ((string_of_int (!count)) ^ ". The attacker has some term "); *)
	Lang.history_item (!count);
	print_string "The attacker has some term ";
	display_attacker_fact tree.thefact;
	print_string ".";
	newline();
	WithLinks.fact tree.thefact;
	print_string ".";
	newline();
	(!count)
      | FRemovedWithProof t' ->
	 begin
	   try
	     find tree.thefact (!seen_list)
	   with Not_found ->
	     display_history t'
	 end
      | FEquation(h) ->
	 let hyp_num = display_history h in
	 incr count;
	 seen_list := (!count, tree.thefact) :: (!seen_list);
	(* print_string ((string_of_int (!count)) ^ ". "); *)
	 Lang.history_item (!count);
	 display_step hyp_num;
	 print_string "we have ";
	 WithLinks.fact h.thefact;
	 print_string ".";
	 newline();
	 print_string "Using an equation, we obtain";
	 newline();
	 WithLinks.fact tree.thefact;
	 print_string ".";
	 newline();
	 (!count)
      | FRule(n, descr, constra, hl) ->
	 match descr with
	   Elem _ | TestUnif ->
	    (* Do not display clauses that conclude member, testunif *)
	     seen_list := (-1, tree.thefact) :: (!seen_list);
	     -1
	 | LblComp ->
	    incr count;
	   Lang.history_item (!count);
	   print_string ("The attacker has all names created in the compromised sessions.");
           newline();
	   seen_list := (!count, tree.thefact) :: (!seen_list);
	   WithLinks.fact tree.thefact;
	   print_string ".";
	   newline();
	   (!count)
	 | _ ->
	    let hyp_num_list = List.map display_history (List.rev hl) in
	    incr count;
	    Lang.history_item (!count);
	    seen_list := (!count, tree.thefact) :: (!seen_list);
	    display_clause_explain n descr (List.rev hyp_num_list) hl constra tree.thefact;
	    WithLinks.fact tree.thefact;
	    print_string ".";
	    newline();
	    (!count)
    in
    print_string Lang.start_numbered_list;
    ignore (display_history tree);
    print_string Lang.end_numbered_list

(* Convert the integer n into a string corresponding to (n+1)-th *)

  let order_of_int n =
    (string_of_int (n+1)) ^
      (
        if (n>=10) && (n<14) then "th" else
          match (n+1) mod 10 with
          | 1 -> "st"
          | 2 -> "nd"
          | 3 -> "rd"
          | _ -> "th")

(* Display reduction step *)

  let display_step = function
  RNil(n) -> print_string ((order_of_int n) ^" process: Reduction 0")
    | RPar(n) -> print_string ((order_of_int n) ^" process: Reduction |")
    | RRepl(n, cpn) -> print_string ((order_of_int n) ^" process: Reduction ! "^(string_of_int cpn)^" copy(ies)")
    | RRestr(n, na, n') ->
       print_string ((order_of_int n) ^" process: new " ^ na.f_name ^ " creating ");
      display_term2 n'
    | RLet1(n, pat, t) ->
       print_string ((order_of_int n) ^" process: let ");
      display_pattern pat;
      print_string " = ";
      display_term2 t;
      print_string " succeeds"
    | RLet2(n, pat, t) ->
       print_string ((order_of_int n) ^" process: let ");
      display_pattern pat;
      print_string " = ";
      display_term2 t;
      print_string " fails"
    | RInput(n, tc, pat, mess_term) ->
       print_string ((order_of_int n) ^" process: in(");
      display_term2 tc;
      print_string ", ";
      display_pattern pat;
      print_string ") done with message ";
      display_term2 mess_term
    | ROutput1(n, tc, t) ->
       print_string ((order_of_int n) ^" process: out(");
      display_term2 tc;
      print_string ", ";
      display_term2 t;
      print_string ") done"
    | ROutput2 (n, tc, t) ->
       print_string ((order_of_int n) ^" process: out(");
      display_term2 tc;
      print_string ", ";
      display_term2 t;
      print_string ") destructor fails"
    | RTest1(n, t) ->
       print_string ((order_of_int n) ^" process: if ");
      display_term2 t;
      print_string " succeeds"
    | RTest2(n, t) ->
       print_string ((order_of_int n) ^" process: if ");
      display_term2 t;
      print_string " fails"
    | RTest3(n, t) ->
       print_string ((order_of_int n) ^" process: if ");
      display_term2 t;
      print_string " destructor fails"
    | RBegin1(n, t) ->
       print_string ((order_of_int n) ^" process: event(");
      display_term2 t;
      print_string ") executed"
    | RBegin2(n, t) ->
       print_string ((order_of_int n) ^" process: event(");
      display_term2 t;
      print_string ") destructor fails or event blocks"
    | REnd(n, t) ->
       print_string ((order_of_int n) ^" process: event(");
      display_term2 t;
      print_string ") is the goal"
    | RPhase(n) ->
       print_string ("Switching to phase " ^ (string_of_int n))
    | RLetFilter1(n, bl, _, f)  ->
       print_string ((order_of_int n) ^" process: let ");
      let first = ref true in
      List.iter (fun b ->
	if !first then
	  first := false
	else
	  print_string ", ";
	print_string (varname b)
      ) bl;
      print_string " suchthat ";
      display_fact2 f;
      print_string " executed"
    | RLetFilter2(n, bl, f)  ->
       print_string ((order_of_int n) ^" process: let ");
      let first = ref true in
      List.iter (fun b ->
	if !first then
	  first := false
	else
	  print_string ", ";
	print_string (varname b)
      ) bl;
      print_string " suchthat ";
      display_fact2 f;
      print_string ": destructor fails or let...suchthat blocks"
    | RLetFilter3(n, bl, f)  ->
       print_string ((order_of_int n) ^" process: let ");
      let first = ref true in
      List.iter (fun b ->
	if !first then
	  first := false
	else
	  print_string ", ";
	print_string (varname b)
      ) bl;
      print_string " suchthat ";
      display_fact2 f;
      print_string ": let...suchthat fails"
    | RIO(ninput, tc', pat, n, tc, t) ->
       print_string ((order_of_int ninput) ^" process: in(");
      display_term2 tc';
      print_string ", ";
      display_pattern pat;
      print_string ") reduces with ";
      print_string ((order_of_int n) ^" process: out(");
      display_term2 tc;
      print_string ", ";
      display_term2 t;
      print_string ")"
    | RIO2(ninput, tc', pat, n, tc, t) ->
       print_string ((order_of_int ninput) ^" process: in(");
      display_term2 tc';
      print_string ", ";
      display_pattern pat;
      print_string ") reduces with ";
      print_string ((order_of_int n) ^" process: out(");
      display_term2 tc;
      print_string ", ";
      display_term2 t;
      print_string ") but input fails"
    | RInsert1(n, t) ->
       print_string ((order_of_int n) ^" process: insert ");
      display_term2 t;
      print_string " done"
    | RInsert2 (n, t) ->
       print_string ((order_of_int n) ^" process: insert ");
      display_term2 t;
      print_string " destructor fails"
    | RGet(n, pat, t, m) ->
       print_string ((order_of_int n) ^" process: get ");
      display_pattern pat;
      begin
	match t with
	  FunApp(f, []) when f == Terms.true_cst -> ()
	| _ -> print_string " suchthat "; display_term2 t
      end;
      print_string " done with entry ";
      display_term2 m
    | RGet2(n, pat) ->
       print_string ((order_of_int n) ^" process: else branch of get ");
      display_pattern pat;
      print_string " taken ";
    | RInit -> print_string "Initial state"
    | RNamedProcess(n, name, tl) ->
	print_string ((order_of_int n) ^ " process: Beginning of " ^ name);
	if tl != [] then
	  begin
	    print_string "(";
	    let first = ref true in
	    List.iter (fun t ->
              if !first then
		first := false
              else
		print_string ", ";
              display_term2 t) tl;
	    print_string ")"
	  end
        

  let display_step_short display_loc = function
  RInput(n, tc, pat, mess_term) ->
    display_keyword "in";
    print_string "(";
    display_term2 tc;
    print_string ", ";
    display_term2 mess_term;
    print_string ")";
    display_loc n;
    newline();
    newline()
    | ROutput1(n, tc, t) ->
       display_keyword "out";
      print_string "(";
      display_term2 tc;
      print_string ", ";
      display_term2 t;
      print_string ")";
      display_loc n;
      newline();
      newline()
    | REnd(n,t) -> () (* REnd is not displayed because it always follows RBegin1 which already displays what we want *)
    | RBegin1(n, t) ->
       display_keyword "event";
      print_string "(";
      display_term2 t;
      print_string ")";
      display_loc n;
      newline();
      newline()
    | RRestr(n,na,n') ->
       display_keyword "new ";
      print_string na.f_name;
      print_string " creating ";
      display_term2 n';
      display_loc n;
      newline();
      newline()
    | RInsert1(n, t) ->
       display_keyword "insert ";
      display_term2 t;
      display_loc n;
      newline();
      newline()
    | RGet(n, pat, t, m) ->
       display_keyword "get ";
      display_term2 m;
      display_loc n;
      newline();
      newline()
    | RGet2(n, pat) ->
       print_string "else branch of get " ;
      display_pattern pat;
      print_string " taken";
      display_loc n;
      newline();
      newline()
    | RIO(ninput, tc', pat, n, tc, t) ->
       display_keyword "out";
      print_string "(";
      display_term2 tc;
      print_string ", ";
      display_term2 t;
      print_string ")";
      display_loc n;
      print_string " received";
      display_loc ninput;
      newline();
      newline()
    | RIO2(ninput, tc', pat, n, tc, t) ->
       display_keyword "out";
      print_string "(";
      display_term2 tc;
      print_string ", ";
      display_term2 t;
      print_string ")";
      display_loc n;
      print_string " received";
      display_loc ninput;
      print_string " (input fails)";
      newline();
      newline()
  (*  | RNamedProcess(n, name, l) ->
      display_keyword ("Beginning of process " ^ name);
      print_string "(";
      let first = ref true in
      List.iter (fun t ->
      if !first then
      first := false
      else
      print_string ", ";
      display_term2 t) l;
      print_string ")";
      newline();
      newline() *)
    | _ -> ()

  let display_bi_term (t1,t2) =
    if Terms.equal_terms t1 t2 then
      display_term2 t1
    else
      begin
        print_string "choice[";
        display_term2 t1;
        print_string ", ";
        display_term2 t2;
        print_string "]"
      end

(* Apply f to the n first elements of a list *)

  let rec itern f n = function
  [] -> ()
    | (a::l) ->
       if n > 0 then
	 begin
	   f a;
	   itern f (n-1) l
	 end

(* TO DO display the additional entries in tables ?
   Perhaps not necessary, since this is clear from the executed "insert" instructions. *)

  let rec display_reduc_state display_a display_state state =
    if (not (!Param.display_init_state)) && (state.previous_state = None) then
    (* Do not display the initial state; used when the
       beginning of the trace has already been displayed *)
      List.length state.public
    else
      let display_next_state =
        match state.comment with
        | RInput _ | RIO _ | RIO2 _ | RPhase _ -> true
        | _ -> false
      in
      let display_cur_state = display_state ||
        match state.comment with
        | RIO _ | RIO2 _ | RPhase _ -> true
        | _ -> state.previous_state = None
      in
      let old_size_public =
        match state.previous_state with
          Some s -> display_reduc_state display_a display_next_state s
        | None -> 0
      in
      display_step state.comment;
      newline ();
      newline ();
      let size_public = List.length state.public in
      if size_public > old_size_public then
        begin
          print_string "Additional knowledge of the attacker:";
          print_string Lang.start_list;
          itern (fun x ->
	    Lang.basic_item();
	    display_a x) (size_public - old_size_public) state.public;
          print_string Lang.end_list;
          print_string Lang.hline
        end;
      if display_cur_state then
        begin
          print_string "New processes:";
          newline();
          let n = ref 0 in
          if List.length state.subprocess > 1 then
	    begin
	      print_string "(";
	      newline()
	    end;
          List.iter (fun (proc, _,_,_,_) ->
	    if !n > 0 then
	      begin
	        print_string ") | (";
	        newline()
	      end;
	    display_process Lang.indentstring proc;
	    incr n) state.subprocess;
          if List.length state.subprocess > 1 then
	    begin
	      print_string ")";
	      newline()
	    end;
          newline ();
          print_string Lang.hline
        end;
      size_public

  let display_process_loc p =
    match p with
      (Test(_,_,_,occ) | Let(_,_,_,_,occ) | Input(_,_,_,occ) | Output(_,_,_,occ) | Restr(_,_,_,occ) |
          LetFilter(_,_,_,_,occ) | Event(_,_,_,occ) | Insert(_,_,occ) | Get(_,_,_,_,occ)),
  name_params, _, _, _ ->
    print_string " at ";
    display_occ occ;
    let first = ref true in
    List.iter (function
  (MSid _, sid, Always) ->
    if !first then print_string " in copy " else print_string ", ";
    first := false;
    display_term2 sid
    | _ -> ()
    ) (List.rev name_params)
    | _ -> Parsing_helper.internal_error "Unexpected process"

  let display_loc = function
  LocAttacker ->
    print_string " by the attacker"
    | LocProcess(n,p) ->
       match !Param.trace_display with
	 Param.NoDisplay | Param.ShortDisplay ->
	   display_process_loc p
       | Param.LongDisplay ->
	  print_string (" in the " ^ (order_of_int n) ^ " process")

  let rec display_labeled_trace state =
    if (!Param.display_init_state) || (state.previous_state != None) then
    (* Do not display the initial state when the
       beginning of the trace has already been displayed *)
      begin
        begin
	  match state.previous_state with
	    Some s -> display_labeled_trace s
	  | None -> ()
        end;
        let display_loc n =
	  match state.previous_state with
	    None -> Parsing_helper.internal_error "Previous state should exist"
	  | Some s ->
	     display_process_loc (List.nth s.subprocess n)
        in
        display_step_short display_loc state.comment
      end

  let display_explained_fact = function
  Pred({p_info = [Attacker(n,_)]} as p, [v]) ->
    print_string "The attacker has the message ";
    display_term2 v;
    display_phase p
    | Pred({p_info = [Mess(n,_)]} as p, [vc;v]) ->
       print_string "The message ";
      display_term2 v;
      print_string " is sent on channel ";
      display_term2 vc;
      display_phase p
    | Pred({p_info = [AttackerBin(n,_)]} as p, [v;v']) ->
       print_string "The attacker has the message ";
      display_term2 v;
      print_string " (resp. ";
      display_term2 v';
      print_string ")";
      display_phase p
    | Pred({p_info = [MessBin(n,_)]} as p, [vc;v;vc';v']) ->
       print_string "The message ";
      display_term2 v;
      print_string " is sent on channel ";
      display_term2 vc;
      print_string " (resp. message ";
      display_term2 v';
      print_string " on channel ";
      display_term2 vc';
      print_string ")";
      display_phase p
    | Pred(p, [e]) when p == Param.end_pred ->
       print_string "The event ";
      display_term2 e;
      print_string " is executed"
    | Pred(p, [e';e]) when p == Param.end_pred_inj ->
       print_string "The event ";
      display_term2 e;
      print_string " is executed in session ";
      display_term2 e'
    | Pred({p_info = [InputP(n)]} as p, [e]) ->
       print_string "An input is executed on channel ";
      display_term2 e;
      display_phase p
    | Pred({p_info = [InputPBin(n)]} as p, [e;e']) ->
       print_string "An input is executed on channel ";
      display_term2 e;
      print_string " (resp. ";
      display_term2 e';
      print_string ")";
      display_phase p
    | Pred({p_info = [OutputP(n)]} as p, [e]) ->
       print_string "An output is executed on channel ";
      display_term2 e;
      display_phase p
    | Pred({p_info = [OutputPBin(n)]} as p, [e;e']) ->
       print_string "An output is executed on channel ";
      display_term2 e;
      print_string " (resp. ";
      display_term2 e';
      print_string ")";
      display_phase p
    | Pred({p_info = [Table(n)]} as p, [e]) ->
       print_string "The table element ";
      display_term2 e;
      print_string " is present";
      display_phase p
    | Pred({p_info = [TableBin(n)]} as p, [e;e']) ->
       print_string "The table element ";
      display_term2 e;
      print_string " (resp. ";
      display_term2 e';
      print_string ") is present";
      display_phase p
    | _ -> Parsing_helper.internal_error "Unexpected goal"


  let display_goal display_a noninterftest_to_string g hyp =
    begin
      match g with
        Fact f ->
      (* WithLinks.fact f; *)
          display_explained_fact f;
          print_string ".";
          newline()
      | InjGoal(f,sid',n) ->
         begin
	   match f with
	     Pred(p, [e';e]) when p == Param.end_pred_inj ->
	       print_string "The event ";
	       display_term2 e;
	       print_string " is executed in session ";
	       display_term2 e';
	       print_string " and in session ";
	       display_term2 sid';
	       print_string ".";
	       newline()
	   | _ -> Parsing_helper.internal_error "InjGoal should have an injective event as argument"
         end
      | WeakSecrGoal(l, t, w1, w2) ->
         print_string "The attacker tests whether ";
        begin
	  match t with
	    FailTest t' ->
	      display_term2 t';
	      print_string " is fail knowing "
	  | EqTest(t1,t2) ->
	     display_term2 t1;
	    print_string " = ";
	    display_term2 t2;
	    print_string " knowing "
        end;
        display_list (fun (t,b) ->
	  print_string ((varname b) ^ " = ");
	  display_term2 t) ", " l;
        print_string ".";
        newline();
        print_string "This allows the attacker to know whether ";
        display_term2 w2;
        print_string " = ";
        display_term2 w1;
        print_string ".";
        newline()
      | NonInterfGoal t ->
         match t with
	   ProcessTest(hypspec,tl,loc) | InputProcessTest(hypspec,tl,_,loc)->
	     begin
	       match !loc with
	         None -> Parsing_helper.internal_error "Location should have been filled"
	       | Some(n,p) ->
		  match !Param.trace_display with
		    Param.NoDisplay | Param.ShortDisplay ->
		      print_string ("A" ^ (noninterftest_to_string t));
		      display_process_loc p;
		      print_string "."
		  | Param.LongDisplay ->
		     print_string ("The " ^ (order_of_int n) ^ (noninterftest_to_string t));
		    print_string "."
	     end;
	     newline()
         |	ApplyTest(f,tl) ->
	    print_string "The attacker tries to apply ";
	   display_function_name f;
	   print_string " to the messages ";
	   display_list display_a ", " tl;
	   print_string " that he has.";
	   newline();
	   print_string (noninterftest_to_string t);
	   newline()
         |	NIFailTest t' ->
	    print_string "The attacker tests whether ";
	   display_a t';
	   print_string " is fail.";
	   newline();
	   print_string (noninterftest_to_string t);
	   newline()
         |	CommTest(t1,t2,loc) ->
	    print_string "An input on channel ";
	   display_a t1;
	   print_string " and an output on channel ";
	   display_a t2;
	   print_string " are present simultaneously.";
	   newline();
	   begin
	     match !loc with
	       None -> Parsing_helper.internal_error "Location should have been filled"
	     | Some(iloc,oloc) ->
		print_string "(The input is performed";
	       display_loc iloc;
	       print_string ";";
	       newline();
	       print_string "The output is performed";
	       display_loc oloc;
	       print_string ".)";
	       newline()
	   end;
	   print_string (noninterftest_to_string t);
	   newline()
         |	InputTest (t1,loc) ->
	    print_string "An input on channel ";
	   display_a t1;
	   print_string " is performed";
	   begin
	     match !loc with
	       None -> Parsing_helper.internal_error "Location should have been filled"
	     | Some iloc -> display_loc iloc
	   end;
	   print_string ".";
	   newline();
	   print_string (noninterftest_to_string t);
	   newline()
         |	OutputTest (t1, loc) ->
	    print_string "An output on channel ";
	   display_a t1;
	   print_string " is performed";
	   begin
	     match !loc with
	       None -> Parsing_helper.internal_error "Location should have been filled"
	     | Some oloc -> display_loc oloc
	   end;
	   print_string ".";
	   newline();
	   print_string (noninterftest_to_string t);
	   newline()
         |	NIEqTest(t1,t2) ->
	    print_string "The attacker tests whether ";
	   display_a t1;
	   print_string " = ";
	   display_a t2;
	   print_string ".";
	   newline();
	   print_string (noninterftest_to_string t);
	   newline()
    end;
    if hyp = [] then
      begin
        print_string "A trace has been found.";
        newline()
      end
    else
      begin
        print_string "A trace has been found, assuming the following hypothesis:";
        display_item_list WithLinks.fact hyp
      end

end

module Html = LangDisp(LangHtml)

module Text = LangDisp(LangText)

module Def =
struct

  let print_line s =
    if !Param.html_output then
      Html.print_line s
    else
      Text.print_line s

end

(* Graphical display of traces *)

module LangGviz  =
struct
  let previousf = ref []

  let f = ref stdout

  let close() =
    match !previousf with
      [] -> Parsing_helper.internal_error "No html file to close"
    | (f'::r) ->
       close_out (!f);
      f := f';
      previousf := r

  let openfile fname title =
    previousf := (!f) :: (!previousf);
    begin
      try
        f := open_out fname
      with Sys_error _ ->
        Parsing_helper.user_error ("Error: could not open dot file.
        The html directory that you specified, " ^ (!Param.html_dir) ^ ",
        probably does not exist.\n")
    end

  let print_string s =
    if (!previousf) == [] then
      Parsing_helper.internal_error "dot output with no open dot file.\n";
    output_string (!f) s

  let wrap_limit = ref 45

  let wrap_mark = ref 0

  let buff = Buffer.create 1024

  let add_buffer = Buffer.add_string buff

  let reset_wrap_mark() =
    wrap_mark := 0

  let wrap_if_necessary() =
    if !wrap_mark > !wrap_limit then
      begin
        add_buffer "\\n";
        reset_wrap_mark();
      end

  let increase_wrap_mark nb =
    wrap_mark := !wrap_mark + nb

  let add_buff_incr_wrap string =
    add_buffer string;
    let string_len = String.length string in
    increase_wrap_mark string_len

  let convert_funname s =
    match s with
      "&&" -> "\\&\\&"
    | "<>" -> "\\<\\>"
    | "||" -> "\\|\\|"
    | _ -> s

  let print_buffer () =
    if (!previousf) == [] then
      Parsing_helper.internal_error "dot output with no open dot file.\n";
    Buffer.output_buffer (!f) buff;
    Buffer.clear buff

  let rec print_list f sep = function
  [] -> ()
    | [a] -> f a
    | (a::l) ->
       f a;
      add_buff_incr_wrap sep;
      print_list f sep l

  let rec print_term term  =
    wrap_if_necessary();
    match term with
      FunApp(f, l) ->
        begin
          match f.f_cat with
            Name _ ->
              add_buff_incr_wrap (convert_funname f.f_name)
          | Choice ->
             begin
               match l with
                 [t1; t2] ->
                   if Terms.equal_terms t1 t2 then
                     print_term t1
                   else
                     begin
                       add_buff_incr_wrap ("choice[");
                       print_term_list l;
                       add_buff_incr_wrap "]"
                     end
               | _ -> Parsing_helper.internal_error "Choice expects 2 arguments"
             end
          | _ ->
             match f.f_name with
               "=" | "||" | "&&" | "<>" ->
		(* Infix functions *)
		 begin
		   match l with
		     [t1;t2] ->
                       add_buff_incr_wrap "(";
                       print_term t1;
		       add_buff_incr_wrap " ";
		       add_buff_incr_wrap ((convert_funname f.f_name) ^ " ");
		       print_term t2;
		       add_buff_incr_wrap ")"
            	   | _ ->
                      Parsing_helper.internal_error
                        "infix operators should have 2 arguments"
		 end
             | "if-then-else" ->
	        begin
		  match l with
		    [t1;t2;t3] ->
		      add_buff_incr_wrap "(if ";
		      print_term t1;
		      add_buff_incr_wrap " then ";
		      print_term t2;
		      add_buff_incr_wrap " else ";
		      print_term t3;
                      add_buff_incr_wrap ")"
		  | _ ->
                     Parsing_helper.internal_error
                       "if-then-else should have 3 arguments"
	        end
	     | _ ->
	        add_buff_incr_wrap (convert_funname f.f_name);
	       if (l != []) || (f.f_name = "") || not (!Param.typed_frontend)
               then
	         begin
	           add_buff_incr_wrap "(";
		   print_term_list l;
		   add_buff_incr_wrap ")"
	         end
        end
    | Var v ->
       add_buff_incr_wrap v.sname;
      let v_index = string_of_int v.vname in
      add_buff_incr_wrap v_index


  and print_term_list l = print_list print_term "," l

  let rec print_pattern pat =
    wrap_if_necessary();
    match pat with
    | PatVar v ->
       add_buff_incr_wrap v.sname;
      let v_index = string_of_int v.vname in
      add_buff_incr_wrap v_index;
      if !Param.typed_frontend then
	begin
	  add_buff_incr_wrap ": ";
	  add_buff_incr_wrap v.btype.tname;
	end
    | PatTuple (f,l) ->
       add_buff_incr_wrap (convert_funname f.f_name);
      if (l != []) || (f.f_name = "") || not (!Param.typed_frontend) then
	begin
	  add_buff_incr_wrap "(";
	  print_pattern_list l;
	  add_buff_incr_wrap ")";
	end
    | PatEqual t ->
       add_buff_incr_wrap "=";
      print_term t

  and print_pattern_list l = print_list print_pattern "," l

  let print_fact fact =
    wrap_if_necessary();
    match fact with
      Pred(chann,t) ->
        add_buff_incr_wrap chann.p_name;
        if not (!Param.typed_frontend) then add_buff_incr_wrap ":";
        if t != [] then
	  begin
	    if !Param.typed_frontend then add_buff_incr_wrap "(";
	    print_term_list t;
	    if !Param.typed_frontend then add_buff_incr_wrap ")";
	  end
    | Out(t,l) ->
       add_buff_incr_wrap "begin";
      if !Param.typed_frontend then
        add_buff_incr_wrap "("
      else
        add_buff_incr_wrap ":";
      print_term t;
      List.iter (fun (v,t) ->
        wrap_if_necessary();
        add_buff_incr_wrap ", ";
        add_buff_incr_wrap v.sname;
        let v_index = string_of_int v.vname in
        add_buff_incr_wrap (v_index);
	print_term t
      ) l;
      if !Param.typed_frontend then
        add_buff_incr_wrap ")"

  let append3 l1 l2 l3 =
    List.rev_append (List.rev (List.rev_append (List.rev l1) l2)) l3

  (* Nil means inactive process *)
  type style_type = Box | Point | Nil | Att

  type proc_type = {pnb: int list; (* if process is attacker, pnb = [] *)
                    pstate: int; (* the process state *)
                    pstyle: style_type; (* the process style *)
                   }

  type ginfo = (*the informations for the graph *)
    { plst: proc_type list; (* the processes list*)
      attacker: proc_type; (* the attacker process *)
      rparinfo: (int * int) option; (* Some(n1, n2) if the previous processes were RPar between n1 and n2 *)
      prev_pnb: int; (* The number of the previous process drawn*)
      prev_pstyle: style_type; (* The style of the previous process *)
      ins_or_get: bool; (* True if the box that is written contains an RGet or RInsert *)
    }
  (* getter and setter methods *)
  let get_pnb proc = proc.pnb

  let get_pstate proc = proc.pstate

  let get_pstyle proc = proc.pstyle

  let is_active proc = not (get_pstyle proc = Nil)

  let is_point proc = (get_pstyle proc = Point)

  let is_box proc = (get_pstyle proc = Box)

  let create_proc pnb pstate pstyle = {pnb; pstate; pstyle}

  let set_pstyle style proc = {proc with pstyle = style}

  let set_pstate  state proc {pnb; pstate; pstyle} =
    {proc with pstate = state}

  let make_proc_inactive = set_pstyle Nil

  let next_pstate new_pstyle proc = {proc with pstyle = new_pstyle; pstate = get_pstate proc + 1 }

  let add_nb_to_proc new_nb proc  = {proc with pnb = new_nb::(get_pnb proc)}

  let get_plst ginfo = ginfo.plst

  let get_attacker ginfo = ginfo.attacker

  let get_rparinfo ginfo = ginfo.rparinfo

  let get_prev_pnb ginfo = ginfo.prev_pnb

  let get_prev_pstyle ginfo = ginfo.prev_pstyle

  let get_ins_or_get ginfo = ginfo.ins_or_get

  let create_ginfo plst attacker rparinfo prev_pnb prev_pstyle ins_or_get =
    {plst; attacker; rparinfo; prev_pnb; prev_pstyle; ins_or_get}

  let set_plst new_plst ginfo = {ginfo with plst = new_plst}

  let set_attacker new_att ginfo = {ginfo with attacker = new_att}

  let set_prev_pnb new_pnb ginfo = {ginfo with prev_pnb = new_pnb}

  let set_prev_pstyle new_style ginfo = {ginfo with prev_pstyle = new_style}

  let set_rparinfo new_rparinfo ginfo = {ginfo with rparinfo = new_rparinfo}

  let set_ins_or_get new_ins_or_get ginfo =
    {ginfo with ins_or_get = new_ins_or_get}

  let prev_is_nil ginfo = (get_prev_pstyle ginfo = Nil)

  let prev_is_box ginfo = (get_prev_pstyle ginfo = Box)

  let get_pnb_from_state = function
  RRestr(n, _, _) | RLet1(n, _, _) | RLet2(n, _, _) | RTest1(n, _)
    | RTest2(n, _) | RTest3(n, _) | RBegin1(n, _) | RBegin2(n, _)
    | RLetFilter1(n, _, _, _) | RLetFilter2(n, _, _) | RLetFilter3(n, _, _)
    | RInsert1(n, _) | RInsert2(n, _) | RGet(n, _, _, _) | RInput(n, _, _, _)
    | RPar(n) | RRepl(n, _) | ROutput1(n, _, _) | ROutput2(n, _, _) | REnd(n, _) | RIO(n, _, _, _, _, _)
    | RIO2(n, _, _, _, _, _) | RGet2(n, _) | RNil(n) | RNamedProcess(n, _, _)  ->
       n
    | RPhase(_) | RInit -> assert false

  let get_ginfo_params ginfo =
    (get_plst ginfo, get_attacker ginfo, get_rparinfo ginfo,
     get_prev_pnb ginfo, get_prev_pstyle ginfo, get_ins_or_get ginfo)

  (* exception for get_active_n_to_m and nth_active *)
  exception Wrong_size of string

 (* get_active_n_to_m n m plst: return (first, med, last),  where *)
 (* first @ med @ last = plst, and the list med starts with the n + 1-th active *)
 (* process and ends with the m + 1-th active process *)
  let get_active_n_to_m n m plst =
    let active_after_n = ref false in
    let rec aux n p plst first med last =
      match n, p with
        0, 0 -> List.rev first, List.rev med, plst
      | 0, p ->
         (match plst with
           [] -> raise (Wrong_size "get_active_n_to_m fails")
         | hd::tl ->
            if is_active hd  then
              begin
                active_after_n := true;
                aux 0 (p - 1) tl first (hd::med) last
              end
            else
              if not !active_after_n then
                aux 0 p tl (hd::first) med last
              else
                aux 0 p tl first (hd::med) last
         )
      | n, p ->
         (match plst with
           [] -> raise (Wrong_size "get_active_n_to_m fails")
         | hd::tl ->
            if is_active hd then
              aux (n - 1) p tl (hd::first) med last
            else
              aux n p tl (hd::first) med last)
    in
    aux n (m - n + 1) plst [] [] []

  let nb_of_active_proc plst =
    let rec aux n = function
    [] -> n
      | hd::tl ->
         if is_active hd then aux (n + 1) tl
         else aux n tl
    in
    aux 0 plst

  (* nth_active plst n: return the nth active process in plst *)
  let rec nth_active plst n  =
    match plst, n with
      [], _ -> raise (Wrong_size "nth_active fails")
    | hd::tail, 0 -> if is_active hd then hd
      else nth_active tail 0
    | hd::tail, n -> if is_active hd then nth_active tail (n - 1)
      else nth_active tail n

  (* string_of_proc proc: get the string corresponding to proc *)
  let string_of_proc proc  =
    let pnb = get_pnb proc and pstate = get_pstate proc
    and pstyle = get_pstyle proc in
    if pstyle = Att then
      "Att__" ^ string_of_int pstate
    else
      let name =
        String.concat "_" (List.rev_map (fun a -> string_of_int a) pnb) in
      "P" ^ name ^ "__" ^ string_of_int  pstate

  (* write_node process lab options: write a node for the process in the *)
  (* open dot file. The node label is the string lab, and the options *)
  (* are options. *)
  let write_node proc lab options =
    let sop = string_of_proc proc in
    add_buffer sop;
    add_buffer " [";
    add_buffer "label = \"";
    add_buffer lab;
    add_buffer "\"";
    List.iter (fun x -> add_buffer (", " ^ x)) options;
    add_buffer "]\n";
    print_buffer()

  (* write_edge p1 p2 term_lab options: write an edge in the open dot file *)
  (* between node p1 and p2. The label of the node is print_term term_lab, *)
  (* and the options are options. *)
  let write_edge p1 p2 term_lab options =
    reset_wrap_mark();
    let string_of_proc1 = string_of_proc p1 in
    let string_of_proc2 = string_of_proc p2 in
    add_buffer (string_of_proc1 ^ " -> " ^ string_of_proc2);
    add_buffer " [";
    add_buffer "label = \"";
    (match term_lab with
      None -> ()
    | Some t ->
       print_term t);
    add_buffer "\"";
    List.iter (fun x -> add_buffer (", " ^ x)) options;
    add_buffer "]\n";
    print_buffer()

  (* write_same_rank plst:write in the open dot file a line to align *)
  (* the processes in plst horizontally *)
  let write_same_rank plst =
    if List.length plst > 1 then
      begin
        add_buffer "{rank = same;";
        List.iter (fun x -> add_buffer (" " ^ (string_of_proc x))) plst;
        add_buffer "}\n";
        print_buffer()
      end



  (* update_plst plst n n_proc lst: replace the n-th active process *)
  (* in plst by the list of new process n_plst, and return *)
  (* the modified list *)
  let update_plst plst n n_plst =
    let (first, _, last) = get_active_n_to_m n n plst in
    append3 first n_plst last


  (* init_node plst n: initialize the nth active process of plst in *)
  (*  the open dot file *)
  let init_node plst n =
    let proc = nth_active plst n in
    let string_of_proc = string_of_proc proc in
    add_buffer string_of_proc;
    add_buffer " [";
    add_buffer "shape = record, label = \"{ "

  (* close_node(): close the last node which is written in the open dot file *)
  let close_node () =
    add_buffer "}\"]\n";
    reset_wrap_mark();
    print_buffer()

  (* add_label_to_buff state: add the label corresponding to the state *)
  (* argument in the open dot file. Return true if state is an Insert or a *)
  (* Get, false otherwise *)
  let add_label_to_buff state = 
    reset_wrap_mark();
    (match state with
      RRestr(n, na, n') ->
      add_buffer "new ";
      print_term n';
    | RLet1(n, pat, t) ->
      add_buffer "let ";
      print_pattern pat;
      add_buff_incr_wrap " = ";
      print_term t
    | RLet2(n, pat, t) ->
      add_buff_incr_wrap "let ";
      print_pattern pat;
      add_buff_incr_wrap " fails";
    | RTest1(n, t) ->
      add_buff_incr_wrap "if ";
      print_term t
    | RTest2(n, t) ->
       add_buff_incr_wrap "if ";
      print_term t;
      add_buff_incr_wrap " fails";
    | RTest3(n, t) ->
       add_buff_incr_wrap "if ";
      print_term t;
      add_buff_incr_wrap " dest. fails";
    | RBegin1(n, t) ->
       add_buff_incr_wrap "event ";
      print_term t
    | RBegin2(n, t) ->
       add_buff_incr_wrap "event ";
      print_term t;
      add_buff_incr_wrap " blocks or dest. fails ";
    | REnd(n, t) ->
       add_buff_incr_wrap "event ";
      print_term t;
      add_buff_incr_wrap " is the goal ";
    | RLetFilter1(n, bl, terms_bl, fact) ->
       add_buff_incr_wrap "let ";
      let first = ref true in
      if not (terms_bl = []) then
        List.iter2 (fun b tb ->
          wrap_if_necessary();
          if !first then
            first := false
          else
            add_buff_incr_wrap ", ";
          add_buff_incr_wrap (b.sname);
          let b_index = string_of_int b.vname in
          add_buff_incr_wrap (b_index);
          print_term tb;
        ) bl terms_bl
      else
        List.iter (fun b ->
          wrap_if_necessary();
          if !first then
            first := false
          else
            add_buff_incr_wrap ", ";
          let b_index = string_of_int b.vname in
          add_buff_incr_wrap (b.sname);
          add_buff_incr_wrap (b_index);
        ) bl;
      add_buff_incr_wrap " suchthat ";
      print_fact fact;
    | RLetFilter2(n, bl, fact) ->
       add_buff_incr_wrap "let ";
      let first = ref true in
      List.iter (fun b ->
        wrap_if_necessary();
        if !first then
          first := false
        else
          add_buff_incr_wrap ", ";
        let b_index = string_of_int b.vname in
        add_buff_incr_wrap (b.sname);
        add_buff_incr_wrap (b_index)
      ) bl;
      add_buff_incr_wrap " suchthat ";
      print_fact fact;
      add_buff_incr_wrap " dest. fails or let... s.t. blocks";
    | RLetFilter3(n, bl, fact) ->
       add_buff_incr_wrap "let ";
      let first = ref true in
      List.iter (fun b ->
        wrap_if_necessary();
        if !first then
          first := false
        else
          add_buffer ", ";
        let b_index = string_of_int b.vname in
        add_buffer (b.sname);
        add_buffer (b_index);
        increase_wrap_mark
          (String.length b.sname + String.length b_index + 2);
      ) bl;
      add_buff_incr_wrap " suchthat ";
      print_fact fact;
      add_buff_incr_wrap " fails"
    | RInsert1(n, t) ->
       add_buff_incr_wrap "insert ";
      print_term t
    | RInsert2(n, t) ->
       add_buff_incr_wrap "insert ";
      print_term t;
      add_buff_incr_wrap " dest. fails"
    | RGet(n, pat, t, m) ->
       add_buff_incr_wrap "get ";
      print_term m
    | RGet2(n, pat) ->
       add_buff_incr_wrap "Else branch of get ";
      print_pattern pat;
      add_buff_incr_wrap " taken";
    | ROutput2(n, tc, t) ->
	add_buff_incr_wrap "out(";
	print_term tc;
	add_buff_incr_wrap ",";
	print_term t;
	add_buff_incr_wrap ") dest. fails";
    | RNamedProcess(n, name, tl) ->
       add_buff_incr_wrap "Beginning of process ";
      add_buff_incr_wrap name;
      if tl != [] then
	begin
	  wrap_if_necessary();
	  add_buff_incr_wrap "(";
	  let first = ref true in
	  List.iter (fun t ->
            if !first then
	      first := false
	    else
	      add_buff_incr_wrap ", ";
            print_term t) tl;
	  add_buff_incr_wrap ")"
	end
    | _ -> assert false);
    match state with
      RGet(_, _, _, _) | RGet2(_, _) | RInsert1(_, _) | RInsert2(_, _) -> true
    | _ -> false

    (* close_box ginfo n: close the n-th active process (a Box) of ginfo.plst *)
    (* and return the  modified ginfo *)
  let close_box ginfo n =
    close_node();
    let (plst, attacker, rparinfo, _, _, ins_or_get) =
      get_ginfo_params ginfo in
    let proc = nth_active plst n in
    let n_proc = next_pstate Point proc in
    write_edge proc n_proc None ["weight = 100"];
    let n_plst = update_plst plst n [n_proc] in
    let new_attacker =
      if ins_or_get then
        begin
          let new_attacker = next_pstate Point attacker in
          write_edge attacker new_attacker None ["weight = 100"];
          write_same_rank [new_attacker; proc];
          new_attacker
        end
      else
        attacker in
    create_ginfo n_plst new_attacker rparinfo n Point false

    (* close_prev_if_box ginfo: close the ginfo.prev_nb process if it s a box *)
    (* and return the modified ginfo *)
  let close_prev_if_box ginfo =
    if (prev_is_box ginfo) then
      let p_pnb = get_prev_pnb ginfo in
      close_box ginfo p_pnb
    else
      ginfo

    (* add_nil ginfo n: make the nth-active process of *)
    (* ginfo.plst (a Point) inactive, and return the modified *)
    (* ginfo *)
  let add_nil ginfo n  =
    let n_ginfo = close_prev_if_box ginfo in
    let (plst, attacker, rparinfo, _, _, _) =
      get_ginfo_params n_ginfo in
    let proc = make_proc_inactive (nth_active plst n) in
    let n_plst = update_plst plst n [proc] in
    create_ginfo n_plst attacker rparinfo n Nil false

  (* add_in_box ginfo n state: add the text corresponding to state in the *)
  (* n-th active process. If it is a box, add it in a new line, otherwise *)
  (* open a new box and add it  *)
  let add_in_box ginfo n state =
    let n_ginfo =
      if (get_prev_pnb ginfo <> n && (not (prev_is_nil ginfo)))  then
        close_prev_if_box ginfo
      else
        ginfo in
    reset_wrap_mark();
    let (plst, attacker, _, _, _, ins_or_get) =
      get_ginfo_params n_ginfo in
    let proc = nth_active plst n in
    if is_point proc then
      begin
	let n_proc = next_pstate Box proc in
        let n_plst = update_plst plst n [n_proc] in
	write_edge proc n_proc None ["weight = 100"];
        init_node n_plst n;
        let new_ins_or_get = (add_label_to_buff state) || ins_or_get in
        create_ginfo n_plst attacker None n Box new_ins_or_get
      end
    else (* is_box proc *)
      begin
        add_buffer " | ";
        let new_ins_or_get = (add_label_to_buff state) || ins_or_get in
        create_ginfo plst attacker None n Box new_ins_or_get
      end

  let add_in_box_and_nil ginfo n state =
    let n_ginfo = add_in_box ginfo n state in
    add_nil n_ginfo n

  (* align_and_write_edge plst term_label edge_options: align the processes *)
  (* in plst, and write an edge in the open dot file from the first process *)
  (* in plst to the last process in plst using the options in the  *)
  (* edge_options array. Return the updated list.*)
  let align_and_write_edge plst term_label edge_options =
    (* align also the inactive processes iff align_inactives is true *)
    let rec align n_plst align_inactives = function
    [] ->
      write_same_rank (n_plst);
      List.rev n_plst
      | proc::tail ->
         if is_active proc then
           begin
             let n_proc = next_pstate Point proc in
             write_edge proc n_proc None ["weight = 100"];
             align (n_proc::n_plst) align_inactives tail
           end
         else
           if align_inactives then
             begin
               let n_proc = next_pstate Nil proc in
               write_node n_proc "" ["style = invisible"];
               write_edge proc n_proc None ["weight = 100"; "style = invisible"];
               align (n_proc::n_plst) true tail
             end
           else
             align (proc::n_plst) false tail
    in
    let write_edge plst =
      let fst = List.hd plst in
      let last = List.hd (List.rev plst) in
      let n_fst = next_pstate Point fst in
      let n_last = next_pstate Point last in
      (* let n_fst' = next_pstate IO n_fst in *)
      (* let n_last' = next_pstate IO n_last in *)
      write_edge fst n_fst None ["weight = 100"];
      write_edge last n_last None ["weight = 100"];
      write_same_rank [n_last; n_fst];
      write_edge n_fst n_last (Some term_label) edge_options;
      (* return the updated list *)
      let plst_tl = List.tl plst in
      let plst_tl_without_last_rev = List.tl (List.rev plst_tl) in
      n_fst::(List.rev_append plst_tl_without_last_rev [n_last])
    in
    align [] true (write_edge (align [] true plst))

  (* write_line_in_out_phase ginfo state: write the line for the *)
  (* state which is RInput or ROutput1 or RPhase in the open dot file and *)
  (* return the modified g_info *)
  let write_line_in_out_phase ginfo state =
    let (n, mess_term, edge_options) =
      match state with
        RInput (n, _, _, t) -> (n, t, ["arrowhead = normal"; "dir = back"])
      | ROutput1(n, _, t) -> (n, t, ["arrowhead = normal"])
      | RPhase(n) ->
         let sname = "Phase " and link = NoLink and unfailing = false
         and btype = {tname = ""} in
         let t = Var({sname; vname = n; unfailing; btype; link}) in
         (0, t, ["style = dotted"])
      | _ -> assert false in
    let n_ginfo = close_prev_if_box ginfo in
    let (plst, attacker, rparinfo, _, _, _) = get_ginfo_params n_ginfo in
    let (first, lst_to_join_aux, last) =
      get_active_n_to_m n (nb_of_active_proc plst - 1) plst in
    let lst_to_join = append3 lst_to_join_aux last [attacker] in
    let lst_draw = align_and_write_edge lst_to_join mess_term edge_options in
    let lst_draw_rev = List.rev lst_draw in
    let n_plst =
      List.rev_append (List.rev first) (List.rev (List.tl lst_draw_rev)) in
    let n_attacker = List.hd lst_draw_rev in
    create_ginfo n_plst n_attacker rparinfo n Point false

  let init_dot_file graph_options edge_options node_options =
    let print_options options =
      let first = ref true in
      List.iter (fun x ->
        if !first then
          first := false
        else
          add_buffer ", ";
        add_buffer x) options
    in
    add_buffer "digraph {\n";
    add_buffer "graph [";
    print_options graph_options;
    add_buffer "]\n";
    add_buffer "edge [";
    print_options edge_options;
    add_buffer "]\n";
    add_buffer "node [";
    print_options node_options;
    add_buffer "]\n";
    print_buffer()

  let end_dot_file () =
    add_buffer "}";
    print_buffer()

  (* write_step_graph plst att rparinfo prev_pnb prev_p_style state: *)
  (* add to the open dot file the necessary lines to display the state state *)
  (* with respect to the given parameters in the open dot file. *)
  (* Return the modified ginfo. *)
  let rec write_step_to_dot_file ginfo state =
    let (plst, attacker, rparinfo, prev_pnb, prev_pstyle, ins_or_get) =
      get_ginfo_params ginfo in
    match rparinfo, state with
      None, RInit ->
        let graph_options = ["ordering = out"] in
        let edge_options = ["arrowhead = none"; "fontsize = 30"] in
        let node_options =
          ["shape = point"; "width = 0"; "height = 0"; "fontsize = 30"] in
        init_dot_file graph_options edge_options node_options;
        let proc0 = create_proc [0] 0 Point and attacker = create_proc [] 0 Att in
        let proc1 = next_pstate Point proc0 in
        write_node attacker "Attacker" ["shape = plaintext"];
        write_node proc0 "Honest Process" ["shape = plaintext"];
        write_same_rank [proc0; attacker];
        write_edge proc0 proc1 None ["weight = 100"];
        create_ginfo [proc1] attacker None 0 Point false

    | None, RNil(n) ->
       add_nil ginfo n

    | None, RRepl(n, cpn) ->
       let n_ginfo = close_prev_if_box ginfo in
       let n_plst = get_plst n_ginfo in
       if cpn = 0 then
         begin
           let proc = nth_active n_plst n in
           write_node proc "!"  ["shape = ellipse"];
           let n_plst' = update_plst n_plst n [make_proc_inactive proc] in
           let n_ginfo = set_prev_pstyle Nil n_ginfo in
           set_prev_pnb n (set_plst n_plst' n_ginfo)
         end
       else
         begin
           let proc = nth_active n_plst n in
           let rec create_cpn acc i = function
           0 -> List.rev acc
             | n -> let proc' = set_pstyle Point proc in
                    create_cpn ((add_nb_to_proc (n - 1) proc')::acc) i (n - 1)
           in
           let cpyl = create_cpn [] 0 cpn in
           write_node proc "!" ["shape = ellipse" ];
           write_same_rank (cpyl);
           List.iter (fun x ->
             write_node x "" ["fixedsize = false"; "width = 0";
                              "height = 0"; "shape = none"];
             if cpn = 1 then
               write_edge proc x None ["weight = 100"]
             else
               write_edge proc x None  []) cpyl;
           let n_plst' = update_plst n_plst n cpyl in
           let n_ginfo = set_prev_pnb n (set_plst n_plst' ginfo) in
           set_prev_pstyle Point n_ginfo
         end

    | None, RRestr(n, _, _) | None, RInsert1(n, _) | None, RGet(n, _, _, _)
    | None, RGet2(n, _) | None, RBegin1(n, _) | None, RNamedProcess(n, _, _) ->
       add_in_box ginfo n state

    | None, REnd(n, _)   ->
       add_in_box_and_nil ginfo n state

    | None, RTest1(n, _) | None, RTest2(n, _)
    | None, RLet1(n, _, _) | None, RLet2(n, _, _)
    | None, RLetFilter1(n, _, _, _)
    | None, RLetFilter3(n, _, _) ->
       if !Param.trace_display = Param.ShortDisplay then
         ginfo
       else
         add_in_box ginfo n state

    | None,  RTest3(n, _) | None, RBegin2(n, _)  | None, RLetFilter2(n, _, _)
    | None, RInsert2(n, _) | None, ROutput2(n, _, _) ->
       if !Param.trace_display = Param.ShortDisplay then
         add_nil ginfo n
       else
         add_in_box_and_nil ginfo n state

    | None, ROutput1(n, _, _) | None,  RInput(n, _, _, _)  | None, RPhase(n) ->
       write_line_in_out_phase ginfo state


    | None,  RIO(ninput, _, _, n, _, t) ->
       let aux_RIO ginfo p q mess_term edge_options=
         let n_ginfo = close_prev_if_box ginfo in
         let (plst, attacker, _, _, _, _) = get_ginfo_params n_ginfo in
         let (first, lst_to_join, last) =
           get_active_n_to_m p q plst in
         let lst_drawn =
           align_and_write_edge lst_to_join mess_term edge_options in
         let n_plst = append3 first lst_drawn last in
         create_ginfo n_plst attacker None n Point false
       in
       if (n < ninput) then
         aux_RIO ginfo n ninput t ["arrowhead = normal"]
       else
         aux_RIO ginfo ninput n t ["arrowhead = normal"; "dir = back"]

    | None, RIO2(ninput, tc', pat, n, tc, t) ->
       let n_ginfo =
         write_step_to_dot_file ginfo (RIO(ninput, tc', pat, n, tc, t)) in
       add_nil n_ginfo ninput

    | None, RPar(n) ->
       let n_ginfo = close_prev_if_box ginfo in
       let (plst, attacker, _, _, _, _) = get_ginfo_params n_ginfo in
       create_ginfo plst attacker (Some(n, n + 1)) n Point false
    | Some(n1, n2),  RPar(n) when (n1 <= n && n <= n2) ->
       create_ginfo plst attacker (Some(n1, n2 + 1)) n Point false

    | Some(n1, n2), s ->
       let print_rpar proc n =
         add_buffer "/*RPar */\n";
         let rec aux acc = function
         0 ->
           write_node proc ""  ["fixedsize = false"; "width = 0";
                                "height = 0"; "shape = none"];
           write_same_rank acc;
           List.rev acc
           | n ->
              let n_proc = set_pstyle Point (add_nb_to_proc (n-1) proc) in
              write_edge proc n_proc None [];
              aux (n_proc::acc) (n - 1)
         in
         aux [] n
       in
       let proc = nth_active plst n1 in
       let (first, _, last) = get_active_n_to_m n1 n1 plst in
       let med = print_rpar proc (n2 - n1 + 1) in
       let n_plst = append3 first med last in
       let n_ginfo =
         create_ginfo n_plst attacker None (get_pnb_from_state state) Point false in
       write_step_to_dot_file n_ginfo s

 (* write_state_to_dot_file state: write the necessary lines to display the *)
 (* trace represented by state in the open dot file. *)
  let write_state_to_dot_file state =
    let rec aux ginfo state =
      if (!Param.display_init_state || (not (state.previous_state = None))) then
        match state.previous_state with
          Some s ->
            let n_ginfo = aux ginfo s in
            write_step_to_dot_file n_ginfo state.comment
        | None ->
           write_step_to_dot_file ginfo state.comment
      else
        ginfo
    in
    let ginfo =
      create_ginfo [] {pnb = []; pstate = 0; pstyle = Att} None 0 Point false in
    let n_ginfo = aux ginfo state in
    ignore (close_prev_if_box n_ginfo);    
    end_dot_file();
end

(*END GRAPH *)
