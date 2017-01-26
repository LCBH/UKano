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
{
open Parsing_helper
open Pitparser

let create_hashtable size init =
  let tbl = Hashtbl.create size in
  List.iter (fun (key,data) -> Hashtbl.add tbl key data) init;
  tbl

(* Typed front-end *)

let keyword_table =
  create_hashtable 11
[ "type", TYPE;
  "set", SET;
  "forall", FORALL;
  "fail", FAIL;
  "or", ORTEXT;
  "const", CONST;
  "letfun", LETFUN;
  "channel", CHANNEL;
  "def", DEFINE;
  "expand", EXPAND;
  "yield", YIELD;
  "proba", PROBA;
  "proof", PROOF;
(* Tables of keys *)
  "table", TABLE;
  "insert", INSERT;
  "get", GET;
(* Common keywords *)
  "param", PARAM;
  "new", NEW;
  "out", OUT;
  "in", IN;
  "if", IF;
  "then", THEN;
  "else", ELSE;
  "fun", FUN;
  "equation", EQUATION;
  "reduc", REDUCTION;
  "pred", PREDICATE;
  "process", PROCESS;
  "let", LET;
  "query", QUERY;
  "putbegin", PUTBEGIN;
  "noninterf", NONINTERF;
  "event", EVENT;
  "not", NOT;
  "elimtrue", ELIMTRUE;
  "free", FREE;
  "clauses", CLAUSES;
  "suchthat", SUCHTHAT;
  "nounif", NOUNIF;
  "phase", PHASE;
  "sync", BARRIER;
  "among", AMONG;
  "weaksecret", WEAKSECRET;
  "equivalence", EQUIVALENCE;
  "otherwise", OTHERWISE;
  "choice", CHOICE;
  "diff", CHOICE]

}

rule token = parse
  "\010" | "\013" | "\013\010"
     { next_line lexbuf; token lexbuf }
| [ ' ' '\009' '\012' ] +
     { token lexbuf }
| [ 'a'-'z' 'A'-'Z' ] (( [ 'a'-'z' 'A'-'Z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9' ] )*)
     { let s = Lexing.lexeme lexbuf in
	 try
	   Hashtbl.find keyword_table s
         with
           Not_found ->
             IDENT (s, extent lexbuf)
     }
| '@' (( [ 'a'-'z' 'A'-'Z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9' ] )*)
     { let s = Lexing.lexeme lexbuf in
        ATIDENT (s, extent lexbuf)
     }
| '\"' (( [ ' ' '!' '#'-'[' ']'-'~' '\192'-'\214' '\216'-'\246' '\248'-'\255' ] )*) '\"'
    { let s = Lexing.lexeme lexbuf in
      STRING (String.sub s 1 (String.length s - 2), extent lexbuf)
    } 
| ([ '0'-'9' ]) +
    { 
      try 
        INT (int_of_string(Lexing.lexeme lexbuf))
      with Failure _ ->
	input_error "Incorrect integer" (extent lexbuf)
    }
| "(*" {
         comment lexbuf;
         token lexbuf
       }
| ',' { COMMA }
| '(' { LPAREN }
| ')' { RPAREN }
| '[' { LBRACKET }
| ']' { RBRACKET }
| '{' { LBRACE }
| '}' { RBRACE }
| '|' { BAR }
| "||" { OR }
| "&&" { WEDGE }
| ';' { SEMI }
| '!' { REPL }
| '=' { EQUAL }
| '/' { SLASH }
| '.' { DOT }
| '*' { STAR }
| ':' { COLON }
| "->" { RED } 
| "<=" { LEQ }
| "<->" { EQUIV } 
| "<=>" { EQUIVEQ } 
| "<>" { DIFF }
| "==>" { BEFORE }
| ">" { GREATER }
| "inj-event" { INJEVENT }
| eof { EOF }	
| _ { input_error "Illegal character" (extent lexbuf) }

and comment = parse
| "*)" { }
| "\010" | "\013" | "\013\010"
     { next_line lexbuf; comment lexbuf }
| eof { }
| _ { comment lexbuf }
