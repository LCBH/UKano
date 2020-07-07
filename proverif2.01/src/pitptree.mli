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
(* Typed front-end *)

(* Terms *)

type ident = Ptree.ident

type options = ident * ident list option

type term =
    PIdent of ident
  | PFail
  | PFunApp of ident * term_e list
  | PProj of ident * term_e
  | PTuple of term_e list

and term_e = term * Parsing_helper.extent

(* Equational theory *)

type equation = term_e * term_e

(* Functions defined by reduction rules *)

type fundef =  (term_e * term_e) list

(* Nounif *)

type gformat =
    PFGIdent of ident
  | PFGFunApp of ident * gformat_e list
  | PFGTuple of gformat_e list
  | PFGName of ident * (ident * gformat_e) list
  | PFGAny of ident
  | PFGLet of ident * gformat_e * gformat_e

and gformat_e = gformat * Parsing_helper.extent

type nounif_t =
    BFLet of ident * gformat_e * nounif_t
  | BFNoUnif of (ident * gformat_e list * int) * int

(* Queries *)

type gterm =
    PGIdent of ident
  | PGFunApp of ident * gterm_e list
  | PGPhase of ident * gterm_e list * int
  | PGTuple of gterm_e list
  | PGName of ident * (ident * gterm_e) list
  | PGLet of ident * gterm_e * gterm_e

and gterm_e = gterm * Parsing_helper.extent

type tquery =
    PPutBegin of bool * ident list
	(* bool value: false -> non-inj event, true -> inj event *)
  | PRealQuery of gterm_e * ident list(*public variables*)
  | PQSecret of ident * ident list(*public variables*) * options list(*options*)

type tlemma =
  gterm_e *  (* The lemma itself *)
  (ident * ident) option * (* When Some(x,opt) then the lemma has been declared for the query secret x [opt] *)
  ident list (* The public vars *)

(* Clauses *)

type tclause =
    PClause of term_e * term_e
  | PFact of term_e
  | PEquiv of term_e * term_e * bool

(* Processes *)

type pterm =
    PPIdent of ident
  | PPFunApp of ident * pterm_e list
  | PPTuple of pterm_e list
  | PPRestr of ident * ident list option(*variables to include as arguments*) * ident(*type*) * pterm_e
  | PPTest of pterm_e * pterm_e * pterm_e option
  | PPLet of tpattern * pterm_e * pterm_e * pterm_e option
  | PPLetFilter of (ident * ident(*type*)) list * pterm_e * pterm_e * pterm_e option
  | PPEvent of ident * pterm_e list * ident list option(*variables to include in environment for injective events*) * pterm_e
  | PPInsert of ident * pterm_e list * pterm_e
  | PPGet of ident * tpattern list * pterm_e option * pterm_e * pterm_e option

and pterm_e = pterm * Parsing_helper.extent

and tpattern =
    PPatVar of ident * ident option(*type*)
  | PPatTuple of tpattern list
  | PPatFunApp of ident * tpattern list
  | PPatEqual of pterm_e

type tprocess =
    PNil
  | PPar of tprocess_e * tprocess_e
  | PRepl of tprocess_e
  | PRestr of ident * ident list option(*variables to include as arguments*) * ident(*type*) * tprocess_e
  | PLetDef of ident * pterm_e list
  | PTest of pterm_e * tprocess_e * tprocess_e
  | PInput of pterm_e * tpattern * tprocess_e * options list
  | POutput of pterm_e * pterm_e * tprocess_e
  | PLet of tpattern * pterm_e * tprocess_e * tprocess_e
  | PLetFilter of (ident * ident(*type*)) list * pterm_e * tprocess_e * tprocess_e * options list
  | PEvent of ident * pterm_e list * ident list option(*variables to include in environment for injective events*) * tprocess_e
  | PPhase of int * tprocess_e
  | PBarrier of int * ident option * tprocess_e
  | PInsert of ident * pterm_e list * tprocess_e
  | PGet of ident * tpattern list * pterm_e option * tprocess_e * tprocess_e * options list

and tprocess_e = tprocess * Parsing_helper.extent

(* Declarations *)

type envdecl = (ident(*variable*) * ident(*type*)) list
type may_fail_env_decl = (ident(*variable*) * ident(*type*) * bool (* may-fail*)) list

type tdecl =
    TTypeDecl of ident (* type declaration *)
  | TFunDecl of ident * ident list(*argument types*) * ident(*result type*) * options list(*options*)
  | TEventDecl of ident * ident list(*argument types*)
  | TConstDecl of ident * ident(*type*) * options list(*options*)
  | TReduc of (envdecl * term_e * term_e) list * options list(*options*)
  | TReducFail of ident * ident list * ident * (may_fail_env_decl * term_e * term_e) list * options list(*options*)
  | TEquation of (envdecl * term_e) list * options list(*options*)
  | TPredDecl of ident * ident list(*argument types*) * options list(*options*)
  | TTableDecl of ident * ident list(*argument types*)
  | TSet of ident * Ptree.pval
  | TPDef of ident * may_fail_env_decl * tprocess_e
  | TQuery of envdecl * tquery list * options list (* options *)
  | TNoninterf of envdecl * (ident * term_e list option) list
  | TWeaksecret of ident
  | TNoUnif of envdecl * nounif_t * options list(*options*)
  | TNot of envdecl * gterm_e
  | TElimtrue of may_fail_env_decl * term_e
  | TFree of ident * ident(*type*) * options list(*options*)
  | TClauses of (may_fail_env_decl * tclause) list
  | TDefine of ident * ident list * tdecl list
  | TExpand of ident * ident list
  | TLetFun of ident * may_fail_env_decl * pterm_e
  | TLemma of bool * envdecl * tlemma list * options list
			(* TLemma(b,env,q_list,options) :
				- b represents whether the queries were declared as lemmas or as axioms (b = true when declared as lemmas)
				- env : variables declared for the queries
				- q_list : the list of queries
				- options : list of options.
			*)
