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

val query_list : (Pitptree.envdecl * Pitptree.tquery list) list ref

val parse_file : string -> process * process option
val display : unit -> unit
val transl_query : Pitptree.envdecl * Pitptree.tquery list -> query list
val query_to_facts : query list -> fact list
val get_noninterf_queries : unit -> (funsymb * term list option) list list
val get_weaksecret_queries : unit -> funsymb list
val get_not : unit -> event list
val get_nounif : unit -> (fact_format * int) list

val destructors_check_deterministic : funsymb list ref
val set_need_vars_in_names : unit -> unit
val reset_need_vars_in_names : unit -> unit
