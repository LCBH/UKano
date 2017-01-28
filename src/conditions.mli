(*************************************************************
 *                                                           *
 *  UKano: UnlinKability and ANOnymity verifier              *
 *                                                           *
 *  Lucca Hirschi                                            *
 *  http://projects.lsv.ens-cachan.fr/ukano/                 *
 *  Copyright (C) Lucca Hirschi 2015-2017                    *
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
(** This module provides functions from the UnlinKability and ANOnymity
    verifier built on top of ProVerif as described in the following paper:
    [1] L. Hirschi, D. Baelde and S. Delaune.
        A Method for Verifying Privacy-Type Properties : The Unbounded Case.
        In IEEE Symposium on Security and Privacy (Oakland), 2016. To appear.
    A copy can be found at http://projects.lsv.ens-cachan.fr/ukano/ *)

(** Help message dedicated to Ukano *)
val helpMess : string

(** If the inputted process is not in the "2-agents protocol class" (see [1]). *)
exception NotInClass of string

(** [transBoth p inNameFile outNameFileFO outNameFileWA] writes in the files [outNameFile*] complete ProVerif files checking respectively
frame opacity and well-authentication for the process [p] and the theory contained in [inNameFile]. Returns the list of string representations
of identity names took into acount for anonymity.*)
val transBoth : Types.process -> string -> string -> string -> Types.funsymb list
								 
(** Display a representation of the 2-agents protocol associated to a given process. *)
val displayProcessProtocol : Types.process -> unit
