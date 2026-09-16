(* This file is part of the Catala compiler, a specification language for tax
   and social benefits computation rules. Copyright (C) 2020 Inria, contributor:
   Denis Merigoux <denis.merigoux@inria.fr>, Alain Delaët
   <alain.delaet--tixeuil@inria.Fr>, Louis Gesbert <louis.gesbert@inria.fr>

   Licensed under the Apache License, Version 2.0 (the "License"); you may not
   use this file except in compliance with the License. You may obtain a copy of
   the License at

   http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
   License for the specific language governing permissions and limitations under
   the License. *)

(** Reference interpreter for the default calculus *)

open Catala_utils
open Shared_ast
module Optimizations = Bobcat_optimizations

val enumerate_branch_objectives :
  int ->
  (Shared_ast.dcalc, 'm) Shared_ast.gexpr Shared_ast.program ->
  Shared_ast.ScopeName.t ->
  string list
(** Compile a scope and enumerate its exact source branch outcomes without
    executing a concrete input or constructing concolic path candidates.  This
    is the front-end census consumed by BOBCat's goal-directed solver. *)

(** Compile exact guarded outcome slices into one shared session, then solve
    and concretely replay each objective. No concrete seed, path prefix, or
    constraint flipping is involved. *)
val solve_branch_objectives :
  demand:bool ->
  intermediate_list_bound:int option ->
  int ->
  int ->
  int ->
  bool ->
  (Shared_ast.dcalc, Shared_ast.typed) Shared_ast.gexpr Shared_ast.program ->
  Shared_ast.ScopeName.t ->
  unit
open Bobcat_types

val interpret_program_concolic :
  ?on_input:((Uid.MarkedString.info * conc_expr) list -> bool) ->
  bool ->
  Optimizations.flag list ->
  int option ->
  int ->
  bool ->
  int ->
  (dcalc, 'm) gexpr program ->
  ScopeName.t ->
  (Uid.MarkedString.info * conc_expr) list
(** Concolic interpreter *)

val solve_path_objectives :
  int -> (dcalc, typed) gexpr program -> ScopeName.t -> unit
