(* This file is part of the Catala compiler, a specification language for tax
   and social benefits computation rules. Copyright (C) 2022 Inria, contributor:
   Aymeric Fromherz <aymeric.fromherz@inria.fr>, Denis Merigoux
   <denis.merigoux@inria.fr>

   Licensed under the Apache License, Version 2.0 (the "License"); you may not
   use this file except in compliance with the License. You may obtain a copy of
   the License at

   http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
   License for the specific language governing permissions and limitations under
   the License. *)

(** Interfacing with the Z3 SMT solver *)

module Io : Io.BackendIO

type direct_session

type coverage_result =
  | Coverage_sat of Yojson.Safe.t * string list
  | Coverage_unsat
  | Coverage_unknown of string

val create_direct_session :
  Shared_ast.decl_ctx ->
  input_var:Shared_ast.typed Dcalc.Ast.naked_expr Bindlib.var ->
  input_ty:Shared_ast.typ ->
  max_list_length:int ->
  array_capacity:int ->
  solver_timeout_ms:int ->
  direct_session

val set_solver_timeout : direct_session -> int -> unit

val compile_reachability :
  ?on_objective:(string -> unit) ->
  direct_session ->
  objective_of_tag:(Shared_ast.tag -> Catala_utils.Pos.t -> string option) ->
  definitions:(Shared_ast.typed Dcalc.Ast.naked_expr Bindlib.var *
               Shared_ast.typed Dcalc.Ast.expr) list ->
  Shared_ast.typed Dcalc.Ast.expr ->
  unit
(** Encode all executable branch outcomes in one guarded formula. If the same
    source outcome occurs at several call sites, its reachability formula is
    the disjunction of those guarded instances. *)

val reachable_objectives :
  objective_of_tag:(Shared_ast.tag -> Catala_utils.Pos.t -> string option) ->
  definitions:(Shared_ast.typed Dcalc.Ast.naked_expr Bindlib.var *
               Shared_ast.typed Dcalc.Ast.expr) list ->
  Shared_ast.typed Dcalc.Ast.expr ->
  string list
(** Cheap source-objective census over the selected entry point's shared,
    acyclic definition graph. This runs before formula construction so a
    solver timeout cannot erase uncovered outcomes from the denominator. *)

val compile_objective :
  ?on_objective:(string -> unit) ->
  ?on_timing:(string -> float -> unit) ->
  direct_session ->
  objective_of_tag:(Shared_ast.tag -> Catala_utils.Pos.t -> string option) ->
  definitions:(Shared_ast.typed Dcalc.Ast.naked_expr Bindlib.var *
               Shared_ast.typed Dcalc.Ast.expr) list ->
  string ->
  Shared_ast.typed Dcalc.Ast.expr ->
  unit
(** Add only the backwards dependency slice for one exact source outcome to
    the shared guarded solver session. *)

val unknown_objectives : direct_session -> (string * string) list

val compiled_objectives : direct_session -> string list

(** Ask the persistent solver for a model reaching any member of the supplied
    uncovered set. *)
val solve_uncovered : direct_session -> string list -> coverage_result

(** Conservatively refine after a failed replay by excluding the Catala-visible
    input equivalence class. Invisible bounded-list padding and inactive sum
    payloads are abstracted away, so one concrete counterexample is not retried
    under a syntactically different Z3 model. *)
val block_last_input : direct_session -> unit
