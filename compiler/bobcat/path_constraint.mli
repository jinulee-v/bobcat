open Catala_utils
open Symb_expr

module PathConstraint : sig
  type s_expr = SymbExpr.z3_expr
  type soft_id = string
  type soft = { symb : s_expr; weight : int; id : soft_id }
  type reentrant = { symb : SymbExpr.reentrant; is_empty : bool }

  type pc_expr =
    | Pc_z3 of s_expr
    | Pc_soft of soft
    | Pc_reentrant of reentrant
    | Pc_incomplete

  (* path constraint cannot be empty (this looks like a GADT but it would be
     overkill I think) *)
  type list_growth = { list_id : int; next_capacity : int }
  type constraint_origin = {
    decision_id : string;
    taken_outcome : string option;
    may_reach_when_flipped : string list;
  }
  type naked_pc = {
    expr : pc_expr;
    pos : Pos.t;
    branch : bool;
    growth : list_growth option;
    origin : constraint_origin option;
  }

  type naked_path = naked_pc list

  type annotated_pc =
    | Negated of naked_pc
        (** the path constraint that has been negated to generate a new input *)
    | Done of naked_pc
        (** a path node that has been explored should, and whose constraint
            should not be negated *)
    | Normal of naked_pc  (** all other constraints *)

  val is_incomplete : naked_pc -> bool
  val growth_request : naked_pc -> list_growth option
  val origin : naked_pc -> constraint_origin option

  type annotated_path = annotated_pc list
  type 'a incremental_action = IncrPush of 'a | IncrPop of 'a
  type incremental_annotated_pc = annotated_pc incremental_action
  type incremental_pc_expr = pc_expr incremental_action

  (** {2 Builders} *)

  val mk_z3 :
    ?growth:list_growth ->
    ?origin:constraint_origin ->
    SymbExpr.t ->
    Pos.t ->
    bool ->
    naked_pc
  val mk_soft : SymbExpr.t -> int -> soft_id option -> Pos.t -> bool -> naked_pc
  val mk_reentrant : SymbExpr.t -> s_expr -> Pos.t -> bool -> naked_pc option

  (** {2 Path operations} *)

  val path_constraint_same_site : naked_pc -> naked_pc -> bool
  (** Whether two constraints describe outcomes at the same evaluation site,
      independently of which outcome was taken. *)

  val compare_paths :
    annotated_path ->
    naked_path ->
    (annotated_path * incremental_annotated_pc list * bool) option
  (** Compare the path of the previous evaluation and the path of the current
      evaluation. If a constraint was previously marked as Done or Normal, then
      check that it stayed the same. If it was previously marked as Negated,
      thus if it was negated before the two evaluations, then check that the
      concrete value was indeed negated and mark it Done. If there are new
      constraints after the last one, add them as Normal. The boolean reports
      that constraints were inserted before an existing suffix, requiring an
      incremental-solver rebuild. [None] reports concrete replay divergence. *)

  val make_expected_path :
    annotated_path -> annotated_path * incremental_annotated_pc list
  (** Remove Done paths until a Normal (not yet negated) constraint is found,
      then mark this branch as Negated. This function shall be called on an
      output of [compare_paths], and thus no Negated constraint should appear in
      its input. *)

  module Scheduler : sig
    type t
    type candidate

    val create : priority_burst:int -> t
    val reset : t -> unit
    val observe :
      t ->
      from:candidate option ->
      is_novel:(naked_pc -> bool) ->
      seeds:(naked_pc -> naked_pc list) ->
      naked_path ->
      unit
    val next : t -> is_novel:(naked_pc -> bool) -> candidate option
    val pc : candidate -> naked_pc
    val synthetic : candidate -> bool
    val annotated_path : candidate -> annotated_path
    val switch_diff :
      candidate option -> candidate -> incremental_annotated_pc list
  end

  (** {2 Printing} *)

  module Print : sig
    open Format

    val pc_expr : formatter -> pc_expr -> unit
    val naked_path : formatter -> naked_path -> unit
    val annotated_path : formatter -> annotated_path -> unit
  end
end
