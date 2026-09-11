open Catala_utils
open Shared_ast
open Symb_expr

module PathConstraint = struct
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

  let mk_z3
      ?growth
      ?origin
      (expr : SymbExpr.t)
      (pos : Pos.t)
      (branch : bool) : naked_pc =
    let expr =
      match expr with
      | Symb_z3 e -> Pc_z3 e
      | Symb_incomplete -> Pc_incomplete
      | _ ->
        invalid_arg
          "[PathConstraint.mk_z3] expects a z3 symbolic expression (or \
           incomplete)"
    in
    { expr; pos; branch; growth; origin }

  let default_id = ref 0

  let fresh_id () =
    incr default_id;
    !default_id

  let id_of_string (id : string option) =
    match id with Some s -> s | None -> "id!" ^ string_of_int (fresh_id ())

  let mk_soft
      (expr : SymbExpr.t)
      (weight : int)
      (id : soft_id option)
      (pos : Pos.t)
      (branch : bool) : naked_pc =
    let expr =
      match expr with
      | Symb_z3 e -> Pc_soft { symb = e; weight; id = id_of_string id }
      | _ ->
        invalid_arg "[PathConstraint.mk_soft] expects a z3 symbolic expression"
    in
    { expr; pos; branch; growth = None; origin = None }

  let mk_reentrant
      (expr : SymbExpr.t)
      (reentrant_const : s_expr)
      (pos : Pos.t)
      (branch : bool) : naked_pc option =
    let expr : pc_expr option =
      match expr with
      | Symb_reentrant r -> Some (Pc_reentrant { symb = r; is_empty = branch })
      | Symb_z3 s when Z3.Expr.equal s reentrant_const ->
        (* If the symbolic expression is the dummy, it means that the default
           being evaluated is in a scope called by the scope under analysis.
           Thus the context variable is not an input variable of the concolic
           engine, and its evaluation should not generate a path constraint. *)
        None
      | _ ->
        Message.error ~pos
          "[PathConstraint.mk_reentrant] expects reentrant symbolic expression \
           or dummy const but got %a"
          SymbExpr.formatter expr
    in
    Option.bind expr (fun expr ->
      Some { expr; pos; branch; growth = None; origin = None })

  let is_incomplete (pc : naked_pc) : bool =
    match pc.expr with Pc_incomplete -> true | _ -> false

  let growth_request (pc : naked_pc) = pc.growth
  let origin (pc : naked_pc) = pc.origin

  type annotated_pc =
    | Negated of naked_pc
        (** the path constraint that has been negated to generate a new input *)
    | Done of naked_pc
        (** a path node that has been explored should, and whose constraint
            should not be negated *)
    | Normal of naked_pc  (** all other constraints *)

  type annotated_path = annotated_pc list

  (** Computation path logic *)

  (* Two path constraint expressions are equal if they are of the same kind, and
     if either their Z3 expressions are equal or their variable name and
     "emptyness" are equal depending on that kind. *)
  let pc_expr_equal e e' : bool =
    match e, e' with
    | Pc_z3 e1, Pc_z3 e2 -> Z3.Expr.equal e1 e2
    | Pc_reentrant e1, Pc_reentrant e2 ->
      StructField.equal e1.symb.name e2.symb.name && e1.is_empty = e2.is_empty
    | _, _ -> false

  (** Two path constraints are equal only at the same evaluation site. Large
      inlined scopes contain many identical predicates (especially [true]
      default guards); treating them as interchangeable realigns a replay with
      the wrong prefix node and can make a sound model appear to diverge. *)
  let path_constraint_equal c c' : bool =
    Pos.equal c.pos c'.pos
    && pc_expr_equal c.expr c'.expr && c.branch = c'.branch

  (** Identity of a branch site independently of the concrete arm taken. Z3
      path expressions store the condition of the arm that was taken, so a
      successful flip normally replaces [q] by [not q]; source position and
      constraint kind are the stable information available here. *)
  let path_constraint_same_site c c' : bool =
    Pos.equal c.pos c'.pos
    &&
    match c.expr, c'.expr with
    | Pc_z3 _, Pc_z3 _ | Pc_soft _, Pc_soft _ | Pc_incomplete, Pc_incomplete ->
      true
    | Pc_reentrant r, Pc_reentrant r' ->
      StructField.equal r.symb.name r'.symb.name
    | _, _ -> false

  type 'a incremental_action = IncrPush of 'a | IncrPop of 'a
  type incremental_annotated_pc = annotated_pc incremental_action
  type incremental_pc_expr = pc_expr incremental_action

  (** Compare the path of the previous evaluation and the path of the current
      evaluation. If a constraint was previously marked as Done or Normal, then
      check that it stayed the same. If it was previously marked as Negated,
      thus if it was negated before the two evaluations, then check that the
      concrete value was indeed negated and mark it Done. If there are new
      constraints after the last one, add them as Normal. Return [None] when
      replay diverged and the old symbolic candidate must be discarded. *)
  let expected_matches apc c' =
    match apc with
    | Normal c | Done c -> path_constraint_equal c c'
    | Negated c -> path_constraint_same_site c c' && c.branch <> c'.branch

  let compare_paths (path_prev : annotated_path) (path_new : naked_path) :
      (annotated_path * incremental_annotated_pc list * bool) option =
    (* Inlined list predicates and large matches can produce tens of thousands
       of constraints. Accumulate in reverse so comparison does not consume
       one native OCaml stack frame per constraint. *)
    let rec aux rev_path rev_diff realigned path_prev path_new =
      match path_prev, path_new with
      | [], [] ->
        Some
          ( List.rev rev_path,
            (if realigned then [] else List.rev rev_diff),
            realigned )
      | [], c' :: p' ->
        aux (Normal c' :: rev_path) (IncrPush (Normal c') :: rev_diff)
          realigned [] p'
      | _ :: _, [] -> None
      | apc :: _, c' :: p' when not (expected_matches apc c') ->
        if List.exists (expected_matches apc) p' then
          aux (Normal c' :: rev_path) [] true path_prev p'
        else None
      | Normal c :: p, _ :: p' ->
        aux (Normal c :: rev_path) rev_diff realigned p p'
      | Negated _ :: p, c' :: p' ->
        aux (Done c' :: rev_path) rev_diff realigned p p'
      | Done c :: p, _ :: p' ->
        aux (Done c :: rev_path) rev_diff realigned p p'
    in
    aux [] [] false path_prev path_new

  (** Remove Done paths until a Normal (not yet negated) constraint is found,
      then mark this branch as Negated. This function shall be called on an
      output of [compare_paths], and thus no Negated constraint should appear in
      its input. *)
  let make_expected_path (path : annotated_path) :
      annotated_path * incremental_annotated_pc list =
    let rec aux rev_diff = function
      | [] -> [], List.rev rev_diff
      | Normal c :: p ->
        ( Negated c :: p,
          List.rev
            (IncrPush (Negated c) :: IncrPop (Normal c) :: rev_diff) )
      | Done c :: p -> aux (IncrPop (Done c) :: rev_diff) p
      | Negated _ :: _ ->
        failwith
          "[make_expected_path] found a negated constraint, which should not \
           happen"
    in
    aux [] path

  (** A persistent prefix tree and a two-worklist scheduler. Every observed
      concrete constraint is interned below its concrete prefix. A candidate is
      represented by the node whose edge should be flipped, so candidates that
      share an execution prefix also share the same nodes. *)
  module Scheduler = struct
    type node = {
      id : int;
      epoch : int;
      parent : node option;
      pc : naked_pc option;
      synthetic : bool;
      mutable children : node list;
      mutable scheduled : bool;
      mutable selected : bool;
    }

    type candidate = node

    let prefix candidate = Option.get candidate.parent

    type t = {
      root : node;
      mutable next_id : int;
      mutable novelty_front : candidate list;
      mutable novelty_back : candidate list;
      mutable dfs_stack : candidate list;
      priority_burst : int;
      mutable priority_left : int;
      mutable epoch : int;
    }

    let create ~priority_burst =
      if priority_burst < 0 then
        invalid_arg "[PathConstraint.Scheduler.create] negative priority burst";
      let root =
        { id = 0; epoch = 0; parent = None; pc = None; synthetic = false;
          children = [];
          scheduled = true; selected = true }
      in
      { root; next_id = 1; novelty_front = []; novelty_back = [];
        dfs_stack = [];
        priority_burst; priority_left = priority_burst; epoch = 0 }

    let reset t =
      t.root.children <- [];
      t.epoch <- t.epoch + 1;
      t.next_id <- 1;
      t.novelty_front <- [];
      t.novelty_back <- [];
      t.dfs_stack <- [];
      t.priority_left <- t.priority_burst

    let child_equal synthetic pc node =
      match node.pc with
      | Some pc' ->
        Bool.equal synthetic node.synthetic
        && path_constraint_equal pc pc' && Pos.equal pc.pos pc'.pos
      | None -> false

    let intern_child t parent ~synthetic pc =
      match List.find_opt (child_equal synthetic pc) parent.children with
      | Some child -> child
      | None ->
        let child =
          { id = t.next_id; epoch = t.epoch; parent = Some parent;
            pc = Some pc; synthetic;
            children = [];
            scheduled = false; selected = false }
        in
        t.next_id <- t.next_id + 1;
        parent.children <- child :: parent.children;
        child

    let is_flippable node =
      match node.pc with
      | Some { expr = (Pc_z3 _ | Pc_reentrant _); _ } -> true
      | Some { expr = (Pc_soft _ | Pc_incomplete); _ } | None -> false

    let schedule t ~is_novel node =
      if is_flippable node && not node.scheduled then begin
        node.scheduled <- true;
        t.dfs_stack <- node :: t.dfs_stack;
        if Option.fold ~none:false ~some:is_novel node.pc then
          t.novelty_back <- node :: t.novelty_back
      end

    let observe t ~from ~is_novel ~seeds path =
      (* Desugaring and inlining can put the same source predicate into the
         concrete constraint path more than once. Seed it at the first (least
         constrained) prefix only; deeper copies produce the same input while
         consuming another solver/evaluation budget slot. *)
      let seen_seeds = ref [] in
      let fresh_seeds pc =
        List.filter
          (fun seed ->
            if
              List.exists
                (fun old ->
                  path_constraint_equal seed old && Pos.equal seed.pos old.pos)
                !seen_seeds
            then false
            else begin
              seen_seeds := seed :: !seen_seeds;
              true
            end)
          (seeds pc)
      in
      let _, new_nodes, seed_nodes =
        List.fold_left
          (fun (parent, nodes, seed_nodes) pc ->
            let seed_nodes =
              List.fold_left
                (fun nodes seed ->
                  intern_child t parent ~synthetic:true seed :: nodes)
                seed_nodes (fresh_seeds pc)
            in
            let child = intern_child t parent ~synthetic:false pc in
            begin match from with
            | Some candidate
              when not candidate.synthetic
                   && (prefix candidate).id = parent.id
                   && path_constraint_same_site (Option.get candidate.pc) pc
                   && (Option.get candidate.pc).branch <> pc.branch ->
              (* Replaying [candidate] reached the opposite edge it requested.
                 Flipping that edge would only recreate the already-observed
                 path, so mark the inverse candidate explored. *)
              child.scheduled <- true;
              child.selected <- true
            | _ -> ()
            end;
            child, child :: nodes, seed_nodes)
          (t.root, [], []) path
      in
      (* [new_nodes] is leaf-first. Visit it root-first and prepend each item,
         leaving the deepest newly discovered flip on top of the DFS stack. *)
      List.iter (schedule t ~is_novel) seed_nodes;
      List.iter (schedule t ~is_novel) (List.rev new_nodes)

    let rec pop_pending epoch (queue : candidate list) =
      match queue with
      | [] -> None, []
      | candidate :: rest
        when candidate.epoch <> epoch || candidate.selected ->
        pop_pending epoch rest
      | candidate :: rest -> Some candidate, rest

    let rec pop_novel epoch is_novel (queue : candidate list) =
      match queue with
      | [] -> None, []
      | candidate :: rest
        when candidate.epoch <> epoch || candidate.selected ->
        pop_novel epoch is_novel rest
      | candidate :: rest -> begin
        match candidate.pc with
        | Some pc when is_novel pc -> Some candidate, rest
        | _ -> pop_novel epoch is_novel rest
        end

    let select candidate =
      candidate.selected <- true;
      candidate

    let next t ~is_novel =
      let ordinary () =
        let candidate, rest = pop_pending t.epoch t.dfs_stack in
        t.dfs_stack <- rest;
        Option.map select candidate
      in
      let priority () =
        let rec take () =
          let candidate, rest =
            pop_novel t.epoch is_novel t.novelty_front
          in
          t.novelty_front <- rest;
          match candidate with
          | Some candidate -> Some (select candidate)
          | None when t.novelty_back <> [] ->
            t.novelty_front <- List.rev t.novelty_back;
            t.novelty_back <- [];
            take ()
          | None -> None
        in
        take ()
      in
      if t.priority_burst = 0 then ordinary ()
      else if t.priority_left > 0 then
        match priority () with
        | Some candidate ->
          t.priority_left <- t.priority_left - 1;
          Some candidate
        | None ->
          t.priority_left <- t.priority_burst;
          ordinary ()
      else begin
        t.priority_left <- t.priority_burst;
        match ordinary () with
        | Some _ as candidate -> candidate
        | None -> priority ()
      end

    let pc candidate = Option.get candidate.pc
    let synthetic candidate = candidate.synthetic

    let rec nodes_to_root acc node =
      match node.parent with
      | None -> acc
      | Some parent -> nodes_to_root (node :: acc) parent

    let annotated_path candidate =
      let rec annotate rev_path = function
        | [] -> List.rev rev_path
        | [flipped] -> List.rev (Negated (pc flipped) :: rev_path)
        | node :: nodes ->
          annotate (Normal (pc node) :: rev_path) nodes
      in
      annotate [] (nodes_to_root [] candidate)

    let ancestors node =
      let rec aux rev_nodes node =
        match node.parent with
        | None -> List.rev (node :: rev_nodes)
        | Some parent -> aux (node :: rev_nodes) parent
      in
      aux [] node

    let lca left right =
      let left_ids = Hashtbl.create 17 in
      List.iter (fun node -> Hashtbl.replace left_ids node.id node)
        (ancestors left);
      List.find (fun node -> Hashtbl.mem left_ids node.id) (ancestors right)

    let rec nodes_until ancestor node acc =
      if node.id = ancestor.id then acc
      else
        match node.parent with
        | None -> assert false
        | Some parent -> nodes_until ancestor parent (node :: acc)

    let switch_diff current next =
      let tail_map f xs = List.rev (List.rev_map f xs) in
      let append_one xs x = List.rev (x :: List.rev xs) in
      let next_prefix = prefix next in
      match current with
      | None ->
        append_one
          (tail_map (fun node -> IncrPush (Normal (pc node)))
             (nodes_to_root [] next_prefix))
          (IncrPush (Negated (pc next)))
      | Some current ->
        let current_prefix = prefix current in
        let ancestor = lca current_prefix next_prefix in
        let pops =
          IncrPop (Negated (pc current))
          :: tail_map (fun node -> IncrPop (Normal (pc node)))
               (List.rev (nodes_until ancestor current_prefix []))
        in
        let pushes =
          append_one
            (tail_map (fun node -> IncrPush (Normal (pc node)))
               (nodes_until ancestor next_prefix []))
            (IncrPush (Negated (pc next)))
        in
        List.rev_append (List.rev pops) pushes
  end

  module Print = struct
    open Format

    let pc_expr (fmt : formatter) (e : pc_expr) : unit =
      match e with
      | Pc_z3 e -> pp_print_string fmt (Z3.Expr.to_string e)
      | Pc_soft { symb; weight; id } ->
        fprintf fmt "Soft(%s, %d, %s)" (Z3.Expr.to_string symb) weight id
      | Pc_reentrant { symb = { name; _ }; is_empty } ->
        fprintf fmt "%s(%s)"
          (if is_empty then "Empty" else "NotEmpty")
          (Mark.remove (StructField.get_info name))
      | Pc_incomplete -> pp_print_string fmt "Incomplete"

    let pc_debug_info (fmt : formatter) (pc : naked_pc) : unit =
      if Global.options.debug then
        fprintf fmt "@%s {%B}" (Pos.to_string_short pc.pos) pc.branch

    let naked_pc (fmt : formatter) (pc : naked_pc) : unit =
      fprintf fmt "%a%a" pc_expr pc.expr pc_debug_info pc

    let naked_path (fmt : formatter) (pcs : naked_path) : unit =
      pp_print_list naked_pc fmt pcs

    let annotated_pc (fmt : formatter) (apc : annotated_pc) : unit =
      let print s pc = fprintf fmt s naked_pc pc in
      match apc with
      | Normal pc -> print "       %a" pc
      | Done pc -> print "DONE   %a" pc
      | Negated pc -> print "NEGATE %a" pc

    let annotated_path (fmt : formatter) (pcs : annotated_path) : unit =
      if pcs = [] then pp_print_string fmt "[No constraints]"
      else pp_print_list annotated_pc fmt pcs
  end
end
