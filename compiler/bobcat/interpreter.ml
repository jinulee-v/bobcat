(* This file is part of the Catala compiler, a specification language for tax
   and social benefits computation rules. Copyright (C) 2020 Inria, contributor:
   Denis Merigoux <denis.merigoux@inria.fr>, Emile Rolley
   <emile.rolley@tuta.io>, Alain Delaët <alain.delaet--tixeuil@inria.Fr>, Louis
   Gesbert <louis.gesbert@inria.fr>

   Licensed under the Apache License, Version 2.0 (the "License"); you may not
   use this file except in compliance with the License. You may obtain a copy of
   the License at

   http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
   License for the specific language governing permissions and limitations under
   the License. *)

(** Concolic interpreter for the default calculus *)

open Catala_utils
open Shared_ast
open Op
module Concrete = Shared_ast.Interpreter
open Z3_utils
open Symb_expr
open Path_constraint
module Optimizations = Bobcat_optimizations
module Runtime = Catala_runtime
open Bobcat_types

let set_conc_info
    (type m)
    (symb_expr : SymbExpr.t)
    (constraints : PathConstraint.naked_path)
    (mk : m mark) : conc_info mark =
  let symb_expr = SymbExpr.simplify symb_expr in
  let custom = { symb_expr; constraints; ty = None } in
  match mk with
  | Untyped { pos } -> Custom { pos; custom }
  | Typed { pos; ty } ->
    let custom = { custom with ty = Some ty } in
    Custom { pos; custom }
    (* NOTE we keep type information. This information is used for instance in
       generating concolic input values, eg in [inputs_of_model] *)
  | Custom m -> Custom { m with custom }

(** Maybe replace constraints, and safely replace the symbolic expression from
    former mark *)
let add_conc_info_m
    (former_mark : conc_info mark)
    (symb_expr : SymbExpr.t)
    ?(constraints : PathConstraint.naked_path option)
    (x : 'a) : ('a, conc_info) marked =
  let (Custom { pos; custom }) = former_mark in
  let symb_expr = SymbExpr.simplify symb_expr in
  let symb_expr = SymbExpr.map_none custom.symb_expr ~none:symb_expr in
  (* only update symb_expr if it does not exist already *)
  let constraints = Option.value ~default:custom.constraints constraints in
  (* only change constraints if new ones are provided *)
  let ty = custom.ty in
  (* we don't change types *)
  Mark.add (Custom { pos; custom = { symb_expr; constraints; ty } }) x

(** Maybe replace the constraints, and safely replace the symbolic expression
    from former expression *)
let add_conc_info_e
    (symb_expr : SymbExpr.t)
    ?(constraints : PathConstraint.naked_path option)
    (x : ('a, conc_info) marked) : ('a, conc_info) marked =
  match constraints with
  | None -> add_conc_info_m (Mark.get x) symb_expr (Mark.remove x)
  | Some constraints ->
    add_conc_info_m (Mark.get x) symb_expr ~constraints (Mark.remove x)

let map_conc_mark
    ?(symb_expr_f = fun x -> x)
    ?(constraints_f = fun x -> x)
    ?(ty_f = fun x -> x)
    ?(pos_f = fun x -> x)
    (m : conc_info mark) : conc_info mark =
  let (Custom { custom = { symb_expr; constraints; ty }; pos }) = m in
  let symb_expr = symb_expr_f symb_expr in
  let constraints = constraints_f constraints in
  let ty = ty_f ty in
  let pos = pos_f pos in
  Custom { custom = { symb_expr; constraints; ty }; pos }

(** Replace concolic information even when the expression already carries a
    symbolic marker.  [add_conc_info_e] deliberately preserves existing
    symbolic information, which is normally what evaluation wants.  Concrete
    external calls, however, initially return [Symb_incomplete]; once their
    array elements have been evaluated we know a strictly better symbolic
    representation and must overwrite that placeholder. *)
let replace_conc_info_e
    (symb_expr : SymbExpr.t)
    ~(constraints : PathConstraint.naked_path)
    (x : ('a, conc_info) marked) : ('a, conc_info) marked =
  let mark =
    map_conc_mark
      ~symb_expr_f:(fun _ -> SymbExpr.simplify symb_expr)
      ~constraints_f:(fun _ -> constraints)
      (Mark.get x)
  in
  Mark.add mark (Mark.remove x)

(* Typing shenanigan to [EGenericError] terms to the AST type. Inspired by
   [Concrete.addcustom]. *)
let add_genericerror e =
  let rec f : type c e.
      ((c, e) conc_interpr_kind, 't) gexpr ->
      ((c, yes) conc_interpr_kind, 't) gexpr boxed = function
    | (ECustom _, _) as e -> Expr.map ~f e
    | (EGenericError, _) as e -> Expr.map ~f e
    | EAppOp { op; tys; args }, m ->
      Expr.eappop ~tys ~args:(List.map f args) ~op:(Operator.translate op) m
    | (EDefault _, _) as e -> Expr.map ~f e
    | (EPureDefault _, _) as e -> Expr.map ~f e
    | (EEmpty, _) as e -> Expr.map ~f e
    | (EErrorOnEmpty _, _) as e -> Expr.map ~f e
    | (EFatalError _, _) as e -> Expr.map ~f e
    | ( ( EAssert _ | ELit _ | EApp _ | EArray _ | EVar _ | EExternal _ | EAbs _
        | EIfThenElse _ | ETuple _ | ETupleAccess _ | EInj _ | EStruct _
        | EStructAccess _ | EMatch _ | EBad | EPos _ ),
        _ ) as e ->
      Expr.map ~f e
    | _ -> .
  in
  let open struct
    external id :
      (('c, 'e) conc_interpr_kind, 't) gexpr ->
      (('c, yes) conc_interpr_kind, 't) gexpr = "%identity"
  end in
  if false then Expr.unbox (f e)
    (* We keep the implementation as a typing proof, but bypass the AST
       traversal for performance. Note that it's not completely 1-1 since the
       traversal would do a reboxing of all bound variables *)
  else id e

(* Coerce a non-error expression into the result type *)
let make_ok : conc_expr -> conc_result = add_genericerror

let make_error mk symb_expr constraints : conc_result =
  let mark =
    set_conc_info symb_expr constraints
      mk (* FIXME this loses type information: is it ok? *)
  in
  Expr.unbox (Expr.egenericerror mark)

let make_error_emptyerror mk constraints message : conc_result =
  let symb_expr = SymbExpr.mk_emptyerror message in
  make_error mk symb_expr constraints

let make_error_conflicterror mk constraints spans message : conc_result =
  let symb_expr = SymbExpr.mk_conflicterror message spans in
  make_error mk symb_expr constraints

let make_error_divisionbyzeroerror mk constraints spans message : conc_result =
  let symb_expr = SymbExpr.mk_divisionbyzeroerror message spans in
  make_error mk symb_expr constraints

let make_error_assertionerror mk constraints message : conc_result =
  let symb_expr = SymbExpr.mk_assertionerror message in
  make_error mk symb_expr constraints

let make_error_external mk constraints message : conc_result =
  make_error mk (SymbExpr.mk_externalerror message) constraints

(* Inspired by [Concrete.delcustom] *)
let del_genericerror e =
  if false then
    let rec f : (conc_dest_kind, 'm) gexpr -> (conc_src_kind, 'm) gexpr boxed =
      function
      | EGenericError, _ ->
        invalid_arg "Generic error remaining after propagation"
      | EAppOp { op; args; tys }, m ->
        Expr.eappop ~tys ~args:(List.map f args) ~op:(Operator.translate op) m
      | ( ( EAssert _ | ELit _ | EApp _ | EArray _ | EVar _ | EExternal _
          | EAbs _ | EIfThenElse _ | ETuple _ | ETupleAccess _ | EInj _
          | EStruct _ | EStructAccess _ | EMatch _ | EDefault _ | EPureDefault _
          | EEmpty | EFatalError _ | EErrorOnEmpty _ | ECustom _ | EBad | EPos _
            ),
          _ ) as e ->
        Expr.map ~f e
      | _ -> .
    in
    (* /!\ don't be tempted to use the same trick here, the function does one
       thing: validate at runtime that the term does not contain [ECustom]
       nodes. *)
    Expr.unbox (f e)
  else
    (* TODO QU RAPHAEL: turns out del_genericerror is pretty costly (~2x), so I
       decided to remove it because I think it is a safety/debugging check now
       =>> OUI c'est un runtime check qui sert à vérifier le type d'expression
       (erreur ou pas), a priori tout doit passer sans ! Peut-être à garder
       comme option pour le debugging/les unit tests *)
    let open struct
      external id : (conc_dest_kind, 'm) gexpr -> (conc_src_kind, 'm) gexpr
        = "%identity"
    end in
    id e

(** Transform any DCalc expression into a concolic expression with no symbolic
    expression and no constraints *)
let init_conc_expr (e : (('c, 'e) conc_interpr_kind, 'm) gexpr) : conc_expr =
  let e = Concrete.addcustom e in
  let f = set_conc_info SymbExpr.none [] in
  Expr.unbox (Expr.map_marks ~f e)

(* taken from z3backend but with the right types *)
(* TODO check if some should be used or removed *)
type binary_source_origin = {
  binary_decision_id : string;
  true_outcomes : string list;
  false_outcomes : string list;
}

type match_source_origin = {
  match_decision_id : string;
  constructor_outcomes : (string * string) list;
}

type context = {
  ctx_z3 : Z3.context;
  (* The Z3 context, used to create symbols and expressions *)
  ctx_decl : decl_ctx;
  (* The declaration context from the Catala program, containing information to
     precisely pretty print Catala expressions *)
  ctx_dummy_sort : Z3.Sort.sort;
  (* A dummy sort for lambda abstractions *)
  ctx_dummy_const : s_expr;
  (* A dummy expression for lambda abstractions *)
  ctx_reentrant_sort : Z3.Sort.sort;
  (* A dummy sort for reentrant variables *)
  ctx_reentrant_const : s_expr;
  (* A dummy expression for reentrant variables *)
  ctx_z3enums : Z3.Sort.sort EnumName.Map.t;
  (* A map from Catala enumeration names to the corresponding Z3 datatype sort,
     from which we can retrieve constructors and accessors *)
  ctx_z3structs : Z3.Sort.sort StructName.Map.t;
  (* A map from Catala struct names to the corresponding Z3 sort, from which we
     can retrieve the constructor and the accessors *)
  ctx_z3options : (string, Z3.Sort.sort) Hashtbl.t;
  (* Options are polymorphic in Catala but Z3 datatypes are monomorphic. Keep
     one instantiated Optional datatype per payload sort. *)
  ctx_z3tuples : (string, Z3.Sort.sort) Hashtbl.t;
  ctx_z3unit : Z3.Sort.sort * s_expr;
      (* A pair containing the Z3 encodings of the unit type, encoded as a tuple
          of 0 elements, and the unit value *)
  ctx_z3duration : Z3.Sort.sort;
  (* Calendar durations are triples [(years, months, days)]. Encoding them as
     one day count is unsound: a month has no fixed number of days. *)
  ctx_z3round : Z3.FuncDecl.func_decl;
  ctx_z3pow10 : Z3.FuncDecl.func_decl;
  ctx_optims : Optimizations.flag list; (* A list of optimizations to apply *)
  ctx_max_list_length : int;
  (* Global bound used when materialising symbolic list inputs. *)
  ctx_nested_lists : (string, SymbExpr.symb_list) Hashtbl.t;
  (* Symbolic lists stored below structure fields, keyed by the symbolic Z3
     accessor for that field. *)
  ctx_growable_lists :
    (int, SymbExpr.symb_list * (int -> unit)) Hashtbl.t;
  (* Input lists allocate one symbolic element initially. The closure appends
     stable, deterministically named elements when DFS crosses that list's
     current length frontier. *)
  ctx_lengths_demanded : (string, unit) Hashtbl.t;
  (* Avoid emitting the same lazy length decision twice in one execution.
     Equivalent non-constant length expressions share one decision. Fixed
     lengths need no solver decision and are deliberately excluded, avoiding
     the old collision between unrelated lists whose length was [1]. *)
  ctx_list_length_guards : (int, s_expr) Hashtbl.t;
  (* Additional bounds for lists derived from scalar inputs. Input-list bounds
     are hard solver constraints, but an external [sequence] needs its bound
     attached to every flippable traversal decision. *)
  ctx_on_expr : (conc_expr -> unit) ref;
  (* Optional instrumentation installed only around concrete path evaluation.
     Keeping it disabled during simplification avoids crediting expressions
     that merely become part of a closure. *)
  ctx_external_names : (Obj.t * string * string) list ref;
  (* [runtime_to_val] may wrap polymorphic runtime functions, so comparing an
     [ECustom] object with a fresh [Runtime.lookup_value] result is not a
     reliable way to identify an external. Record the qualified name at the
     [EExternal] node, before that source information is erased. *)
  ctx_branch_pairs : (string, string) Hashtbl.t;
  ctx_branch_hits : (string, unit) Hashtbl.t;
  ctx_binary_origins : (string, binary_source_origin) Hashtbl.t;
  ctx_match_origins : (string, match_source_origin) Hashtbl.t;
}

(** adds the mapping between the Catala struct [s] and the corresponding Z3
    datatype [sort] to the context **)
let add_z3struct (s : StructName.t) (sort : Z3.Sort.sort) (ctx : context) :
    context =
  { ctx with ctx_z3structs = StructName.Map.add s sort ctx.ctx_z3structs }

(** adds the mapping between the Catala enum [enum] and the corresponding Z3
    datatype [sort] to the context **)
let add_z3enum (enum : EnumName.t) (sort : Z3.Sort.sort) (ctx : context) :
    context =
  { ctx with ctx_z3enums = EnumName.Map.add enum sort ctx.ctx_z3enums }

let integer_of_symb_expr (e : s_expr) : Runtime.integer =
  match Z3.Sort.get_sort_kind (Z3.Expr.get_sort e) with
  | Z3enums.INT_SORT -> Z3.Arithmetic.Integer.get_big_int e
  | _ -> invalid_arg "[integer_of_symb_expr] expected a Z3 Integer"

let bool_of_symb_expr (e : s_expr) : Runtime.bool =
  match Z3.Sort.get_sort_kind (Z3.Expr.get_sort e) with
  | Z3enums.BOOL_SORT -> begin
    match Z3.Boolean.get_bool_value e with
    | L_FALSE -> false
    | L_TRUE -> true
    | L_UNDEF -> failwith "boolean value undefined"
  end
  | _ -> invalid_arg "[bool_of_symb_expr] expected a Z3 Boolean"

let decimal_of_symb_expr (e : s_expr) : Runtime.decimal =
  match Z3.Sort.get_sort_kind (Z3.Expr.get_sort e) with
  | Z3enums.REAL_SORT -> Z3.Arithmetic.Real.get_ratio e
  | _ -> invalid_arg "[decimal_of_symb_expr] expected a Z3 Real"

module DateEncoding = struct
  (* Dates are serial Gregorian days relative to 2010-01-01. Durations remain
     calendar triples; this keeps month/year arithmetic calendar-aware while
     preserving the efficient total ordering of dates. *)
  let mk_sort_date ctx = Z3.Arithmetic.Integer.mk_sort ctx.ctx_z3

  let mk_sort_duration ctx = ctx.ctx_z3duration

  let int ctx n = Z3.Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 n
  let add ctx xs = Z3.Arithmetic.mk_add ctx.ctx_z3 xs
  let sub ctx xs = Z3.Arithmetic.mk_sub ctx.ctx_z3 xs
  let mul ctx xs = Z3.Arithmetic.mk_mul ctx.ctx_z3 xs
  let div ctx a b = Z3.Arithmetic.mk_div ctx.ctx_z3 a b
  let modulo ctx a b = Z3.Arithmetic.Integer.mk_mod ctx.ctx_z3 a b
  let ite ctx c a b = Z3.Boolean.mk_ite ctx.ctx_z3 c a b

  let duration_parts ctx duration =
    match Z3.Tuple.get_field_decls ctx.ctx_z3duration with
    | [years; months; days] ->
      let get accessor = Z3.Expr.mk_app ctx.ctx_z3 accessor [duration] in
      get years, get months, get days
    | _ -> assert false

  let make_duration ctx years months days =
    Z3.Expr.mk_app ctx.ctx_z3 (Z3.Tuple.get_mk_decl ctx.ctx_z3duration)
      [years; months; days]

  let encode_duration ctx (dur : Runtime.duration) : s_expr =
    let y, m, d = Runtime.duration_to_years_months_days dur in
    make_duration ctx (int ctx y) (int ctx m) (int ctx d)

  let decode_duration (e : s_expr) : Runtime.duration =
    let args = Z3.Expr.get_args (Z3.Expr.simplify e None) in
    match args with
    | [years; months; days] ->
      Runtime.duration_of_numbers
        (Z.to_int (integer_of_symb_expr years))
        (Z.to_int (integer_of_symb_expr months))
        (Z.to_int (integer_of_symb_expr days))
    | _ -> invalid_arg "[DateEncoding.decode_duration] expected a duration"

  let default_duration : Runtime.duration = Runtime.duration_of_numbers 0 0 10
  let base_day : Runtime.date = Runtime.date_of_numbers 2010 1 1

  (** [date_to_bigint] translates [d] to an integer corresponding to the number
      of days since the base date. Adapted from z3backend *)
  let date_to_bigint (d : Runtime.date) : Z.t =
    let period = Runtime.Oper.o_sub_dat_dat d base_day in
    let y, m, d = Runtime.duration_to_years_months_days period in
    assert (y = 0 && m = 0);
    Z.of_int d

  let encode_date (ctx : context) (date : Runtime.date) : s_expr =
    let days = date_to_bigint date in
    z3_int_of_bigint ctx.ctx_z3 days

  let decode_date
      ?(round : Runtime.date_rounding = Dates_calc.AbortOnRound)
        (e : s_expr) : Runtime.date =
    let days =
      Runtime.duration_of_numbers 0 0
        (Z.to_int (integer_of_symb_expr e))
    in
    Runtime.o_add_dat_dur round (Expr.pos_to_runtime Pos.void) base_day days

  (* Default date is epoch *)
  let default_date : Runtime.date = base_day

  (* Howard Hinnant's proleptic-Gregorian civil/serial conversion, expressed
     entirely with integer div/mod/ite. The constant is the civil-day number
     of 2010-01-01 under the same formula. *)
  let civil_to_date ctx year month day =
    let year =
      sub ctx
        [year; ite ctx (Z3.Arithmetic.mk_le ctx.ctx_z3 month (int ctx 2))
                 (int ctx 1) (int ctx 0)]
    in
    let era = div ctx year (int ctx 400) in
    let yoe = sub ctx [year; mul ctx [era; int ctx 400]] in
    let mp =
      add ctx
        [month; ite ctx (Z3.Arithmetic.mk_gt ctx.ctx_z3 month (int ctx 2))
                  (int ctx (-3)) (int ctx 9)]
    in
    let doy =
      add ctx
        [ div ctx (add ctx [mul ctx [int ctx 153; mp]; int ctx 2])
            (int ctx 5);
          day; int ctx (-1) ]
    in
    let doe =
      add ctx
        [ mul ctx [yoe; int ctx 365]; div ctx yoe (int ctx 4);
          Z3.Arithmetic.mk_unary_minus ctx.ctx_z3 (div ctx yoe (int ctx 100));
          doy ]
    in
    sub ctx [add ctx [mul ctx [era; int ctx 146097]; doe]; int ctx 734078]

  let date_to_civil ctx date =
    let z = add ctx [date; int ctx 734078] in
    let era = div ctx z (int ctx 146097) in
    let doe = sub ctx [z; mul ctx [era; int ctx 146097]] in
    let yoe =
      div ctx
        (add ctx
           [ doe;
             Z3.Arithmetic.mk_unary_minus ctx.ctx_z3
               (div ctx doe (int ctx 1460));
             div ctx doe (int ctx 36524);
             Z3.Arithmetic.mk_unary_minus ctx.ctx_z3
               (div ctx doe (int ctx 146096)) ])
        (int ctx 365)
    in
    let year0 = add ctx [yoe; mul ctx [era; int ctx 400]] in
    let doy =
      sub ctx
        [ doe;
          add ctx
            [mul ctx [yoe; int ctx 365]; div ctx yoe (int ctx 4);
             Z3.Arithmetic.mk_unary_minus ctx.ctx_z3
               (div ctx yoe (int ctx 100))] ]
    in
    let mp = div ctx (add ctx [mul ctx [int ctx 5; doy]; int ctx 2])
        (int ctx 153) in
    let day =
      add ctx
        [ doy;
          Z3.Arithmetic.mk_unary_minus ctx.ctx_z3
            (div ctx (add ctx [mul ctx [int ctx 153; mp]; int ctx 2])
               (int ctx 5));
          int ctx 1 ]
    in
    let month =
      add ctx
        [mp; ite ctx (Z3.Arithmetic.mk_lt ctx.ctx_z3 mp (int ctx 10))
               (int ctx 3) (int ctx (-9))]
    in
    let year =
      add ctx
        [year0; ite ctx (Z3.Arithmetic.mk_le ctx.ctx_z3 month (int ctx 2))
                  (int ctx 1) (int ctx 0)]
    in
    year, month, day

  let is_leap ctx year =
    let eq0 x = Z3.Boolean.mk_eq ctx.ctx_z3 x (int ctx 0) in
    Z3.Boolean.mk_or ctx.ctx_z3
      [ eq0 (modulo ctx year (int ctx 400));
        Z3.Boolean.mk_and ctx.ctx_z3
          [eq0 (modulo ctx year (int ctx 4));
           Z3.Boolean.mk_not ctx.ctx_z3
             (eq0 (modulo ctx year (int ctx 100)))] ]

  let days_in_month ctx year month =
    let eq n = Z3.Boolean.mk_eq ctx.ctx_z3 month (int ctx n) in
    ite ctx (eq 2) (ite ctx (is_leap ctx year) (int ctx 29) (int ctx 28))
      (ite ctx
         (Z3.Boolean.mk_or ctx.ctx_z3 [eq 4; eq 6; eq 9; eq 11])
         (int ctx 30) (int ctx 31))

  let valid_ymd ctx year month day =
    Z3.Boolean.mk_and ctx.ctx_z3
      [ Z3.Arithmetic.mk_ge ctx.ctx_z3 month (int ctx 1);
        Z3.Arithmetic.mk_le ctx.ctx_z3 month (int ctx 12);
        Z3.Arithmetic.mk_ge ctx.ctx_z3 day (int ctx 1);
        Z3.Arithmetic.mk_le ctx.ctx_z3 day (days_in_month ctx year month) ]

  let requires_rounding ctx date duration =
    let years, months, _days = duration_parts ctx duration in
    let year, month, day = date_to_civil ctx date in
    let total_month = add ctx [month; months; int ctx (-1)] in
    let new_year = add ctx [year; years; div ctx total_month (int ctx 12)] in
    let new_month = add ctx [modulo ctx total_month (int ctx 12); int ctx 1] in
    Z3.Arithmetic.mk_gt ctx.ctx_z3 day
      (days_in_month ctx new_year new_month)

  let add_dat_dur ctx round date duration =
    let years, months, days = duration_parts ctx duration in
    let year, month, day = date_to_civil ctx date in
    let total_month = add ctx [month; months; int ctx (-1)] in
    let new_year = add ctx [year; years; div ctx total_month (int ctx 12)] in
    let new_month = add ctx [modulo ctx total_month (int ctx 12); int ctx 1] in
    let last = days_in_month ctx new_year new_month in
    let invalid = Z3.Arithmetic.mk_gt ctx.ctx_z3 day last in
    let rounded_year, rounded_month, rounded_day =
      match round with
      | Dates_calc.RoundDown | Dates_calc.AbortOnRound ->
        new_year, new_month, ite ctx invalid last day
      | Dates_calc.RoundUp ->
        let next_total = add ctx [new_month; int ctx 0] in
        ( ite ctx invalid
            (add ctx [new_year; div ctx next_total (int ctx 12)]) new_year,
          ite ctx invalid
            (add ctx [modulo ctx next_total (int ctx 12); int ctx 1]) new_month,
          ite ctx invalid (int ctx 1) day )
    in
    add ctx [civil_to_date ctx rounded_year rounded_month rounded_day; days]

  let minus_dur ctx duration =
    let y, m, d = duration_parts ctx duration in
    make_duration ctx
      (Z3.Arithmetic.mk_unary_minus ctx.ctx_z3 y)
      (Z3.Arithmetic.mk_unary_minus ctx.ctx_z3 m)
      (Z3.Arithmetic.mk_unary_minus ctx.ctx_z3 d)

  let add_dur_dur ctx a b =
    let ay, am, ad = duration_parts ctx a and by, bm, bd = duration_parts ctx b in
    make_duration ctx (add ctx [ay; by]) (add ctx [am; bm]) (add ctx [ad; bd])

  let sub_dat_dat ctx a b = make_duration ctx (int ctx 0) (int ctx 0) (sub ctx [a; b])
  let sub_dur_dur ctx a b =
    let ay, am, ad = duration_parts ctx a and by, bm, bd = duration_parts ctx b in
    make_duration ctx (sub ctx [ay; by]) (sub ctx [am; bm]) (sub ctx [ad; bd])

  let mult_dur_int ctx duration factor =
    let y, m, d = duration_parts ctx duration in
    make_duration ctx (mul ctx [y; factor]) (mul ctx [m; factor])
      (mul ctx [d; factor])

  (** Catala durations have two comparable domains: calendar durations
      (years/months, with zero days) and exact day durations (zero
      years/months). A mixed comparison is a runtime [DateError]. Keep that
      partial semantics explicit instead of passing the duration tuple to an
      arithmetic Z3 comparator. *)
  let duration_comparison ctx comparison left right =
    let ly, lm, ld = duration_parts ctx left in
    let ry, rm, rd = duration_parts ctx right in
    let zero = int ctx 0 in
    let eq0 value = Z3.Boolean.mk_eq ctx.ctx_z3 value zero in
    let calendar_mode =
      Z3.Boolean.mk_and ctx.ctx_z3 [eq0 ld; eq0 rd]
    in
    let day_mode =
      Z3.Boolean.mk_and ctx.ctx_z3 [eq0 ly; eq0 lm; eq0 ry; eq0 rm]
    in
    let valid =
      Z3.Boolean.mk_or ctx.ctx_z3 [calendar_mode; day_mode]
    in
    let months years months = add ctx [mul ctx [int ctx 12; years]; months] in
    let calendar_result = comparison (months ly lm) (months ry rm) in
    let day_result = comparison ld rd in
    valid, ite ctx calendar_mode calendar_result day_result

  let duration_equality ctx left right =
    let structural = Z3.Boolean.mk_eq ctx.ctx_z3 left right in
    let comparable, numerical =
      duration_comparison ctx (Z3.Boolean.mk_eq ctx.ctx_z3) left right
    in
    ( Z3.Boolean.mk_or ctx.ctx_z3 [structural; comparable],
      Z3.Boolean.mk_or ctx.ctx_z3 [structural; numerical] )

  let div_dur_dur ctx dur1 dur2 =
    (* TODO factorize with [Div_int_int]? *)
    (* convert e1 to a [Real] explicitely to avoid using integer division *)
    let _, _, days1 = duration_parts ctx dur1 in
    let _, _, days2 = duration_parts ctx dur2 in
    let dur1_rat = z3_force_real ctx.ctx_z3 days1 in
    Z3.Arithmetic.mk_div ctx.ctx_z3 dur1_rat days2
end

(** [translate_typ_lit] returns the Z3 sort corresponding to the Catala literal
    type [t] **)
let translate_typ_lit (ctx : context) (t : typ_lit) : Z3.Sort.sort =
  match t with
  | TBool -> Z3.Boolean.mk_sort ctx.ctx_z3
  | TPos | TUnit -> fst ctx.ctx_z3unit
  | TInt -> Z3.Arithmetic.Integer.mk_sort ctx.ctx_z3
  | TRat -> Z3.Arithmetic.Real.mk_sort ctx.ctx_z3
  | TMoney -> Z3.Arithmetic.Integer.mk_sort ctx.ctx_z3
  | TDate -> DateEncoding.mk_sort_date ctx
  | TDuration -> DateEncoding.mk_sort_duration ctx

(** [translate_typ] returns the Z3 sort correponding to the Catala type [t] **)
let rec translate_typ (ctx : context) (t : naked_typ) : context * Z3.Sort.sort =
  match t with
  | TLit t -> ctx, translate_typ_lit ctx t
  | TStruct name ->
    find_or_create_struct ctx name
    (* DONE CONC are declarations sorted in topological order? "Yes" -Denis *)
    (* use [type_ordering] from Driver to make sure ? =>> actually it does not
       work because the input struct for scope [A], called [A_in], is not a part
       of this order *)
  | TTuple tys -> find_or_create_tuple ctx tys
  | TEnum name -> find_or_create_enum ctx name
  | TOption ty -> find_or_create_option ctx ty
  | TArrow ([(TLit TUnit, _)], (TDefault _, _)) ->
    failwith "[translate_typ] no more thunk"
    (* FIXME CONTEXT *)
    (* context variable *)
    (* ctx, ctx.ctx_dummy_sort *)
  | TArrow _ -> ctx, ctx.ctx_dummy_sort (* other functions *)
  | TArray _ ->
    ( ctx,
      ctx.ctx_dummy_sort
      (* TODO maybe put a better sort here? this should not be read anyway... *)
    )
  | TForAll b ->
    let vars, _ = Bindlib.unmbind b in
    begin match vars with
    | [| v |] ->
      ( ctx,
        Z3.Sort.mk_uninterpreted_s ctx.ctx_z3
          (Bindlib.name_of v ^ (Bindlib.uid_of v |> string_of_int)) )
    | _ -> failwith "[translate_typ] TForAll(tuple) not implemented"
    end
  | TClosureEnv -> failwith "[translate_typ] TClosureEnv not implemented"
  | TDefault _ ->
    (* context variable *)
    ctx, ctx.ctx_reentrant_sort
  | TVar v ->
    (* (\* A type variable being an unresolved type, it can't be deconstructed, so *)
    (*    we can let it pass through. *\) *)
    (* failwith "[translate_typ] TVar not implemented" *)
    (* ?? *)
    ( ctx,
      Z3.Sort.mk_uninterpreted_s ctx.ctx_z3
        (Bindlib.name_of v ^ (Bindlib.uid_of v |> string_of_int)) )
  | TAbstract _ -> failwith "[translate_typ] TAbstract not implemented"
  | TError -> assert false

(* taken from z3backend's find_or_create_struct *)
and find_or_create_struct (ctx : context) (s : StructName.t) :
    context * Z3.Sort.sort =
  Message.debug "[Struct] Find or create struct %s"
    (Mark.remove (StructName.get_info s));
  match StructName.Map.find_opt s ctx.ctx_z3structs with
  | Some s ->
    Message.debug "[Struct] . found!";
    ctx, s
  | None ->
    (* Z3 sort names live in one global namespace. The source-level basename
       is not unique under [-W] (for example, multiple modules declare a
       [FilingStatus]), and a struct and enum may also share a basename. *)
    let s_name = "struct!" ^ StructName.to_string s in
    let fields = StructName.Map.find s ctx.ctx_decl.ctx_structs in

    let mk_struct_s =
      "mk!" ^ s_name
      (* struct constructor *)
    in
    let is_struct_s =
      "is!" ^ s_name
      (* recognizer *)
    in
    let z3_fieldnames =
      List.map
        (fun f ->
          let raw_field_name = Mark.remove (StructField.get_info f) in
          let field_name = "fd!" ^ raw_field_name in
          Z3.Symbol.mk_string ctx.ctx_z3 field_name)
        (StructField.Map.keys fields)
    in
    let ctx, z3_fieldtypes_rev =
      StructField.Map.fold
        (fun f ty (ctx, ftypes) ->
          Message.debug "[Struct] . %s : %a"
            (Mark.remove (StructField.get_info f))
            Print.typ ty;
          let ctx, ftype = translate_typ ctx (Mark.remove ty) in
          ctx, ftype :: ftypes)
        fields (ctx, [])
    in
    let z3_fieldtypes = List.rev z3_fieldtypes_rev in
    let z3_sortrefs =
      List.map (fun _ -> 0) z3_fieldtypes (* will not be used *)
    in

    let z3_mk_struct =
      Z3.Datatype.mk_constructor_s ctx.ctx_z3 mk_struct_s
        (Z3.Symbol.mk_string ctx.ctx_z3 is_struct_s)
        z3_fieldnames
        (List.map Option.some z3_fieldtypes)
        z3_sortrefs
    in
    let z3_struct = Z3.Datatype.mk_sort_s ctx.ctx_z3 s_name [z3_mk_struct] in
    add_z3struct s z3_struct ctx, z3_struct

(* inspired by z3backend *)
and find_or_create_option (ctx : context) (payload_ty : typ) :
    context * Z3.Sort.sort =
  let ctx, payload_sort = translate_typ ctx (Mark.remove payload_ty) in
  find_or_create_option_sort ctx payload_sort

and find_or_create_option_sort (ctx : context) (payload_sort : Z3.Sort.sort) :
    context * Z3.Sort.sort =
  let key = Z3.Sort.to_string payload_sort in
  match Hashtbl.find_opt ctx.ctx_z3options key with
  | Some sort -> ctx, sort
  | None ->
    let suffix = Digest.(to_hex (string key)) in
    let constructor name payload =
      Z3.Datatype.mk_constructor_s ctx.ctx_z3
        ("mk!" ^ name ^ "!" ^ suffix)
        (Z3.Symbol.mk_string ctx.ctx_z3 ("is!" ^ name ^ "!" ^ suffix))
        [Z3.Symbol.mk_string ctx.ctx_z3 (name ^ "!0!" ^ suffix)]
        [Some payload] [0]
    in
    let sort =
      Z3.Datatype.mk_sort_s ctx.ctx_z3 ("Optional!" ^ suffix)
        [ constructor "Absent" (fst ctx.ctx_z3unit);
          constructor "Present" payload_sort ]
    in
    Hashtbl.add ctx.ctx_z3options key sort;
    ctx, sort

and find_or_create_tuple (ctx : context) (tys : typ list) :
    context * Z3.Sort.sort =
  let ctx, sorts =
    List.fold_left_map translate_typ ctx (List.map Mark.remove tys)
  in
  find_or_create_tuple_sort ctx sorts

and find_or_create_tuple_sort (ctx : context) (sorts : Z3.Sort.sort list) :
    context * Z3.Sort.sort =
  let key = String.concat "*" (List.map Z3.Sort.to_string sorts) in
  match Hashtbl.find_opt ctx.ctx_z3tuples key with
  | Some sort -> ctx, sort
  | None ->
    let suffix = Digest.(to_hex (string key)) in
    let fields =
      List.mapi
        (fun i _ -> Z3.Symbol.mk_string ctx.ctx_z3
            (Printf.sprintf "tuple_%d!%s" i suffix)) sorts
    in
    let sort =
      Z3.Tuple.mk_sort ctx.ctx_z3
        (Z3.Symbol.mk_string ctx.ctx_z3 ("tuple!" ^ suffix)) fields sorts
    in
    Hashtbl.add ctx.ctx_z3tuples key sort;
    ctx, sort

and find_or_create_enum (ctx : context) (enum : EnumName.t) :
    context * Z3.Sort.sort =
  Message.debug "[Enum] Find or create enum %s"
    (Mark.remove (EnumName.get_info enum));

  let create_constructor (name : EnumConstructor.t) (ty : typ) (ctx : context) :
      context * Z3.Datatype.Constructor.constructor =
    let cstr_name = Mark.remove (EnumConstructor.get_info name) in
    let mk_cstr_s =
      "mk!" ^ cstr_name
      (* case constructor *)
    in
    let is_cstr_s =
      "is!" ^ cstr_name
      (* recognizer *)
    in
    let fieldname_s =
      cstr_name ^ "!0"
      (* name of the argument *)
    in
    let ctx, z3_arg_ty = translate_typ ctx (Mark.remove ty) in
    let z3_sortrefs =
      [0]
      (* will not be used *)
    in

    Message.debug "[Enum] . %s : %a" cstr_name Print.typ ty;
    ( ctx,
      Z3.Datatype.mk_constructor_s ctx.ctx_z3 mk_cstr_s
        (Z3.Symbol.mk_string ctx.ctx_z3 is_cstr_s)
        [Z3.Symbol.mk_string ctx.ctx_z3 fieldname_s]
        [Some z3_arg_ty] z3_sortrefs )
  in

  match EnumName.Map.find_opt enum ctx.ctx_z3enums with
  | Some e ->
    Message.debug "[Enum] . found!";
    ctx, e
  | None ->
    let ctrs = EnumName.Map.find enum ctx.ctx_decl.ctx_enums in
    let ctx, z3_ctrs =
      EnumConstructor.Map.fold
        (fun ctr ty (ctx, ctrs) ->
          let ctx, ctr = create_constructor ctr ty ctx in
          ctx, ctr :: ctrs)
        ctrs (ctx, [])
    in
    let z3_enum =
      Z3.Datatype.mk_sort_s ctx.ctx_z3
        ("enum!" ^ EnumName.to_string enum)
        (List.rev z3_ctrs)
    in
    add_z3enum enum z3_enum ctx, z3_enum

(** [create_z3unit] creates a Z3 sort and expression corresponding to the unit
    type and value respectively. Concretely, we represent unit as a tuple with 0
    elements. Taken from z3backend. **)
let create_z3unit (ctx : Z3.context) : Z3.Sort.sort * Z3.Expr.expr =
  let unit_sort = Z3.Tuple.mk_sort ctx (Z3.Symbol.mk_string ctx "unit") [] [] in
  let mk_unit = Z3.Tuple.get_mk_decl unit_sort in
  let unit_val = Z3.Expr.mk_app ctx mk_unit [] in
  unit_sort, unit_val

let create_z3round (ctx : Z3.context) : Z3.FuncDecl.func_decl =
  let real_sort = Z3.Arithmetic.Real.mk_sort ctx in
  let int_sort = Z3.Arithmetic.Integer.mk_sort ctx in
  let func_decl =
    Z3.FuncDecl.mk_rec_func_decl_s ctx "!round!" [real_sort] int_sort
  in
  let var = Z3.Arithmetic.Real.mk_const_s ctx "!q!" in
  Z3.FuncDecl.add_rec_def ctx func_decl [var] (z3_round_expr ctx var);
  func_decl

let create_z3pow10 (ctx : Z3.context) : Z3.FuncDecl.func_decl =
  let int_sort = Z3.Arithmetic.Integer.mk_sort ctx in
  let func_decl =
    Z3.FuncDecl.mk_rec_func_decl_s ctx "!pow10!" [int_sort] int_sort
  in
  let n = Z3.Arithmetic.Integer.mk_const_s ctx "!pow10_n!" in
  let int k = Z3.Arithmetic.Integer.mk_numeral_i ctx k in
  let body =
    Z3.Boolean.mk_ite ctx
      (Z3.Arithmetic.mk_le ctx n (int 0)) (int 1)
      (Z3.Arithmetic.mk_mul ctx
         [int 10; Z3.Expr.mk_app ctx func_decl
                    [Z3.Arithmetic.mk_sub ctx [n; int 1]]])
  in
  Z3.FuncDecl.add_rec_def ctx func_decl [n] body;
  func_decl

(* TODO move to utils? *)
let z3_round ctx = Z3_utils.z3_round_func ctx.ctx_z3round

(* taken from z3backend, but without the option check *)
let make_empty_context
    (decl_ctx : decl_ctx)
    (optims : Optimizations.flag list)
    (max_list_length : int) : context =
  let z3_cfg = ["model", "true"; "proof", "false"] in
  let z3_ctx = Z3.mk_context z3_cfg in
  let z3_dummy_sort = Z3.Sort.mk_uninterpreted_s z3_ctx "!dummy_sort!" in
  let z3_dummy_const =
    Z3.Expr.mk_const_s z3_ctx "!dummy_const!" z3_dummy_sort
  in
  let int_sort = Z3.Arithmetic.Integer.mk_sort z3_ctx in
  let z3_duration =
    Z3.Tuple.mk_sort z3_ctx (Z3.Symbol.mk_string z3_ctx "duration")
      [ Z3.Symbol.mk_string z3_ctx "years";
        Z3.Symbol.mk_string z3_ctx "months";
        Z3.Symbol.mk_string z3_ctx "days" ]
      [int_sort; int_sort; int_sort]
  in
  let z3_reentrant_sort =
    Z3.Sort.mk_uninterpreted_s z3_ctx "!reentrant_sort!"
  in
  let z3_reentrant_const =
    Z3.Expr.mk_const_s z3_ctx "!reentrant_const!" z3_reentrant_sort
  in
  {
    ctx_z3 = z3_ctx;
    ctx_decl = decl_ctx;
    (*     ctx_funcdecl = Var.Map.empty; *)
    (*     ctx_z3vars = StringMap.empty; *)
    ctx_z3enums = EnumName.Map.empty;
    (* ctx_z3matchsubsts = Var.Map.empty; *)
    ctx_z3structs = StructName.Map.empty;
    ctx_z3options = Hashtbl.create 17;
    ctx_z3tuples = Hashtbl.create 17;
    ctx_z3unit = create_z3unit z3_ctx;
    ctx_z3duration = z3_duration;
    ctx_z3round = create_z3round z3_ctx;
    ctx_z3pow10 = create_z3pow10 z3_ctx;
    (* ctx_z3constraints = []; *)
    ctx_dummy_sort = z3_dummy_sort;
    ctx_dummy_const = z3_dummy_const;
    ctx_reentrant_sort = z3_reentrant_sort;
    ctx_reentrant_const = z3_reentrant_const;
    ctx_optims = optims;
    ctx_max_list_length = max_list_length;
    ctx_nested_lists = Hashtbl.create 31;
    ctx_growable_lists = Hashtbl.create 31;
    ctx_lengths_demanded = Hashtbl.create 31;
    ctx_list_length_guards = Hashtbl.create 31;
    ctx_on_expr = ref (fun _ -> ());
    ctx_external_names = ref [];
    ctx_branch_pairs = Hashtbl.create 257;
    ctx_branch_hits = Hashtbl.create 257;
    ctx_binary_origins = Hashtbl.create 257;
    ctx_match_origins = Hashtbl.create 257;
  }

let init_context (ctx : context) : context =
  (* create all struct sorts *)
  let ctx =
    StructName.Map.fold
      (fun s _ ctx -> fst (find_or_create_struct ctx s))
      ctx.ctx_decl.ctx_structs ctx
  in
  let ctx =
    EnumName.Map.fold
      (fun enum _ ctx -> fst (find_or_create_enum ctx enum))
      ctx.ctx_decl.ctx_enums ctx
  in
  ctx

let position_id pos =
  Printf.sprintf "%s:%d:%d-%d:%d" (Pos.get_file pos)
    (Pos.get_start_line pos) (Pos.get_start_column pos)
    (Pos.get_end_line pos) (Pos.get_end_column pos)

let outcome_key tag pos =
  match tag with
  | Branching _ -> "branch@" ^ position_id pos
  | Exception { cons_pos; _ } ->
    "default@" ^ position_id pos ^ "=>" ^ position_id cons_pos
  | _ -> ""

let decision_id kind pos = kind ^ "@" ^ position_id pos

(** Build the source-semantic branch manifest from trace tags and match-arm
    positions inserted during surface desugaring. Wildcard expansion gives all
    compiler-generated constructor arms the position of the one written arm,
    so [Hashtbl.replace] folds them back together. *)
let index_source_branches ?(definitions = Var.Map.empty) ctx root =
  Hashtbl.clear ctx.ctx_branch_pairs;
  Hashtbl.clear ctx.ctx_binary_origins;
  Hashtbl.clear ctx.ctx_match_origins;
  let decision_by_pair = Hashtbl.create 257 in
  let outcomes_by_decision = Hashtbl.create 257 in
  let visited_definitions = ref Var.Set.empty in
  let register_outcome decision outcome =
    let pair = decision ^ "/" ^ outcome in
    Hashtbl.replace ctx.ctx_branch_pairs outcome pair;
    Hashtbl.replace decision_by_pair pair decision;
    let outcomes =
      Option.value ~default:[]
        (Hashtbl.find_opt outcomes_by_decision decision)
    in
    Hashtbl.replace outcomes_by_decision decision (pair :: outcomes)
  in
  let rec walk current_decision e =
    match Mark.remove e with
    | EVar var ->
      begin match Var.Map.find_opt var definitions with
      | Some definition when not (Var.Set.mem var !visited_definitions) ->
        visited_definitions := Var.Set.add var !visited_definitions;
        walk None definition
      | _ -> ()
      end
    | EIfThenElse { cond; etrue; efalse } ->
      walk None cond;
      let decision = decision_id "if" (Expr.pos e) in
      walk (Some decision) etrue;
      walk (Some decision) efalse
    | EMatch { e = subject; cases; _ } ->
      walk None subject;
      let decision = decision_id "match" (Expr.pos e) in
      (* Wildcard arms are desugared to one arm per missing constructor and
         their payload may then be hoisted out of the match. The arm position
         still identifies the case that the author wrote: duplicate wildcard
         arms collapse, while same-line written arms retain distinct columns. *)
      EnumConstructor.Map.iter
        (fun _ arm ->
          register_outcome decision ("branch@" ^ position_id (Expr.pos arm));
          walk None arm)
        cases
    | EDefault { excepts; just; cons } ->
      let current =
        if List.length excepts >= 1 then
          Some (decision_id "default" (Expr.pos e))
        else current_decision
      in
      List.iter (walk current) excepts;
      walk current just;
      walk current cons
    | EAppOp { op = Tag tag, _; args = [inner]; _ } ->
      begin match tag, current_decision with
      | (Branching _ | Exception _), Some decision ->
        let outcome = outcome_key tag (Expr.pos e) in
        register_outcome decision outcome
      | _ -> ()
      end;
      walk None inner
    | _ -> Expr.shallow_fold (fun child () -> walk current_decision child) e ()
  in
  walk None root;
  (* A source decision needs at least two distinct outcomes. In particular,
     wildcard expansion may create several compiler arms for one source arm;
     those still collapse to one outcome and must not turn a single-arm match
     into a branch. *)
  Hashtbl.filter_map_inplace
    (fun _ pair ->
      match Hashtbl.find_opt decision_by_pair pair with
      | None -> None
      | Some decision ->
        let outcomes =
          Option.value ~default:[]
            (Hashtbl.find_opt outcomes_by_decision decision)
          |> List.sort_uniq String.compare
        in
        if List.length outcomes >= 2 then Some pair else None)
    ctx.ctx_branch_pairs;
  let pair_has_decision decision pair =
    let prefix = decision ^ "/" in
    String.length pair >= String.length prefix
    && String.equal prefix (String.sub pair 0 (String.length prefix))
  in
  let rec outcomes_below decision e =
    match Mark.remove e with
    | EAppOp { op = Tag ((Branching _ | Exception _) as tag), _;
               args = [inner]; _ } ->
      let own =
        Hashtbl.find_opt ctx.ctx_branch_pairs (outcome_key tag (Expr.pos e))
        |> Option.to_list
        |> List.filter (pair_has_decision decision)
      in
      if own = [] then outcomes_below decision inner else own
    | _ ->
      Expr.shallow_fold
        (fun child outcomes -> outcomes_below decision child @ outcomes)
        e []
  in
  let uniq = List.sort_uniq String.compare in
  let difference all selected =
    List.filter (fun outcome -> not (List.mem outcome selected)) all
  in
  let add_binary pos decision true_outcomes false_outcomes =
    Hashtbl.replace ctx.ctx_binary_origins (position_id pos)
      { binary_decision_id = decision;
        true_outcomes = uniq true_outcomes;
        false_outcomes = uniq false_outcomes }
  in
  let rec index_default_conditions decision all_outcomes e =
    match Mark.remove e with
    | EIfThenElse _ | EMatch _ -> ()
    | EDefault { excepts = []; just; cons } ->
      let selected = uniq (outcomes_below decision cons) in
      if selected <> [] then
        add_binary (Expr.pos just) decision selected
          (difference all_outcomes selected);
      index_default_conditions decision all_outcomes just;
      index_default_conditions decision all_outcomes cons
    | EDefault _ -> ()
    | _ ->
      Expr.shallow_fold
        (fun child () -> index_default_conditions decision all_outcomes child)
        e ()
  in
  let rec index_origins e =
    match Mark.remove e with
    | EIfThenElse { cond; etrue; efalse } ->
      let decision = decision_id "if" (Expr.pos e) in
      add_binary (Expr.pos cond) decision
        (outcomes_below decision etrue)
        (outcomes_below decision efalse);
      index_origins cond;
      index_origins etrue;
      index_origins efalse
    | EMatch { e = subject; cases; _ } ->
      let decision = decision_id "match" (Expr.pos e) in
      let constructor_outcomes =
        EnumConstructor.Map.bindings cases
        |> List.filter_map (fun (constructor, arm) ->
             Hashtbl.find_opt ctx.ctx_branch_pairs
               ("branch@" ^ position_id (Expr.pos arm))
             |> Option.map (fun outcome ->
                  EnumConstructor.to_string constructor, outcome))
      in
      Hashtbl.replace ctx.ctx_match_origins (position_id (Expr.pos subject))
        { match_decision_id = decision; constructor_outcomes };
      index_origins subject;
      EnumConstructor.Map.iter (fun _ arm -> index_origins arm) cases
    | EDefault { excepts; just; cons } when List.length excepts >= 1 ->
      let decision = decision_id "default" (Expr.pos e) in
      let all_outcomes = uniq (outcomes_below decision e) in
      List.iter
        (index_default_conditions decision all_outcomes)
        (cons :: excepts);
      List.iter index_origins excepts;
      index_origins just;
      index_origins cons
    | _ -> Expr.shallow_fold (fun child () -> index_origins child) e ()
  in
  index_origins root

let origin_for_binary ctx pos branch =
  Option.map
    (fun source_origin ->
      let taken, flipped =
        if branch then source_origin.true_outcomes, source_origin.false_outcomes
        else source_origin.false_outcomes, source_origin.true_outcomes
      in
      PathConstraint.
        { decision_id = source_origin.binary_decision_id;
          taken_outcome = List.nth_opt taken 0;
          may_reach_when_flipped = flipped })
    (Hashtbl.find_opt ctx.ctx_binary_origins (position_id pos))

let origin_for_match ctx pos constructor actual_constructor is_selected =
  Option.map
    (fun source_origin ->
      let outcome_for name =
        List.assoc_opt (EnumConstructor.to_string name)
          source_origin.constructor_outcomes
      in
      let selected = outcome_for constructor in
      let actual = outcome_for actual_constructor in
      let flipped =
        if is_selected then
          List.filter_map
            (fun (name, outcome) ->
              if String.equal name (EnumConstructor.to_string constructor) then
                None
              else Some outcome)
            source_origin.constructor_outcomes
        else Option.to_list selected
      in
      PathConstraint.
        { decision_id = source_origin.match_decision_id;
          taken_outcome = actual;
          may_reach_when_flipped = List.sort_uniq String.compare flipped })
    (Hashtbl.find_opt ctx.ctx_match_origins (position_id pos))

let record_taken_origin ctx = function
  | Some { PathConstraint.taken_outcome = Some outcome; _ } ->
    Hashtbl.replace ctx.ctx_branch_hits outcome ()
  | Some { taken_outcome = None; _ } | None -> ()

let record_match_origin ctx pos constructor =
  Option.iter
    (fun source_origin ->
      List.assoc_opt (EnumConstructor.to_string constructor)
        source_origin.constructor_outcomes
      |> Option.iter (fun outcome ->
           Hashtbl.replace ctx.ctx_branch_hits outcome ()))
    (Hashtbl.find_opt ctx.ctx_match_origins (position_id pos))

let record_source_branch ctx tag tagged result =
  let taken =
    match tag, Mark.remove result with
    | Branching _, _ -> true
    | Exception _, ELit (LBool true) -> true
    | Exception _, _ -> false
    | _ -> false
  in
  if taken then
    let key = outcome_key tag (Expr.pos tagged) in
    Option.iter
      (fun pair -> Hashtbl.replace ctx.ctx_branch_hits pair ())
      (Hashtbl.find_opt ctx.ctx_branch_pairs key)

let sorted_table_keys table =
  Hashtbl.fold (fun key () keys -> key :: keys) table [] |> List.sort String.compare

let print_json_string_list prefix strings =
  let json = `List (List.map (fun value -> `String value) strings) in
  Message.result "%s %s" prefix (Yojson.Safe.to_string json)

(* loosely taken from z3backend, could be exposed instead? not necessarily,
   especially if they become plugins *)
let z3_of_lit ctx (l : lit) : s_expr =
  match l with
  | LBool b -> Z3.Boolean.mk_val ctx.ctx_z3 b
  | LInt n -> z3_int_of_bigint ctx.ctx_z3 n
  | LRat r ->
    Z3.Arithmetic.Real.mk_numeral_s ctx.ctx_z3
      (Z.to_string r.num ^ "/" ^ Z.to_string r.den)
  | LMoney m ->
    let cents = Runtime.money_to_cents m in
    z3_int_of_bigint ctx.ctx_z3 cents
  | LUnit -> snd ctx.ctx_z3unit
  | LDate date -> DateEncoding.encode_date ctx date
  | LDuration dur -> DateEncoding.encode_duration ctx dur

(** Truncation of a real towards zero, which is what [ToInt_rat] does
    concretely: [o_toint_rat] is [Q.to_bigint], and Zarith's division rounds
    towards zero.  Z3's [mk_real2int] is *floor*, so the two agree on positive
    values and disagree on every negative one --- [-1.5] truncates to [-1] but
    floors to [-2].  A concolic engine cannot afford that: the solver would
    hand back an input whose concrete re-execution takes a different path.  So
    negatives are reflected through zero. *)
let z3_trunc_to_int ctx (x : s_expr) : s_expr =
  let zero = Z3.Arithmetic.Real.mk_numeral_i ctx 0 in
  let floor e = Z3.Arithmetic.Real.mk_real2int ctx e in
  Z3.Boolean.mk_ite ctx
    (Z3.Arithmetic.mk_ge ctx x zero)
    (floor x)
    (Z3.Arithmetic.mk_unary_minus ctx
       (floor (Z3.Arithmetic.mk_unary_minus ctx x)))

let symb_of_lit ctx (l : lit) : SymbExpr.t = SymbExpr.mk_z3 (z3_of_lit ctx l)

let _get_symb_expr_unsafe (e : ((yes, 'e) conc_interpr_kind, conc_info) gexpr) :
    SymbExpr.t =
  let (Custom { custom; _ }) = Mark.get e in
  custom.symb_expr

(** Get the symbolic expression corresponding to concolic expression [e]. This
    function makes sure that an expression that can't be [EGenericError] does
    not have a [Symb_error] symbolic expression. *)
let get_symb_expr (e : conc_expr) : SymbExpr.t =
  match _get_symb_expr_unsafe e with
  | Symb_error _ ->
    invalid_arg
      "[get_symb_expr] an expression that can't be an error cannot have an \
       error symbolic expression"
  | _ as s -> s

(** Get the symbolic expression corresponding to concolic result [e]. The
    symbolic expression can be a [Symb_error] here *)
let get_symb_expr_r (e : conc_result) : SymbExpr.t = _get_symb_expr_unsafe e

let _get_constraints_unsafe (e : ((yes, 'e) conc_interpr_kind, conc_info) gexpr)
    : PathConstraint.naked_path =
  let (Custom { custom; _ }) = Mark.get e in
  custom.constraints

(* Get constraints from concolic expression that cannot be an error. The
   signature of this function helps making sure that errors are always properly
   propagated during execution. By forcing [get_constraints_r] to be called
   explicitely if the expression is a result. *)
let get_constraints (e : conc_expr) : PathConstraint.naked_path =
  _get_constraints_unsafe e

let get_constraints_r (e : conc_result) : PathConstraint.naked_path =
  _get_constraints_unsafe e

(** [Stdlib.(@)] is recursive in the length of its left operand. Concolic
    paths routinely contain tens of thousands of constraints, so ordinary
    append can overflow while merely assembling a perfectly valid path. *)
let append_constraints left right = List.rev_append (List.rev left) right

let concat_constraints chunks =
  List.fold_left
    (fun acc chunk -> append_constraints chunk acc)
    [] (List.rev chunks)

(** Concatenate the constraints from a list of evaluated expressions [es]. [es]
    is expected to be in the order of evaluation of the expressions. *)
let gather_constraints (es : conc_expr list) =
  (* NOTE The expression evaluated last has its constraint on top, hence the
     list reversal. The constraints inside each expression are expected to be in
     the right order, with the "most recent" constraint first. Thus, the most
     recent constraint of the last evaluated (most recent) expression is on the
     top of the output list. *)
  let es_rev = List.rev es in
  concat_constraints (List.map get_constraints es_rev)

let get_type (e : conc_expr) : typ option =
  let (Custom { custom; _ }) = Mark.get e in
  custom.ty

let combine_exact what left right =
  if List.length left <> List.length right then
    Message.error
      "[CUTECat] %s arity mismatch: Catala has %d entries, Z3 has %d" what
      (List.length left) (List.length right);
  List.combine left right

let make_z3_struct ctx (name : StructName.t) (es : conc_expr list) : s_expr =
  let sort = StructName.Map.find name ctx.ctx_z3structs in
  let constructor = List.hd (Z3.Datatype.get_constructors sort) in
  let z3_of_expr (e : conc_expr) (d : Z3.Sort.sort) : s_expr =
    (* To build a Z3 struct, all of the fields of the concolic struct must have
     * a z3 symbolic expression.
     * - Normal fields will have a z3 symbolic expression computed during their
     *   evaluation (just before this function is called)
     * - Context variables in input structures will have their reentrant
     *   symbolic expression: we can put a dummy z3 constant (of the designated
     *   dummy z3 sort), because this constant will not be accessed by a
     *   StructAccess. Indeed, the only access to a reentrant field is during a
     *   Default case that is handled in a specific way.
     * - Functions do not have a symbolic value for now, so they can also have
     *   the dummy z3 constant. They won't be accessed in a symbolic way because
     *   the only expression in which they can be used is an application: in such a
     *   case, the symbolic expression of the function is ignored and a new
     *   symbolic expression is computed concolically (following the symbolic
     *   expressoin of the body of function).
     * - If a field is not a function but has no symbolic value, an error is
     *   raised because its value should have been computed before.
     *)
    (* FIXME CONTEXT is this right? *)
    (* don't if the field is of sort reentrant, we don't need the underlying
     * symbolic expression because it would be of the wrong sort *)
    if d = ctx.ctx_reentrant_sort then ctx.ctx_reentrant_const
    else
      let e_symb = get_symb_expr e in
      match e_symb with
      | Symb_z3 s -> s
      | Symb_reentrant _ -> ctx.ctx_reentrant_const
      | Symb_list _ -> ctx.ctx_dummy_const
      | Symb_abs -> ctx.ctx_dummy_const
      | Symb_none ->
        Message.error ~pos:(Expr.pos e)
          "Fields of structs that are not functions or context variables must \
           have a symbolic expression. This should not happen if the \
           evaluation of fields worked."
      | Symb_incomplete ->
        Message.error ~pos:(Expr.pos e)
          "Fields of structs cannot be incomplete" (* TODO INC *)
      | Symb_error _ ->
        Message.error ~pos:(Expr.pos e)
          "Fields of structs cannot be errors when making the symbolic \
           expression. This should not happen if errors were handled properly."
  in
  let domain = Z3.FuncDecl.get_domain constructor in
  let es_symb = List.map2 z3_of_expr es domain in
  Z3.Expr.mk_app ctx.ctx_z3 constructor es_symb

(* taken loosely from z3backend *)
let make_z3_struct_access
    ctx
    (name : StructName.t)
    (field : StructField.t)
    (struct_expr : SymbExpr.t)
    (field_expr : SymbExpr.t) : SymbExpr.t =
  match field_expr with
  | Symb_reentrant _ ->
    (* If the field is for a reentrant variable, we want the symbolic expression
       of the access to be the actual symbolic expression for the reentrant
       variable and not a Z3 struct access (which would return a dummy) *)
    field_expr
  | _ ->
    let sort = StructName.Map.find name ctx.ctx_z3structs in
    let fields = StructName.Map.find name ctx.ctx_decl.ctx_structs in
    let z3_accessors = List.hd (Z3.Datatype.get_accessors sort) in
    (*  Message.debug "struct accessors %s"
       (List.fold_left (fun acc a -> Z3.FuncDecl.to_string a ^ "," ^ acc) ""
       z3_accessors); *)
    let idx_mappings =
      combine_exact
        ("structure accessor " ^ Mark.remove (StructName.get_info name))
        (StructField.Map.keys fields) z3_accessors
    in
    let _, z3_accessor =
      List.find (fun (field1, _) -> StructField.equal field field1) idx_mappings
    in
    let range = Z3.FuncDecl.get_range z3_accessor in
    (* FIXME CONTEXT: is this ok? *)
    (* Same as the Symb_reentrant _ case of the match *)
    if range = ctx.ctx_reentrant_sort then field_expr
    else
      let access =
        SymbExpr.app_z3
          (fun s -> Z3.Expr.mk_app ctx.ctx_z3 z3_accessor [s])
          struct_expr
      in
      match access with
      | Symb_z3 e -> begin
        let key = Z3.Expr.to_string e in
        match Hashtbl.find_opt ctx.ctx_nested_lists key with
        | Some list ->
          Message.debug "Using nested symbolic list %s" key;
          let elts =
            match field_expr with
            | Symb_list concrete -> concrete.elts
            | _ -> list.elts
          in
          Symb_list { list with elts }
        | None -> begin match field_expr with
          | Symb_list _ -> field_expr
          | _ -> access
          end
        end
      | _ -> access

let make_z3_enum_inj
    ctx
    (name : EnumName.t)
    (cons : EnumConstructor.t)
    (enum_ty : typ)
    (s : s_expr) =
  let sort =
    match Mark.remove enum_ty with
    | TOption payload_ty ->
      (* Polymorphic standard-library helpers can leave a [TVar] on their
         internal [Present] injection even after the application itself has
         been instantiated.  The evaluated payload has the authoritative Z3
         sort in that case.  Using it prevents constructing, for example, an
         [Optional<t>] constructor and applying it to an encoded date [Int]. *)
      if EnumConstructor.equal cons ConstantNames.some_constr then
        snd (find_or_create_option_sort ctx (Z3.Expr.get_sort s))
      else snd (find_or_create_option ctx payload_ty)
    | _ -> EnumName.Map.find name ctx.ctx_z3enums
  in
  let constructors = EnumName.Map.find name ctx.ctx_decl.ctx_enums in
  let z3_constructors = Z3.Datatype.get_constructors sort in

  Message.debug "enum constructors: @[<hov>%a@]"
    (Format.pp_print_list
       ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ")
       (fun fmt c -> Format.pp_print_string fmt (Z3.FuncDecl.to_string c)))
    z3_constructors;
  (* NOTE assumption: they are in the right order *)
  (* TODO for all instances of this "mappings" pattern, maybe have more
     information in the context to avoid it *)
  let idx_mappings =
    combine_exact "enumeration constructor"
      (EnumConstructor.Map.keys constructors) z3_constructors
  in
  let _, z3_constructor =
    List.find (fun (cons1, _) -> EnumConstructor.equal cons cons1) idx_mappings
  in
  Z3.Expr.mk_app ctx.ctx_z3 z3_constructor [s]

let make_z3_enum_access
    ctx
    (name : EnumName.t)
    (cons : EnumConstructor.t)
    (s : s_expr) =
  let sort = Z3.Expr.get_sort s in
  let constructors = EnumName.Map.find name ctx.ctx_decl.ctx_enums in
  (* [get_accessors] returns a list containing the list of accessors for each
     constructor. In a Catala enum, each constructor has exactly (possibly
     [unit]) accessor, so we can safely [List.hd]. *)
  let z3_accessors = List.map List.hd (Z3.Datatype.get_accessors sort) in

  Message.debug "enum accessors: @[<hov>%a@]"
    (Format.pp_print_list
       ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ")
       (fun fmt c -> Format.pp_print_string fmt (Z3.FuncDecl.to_string c)))
    z3_accessors;
  let idx_mappings =
    combine_exact "enumeration accessor"
      (EnumConstructor.Map.keys constructors) z3_accessors
  in
  let _, z3_accessor =
    List.find (fun (cons1, _) -> EnumConstructor.equal cons cons1) idx_mappings
  in
  Z3.Expr.mk_app ctx.ctx_z3 z3_accessor [s]

(** Return the list of conditions corresponding to a pattern match on
    enumeration [name], where the arm that matches [s] is [cons]. The condition
    is [is!C s] when [C] is the [cons] arm, and [not (is!C s)] for any other
    arm. Additionaly, return along the condition whether it corresponds to
    [cons]. *)
let make_z3_arm_conditions
    ctx
    (name : EnumName.t)
    (cons : EnumConstructor.t)
    (s : SymbExpr.t) : (EnumConstructor.t * SymbExpr.t * bool) list =
  let sort =
    match s with
    | Symb_z3 e -> Z3.Expr.get_sort e
    | _ -> invalid_arg "[make_z3_arm_conditions] expected a Z3 expression"
  in
  let constructors = EnumName.Map.find name ctx.ctx_decl.ctx_enums in
  let z3_recognizers = Z3.Datatype.get_recognizers sort in
  let make_case_condition cstr_name z3_recognizer =
    let app =
      SymbExpr.applist_z3 (Z3.Expr.mk_app ctx.ctx_z3 z3_recognizer) [s]
    in
    let is_cons = EnumConstructor.equal cons cstr_name in
    let prefix = if is_cons then fun x -> x else Z3.Boolean.mk_not ctx.ctx_z3 in
    cstr_name, SymbExpr.app_z3 prefix app, is_cons
  in
  (* NOTE assumption: the lists are in the right order *)
  List.map2 make_case_condition
    (EnumConstructor.Map.keys constructors)
    z3_recognizers

let make_vars_args_map
    (vars : conc_naked_expr Bindlib.var array)
    (args : conc_expr list) : (conc_expr, conc_expr) Var.Map.t =
  let zipped = Array.combine vars (Array.of_list args) in
  Array.fold_left (fun acc (v, a) -> Var.Map.add v a acc) Var.Map.empty zipped

let replace_EVar_mark
    (vars_args : (conc_expr, conc_expr) Var.Map.t)
    (e : conc_expr) : conc_expr =
  match Mark.remove e with
  | EVar v -> (
    match Var.Map.find_opt v vars_args with
    | Some arg ->
      let symb_expr = get_symb_expr arg in
      (* Message.debug "EApp>binder put mark %a on
        var " SymbExpr.formatter symb_expr (* (Print.expr ()) e *);*)
      add_conc_info_e symb_expr ~constraints:[] e
    (* NOTE CONC we keep the position from the var, as in concrete
       interpreter *)
    | None -> e)
  | _ -> e

let propagate_generic_error
    (e : conc_result)
    (other_constraints : PathConstraint.naked_path)
    (f : conc_expr -> conc_result) : conc_result =
  let e_symb = get_symb_expr_r e in
  match Mark.remove e, e_symb with
  | EGenericError, Symb_error _ ->
    let e_constraints = get_constraints_r e in

    Message.debug "Propagating error %a" SymbExpr.formatter e_symb;
    let constraints = append_constraints e_constraints other_constraints in
    (* Add the new constraints but don't change the symbolic expression *)
    add_conc_info_e SymbExpr.none ~constraints e
  | _, Symb_error _ ->
    Message.error ~internal:true
      "A non-error case cannot have an error symbolic expression"
  | _, _ ->
    let e_noerror = del_genericerror e in
    (* NOTE LUNDI [del_genericerror] should not be too costly because [e] is
       supposed to be a value *)
    f e_noerror

(* TODO check order NOTE this evaluates [v1;v2;err;v4] to err(new_constraints @
   pc1 @ pc2) and ignores pc4 *)
let propagate_generic_error_list l other_constraints f =
  let rec aux acc constraints = function
    | [] -> f (List.rev acc)
    | e :: r ->
      propagate_generic_error e constraints
        (* FIXME this seems very slow *)
        (fun e ->
          aux (e :: acc)
            (append_constraints (get_constraints e) constraints) r)
  in
  aux [] other_constraints l

(* TODO QU RAPHAEL: these empty errors have been removed from the standard
   interpreter =>> OK *)
(* (\* NOTE We have to rewrite EmptyError propagation functions from
   [Concrete] *)
(* because they don't allow for [f] have a different input and output type
   *\) *)
(* let propagate_empty_error (e : conc_expr) (f : conc_expr -> conc_result) : *)
(*     conc_result = *)
(*   match e with (EEmptyError, _) as e -> e | _ -> f e *)

(* let propagate_empty_error_list *)
(*     (elist : conc_expr list) *)
(*     (f : conc_expr list -> conc_result) : conc_result = *)
(*   let rec aux acc = function *)
(*     | [] -> f (List.rev acc) *)
(*     | e :: r -> propagate_empty_error e (fun e -> aux (e :: acc) r) *)
(*   in *)
(*   aux [] elist *)

let handle_eq ctx pos e1 e2 =
  Runtime.Value.equal (Expr.pos_to_runtime pos) (Expr.embed_value ctx e1)
    (Expr.embed_value ctx e2)

let handle_compare ctx pos e1 e2 =
  Runtime.Value.compare (Expr.pos_to_runtime pos) (Expr.embed_value ctx e1)
    (Expr.embed_value ctx e2)

let op1
    ctx
    m
    (concrete_f : 'x -> conc_naked_result)
    (symbolic_f : Z3.context -> s_expr -> s_expr)
    x
    e : conc_result =
  let concrete = concrete_f x in
  let e = get_symb_expr e in
  let symb_expr = SymbExpr.app_z3 (symbolic_f ctx.ctx_z3) e in
  (* TODO handle errors *)
  add_conc_info_m m symb_expr ~constraints:[] concrete

let op2
    ctx
    m
    (concrete : conc_naked_result)
    (symbolic_f : Z3.context -> s_expr -> s_expr -> s_expr)
    e1
    e2 : conc_result =
  let e1 = get_symb_expr e1 in
  let e2 = get_symb_expr e2 in
  Message.debug "[op2] args %a, %a" SymbExpr.formatter_typed e1
    SymbExpr.formatter_typed e2;
  let symb_expr = SymbExpr.app2_z3 (symbolic_f ctx.ctx_z3) e1 e2 in
  (* TODO handle errors *)
  add_conc_info_m m symb_expr ~constraints:[] concrete

let op2list
    ctx
    m
    (concrete : conc_naked_result)
    (symbolic_f : Z3.context -> s_expr list -> s_expr)
    e1
    e2 : conc_result =
  let symbolic_f_curry ctx e1 e2 = symbolic_f ctx [e1; e2] in
  op2 ctx m concrete symbolic_f_curry e1 e2

let list_capacity ctx (list : SymbExpr.symb_list) =
  match Hashtbl.find_opt ctx.ctx_growable_lists list.id with
  | Some (canonical, _) -> List.length canonical.elts
  | None -> List.length list.elts

let request_list_growth ctx (growth : PathConstraint.list_growth) =
  match Hashtbl.find_opt ctx.ctx_growable_lists growth.list_id with
  | None -> false
  | Some (list, grow) ->
    let before = List.length list.elts in
    grow growth.next_capacity;
    List.length list.elts > before

let list_length_constraints ctx pos (list : SymbExpr.symb_list) =
  let simplified_len = Z3.Expr.simplify list.len None in
  let fixed_length =
    try
      ignore (Z3.Arithmetic.Integer.get_big_int simplified_len);
      true
    with Z3.Error _ | Invalid_argument _ -> false
  in
  let key = Z3.Expr.to_string simplified_len in
  if fixed_length || Hashtbl.mem ctx.ctx_lengths_demanded key then []
  else begin
  Hashtbl.add ctx.ctx_lengths_demanded key ();
  let int k = Z3.Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 k in
  let gt k =
    let longer = Z3.Arithmetic.mk_gt ctx.ctx_z3 list.len (int k) in
    match Hashtbl.find_opt ctx.ctx_list_length_guards list.id with
    | None -> longer
    | Some guard -> Z3.Boolean.mk_and ctx.ctx_z3 [guard; longer]
  in
  let continues =
    List.init (List.length list.elts) (fun k ->
        PathConstraint.mk_z3 (SymbExpr.mk_z3 (gt k)) pos true)
  in
  let concrete_length = List.length list.elts in
  let growth =
    let capacity = list_capacity ctx list in
    if concrete_length = capacity && capacity < ctx.ctx_max_list_length
       && Hashtbl.mem ctx.ctx_growable_lists list.id
    then Some PathConstraint.{ list_id = list.id; next_capacity = capacity + 1 }
    else None
  in
  let stop =
    PathConstraint.mk_z3 ?growth
      (SymbExpr.mk_z3
         (Z3.Boolean.mk_not ctx.ctx_z3 (gt concrete_length)))
      pos false
  in
  stop :: List.rev continues
  end

let concrete_symbolic_list ctx es =
  let len = Z3.Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 (List.length es) in
  match SymbExpr.mk_list len (List.map get_symb_expr es) with
  | Symb_list list -> list
  | _ -> assert false

let symbolic_list ctx e =
  match SymbExpr.as_list (get_symb_expr e) with
  | Some l -> l
  | None -> begin
    (* Lists created by concrete runtime helpers can retain the helper's
       [Symb_incomplete] marker even though the returned array and all its
       elements are available. Such a list has a fixed concrete length for
       this execution, but its elements may still be symbolic. *)
    match Mark.remove e with
    | EArray es -> concrete_symbolic_list ctx es
    | _ -> invalid_arg "[symbolic_list] expected a symbolic list"
    end

let handle_division
    ?zero
    ctx
    m
    (concrete_f : unit -> conc_naked_result)
    (symbolic_f : Z3.context -> s_expr -> s_expr -> s_expr)
    e1
    e2 : conc_result =
  let e1_symb = get_symb_expr e1 in
  let e2_symb = get_symb_expr e2 in
  Message.debug "[handle_div] args %a, %a" SymbExpr.formatter_typed e1_symb
    SymbExpr.formatter_typed e2_symb;

  let zero =
    Option.value zero
      ~default:
        (SymbExpr.mk_z3
           (Z3.Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 0))
  in
  let den_zero = SymbExpr.app2_z3 (Z3.Boolean.mk_eq ctx.ctx_z3) e2_symb zero in
  try
    let concrete = concrete_f () in
    let den_not_zero =
      SymbExpr.app_z3 (Z3.Boolean.mk_not ctx.ctx_z3) den_zero
    in
    let den_not_zero_pc =
      PathConstraint.mk_z3 den_not_zero (Expr.pos e2) false
    in
    let symb_expr = SymbExpr.app2_z3 (symbolic_f ctx.ctx_z3) e1_symb e2_symb in
    (* TODO handle errors *)
    (* A successful division adds one constraint : the denominator is not zero.
       The constraints from e1 and e2 are ignored here because those are fully
       evaluated expressions, and their constraints are handled by [EAppOp]. *)
    let constraints = [den_not_zero_pc] in
    add_conc_info_m m symb_expr ~constraints concrete
  with Runtime.(Error (DivisionByZero, _, _)) ->
    let den_zero_pc = PathConstraint.mk_z3 den_zero (Expr.pos e2) true in
    make_error_divisionbyzeroerror m [den_zero_pc]
      [
        Some "The division operator:", Expr.mark_pos m;
        Some "The null denominator:", Expr.pos e2;
      ]
      "division by zero at runtime"

let handle_date_duration
    ctx
    m
    round
    ~(subtract : bool)
    (concrete_f : unit -> conc_naked_result)
    date
    duration : conc_result =
  let date_symb = get_symb_expr date in
  let duration_symb = get_symb_expr duration in
  match date_symb, duration_symb with
  | Symb_z3 date_z3, Symb_z3 duration_z3 ->
    let duration_z3 =
      if subtract then DateEncoding.minus_dur ctx duration_z3 else duration_z3
    in
    let requires_rounding =
      DateEncoding.requires_rounding ctx date_z3 duration_z3
    in
    let valid = Z3.Boolean.mk_not ctx.ctx_z3 requires_rounding in
    let constraint_for successful =
      if round <> Dates_calc.AbortOnRound then []
      else
        [PathConstraint.mk_z3
           (SymbExpr.mk_z3 (if successful then valid else requires_rounding))
           (Expr.pos date) successful]
    in
    begin
      try
        let concrete = concrete_f () in
        let symbolic =
          DateEncoding.add_dat_dur ctx round date_z3 duration_z3
        in
        add_conc_info_m m (SymbExpr.mk_z3 symbolic)
          ~constraints:(constraint_for true) concrete
      with Runtime.(Error (DateError message, _, _)) ->
        make_error_external m (constraint_for false) message
    end
  | _ ->
    make_error_external m [PathConstraint.mk_z3 SymbExpr.incomplete
                              (Expr.pos date) false]
      "date arithmetic received an unmodeled symbolic value"

let handle_duration_relation
    ctx
    m
    pos
    symbolic_relation
    concrete_relation
    left
    right : conc_result =
  match get_symb_expr left, get_symb_expr right with
  | Symb_z3 left_z3, Symb_z3 right_z3 ->
    let valid, symbolic = symbolic_relation left_z3 right_z3 in
    let validity successful =
      let constraint_ =
        if successful then valid
        else Z3.Boolean.mk_not ctx.ctx_z3 valid
      in
      [PathConstraint.mk_z3 (SymbExpr.mk_z3 constraint_) pos successful]
    in
    begin
      try
        let concrete = ELit (LBool (concrete_relation ())) in
        add_conc_info_m m (SymbExpr.mk_z3 symbolic)
          ~constraints:(validity true) concrete
      with Runtime.(Error (DateError message, _, _)) ->
        make_error_external m (validity false) message
    end
  | _ ->
    make_error_external m
      [PathConstraint.mk_z3 SymbExpr.incomplete pos false]
      "duration comparison received an unmodeled symbolic value"

(* Call-by-value: the arguments are expected to be already evaluated here *)
let evaluate_operator
    evaluate_expr
    ctx
    ((op, opos) : < overloaded : no ; .. > operator Mark.pos)
    (m : conc_info mark)
    (args : conc_expr list) : conc_result =
  let pos = Expr.mark_pos m in
  let rpos () = Expr.pos_to_runtime opos in
  let div_pos () =
    (* Division by 0 errors point to their 2nd operand *)
    Expr.pos_to_runtime
    @@ match args with _ :: denom :: _ -> Expr.pos denom | _ -> opos
  in
  (* let protect f x y = *)
  (*   (\* TODO CONC For now, I crash on date ambiguities, because they should not *)
  (*      happen: any duration expressed with months or years is rejected early *)
  (*      on. *\) *)
  (*   let get_binop_args_pos = function *)
  (*     | (arg0 :: arg1 :: _ : ('t, 'm) gexpr list) -> *)
  (*       ["", Expr.pos arg0; "", Expr.pos arg1] *)
  (*     | _ -> assert false *)
  (*   in *)
  (*   try f (rpos ()) x y *)
  (*   with Runtime.(Error (UncomparableValues, _, _)) -> *)
  (*     Message.error ~extra_pos:(get_binop_args_pos args) *)
  (*       "Cannot compare together durations that cannot be converted to a \ *)
  (*        precise number of days" *)
  (* in *)
  let err () =
    Message.error
      ~extra_pos:
        ([
           ( Format.asprintf "Operator (value %a):"
               (Print.operator ~debug:true)
               op,
             pos );
         ]
        @ List.mapi
            (fun i arg ->
              ( Format.asprintf "Argument n°%d, value %a" (i + 1)
                  (Print.expr ()) arg,
                Expr.pos arg ))
            args)
      "Operator %a applied to the wrong@ arguments@ (should not happen if the \
       term was well-typed)"
      (Print.operator ~debug:true)
      op
  in
  let open Runtime.Oper in
  (* trick to have this function type correctly *)
  let z3_round _ = z3_round ctx in
  (* Mark.add m @@ *)
  match op, args with
  | Length, [((EArray es, _) as e)] ->
    let l = Runtime.integer_of_int (List.length es) in
    let list = symbolic_list ctx e in
    let constraints = list_length_constraints ctx (Expr.pos e) list in
    add_conc_info_m m (SymbExpr.mk_z3 list.len) ~constraints (ELit (LInt l))
  | ConstructorCheck (name, expected),
      [((EInj { cons; _ }, _) as enum_expr)] ->
    let concrete = EnumConstructor.equal expected cons in
    let symb =
      match get_symb_expr enum_expr with
      | Symb_z3 _ as enum_symb ->
        make_z3_arm_conditions ctx name expected enum_symb
        |> List.find (fun (_, _, is_expected) -> is_expected)
        |> fun (_, condition, _) -> condition
      | Symb_incomplete ->
        SymbExpr.mk_z3 (Z3.Boolean.mk_val ctx.ctx_z3 concrete)
      | _ ->
        invalid_arg "[ConstructorCheck] expected a symbolic enumeration"
    in
    add_conc_info_m m symb ~constraints:[] (ELit (LBool concrete))
  | Tag tag, [value] ->
    record_source_branch ctx tag value value;
    make_ok value
  | Tag _, _ -> err ()
  | (FromClosureEnv | ToClosureEnv), _ ->
    (* NOTE CONC used for typing only *)
    failwith "Eop From/ToClosureEnv should not appear in concolic evaluation"
  | Eq,
      [ ((ELit (LDuration _), _) as e1);
        ((ELit (LDuration _), _) as e2) ] ->
    handle_duration_relation ctx m opos
      (DateEncoding.duration_equality ctx)
      (fun () -> handle_eq ctx.ctx_decl opos e1 e2)
      e1 e2
  | Eq, [e1; e2] ->
    let concrete = ELit (LBool (handle_eq ctx.ctx_decl opos e1 e2)) in
    let s_e1 = get_symb_expr e1 in
    let s_e2 = get_symb_expr e2 in
    let symb_expr =
      match SymbExpr.as_list s_e1, SymbExpr.as_list s_e2 with
      | Some l1, Some l2 ->
        let equal a b = SymbExpr.app2_z3 (Z3.Boolean.mk_eq ctx.ctx_z3) a b in
        let element_equalities =
          if List.length l1.elts = List.length l2.elts then
            List.map2 equal l1.elts l2.elts
          else []
        in
        let length_equality =
          SymbExpr.mk_z3 (Z3.Boolean.mk_eq ctx.ctx_z3 l1.len l2.len)
        in
        SymbExpr.applist_z3 (Z3.Boolean.mk_and ctx.ctx_z3)
          (length_equality :: element_equalities)
      | None, None ->
        SymbExpr.app2_z3 (Z3.Boolean.mk_eq ctx.ctx_z3) s_e1 s_e2
      | _ -> invalid_arg "[Eq] cannot compare a list with a non-list"
    in
    (* TODO catch errors here, or maybe propagate [None]? *)
    add_conc_info_m m symb_expr ~constraints:[] concrete
  | Lt,
      [ ((ELit (LDuration _), _) as e1);
        ((ELit (LDuration _), _) as e2) ] ->
    handle_duration_relation ctx m opos
      (DateEncoding.duration_comparison ctx
         (Z3.Arithmetic.mk_lt ctx.ctx_z3))
      (fun () -> handle_compare ctx.ctx_decl opos e1 e2 < 0)
      e1 e2
  | Lt, [e1; e2] ->
    (* TODO CONC incompleteness warning for comparisons? eg on day < month *)
    let concrete = ELit (LBool (handle_compare ctx.ctx_decl opos e1 e2 < 0)) in
    op2 ctx m concrete Z3.Arithmetic.mk_lt e1 e2
  | Lte,
      [ ((ELit (LDuration _), _) as e1);
        ((ELit (LDuration _), _) as e2) ] ->
    handle_duration_relation ctx m opos
      (DateEncoding.duration_comparison ctx
         (Z3.Arithmetic.mk_le ctx.ctx_z3))
      (fun () -> handle_compare ctx.ctx_decl opos e1 e2 <= 0)
      e1 e2
  | Lte, [e1; e2] ->
    let concrete = ELit (LBool (handle_compare ctx.ctx_decl opos e1 e2 <= 0)) in
    op2 ctx m concrete Z3.Arithmetic.mk_le e1 e2
  | Gt,
      [ ((ELit (LDuration _), _) as e1);
        ((ELit (LDuration _), _) as e2) ] ->
    handle_duration_relation ctx m opos
      (DateEncoding.duration_comparison ctx
         (Z3.Arithmetic.mk_gt ctx.ctx_z3))
      (fun () -> handle_compare ctx.ctx_decl opos e1 e2 > 0)
      e1 e2
  | Gt, [e1; e2] ->
    let concrete = ELit (LBool (handle_compare ctx.ctx_decl opos e1 e2 > 0)) in
    op2 ctx m concrete Z3.Arithmetic.mk_gt e1 e2
  | Gte,
      [ ((ELit (LDuration _), _) as e1);
        ((ELit (LDuration _), _) as e2) ] ->
    handle_duration_relation ctx m opos
      (DateEncoding.duration_comparison ctx
         (Z3.Arithmetic.mk_ge ctx.ctx_z3))
      (fun () -> handle_compare ctx.ctx_decl opos e1 e2 >= 0)
      e1 e2
  | Gte, [e1; e2] ->
    let concrete = ELit (LBool (handle_compare ctx.ctx_decl opos e1 e2 >= 0)) in
    op2 ctx m concrete Z3.Arithmetic.mk_ge e1 e2
  | Map, [f; ((EArray es, _) as list_expr)] ->
    let results =
      List.map
           (fun e' ->
             evaluate_expr
               (Mark.copy e'
                  (EApp { f; args = [e']; tys = [Expr.maybe_ty (Mark.get e')] })))
           es
    in
    propagate_generic_error_list results [] @@ fun results ->
    let list = symbolic_list ctx list_expr in
    let symb =
      SymbExpr.Symb_list
        { list with elts = List.map get_symb_expr results }
    in
    let constraints =
      append_constraints (gather_constraints results)
        (list_length_constraints ctx pos list)
    in
    add_conc_info_m m symb ~constraints (EArray results) |> make_ok
  | Map2, [f; ((EArray es1, _) as list1); ((EArray es2, _) as list2)] ->
    let results =
      List.map2
           (fun e1 e2 ->
             evaluate_expr
               (Mark.add m
                  (EApp
                     {
                       f;
                       args = [e1; e2];
                       tys =
                         [
                           Expr.maybe_ty (Mark.get e1);
                           Expr.maybe_ty (Mark.get e2);
                         ];
                     })))
           es1 es2
    in
    propagate_generic_error_list results [] @@ fun results ->
    let sl1 = symbolic_list ctx list1 and sl2 = symbolic_list ctx list2 in
    let len = Z3.Boolean.mk_ite ctx.ctx_z3
        (Z3.Arithmetic.mk_le ctx.ctx_z3 sl1.len sl2.len) sl1.len sl2.len in
    let symb = SymbExpr.mk_list len (List.map get_symb_expr results) in
    let constraints =
      concat_constraints
        [ gather_constraints results;
          list_length_constraints ctx pos sl2;
          list_length_constraints ctx pos sl1 ]
    in
    add_conc_info_m m symb ~constraints (EArray results) |> make_ok
  | Reduce, [_; ((EArray [], list_mark) as list_expr)] ->
    let list = symbolic_list ctx list_expr in
    let unit_ty = TLit TUnit, pos in
    let payload_mark =
      map_conc_mark
        ~symb_expr_f:(fun _ -> SymbExpr.mk_z3 (snd ctx.ctx_z3unit))
        ~constraints_f:(fun _ -> [])
        ~ty_f:(fun _ -> Some unit_ty)
        list_mark
    in
    let payload = Mark.add payload_mark (ELit LUnit) in
    let option =
      Mark.add m
        (EInj
           { name = ConstantNames.option_enum;
             cons = ConstantNames.none_constr;
             e = payload })
    in
    propagate_generic_error (evaluate_expr option)
      (list_length_constraints ctx pos list) make_ok
  | Reduce, [f; ((EArray (x0 :: xn), _) as list_expr)] ->
    let result =
      List.fold_left
           (fun acc x ->
             propagate_generic_error acc []
             @@ fun acc ->
             evaluate_expr
               (Mark.copy f
                  (EApp
                     {
                       f;
                       args = [acc; x];
                       tys =
                         [
                           Expr.maybe_ty (Mark.get acc);
                           Expr.maybe_ty (Mark.get x);
                         ];
                     })))
           (make_ok x0) xn
    in
    let list = symbolic_list ctx list_expr in
    propagate_generic_error result (list_length_constraints ctx pos list)
    @@ fun payload ->
    let option =
      Mark.add m
        (EInj
           { name = ConstantNames.option_enum;
             cons = ConstantNames.some_constr;
             e = payload })
    in
    evaluate_expr option
  | Concat, [((EArray es1, _) as e1); ((EArray es2, _) as e2)] ->
    let concrete = EArray (es1 @ es2) in
    let l1 = symbolic_list ctx e1 and l2 = symbolic_list ctx e2 in
    let len = Z3.Arithmetic.mk_add ctx.ctx_z3 [l1.len; l2.len] in
    let symb = SymbExpr.mk_list len (l1.elts @ l2.elts) in
    let constraints =
      append_constraints (list_length_constraints ctx pos l2)
        (list_length_constraints ctx pos l1)
    in
    add_conc_info_m m symb ~constraints concrete |> make_ok
  | Filter, [f; ((EArray es, _) as list_expr)] ->
    let results =
      List.map
        (fun e' ->
          evaluate_expr
            (Mark.copy e'
               (EApp { f; args = [e']; tys = [Expr.maybe_ty (Mark.get e')] })))
        es
    in
    propagate_generic_error_list results [] @@ fun results ->
    let step (kept, pcs) e' result =
      let q = get_symb_expr result in
      let own = get_constraints result in
      match Mark.remove result with
      | ELit (LBool true) ->
        ( e' :: kept,
          PathConstraint.mk_z3 (SymbExpr.simplify q) (Expr.pos e') true
          :: append_constraints own pcs )
      | ELit (LBool false) ->
        let nq = SymbExpr.app_z3 (Z3.Boolean.mk_not ctx.ctx_z3) q |> SymbExpr.simplify in
        kept, PathConstraint.mk_z3 nq (Expr.pos e') false
              :: append_constraints own pcs
      | _ -> Message.error ~pos:(Expr.pos (List.hd args))
          "List filter predicate did not evaluate to a boolean"
    in
    let kept, constraints = List.fold_left2 step ([], []) es results in
    let kept = List.rev kept in
    let list = symbolic_list ctx list_expr in
    let len = Z3.Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 (List.length kept) in
    let symb = SymbExpr.mk_list len (List.map get_symb_expr kept) in
    add_conc_info_m m symb
      ~constraints:
        (append_constraints constraints (list_length_constraints ctx pos list))
      (EArray kept) |> make_ok
  | Fold, [f; init; ((EArray es, _) as list_expr)] ->
    let result =
      List.fold_left
           (fun acc e' ->
             propagate_generic_error acc []
             @@ fun acc ->
             evaluate_expr
               (Mark.copy e'
                  (EApp
                     {
                       f;
                       args = [acc; e'];
                       tys =
                         [
                           Expr.maybe_ty (Mark.get acc);
                           Expr.maybe_ty (Mark.get e');
                         ];
                     })))
           (make_ok init) es
    in
    let list = symbolic_list ctx list_expr in
    add_conc_info_m m (get_symb_expr_r result)
      ~constraints:
        (append_constraints (get_constraints_r result)
           (list_length_constraints ctx pos list))
      (Mark.remove result)
  | Find, [f; ((EArray es, _) as list_expr)] ->
    let list = symbolic_list ctx list_expr in
    let rec find constraints = function
      | [] ->
        let unit =
          add_conc_info_m m (symb_of_lit ctx LUnit) ~constraints:[] (ELit LUnit)
        in
        add_conc_info_m m Symb_incomplete
          ~constraints:
            (append_constraints constraints
               (list_length_constraints ctx pos list))
          (EInj
             {
               name = ConstantNames.option_enum;
               cons = ConstantNames.none_constr;
               e = unit;
             })
        |> make_ok
      | element :: rest ->
        let predicate =
          evaluate_expr
            (Mark.copy element
               (EApp
                  {
                    f;
                    args = [element];
                    tys = [Expr.maybe_ty (Mark.get element)];
                  }))
        in
        propagate_generic_error predicate constraints @@ fun predicate ->
        let q = get_symb_expr predicate |> SymbExpr.simplify in
        let own = get_constraints predicate in
        begin match Mark.remove predicate with
        | ELit (LBool true) ->
          let pc = PathConstraint.mk_z3 q (Expr.pos element) true in
          add_conc_info_m m Symb_incomplete
            ~constraints:
              (pc
              :: concat_constraints
                   [ own; constraints; list_length_constraints ctx pos list ])
            (EInj
               {
                 name = ConstantNames.option_enum;
                 cons = ConstantNames.some_constr;
                 e = element;
               })
          |> make_ok
        | ELit (LBool false) ->
          let nq =
            SymbExpr.app_z3 (Z3.Boolean.mk_not ctx.ctx_z3) q
            |> SymbExpr.simplify
          in
          let pc = PathConstraint.mk_z3 nq (Expr.pos element) false in
          find (pc :: append_constraints own constraints) rest
        | _ ->
          Message.error ~pos:(Expr.pos f)
            "List find predicate did not evaluate to a boolean"
        end
    in
    find [] es
  | Sort _, _ :: _ -> failwith "sort evaluation not implemented yet"
  | ArrayAccess i, [((EArray es, _) as list_expr)] ->
    let element = List.nth es i in
    let list = symbolic_list ctx list_expr in
    let symb = List.nth list.elts i in
    add_conc_info_m m symb
      ~constraints:(list_length_constraints ctx pos list)
      (Mark.remove element) |> make_ok
  | ( ( Length | Eq | Map | Map2 | Concat | Filter | Fold | Reduce | Find
      | Sort _ | ArrayAccess _ ),
      _ ) ->
    err ()
  | Not, [((ELit (LBool b), _) as e)] ->
    op1 ctx m (fun x -> ELit (LBool (o_not x))) Z3.Boolean.mk_not b e
  | And, [((ELit (LBool b1), _) as e1); ((ELit (LBool b2), _) as e2)] ->
    op2list ctx m (ELit (LBool (o_and b1 b2))) Z3.Boolean.mk_and e1 e2
  | Or, [((ELit (LBool b1), _) as e1); ((ELit (LBool b2), _) as e2)] ->
    op2list ctx m (ELit (LBool (o_or b1 b2))) Z3.Boolean.mk_or e1 e2
  | Xor, [((ELit (LBool b1), _) as e1); ((ELit (LBool b2), _) as e2)] ->
    op2 ctx m (ELit (LBool (o_xor b1 b2))) Z3.Boolean.mk_xor e1 e2
  | (Not | And | Or | Xor), _ -> err ()
  | Minus_int, [((ELit (LInt x), _) as e)] ->
    op1 ctx m
      (fun x -> ELit (LInt (o_minus_int x)))
      Z3.Arithmetic.mk_unary_minus x e
  | Minus_rat, [((ELit (LRat x), _) as e)] ->
    op1 ctx m
      (fun x -> ELit (LRat (o_minus_rat x)))
      Z3.Arithmetic.mk_unary_minus x e
  | Minus_mon, [((ELit (LMoney x), _) as e)] ->
    op1 ctx m
      (fun x -> ELit (LMoney (o_minus_mon x)))
      Z3.Arithmetic.mk_unary_minus x e
    (* TODO CONC maybe abstract this symbolic operation? like s_minus_mon and
       s_minus_int... *)
  | Minus_dur, [((ELit (LDuration x), _) as e)] ->
    op1 ctx m
      (fun x -> ELit (LDuration (o_minus_dur x)))
      (fun _ x -> DateEncoding.minus_dur ctx x) x e
  | ToInt_mon, [(ELit (LMoney _x), _)] ->
    failwith "ToInt_mon not implemented yet"
  | ToInt_rat, [((ELit (LRat x), _) as e)] ->
    op1 ctx m (fun x -> ELit (LInt (o_toint_rat x))) z3_trunc_to_int x e
  | ToRat_int, [((ELit (LInt i), _) as e)] ->
    (* TODO maybe write specific tests for this and other similar cases? *)
    op1 ctx m (fun x -> ELit (LRat (o_torat_int x))) z3_force_real i e
  | ToRat_mon, [((ELit (LMoney i), _) as e)] ->
    op1 ctx m
      (fun x -> ELit (LRat (o_torat_mon x)))
      (fun ctx e ->
        (* Money is encoded as integer cents. Coerce it before division:
           Z3's division of two Int terms is integer division (and rounds
           negative values down), whereas Catala converts cents to the exact
           rational number of currency units. *)
        let e = z3_force_real ctx e in
        let hundred = Z3.Arithmetic.Integer.mk_numeral_i ctx 100 in
        Z3.Arithmetic.mk_div ctx e hundred)
      i e
  | ToMoney_rat, [((ELit (LRat i), _) as e)] ->
    (* TODO be careful with this, [Round_mon], [Round_rat], [Mult_mon_rat],
       [Div_mon_rat] because of rounding *)
    op1 ctx m
      (fun x -> ELit (LMoney (o_tomoney_rat x)))
      (fun ctx e ->
        let cents =
          Z3.Arithmetic.mk_mul ctx [e; Z3.Arithmetic.Real.mk_numeral_i ctx 100]
        in
        z3_round ctx cents)
      i e
  | ToMoney_int, [((ELit (LInt i), _) as e)] ->
    op1 ctx m
      (fun x -> ELit (LMoney (o_tomoney_int x)))
      (fun ctx e ->
        let cents =
          Z3.Arithmetic.mk_mul ctx [e; Z3.Arithmetic.Real.mk_numeral_i ctx 100]
        in
        z3_round ctx cents)
      i e
  | Round_mon, [((ELit (LMoney mon), _) as e)] ->
    op1 ctx m
      (fun mon -> ELit (LMoney (o_round_mon mon)))
      (fun ctx e ->
        (* careful here: use multiplication by 1/100 instead of division by 100
           to prevent [units] from being an integer (rounded down automatically
           by Z3) *)
        let units =
          Z3.Arithmetic.mk_mul ctx
            [e; Z3.Arithmetic.Real.mk_numeral_nd ctx 1 100]
        in
        let units_round = z3_round ctx units in
        Z3.Arithmetic.mk_mul ctx
          [units_round; Z3.Arithmetic.Integer.mk_numeral_i ctx 100])
      mon e
  | Round_rat, [((ELit (LRat q), _) as e)] ->
    op1 ctx m
      (fun q -> ELit (LRat (o_round_rat q)))
      (fun ctx e -> z3_round ctx e)
      q e
  | Add_int_int, [((ELit (LInt x), _) as e1); ((ELit (LInt y), _) as e2)] ->
    op2list ctx m (ELit (LInt (o_add_int_int x y))) Z3.Arithmetic.mk_add e1 e2
  | Add_rat_rat, [((ELit (LRat x), _) as e1); ((ELit (LRat y), _) as e2)] ->
    op2list ctx m (ELit (LRat (o_add_rat_rat x y))) Z3.Arithmetic.mk_add e1 e2
  | Add_mon_mon, [((ELit (LMoney x), _) as e1); ((ELit (LMoney y), _) as e2)] ->
    op2list ctx m (ELit (LMoney (o_add_mon_mon x y))) Z3.Arithmetic.mk_add e1 e2
  | ( Add_dat_dur r,
      [((ELit (LDate x), _) as e1); ((ELit (LDuration y), _) as e2)] ) ->
    handle_date_duration ctx m r ~subtract:false
      (fun () -> ELit (LDate (o_add_dat_dur r (rpos ()) x y))) e1 e2
  | ( Add_dur_dur,
      [((ELit (LDuration x), _) as e1); ((ELit (LDuration y), _) as e2)] ) ->
    op2 ctx m
      (ELit (LDuration (o_add_dur_dur x y)))
      (fun _ a b -> DateEncoding.add_dur_dur ctx a b) e1 e2
  | Sub_int_int, [((ELit (LInt x), _) as e1); ((ELit (LInt y), _) as e2)] ->
    op2list ctx m (ELit (LInt (o_sub_int_int x y))) Z3.Arithmetic.mk_sub e1 e2
  | Sub_rat_rat, [((ELit (LRat x), _) as e1); ((ELit (LRat y), _) as e2)] ->
    op2list ctx m (ELit (LRat (o_sub_rat_rat x y))) Z3.Arithmetic.mk_sub e1 e2
  | Sub_mon_mon, [((ELit (LMoney x), _) as e1); ((ELit (LMoney y), _) as e2)] ->
    op2list ctx m (ELit (LMoney (o_sub_mon_mon x y))) Z3.Arithmetic.mk_sub e1 e2
  | Sub_dat_dat, [((ELit (LDate x), _) as e1); ((ELit (LDate y), _) as e2)] ->
    op2 ctx m
      (ELit (LDuration (o_sub_dat_dat x y)))
      (fun _ a b -> DateEncoding.sub_dat_dat ctx a b) e1 e2
  | ( Sub_dat_dur r,
      [((ELit (LDate x), _) as e1); ((ELit (LDuration y), _) as e2)] ) ->
    handle_date_duration ctx m r ~subtract:true
      (fun () -> ELit (LDate (o_sub_dat_dur r (rpos ()) x y))) e1 e2
  | ( Sub_dur_dur,
      [((ELit (LDuration x), _) as e1); ((ELit (LDuration y), _) as e2)] ) ->
    op2 ctx m
      (ELit (LDuration (o_sub_dur_dur x y)))
      (fun _ a b -> DateEncoding.sub_dur_dur ctx a b) e1 e2
  | Mult_int_int, [((ELit (LInt x), _) as e1); ((ELit (LInt y), _) as e2)] ->
    op2list ctx m (ELit (LInt (o_mult_int_int x y))) Z3.Arithmetic.mk_mul e1 e2
  | Mult_rat_rat, [((ELit (LRat x), _) as e1); ((ELit (LRat y), _) as e2)] ->
    op2list ctx m (ELit (LRat (o_mult_rat_rat x y))) Z3.Arithmetic.mk_mul e1 e2
  | Mult_mon_rat, [((ELit (LMoney x), _) as e1); ((ELit (LRat y), _) as e2)] ->
    op2 ctx m
      (ELit (LMoney (o_mult_mon_rat x y)))
      (fun ctx cents r ->
        let product = Z3.Arithmetic.mk_mul ctx [cents; r] in
        z3_round ctx product)
      e1 e2
  | Mult_mon_int, [((ELit (LMoney x), _) as e1); ((ELit (LInt y), _) as e2)] ->
    op2 ctx m
      (ELit (LMoney (o_mult_mon_int x y)))
      (fun ctx cents r ->
        let product = Z3.Arithmetic.mk_mul ctx [cents; r] in
        z3_round ctx product)
      e1 e2
  | Mult_dur_int, [((ELit (LDuration x), _) as e1); ((ELit (LInt y), _) as e2)]
    ->
    op2 ctx m
      (ELit (LDuration (o_mult_dur_int x y)))
      (fun _ duration factor -> DateEncoding.mult_dur_int ctx duration factor)
      e1 e2
  | Div_int_int, [((ELit (LInt x), _) as e1); ((ELit (LInt y), _) as e2)] ->
    handle_division ctx m
      (fun () -> ELit (LRat (o_div_int_int (div_pos ()) x y)))
      (fun ctx e1 e2 ->
        (* convert e1 to a [Real] explicitely to avoid using integer division *)
        let e1_rat = z3_force_real ctx e1 in
        Z3.Arithmetic.mk_div ctx e1_rat e2)
      e1 e2
  | Div_rat_rat, [((ELit (LRat x), _) as e1); ((ELit (LRat y), _) as e2)] ->
    handle_division ctx m
      (fun () -> ELit (LRat (o_div_rat_rat (div_pos ()) x y)))
      (* Z3.Arithmetic.mk_div x y e1 e2 *)
      (fun ctx e1 e2 ->
        (* convert e1 to a [Real] explicitely to avoid using integer division *)
        let e1_rat = z3_force_real ctx e1 in
        Z3.Arithmetic.mk_div ctx e1_rat e2)
      e1 e2
  | Div_mon_mon, [((ELit (LMoney x), _) as e1); ((ELit (LMoney y), _) as e2)] ->
    handle_division ctx m
      (fun () -> ELit (LRat (o_div_mon_mon (div_pos ()) x y)))
      (fun ctx e1 e2 ->
        (* TODO factorize with [Div_int_int]? *)
        (* convert e1 to a [Real] explicitely to avoid using integer division *)
        let e1_rat = z3_force_real ctx e1 in
        Z3.Arithmetic.mk_div ctx e1_rat e2)
      e1 e2
  | Div_mon_rat, [((ELit (LMoney x), _) as e1); ((ELit (LRat y), _) as e2)] ->
    handle_division ctx m
      (fun () -> ELit (LMoney (o_div_mon_rat (div_pos ()) x y)))
      (fun ctx cents r ->
        (* TODO maybe factorize with [Mult_mon_rat] and [ToRat_int]? *)
        let cents_rat = z3_force_real ctx cents in
        let div = Z3.Arithmetic.mk_div ctx cents_rat r in
        z3_round ctx div)
      e1 e2
  | Div_mon_int, [((ELit (LMoney x), _) as e1); ((ELit (LInt y), _) as e2)] ->
    handle_division ctx m
      (fun () -> ELit (LMoney (o_div_mon_int (div_pos ()) x y)))
      (fun ctx cents r ->
        (* TODO maybe factorize with [Mult_mon_rat] and [ToRat_int]? *)
        let cents_rat = z3_force_real ctx cents in
        let div = Z3.Arithmetic.mk_div ctx cents_rat r in
        z3_round ctx div)
      e1 e2
  (* TODO with careful rounding *)
  | ( Div_dur_dur,
      [((ELit (LDuration x), _) as e1); ((ELit (LDuration y), _) as e2)] ) ->
    let zero_duration =
      DateEncoding.make_duration ctx (DateEncoding.int ctx 0)
        (DateEncoding.int ctx 0) (DateEncoding.int ctx 0)
      |> SymbExpr.mk_z3
    in
    handle_division ~zero:zero_duration ctx m
      (fun () -> ELit (LRat (o_div_dur_dur (div_pos ()) x y)))
      (fun _ a b -> DateEncoding.div_dur_dur ctx a b) e1 e2
  | HandleExceptions, [(EArray _exps, _)] ->
    failwith "HandleExceptions not implemented yet"
  | ConstructorCheck _, _ -> failwith "ConstructorCheck not implemented yet"
  | DebugPrint _, _ -> failwith "DebugPrint not implemented yet"
  | ValueFromJson _, _ -> failwith "ValueFromJson not implemented yet"
  (* ( let valid_exceptions = ListLabels.filter exps ~f:(function | EInj { name;
     cons; _ }, _ when EnumName.equal name Expr.option_enum ->
     EnumConstructor.equal cons Expr.some_constr | _ -> err ()) in match
     valid_exceptions with | [] -> EInj { name = Expr.option_enum; cons =
     Expr.none_constr; e = ELit LUnit, m } | [((EInj { cons; name; _ } as e),
     _)] when EnumName.equal name Expr.option_enum && EnumConstructor.equal cons
     Expr.some_constr -> e | [_] -> err () | excs -> raise Runtime.( Error
     (Conflict, List.map Expr.(fun e -> pos_to_runtime (pos e)) excs)) ) *)
  | ( ( Minus_int | Minus_rat | Minus_mon | Minus_dur | ToInt_mon | ToInt_rat
      | ToRat_int | ToRat_mon | ToMoney_int | ToMoney_rat | Round_rat
      | Round_mon | Add_int_int | Add_rat_rat | Add_mon_mon | Add_dat_dur _
      | Add_dur_dur | Sub_int_int | Sub_rat_rat | Sub_mon_mon | Sub_dat_dat
      | Sub_dat_dur _ | Sub_dur_dur | Mult_int_int | Mult_rat_rat | Mult_mon_rat
      | Mult_mon_int | Mult_dur_int | Div_int_int | Div_rat_rat | Div_mon_mon
      | Div_mon_rat | Div_mon_int | Div_dur_dur | HandleExceptions | Lt | Gt
      | Lte | Gte ),
      _ ) ->
    err ()

let z3_of_symb = function SymbExpr.Symb_z3 e -> Some e | _ -> None

(** [List_internal.sequence start stop] returns [start, ..., stop - 1]. *)
let eval_external_sequence ctx pos args concrete : conc_result =
  match args, Mark.remove concrete with
  | [start; stop], EArray elements -> begin
    match z3_of_symb (get_symb_expr start), z3_of_symb (get_symb_expr stop) with
    | Some start_z3, Some stop_z3 ->
      let zero = Z3.Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 0 in
      let positive = Z3.Arithmetic.mk_gt ctx.ctx_z3 stop_z3 start_z3 in
      let difference = Z3.Arithmetic.mk_sub ctx.ctx_z3 [stop_z3; start_z3] in
      let len =
        Z3.Boolean.mk_ite ctx.ctx_z3 positive difference zero
      in
      let maximum =
        Z3.Arithmetic.Integer.mk_numeral_i ctx.ctx_z3
          ctx.ctx_max_list_length
      in
      let elements =
        List.mapi
          (fun i element ->
            let offset = Z3.Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 i in
            let symbol =
              Z3.Arithmetic.mk_add ctx.ctx_z3 [start_z3; offset]
              |> SymbExpr.mk_z3
            in
            replace_conc_info_e symbol ~constraints:[] element)
          elements
      in
      let symb = SymbExpr.mk_list len (List.map get_symb_expr elements) in
      begin match symb with
      | Symb_list list ->
        Hashtbl.replace ctx.ctx_list_length_guards list.id
          (Z3.Arithmetic.mk_le ctx.ctx_z3 len maximum)
      | _ -> assert false
      end;
      let constraints =
        if List.length elements <= ctx.ctx_max_list_length then []
        else [PathConstraint.mk_z3 SymbExpr.incomplete pos true]
      in
      replace_conc_info_e symb ~constraints
        (EArray elements, Mark.get concrete)
      |> make_ok
    | _ ->
      replace_conc_info_e SymbExpr.incomplete
        ~constraints:[PathConstraint.mk_z3 SymbExpr.incomplete pos true]
        concrete
      |> make_ok
    end
  | _ ->
    Message.error ~pos
      "Unexpected arguments or result for List_internal.sequence"

(** Exact path condition and payload provenance for the primitive underlying
    both [List.nth_element] and [List.first_element]. When its elements have Z3
    representations, the optional result contains a bounded symbolic selector.
    Otherwise an explicit validity constraint is retained and the option is
    conservatively marked incomplete. *)
let eval_external_nth_element ctx pos args concrete : conc_result =
  match args, Mark.remove concrete with
  | [((EArray elements, _) as list_expr); index],
    EInj { name; cons; e = concrete_payload } -> begin
    match SymbExpr.as_list (get_symb_expr list_expr),
          z3_of_symb (get_symb_expr index), Mark.remove index with
    | Some list, Some index_z3, ELit (LInt concrete_index) ->
      let int n = Z3.Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 n in
      let valid =
        Z3.Boolean.mk_and ctx.ctx_z3
          [ Z3.Arithmetic.mk_ge ctx.ctx_z3 index_z3 (int 1);
            Z3.Arithmetic.mk_le ctx.ctx_z3 index_z3 list.len ]
      in
      let present =
        EnumConstructor.equal cons ConstantNames.some_constr
      in
      let decision =
        if present then valid else Z3.Boolean.mk_not ctx.ctx_z3 valid
      in
      let concrete_payload =
        if present then
          let i = Z.to_int concrete_index - 1 in
          if i < 0 || i >= List.length elements then
            Message.error ~pos
              "List_internal.nth_element returned Present outside its list"
          else List.nth elements i
        else concrete_payload
      in
      let element_symbols =
        List.filter_map (fun e -> z3_of_symb (get_symb_expr e)) elements
      in
      if element_symbols <> []
         && List.length element_symbols = List.length elements
      then begin
        let selected =
          List.mapi (fun i symbol -> i + 1, symbol) element_symbols
          |> List.fold_left
               (fun selected (i, symbol) ->
                 let at_i =
                   Z3.Boolean.mk_eq ctx.ctx_z3 index_z3 (int i)
                 in
                 Z3.Boolean.mk_ite ctx.ctx_z3 at_i symbol selected)
               (List.hd element_symbols)
        in
        let payload =
          if present then
            replace_conc_info_e (SymbExpr.mk_z3 selected) ~constraints:[]
              concrete_payload
          else concrete_payload
        in
        let enum_ty = Option.get (get_type concrete) in
        let present_value =
          make_z3_enum_inj ctx name ConstantNames.some_constr enum_ty selected
        in
        let absent_value =
          let option_sort = Z3.Expr.get_sort present_value in
          let absent_constructor =
            List.hd (Z3.Datatype.get_constructors option_sort)
          in
          Z3.Expr.mk_app ctx.ctx_z3 absent_constructor [z3_of_lit ctx LUnit]
        in
        let option_value =
          Z3.Boolean.mk_ite ctx.ctx_z3 valid present_value absent_value
          |> SymbExpr.mk_z3
        in
        replace_conc_info_e option_value
          ~constraints:(list_length_constraints ctx pos list)
          (EInj { name; cons; e = payload }, Mark.get concrete)
        |> make_ok
      end
      else
        let decision_pc =
          PathConstraint.mk_z3
            (SymbExpr.mk_z3 decision |> SymbExpr.simplify) pos present
        in
        replace_conc_info_e SymbExpr.incomplete
          ~constraints:(decision_pc :: list_length_constraints ctx pos list)
          (EInj { name; cons; e = concrete_payload }, Mark.get concrete)
        |> make_ok
    | _ ->
      replace_conc_info_e SymbExpr.incomplete
        ~constraints:[PathConstraint.mk_z3 SymbExpr.incomplete pos true]
        concrete
      |> make_ok
    end
  | _ ->
    Message.error ~pos
      "Unexpected arguments or result for List_internal.nth_element"

(** Symbolic semantics of [List_internal.remove_nth_element]. Catala indexes
    lists from one.  The concrete execution fixes whether the index is valid;
    within that path the output slots remain symbolic [ite] selectors so Z3
    may choose any valid index without losing element provenance. *)
let eval_external_remove_nth_element ctx pos args concrete : conc_result =
  match args, Mark.remove concrete with
  | [((EArray _, _) as list_expr); index], EArray concrete_elements -> begin
    match SymbExpr.as_list (get_symb_expr list_expr),
          z3_of_symb (get_symb_expr index) with
    | Some list, Some index_z3 ->
      let int n = Z3.Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 n in
      let valid =
        Z3.Boolean.mk_and ctx.ctx_z3
          [ Z3.Arithmetic.mk_ge ctx.ctx_z3 index_z3 (int 1);
            Z3.Arithmetic.mk_le ctx.ctx_z3 index_z3 list.len ]
      in
      let removed = List.length concrete_elements < List.length list.elts in
      let path_condition =
        if removed then valid else Z3.Boolean.mk_not ctx.ctx_z3 valid
      in
      let output_symbols =
        if removed then
          List.mapi
            (fun j before ->
              let after = List.nth list.elts (j + 1) in
              match z3_of_symb before, z3_of_symb after with
              | Some before, Some after ->
                SymbExpr.mk_z3
                  (Z3.Boolean.mk_ite ctx.ctx_z3
                     (Z3.Arithmetic.mk_le ctx.ctx_z3 index_z3 (int (j + 1)))
                     after before)
              | _ -> SymbExpr.incomplete)
            (List.rev (List.tl (List.rev list.elts)))
        else list.elts
      in
      let concrete_elements =
        List.map2
          (fun element symbol ->
            replace_conc_info_e symbol ~constraints:[] element)
          concrete_elements output_symbols
      in
      let output_len =
        Z3.Boolean.mk_ite ctx.ctx_z3 valid
          (Z3.Arithmetic.mk_sub ctx.ctx_z3 [list.len; int 1]) list.len
      in
      let output = SymbExpr.mk_list output_len output_symbols in
      let constraints =
        PathConstraint.mk_z3 (SymbExpr.mk_z3 path_condition) pos removed
        :: list_length_constraints ctx pos list
      in
      replace_conc_info_e output ~constraints
        (EArray concrete_elements, Mark.get concrete)
      |> make_ok
    | _ ->
      Message.error ~pos
        "List_internal.remove_nth_element received an unmodeled symbolic value"
    end
  | _ ->
    Message.error ~pos
      "Unexpected arguments or result for List_internal.remove_nth_element"

let eval_external_reverse ctx pos args concrete : conc_result =
  match args, Mark.remove concrete with
  | [((EArray _, _) as list_expr)], EArray concrete_elements -> begin
    match SymbExpr.as_list (get_symb_expr list_expr) with
    | Some list ->
      let output_symbols = List.rev list.elts in
      let concrete_elements =
        List.map2
          (fun element symbol ->
            replace_conc_info_e symbol ~constraints:[] element)
          concrete_elements output_symbols
      in
      replace_conc_info_e
        (SymbExpr.mk_list list.len output_symbols)
        ~constraints:(list_length_constraints ctx pos list)
        (EArray concrete_elements, Mark.get concrete)
      |> make_ok
    | None ->
      Message.error ~pos
        "List_internal.reverse received an unmodeled symbolic value"
    end
  | _ ->
    Message.error ~pos "Unexpected arguments or result for List_internal.reverse"

let symbolic_integer mark concrete symbolic =
  replace_conc_info_e (SymbExpr.mk_z3 symbolic) ~constraints:[]
    (ELit (LInt (Z.of_int concrete)), mark)

let eval_external_first_element ctx pos args concrete : conc_result =
  match args with
  | [list_expr] ->
    let one = DateEncoding.int ctx 1 in
    eval_external_nth_element ctx pos
      [list_expr; symbolic_integer (Mark.get list_expr) 1 one]
      concrete
  | _ -> Message.error ~pos "List.first_element expected one list"

let eval_external_last_element ctx pos args concrete : conc_result =
  match args with
  | [((EArray elements, _) as list_expr)] -> begin
    match SymbExpr.as_list (get_symb_expr list_expr) with
    | Some list ->
      let index =
        symbolic_integer (Mark.get list_expr) (List.length elements) list.len
      in
      eval_external_nth_element ctx pos [list_expr; index] concrete
    | None ->
      replace_conc_info_e SymbExpr.incomplete
        ~constraints:[PathConstraint.mk_z3 SymbExpr.incomplete pos true]
        concrete
      |> make_ok
    end
  | _ -> Message.error ~pos "List.last_element expected one list"

let eval_external_remove_first_element ctx pos args concrete : conc_result =
  match args with
  | [list_expr] ->
    let one = DateEncoding.int ctx 1 in
    eval_external_remove_nth_element ctx pos
      [list_expr; symbolic_integer (Mark.get list_expr) 1 one]
      concrete
  | _ -> Message.error ~pos "List.remove_first_element expected one list"

let eval_external_remove_last_element ctx pos args concrete : conc_result =
  match args with
  | [((EArray elements, _) as list_expr)] -> begin
    match SymbExpr.as_list (get_symb_expr list_expr) with
    | Some list ->
      let index =
        symbolic_integer (Mark.get list_expr) (List.length elements) list.len
      in
      eval_external_remove_nth_element ctx pos [list_expr; index] concrete
    | None ->
      replace_conc_info_e SymbExpr.incomplete
        ~constraints:[PathConstraint.mk_z3 SymbExpr.incomplete pos true]
        concrete
      |> make_ok
    end
  | _ -> Message.error ~pos "List.remove_last_element expected one list"

let z3_abs_int ctx x =
  let zero = Z3.Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 0 in
  Z3.Boolean.mk_ite ctx.ctx_z3 (Z3.Arithmetic.mk_ge ctx.ctx_z3 x zero) x
    (Z3.Arithmetic.mk_unary_minus ctx.ctx_z3 x)

let z3_pow10 ctx n =
  Z3.Expr.mk_app ctx.ctx_z3 ctx.ctx_z3pow10 [z3_abs_int ctx n]

let z3_int_to_real ctx x = Z3.Arithmetic.Integer.mk_int2real ctx.ctx_z3 x

let eval_external_decimal_round ctx pos args concrete : conc_result =
  match args, Mark.remove concrete with
  | [value; precision], ELit (LRat result) -> begin
    match z3_of_symb (get_symb_expr value),
          z3_of_symb (get_symb_expr precision) with
    | Some value, Some precision ->
      let zero = Z3.Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 0 in
      let pow = z3_pow10 ctx precision |> z3_int_to_real ctx in
      let positive = Z3.Arithmetic.mk_gt ctx.ctx_z3 precision zero in
      let negative = Z3.Arithmetic.mk_lt ctx.ctx_z3 precision zero in
      let scaled =
        Z3.Boolean.mk_ite ctx.ctx_z3 positive
          (Z3.Arithmetic.mk_mul ctx.ctx_z3 [value; pow])
          (Z3.Boolean.mk_ite ctx.ctx_z3 negative
             (Z3.Arithmetic.mk_div ctx.ctx_z3 value pow) value)
      in
      let rounded = z3_round ctx scaled |> z3_int_to_real ctx in
      let symbolic =
        Z3.Boolean.mk_ite ctx.ctx_z3 positive
          (Z3.Arithmetic.mk_div ctx.ctx_z3 rounded pow)
          (Z3.Boolean.mk_ite ctx.ctx_z3 negative
             (Z3.Arithmetic.mk_mul ctx.ctx_z3 [rounded; pow]) rounded)
      in
      replace_conc_info_e (SymbExpr.mk_z3 symbolic) ~constraints:[]
        (ELit (LRat result), Mark.get concrete)
      |> make_ok
    | _ ->
      Message.error ~pos
        "Decimal_internal.round_to_decimal received an unmodeled symbolic value"
    end
  | _ ->
    Message.error ~pos
      "Unexpected arguments or result for Decimal_internal.round_to_decimal"

let eval_external_money_round ctx pos args concrete : conc_result =
  match args, Mark.remove concrete with
  | [value; precision], ELit (LMoney result) -> begin
    match z3_of_symb (get_symb_expr value),
          z3_of_symb (get_symb_expr precision) with
    | Some value, Some precision ->
      let int n = Z3.Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 n in
      let round_money cents =
        let units =
          Z3.Arithmetic.mk_div ctx.ctx_z3 (z3_int_to_real ctx cents)
            (Z3.Arithmetic.Real.mk_numeral_i ctx.ctx_z3 100)
        in
        Z3.Arithmetic.mk_mul ctx.ctx_z3 [z3_round ctx units; int 100]
      in
      let at_one =
        let tenths =
          Z3.Arithmetic.mk_div ctx.ctx_z3 (z3_int_to_real ctx value)
            (Z3.Arithmetic.Real.mk_numeral_i ctx.ctx_z3 10)
        in
        Z3.Arithmetic.mk_mul ctx.ctx_z3 [z3_round ctx tenths; int 10]
      in
      let pow = z3_pow10 ctx precision in
      let divided =
        Z3.Arithmetic.mk_div ctx.ctx_z3 (z3_int_to_real ctx value)
          (z3_int_to_real ctx pow)
        |> z3_trunc_to_int ctx.ctx_z3
      in
      let at_nonpositive =
        Z3.Arithmetic.mk_mul ctx.ctx_z3 [round_money divided; pow]
      in
      let symbolic =
        Z3.Boolean.mk_ite ctx.ctx_z3
          (Z3.Arithmetic.mk_ge ctx.ctx_z3 precision (int 2)) value
          (Z3.Boolean.mk_ite ctx.ctx_z3
             (Z3.Boolean.mk_eq ctx.ctx_z3 precision (int 1))
             at_one at_nonpositive)
      in
      replace_conc_info_e (SymbExpr.mk_z3 symbolic) ~constraints:[]
        (ELit (LMoney result), Mark.get concrete)
      |> make_ok
    | _ ->
      Message.error ~pos
        "Money_internal.round_to_decimal received an unmodeled symbolic value"
    end
  | _ ->
    Message.error ~pos
      "Unexpected arguments or result for Money_internal.round_to_decimal"

let eval_external_date_of_ymd ctx pos args concrete : conc_result =
  match args, Mark.remove concrete with
  | [_position; year; month; day], ELit (LDate result) -> begin
    match z3_of_symb (get_symb_expr year), z3_of_symb (get_symb_expr month),
          z3_of_symb (get_symb_expr day) with
    | Some year, Some month, Some day ->
      let valid = DateEncoding.valid_ymd ctx year month day in
      let symbolic = DateEncoding.civil_to_date ctx year month day in
      replace_conc_info_e (SymbExpr.mk_z3 symbolic)
        ~constraints:[PathConstraint.mk_z3 (SymbExpr.mk_z3 valid) pos true]
        (ELit (LDate result), Mark.get concrete)
      |> make_ok
    | _ ->
      Message.error ~pos
        "Date_internal.of_ymd received an unmodeled symbolic value"
    end
  | _ ->
    Message.error ~pos "Unexpected arguments or result for Date_internal.of_ymd"

let eval_external_date_of_ymd_error ctx pos mark args message : conc_result =
  match args with
  | [_position; year; month; day] -> begin
    match z3_of_symb (get_symb_expr year), z3_of_symb (get_symb_expr month),
          z3_of_symb (get_symb_expr day) with
    | Some year, Some month, Some day ->
      let invalid =
        Z3.Boolean.mk_not ctx.ctx_z3
          (DateEncoding.valid_ymd ctx year month day)
      in
      make_error_external mark
        [PathConstraint.mk_z3 (SymbExpr.mk_z3 invalid) pos false] message
    | _ -> make_error_external mark [PathConstraint.mk_z3 SymbExpr.incomplete pos false] message
    end
  | _ -> make_error_external mark [] message

let eval_external_date_of_ymd_direct ctx pos mark args : conc_result =
  match args with
  | [_position; (ELit (LInt year), _); (ELit (LInt month), _);
      (ELit (LInt day), _)] ->
    let yi, mi, di = Z.to_int year, Z.to_int month, Z.to_int day in
    begin
      try
        let result = Dates_calc.make_date ~year:yi ~month:mi ~day:di in
        eval_external_date_of_ymd ctx pos args (ELit (LDate result), mark)
      with Dates_calc.InvalidDate ->
        eval_external_date_of_ymd_error ctx pos mark args
          (Printf.sprintf "|%04d-%02d-%02d| is not a valid date" yi mi di)
    end
  | _ -> Message.error ~pos "Date_internal.of_ymd expected integer arguments"

let eval_external_date_to_ymd ctx pos args concrete : conc_result =
  match args, Mark.remove concrete with
  | [date], ETuple [year; month; day] -> begin
    match z3_of_symb (get_symb_expr date) with
    | Some date ->
      let sy, sm, sd = DateEncoding.date_to_civil ctx date in
      let mark symbol value =
        replace_conc_info_e (SymbExpr.mk_z3 symbol) ~constraints:[] value
      in
      replace_conc_info_e SymbExpr.none ~constraints:[]
        (ETuple [mark sy year; mark sm month; mark sd day], Mark.get concrete)
      |> make_ok
    | None ->
      Message.error ~pos
        "Date_internal.to_ymd received an unmodeled symbolic value"
    end
  | _ ->
    Message.error ~pos "Unexpected arguments or result for Date_internal.to_ymd"

let eval_external_date_component component ctx pos args concrete : conc_result =
  match args, Mark.remove concrete with
  | [date], ELit (LInt result) -> begin
    match z3_of_symb (get_symb_expr date) with
    | Some date ->
      let year, month, day = DateEncoding.date_to_civil ctx date in
      let symbolic =
        match component with
        | 0 -> year
        | 1 -> month
        | 2 -> day
        | _ -> invalid_arg "[eval_external_date_component] invalid component"
      in
      replace_conc_info_e (SymbExpr.mk_z3 symbolic) ~constraints:[]
        (ELit (LInt result), Mark.get concrete)
      |> make_ok
    | None ->
      Message.error ~pos
        "A date component accessor received an unmodeled symbolic value"
    end
  | _ -> Message.error ~pos "Unexpected arguments for a date component accessor"

let eval_external_date_last_day ctx pos args concrete : conc_result =
  match args, Mark.remove concrete with
  | [date], ELit (LDate result) -> begin
    match z3_of_symb (get_symb_expr date) with
    | Some date ->
      let year, month, _ = DateEncoding.date_to_civil ctx date in
      let day = DateEncoding.days_in_month ctx year month in
      let symbolic = DateEncoding.civil_to_date ctx year month day in
      replace_conc_info_e (SymbExpr.mk_z3 symbolic) ~constraints:[]
        (ELit (LDate result), Mark.get concrete)
      |> make_ok
    | None ->
      Message.error ~pos
        "Date_internal.last_day_of_month received an unmodeled symbolic value"
    end
  | _ ->
    Message.error ~pos
      "Unexpected arguments or result for Date_internal.last_day_of_month"

let eval_external_date_add round ctx pos args concrete : conc_result =
  match args, Mark.remove concrete with
  | [date; duration], ELit (LDate result) -> begin
    match z3_of_symb (get_symb_expr date),
          z3_of_symb (get_symb_expr duration) with
    | Some date, Some duration ->
      let symbolic = DateEncoding.add_dat_dur ctx round date duration in
      replace_conc_info_e (SymbExpr.mk_z3 symbolic) ~constraints:[]
        (ELit (LDate result), Mark.get concrete)
      |> make_ok
    | _ ->
      Message.error ~pos
        "Date_internal date addition received an unmodeled symbolic value"
    end
  | _ ->
    Message.error ~pos "Unexpected arguments or result for Date_internal.add"

let eval_external_date_sub round ctx pos args concrete : conc_result =
  match args, Mark.remove concrete with
  | [date; duration], ELit (LDate result) -> begin
    match z3_of_symb (get_symb_expr date),
          z3_of_symb (get_symb_expr duration) with
    | Some date, Some duration ->
      let duration = DateEncoding.minus_dur ctx duration in
      let symbolic = DateEncoding.add_dat_dur ctx round date duration in
      replace_conc_info_e (SymbExpr.mk_z3 symbolic) ~constraints:[]
        (ELit (LDate result), Mark.get concrete)
      |> make_ok
    | _ ->
      Message.error ~pos
        "Date subtraction received an unmodeled symbolic value"
    end
  | _ -> Message.error ~pos "Unexpected arguments or result for date subtraction"

let find_named_struct_field names fields =
  StructField.Map.bindings fields
  |> List.find_map (fun (field, value) ->
       let name = Mark.remove (StructField.get_info field) in
       if List.exists (String.equal name) names then Some value else None)

let period_dates expression =
  match Mark.remove expression with
  | ETuple [start; stop] -> start, stop
  | EStruct { fields; _ } ->
    let start =
      find_named_struct_field ["begin"; "début"] fields |> Option.get
    in
    let stop = find_named_struct_field ["end"; "fin"] fields |> Option.get in
    start, stop
  | _ -> invalid_arg "[period_dates] expected a pair or period structure"

let period_entry_dates expression =
  match Mark.remove expression with
  | ETuple [period; _payload] -> period_dates period
  | _ -> invalid_arg "[period_entry_dates] expected ((date,date), value)"

let concrete_date expression =
  match Mark.remove expression with
  | ELit (LDate date) -> date
  | _ -> invalid_arg "[concrete_date] expected a date"

let eval_external_period_sort ctx pos args _concrete : conc_result =
  match args with
  | [((EArray entries, list_mark) as list_expr)] -> begin
    match SymbExpr.as_list (get_symb_expr list_expr) with
    | Some list ->
      let sorted =
        List.stable_sort
          (fun a b ->
            let a, _ = period_entry_dates a and b, _ = period_entry_dates b in
            Dates_calc.compare_dates (concrete_date a) (concrete_date b))
          entries
      in
      let starts =
        List.map
          (fun entry ->
            let start, _ = period_entry_dates entry in
            Option.get (z3_of_symb (get_symb_expr start)))
          entries
      in
      let concrete_starts =
        List.map
          (fun entry ->
            let start, _ = period_entry_dates entry in concrete_date start)
          entries
      in
      let pairwise =
        List.concat
          (List.mapi
             (fun i a ->
               List.filter_map
                 (fun (j, b) ->
                   if j <= i then None
                   else
                     let branch =
                       Dates_calc.compare_dates (List.nth concrete_starts i)
                         (List.nth concrete_starts j) <= 0
                     in
                     let condition = Z3.Arithmetic.mk_le ctx.ctx_z3 a b in
                     let condition =
                       if branch then condition
                       else Z3.Boolean.mk_not ctx.ctx_z3 condition
                     in
                     Some
                       (PathConstraint.mk_z3 (SymbExpr.mk_z3 condition) pos branch))
                 (List.mapi (fun j b -> j, b) starts))
             starts)
      in
      let symbolic = SymbExpr.mk_list list.len (List.map get_symb_expr sorted) in
      replace_conc_info_e symbolic
        ~constraints:
          (append_constraints pairwise (list_length_constraints ctx pos list))
        (EArray sorted, list_mark)
      |> make_ok
    | None ->
      Message.error ~pos "Period_internal.sort_ expected a symbolic list"
    end
  | _ -> Message.error ~pos "Unexpected arguments for Period_internal.sort_"

let first_day_of_month ctx date =
  let year, month, _ = DateEncoding.date_to_civil ctx date in
  DateEncoding.civil_to_date ctx year month (DateEncoding.int ctx 1)

let add_calendar ctx date years months =
  DateEncoding.add_dat_dur ctx Dates_calc.RoundDown date
    (DateEncoding.make_duration ctx years months (DateEncoding.int ctx 0))

let mark_period start_symbol stop_symbol concrete =
  match Mark.remove concrete with
  | ETuple [start; stop] ->
    let start =
      replace_conc_info_e (SymbExpr.mk_z3 start_symbol) ~constraints:[] start
    in
    let stop =
      replace_conc_info_e (SymbExpr.mk_z3 stop_symbol) ~constraints:[] stop
    in
    replace_conc_info_e SymbExpr.none ~constraints:[]
      (ETuple [start; stop], Mark.get concrete)
  | EStruct { fields; name } ->
    let fields =
      StructField.Map.mapi
        (fun field value ->
          let field_name = Mark.remove (StructField.get_info field) in
          if List.mem field_name ["begin"; "début"] then
            replace_conc_info_e (SymbExpr.mk_z3 start_symbol) ~constraints:[] value
          else if List.mem field_name ["end"; "fin"] then
            replace_conc_info_e (SymbExpr.mk_z3 stop_symbol) ~constraints:[] value
          else value)
        fields
    in
    replace_conc_info_e SymbExpr.none ~constraints:[]
      (EStruct { fields; name }, Mark.get concrete)
  | _ -> invalid_arg "[mark_period] expected a pair or period structure"

let finish_period_split ctx pos stop starts concrete : conc_result =
  match Mark.remove concrete with
  | EArray concrete_periods ->
    if List.length concrete_periods > ctx.ctx_max_list_length then
      Message.error ~pos
        "Period split produced %d elements, above --conc-max-list-length=%d"
        (List.length concrete_periods) ctx.ctx_max_list_length;
    let exists s = Z3.Arithmetic.mk_lt ctx.ctx_z3 s stop in
    let int n = DateEncoding.int ctx n in
    let symbolic_len =
      List.fold_left
        (fun total s ->
          Z3.Arithmetic.mk_add ctx.ctx_z3
            [total; Z3.Boolean.mk_ite ctx.ctx_z3 (exists s) (int 1) (int 0)])
        (int 0) starts
    in
    let concrete_periods =
      List.mapi
        (fun i period ->
          let period_start = List.nth starts i in
          let next = List.nth starts (i + 1) in
          let period_stop =
            Z3.Boolean.mk_ite ctx.ctx_z3
              (Z3.Arithmetic.mk_lt ctx.ctx_z3 next stop)
              (Z3.Arithmetic.mk_sub ctx.ctx_z3 [next; int 1]) stop
          in
          mark_period period_start period_stop period)
        concrete_periods
    in
    let n = List.length concrete_periods in
    let constraints =
      List.mapi
        (fun i s ->
          PathConstraint.mk_z3
            (SymbExpr.mk_z3
               (if i < n then exists s
                else Z3.Boolean.mk_not ctx.ctx_z3 (exists s)))
            pos (i < n))
        (List.filteri (fun i _ -> i <= n) starts)
    in
    replace_conc_info_e
      (SymbExpr.mk_list symbolic_len (List.map get_symb_expr concrete_periods))
      ~constraints
      (EArray concrete_periods, Mark.get concrete)
    |> make_ok
  | _ -> Message.error ~pos "Period split did not return a list"

let eval_external_period_split_month ctx pos args concrete : conc_result =
  match args with
  | [period] ->
    let start, stop = period_dates period in
    let start = Option.get (z3_of_symb (get_symb_expr start)) in
    let stop = Option.get (z3_of_symb (get_symb_expr stop)) in
    let first = first_day_of_month ctx start in
    let starts =
      start
      :: List.init ctx.ctx_max_list_length (fun i ->
             add_calendar ctx first (DateEncoding.int ctx 0)
               (DateEncoding.int ctx (i + 1)))
    in
    finish_period_split ctx pos stop starts concrete
  | _ ->
    Message.error ~pos "Unexpected arguments for Period_internal.split_by_month"

let eval_external_period_split_year ctx pos args concrete : conc_result =
  match args with
  | [start_month; period] ->
    let start, stop = period_dates period in
    let start = Option.get (z3_of_symb (get_symb_expr start)) in
    let stop = Option.get (z3_of_symb (get_symb_expr stop)) in
    let start_month = Option.get (z3_of_symb (get_symb_expr start_month)) in
    let year, month, _ = DateEncoding.date_to_civil ctx start in
    let rolling_year =
      Z3.Boolean.mk_ite ctx.ctx_z3
        (Z3.Arithmetic.mk_lt ctx.ctx_z3 month start_month)
        (Z3.Arithmetic.mk_sub ctx.ctx_z3 [year; DateEncoding.int ctx 1]) year
    in
    let first =
      DateEncoding.civil_to_date ctx rolling_year start_month
        (DateEncoding.int ctx 1)
    in
    let starts =
      start
      :: List.init ctx.ctx_max_list_length (fun i ->
             add_calendar ctx first (DateEncoding.int ctx (i + 1))
               (DateEncoding.int ctx 0))
    in
    let valid_month =
      Z3.Boolean.mk_and ctx.ctx_z3
        [ Z3.Arithmetic.mk_ge ctx.ctx_z3 start_month (DateEncoding.int ctx 1);
          Z3.Arithmetic.mk_le ctx.ctx_z3 start_month (DateEncoding.int ctx 12) ]
    in
    let result = finish_period_split ctx pos stop starts concrete in
    propagate_generic_error result
      [PathConstraint.mk_z3 (SymbExpr.mk_z3 valid_month) pos true] make_ok
  | _ ->
    Message.error ~pos "Unexpected arguments for Period_internal.split_by_year"

let month_number = function
  | "January" | "Janvier" -> 1
  | "February" | "Février" -> 2
  | "March" | "Mars" -> 3
  | "April" | "Avril" -> 4
  | "May" | "Mai" -> 5
  | "June" | "Juin" -> 6
  | "July" | "Juillet" -> 7
  | "August" | "Août" -> 8
  | "September" | "Septembre" -> 9
  | "October" | "Octobre" -> 10
  | "November" | "Novembre" -> 11
  | "December" | "Décembre" -> 12
  | name -> invalid_arg ("[month_number] unknown month constructor " ^ name)

let eval_external_public_period_split_year ctx pos args concrete : conc_result =
  match args with
  | [start_month; period] -> begin
    match Mark.remove start_month with
    | EInj { cons; _ } ->
      (* The public API accepts its Month enumeration, while the primitive
         accepts an integer. Preserve that concrete choice as an integer; the
         period endpoints remain fully symbolic. *)
      let month = month_number (EnumConstructor.to_string cons) in
      let month_expr =
        replace_conc_info_e
          (SymbExpr.mk_z3 (DateEncoding.int ctx month)) ~constraints:[]
          (ELit (LInt (Z.of_int month)), Mark.get start_month)
      in
      eval_external_period_split_year ctx pos [month_expr; period] concrete
    | _ -> Message.error ~pos "Period.split_by_year expected a month"
    end
  | _ -> Message.error ~pos "Unexpected arguments for Period.split_by_year"

type external_handler =
  context -> Pos.t -> conc_expr list -> conc_expr -> conc_result

let external_handlers : (string * string * external_handler) list =
  [ "List_internal", "sequence", eval_external_sequence;
    "List_internal", "nth_element", eval_external_nth_element;
    ( "List_internal", "remove_nth_element",
      eval_external_remove_nth_element );
    "List_internal", "reverse", eval_external_reverse;
    ( "Decimal_internal", "round_to_decimal",
      eval_external_decimal_round );
    "Money_internal", "round_to_decimal", eval_external_money_round;
    "Date_internal", "of_ymd", eval_external_date_of_ymd;
    "Date_internal", "to_ymd", eval_external_date_to_ymd;
    ( "Date_internal", "last_day_of_month",
      eval_external_date_last_day );
    ( "Date_internal", "add_rounded_down",
      eval_external_date_add Dates_calc.RoundDown );
    ( "Date_internal", "add_rounded_up",
      eval_external_date_add Dates_calc.RoundUp );
    "Period_internal", "sort_", eval_external_period_sort;
    ( "Period_internal", "split_by_month",
      eval_external_period_split_month );
    "Period_internal", "split_by_year", eval_external_period_split_year;
    (* Imported Catala modules are represented as runtime externals too. Keep
       the public standard-library wrappers connected to the same symbolic
       implementations instead of degrading them to concrete-only calls. *)
    "List_en", "sequence", eval_external_sequence;
    "List_en", "nth_element", eval_external_nth_element;
    "List_en", "first_element", eval_external_first_element;
    "List_en", "last_element", eval_external_last_element;
    "List_en", "remove_nth_element", eval_external_remove_nth_element;
    "List_en", "remove_first_element", eval_external_remove_first_element;
    "List_en", "remove_last_element", eval_external_remove_last_element;
    "List_en", "reverse", eval_external_reverse;
    "List_fr", "séquence", eval_external_sequence;
    "List_fr", "nième_élément", eval_external_nth_element;
    "List_fr", "premier_élément", eval_external_first_element;
    "List_fr", "dernier_élément", eval_external_last_element;
    "List_fr", "retire_nième_élément", eval_external_remove_nth_element;
    "List_fr", "retire_premier_élément", eval_external_remove_first_element;
    "List_fr", "retire_dernier_élément", eval_external_remove_last_element;
    "List_fr", "inverse", eval_external_reverse;
    "Decimal_en", "round_to_decimal", eval_external_decimal_round;
    "Decimal_fr", "arrondi_à_la_décimale", eval_external_decimal_round;
    "Money_en", "round_to_decimal", eval_external_money_round;
    "Money_fr", "arrondi_à_la_décimale", eval_external_money_round;
    "Period_en", "sort_by_date", eval_external_period_sort;
    "Period_en", "split_by_month", eval_external_period_split_month;
    ( "Period_en", "split_by_year",
      eval_external_public_period_split_year );
    "Period_fr", "tri_par_date", eval_external_period_sort;
    "Period_fr", "divise_par_mois", eval_external_period_split_month;
    ( "Period_fr", "divise_par_année",
      eval_external_public_period_split_year );
    "Date_en", "of_year_month_day", eval_external_date_of_ymd;
    "Date_en", "to_year_month_day", eval_external_date_to_ymd;
    "Date_en", "get_year", eval_external_date_component 0;
    "Date_en", "get_month", eval_external_date_component 1;
    "Date_en", "get_day", eval_external_date_component 2;
    "Date_en", "last_day_of_month", eval_external_date_last_day;
    ( "Date_en", "add_round_down",
      eval_external_date_add Dates_calc.RoundDown );
    ( "Date_en", "add_round_up",
      eval_external_date_add Dates_calc.RoundUp );
    ( "Date_en", "sub_round_down",
      eval_external_date_sub Dates_calc.RoundDown );
    ( "Date_en", "sub_round_up",
      eval_external_date_sub Dates_calc.RoundUp );
    "Date_fr", "depuis_année_mois_jour", eval_external_date_of_ymd;
    "Date_fr", "vers_année_mois_jour", eval_external_date_to_ymd;
    "Date_fr", "accès_année", eval_external_date_component 0;
    "Date_fr", "accès_mois", eval_external_date_component 1;
    "Date_fr", "accès_jour", eval_external_date_component 2;
    "Date_fr", "dernier_jour_du_mois", eval_external_date_last_day;
    ( "Date_fr", "ajout_arrondi_inférieur",
      eval_external_date_add Dates_calc.RoundDown );
    ( "Date_fr", "ajout_arrondi_supérieur",
      eval_external_date_add Dates_calc.RoundUp );
    ( "Date_fr", "soustraction_arrondi_inférieur",
      eval_external_date_sub Dates_calc.RoundDown );
    ( "Date_fr", "soustraction_arrondi_supérieur",
      eval_external_date_sub Dates_calc.RoundUp ) ]

let find_external_handler ctx obj =
  let qualified_name =
    List.find_map
      (fun (registered, runtime_module, name) ->
        if registered == obj then Some (runtime_module, name) else None)
      !(ctx.ctx_external_names)
  in
  Option.bind qualified_name @@ fun (runtime_module, name) ->
  List.find_map
    (fun (candidate_module, candidate_name, handler) ->
      if String.equal candidate_module runtime_module
         && String.equal candidate_name name
      then Some (runtime_module, name, handler)
      else None)
    external_handlers

let external_runtime_name name =
  let path =
    match Mark.remove name with
    | External_value td -> TopdefName.path td
    | External_scope scope -> ScopeName.path scope
  in
  ( ModuleName.to_string (Option.get (Uid.Path.last_member path)),
    match Mark.remove name with
    | External_value td -> TopdefName.base td
    | External_scope scope -> ScopeName.base scope )

let rec evaluate_expr :
    context -> Global.backend_lang -> conc_expr -> conc_result =
 fun ctx lang e ->
  !(ctx.ctx_on_expr) e;
  Message.debug "@[<v 0>eval %a@,symbolic: %a@]" (Print.expr ()) e
    SymbExpr.formatter (get_symb_expr e);
  (*  Message.debug "eval symbolic: %a"
     SymbExpr.formatter (get_symb_expr e); *)
  let m = Mark.get e in
  let pos = Expr.mark_pos m in
  let ret =
    match Mark.remove e with
    | EVar _ ->
      Message.error ~pos
        "free variable found at evaluation (should not happen if term was \
         well-typed)"
    | EExternal { name } ->
      let concrete = Concrete.evaluate_expr ctx.ctx_decl lang e in
      begin match Mark.remove concrete with
      | ECustom { obj; _ } ->
        let runtime_module, function_name = external_runtime_name name in
        ctx.ctx_external_names :=
          (obj, runtime_module, function_name) :: !(ctx.ctx_external_names)
      | _ -> ()
      end;
      add_conc_info_e Symb_incomplete concrete |> make_ok
    | EApp { f = e1; args; _ } -> (
      Message.debug "... it's an EApp";
      let e1 = evaluate_expr ctx lang e1 in
      Message.debug "EApp f evaluated";
      propagate_generic_error e1 []
      @@ fun e1 ->
      let f_constraints = get_constraints e1 in
      let args = List.map (evaluate_expr ctx lang) args in
      Message.debug "EApp args evaluated";
      propagate_generic_error_list args f_constraints
      @@ fun args ->
      let args_constraints = gather_constraints args in
      match Mark.remove e1 with
      | EAbs { binder; _ } ->
        (* TODO make this discussion into a doc? should constraints from the
           args be added, or should we trust the call to return them? We could
           take both for safety but there will be duplication... I think we
           should trust the recursive call, and we'll see if it's better not to
           =>> actually it's better not to : it can lead to duplication, and the
           subexpression does not need the constraints anyway =>> see the big
           concatenation below *)
        (* The arguments passed to [Bindlib.msubst] are unmarked. To circumvent
           this, I change the corresponding marks in the receiving expression,
           ie the expression in which substitution happens: 1/ unbind 2/ change
           marks 3/ rebind 4/ substitute concrete expressions normally *)
        if Bindlib.mbinder_arity binder = List.length args then (
          let vars, eb = Bindlib.unmbind binder in
          let vars_args_map = make_vars_args_map vars args in

          Message.debug "EApp>EAbs vars are %a"
            (Format.pp_print_list Print.var_debug)
            (Array.to_list vars);
          Message.debug "EApp>EAbs args are";
          List.iter
            (fun arg ->
              Message.debug "EApp>EAbs arg | %a | %i"
                (* (Print.expr ()) arg *) SymbExpr.formatter (get_symb_expr arg)
                (List.length (get_constraints arg)))
            args;
          let marked_eb =
            Expr.map_top_down ~f:(replace_EVar_mark vars_args_map) eb
          in

          Message.debug "EApp>EAbs vars replaced in box";
          let marked_binder = Bindlib.unbox (Expr.bind vars marked_eb) in

          Message.debug "EApp>EAbs binder reconstructed";
          let result =
            evaluate_expr ctx lang
              (Bindlib.msubst marked_binder
                 (Array.of_list (List.map Mark.remove args)))
          in

          Message.debug "EApp>EAbs substituted binder evaluated";
          (* TODO [Expr.subst]? *)
          propagate_generic_error result
            (append_constraints args_constraints f_constraints)
          @@ fun result ->
          let r_symb = get_symb_expr result in

          Message.debug
            "EApp>EAbs extracted symbolic expression from result: %a"
            SymbExpr.formatter r_symb;
          let r_constraints = get_constraints result in
          (* the constraints generated by the evaluation of the application are:
           * - those generated by the evaluation of the function
           * - those generated by the evaluation of the arguments
           * - the NEW ones generated by the evaluation of the subexpression
           *   (where the ones of the arguments are neither passed down, nor
           *   re-generated as this is cbv)
           *)
          let constraints =
            concat_constraints [r_constraints; args_constraints; f_constraints]
          in
          add_conc_info_e r_symb ~constraints result |> make_ok
          (* NOTE that here the position comes from [result], while in other
             cases of this function the position comes from the input
             expression. This is the behaviour of the concrete interpreter *))
        else
          Message.error ~pos
            "wrong function call, expected %d arguments, got %d"
            (Bindlib.mbinder_arity binder)
            (List.length args)
      | ECustom { obj; _ } ->
        begin match find_external_handler ctx obj with
        | Some (runtime_module, function_name, handler) ->
          if
            (String.equal runtime_module "Date_internal"
             && String.equal function_name "of_ymd")
            || (String.equal runtime_module "Date_en"
                && String.equal function_name "of_year_month_day")
            || (String.equal runtime_module "Date_fr"
                && String.equal function_name "depuis_année_mois_jour")
          then eval_external_date_of_ymd_direct ctx pos m args
          else begin
              let concrete = Concrete.evaluate_expr ctx.ctx_decl lang e in
              handler ctx pos args concrete
          end
        | None ->
          (* An imported Catala helper may appear as an external runtime
             closure even though it is not one of Catala's primitive external
             operations. Its concrete result remains valid. Preserve it as an
             incomplete symbolic value so projections and downstream concrete
             execution can continue; coverage prediction for constraints that
             depend on it is deliberately unavailable. *)
          Message.warning ~pos
            "CUTECat has no symbolic semantics for this imported function; \
             continuing with its concrete result";
          let concrete = Concrete.evaluate_expr ctx.ctx_decl lang e in
          replace_conc_info_e Symb_incomplete
            ~constraints:[PathConstraint.mk_z3 SymbExpr.incomplete pos true]
            concrete
          |> make_ok
        end
      | _ ->
        Message.error ~pos
          "function has not been reduced to a lambda at evaluation (should not \
           happen if the term was well-typed")
    | EAppOp { op; args; _ } ->
      Message.debug "... it's an EAppOp";
      let args = List.map (evaluate_expr ctx lang) args in
      Message.debug "EAppOp args evaluated";
      propagate_generic_error_list args []
      @@ fun args ->
      let args_constraints = gather_constraints args in
      let result = evaluate_operator (evaluate_expr ctx lang) ctx op m args in
      propagate_generic_error result args_constraints
      @@ fun result ->
      let r_symb = get_symb_expr result in
      let r_constraints = get_constraints result in
      (* the constraints generated by the evaluation of the evaluation of the
       * operation are:
       * - those generated by the evaluation of the arguments
       * - those possibly generated by the application of the operator to the
       *   arguments *)
      let constraints = append_constraints r_constraints args_constraints in
      add_conc_info_e r_symb ~constraints result |> make_ok
    | EAbs _ ->
      Message.debug "... it's an EAbs";
      (* Give Symb_abs symbolic expression if it is not already something else.
         This is mainly used in [make_z3_struct] *)
      add_conc_info_e SymbExpr.abs e |> make_ok
    | ELit l as e ->
      Message.debug "... it's an ELit";
      let symb_expr = symb_of_lit ctx l in
      (* no constraints generated *)
      add_conc_info_m m symb_expr ~constraints:[] e
    (* | EAbs _ as e -> Marked.mark m e (* these are values *) *)
    | EStruct { fields = es; name } ->
      Message.debug "... it's an EStruct";
      let fields, es = List.split (StructField.Map.bindings es) in
      (* compute all subexpressions *)
      let es = List.map (evaluate_expr ctx lang) es in
      propagate_generic_error_list es []
      @@ fun es ->
      (* make symbolic expression using the symbolic sub-expressions *)
      (* TODO INC *)
      let symb_expr =
        if List.exists (fun x -> get_symb_expr x = SymbExpr.incomplete) es then
          SymbExpr.incomplete
        else SymbExpr.mk_z3 (make_z3_struct ctx name es)
      in
      (* TODO catch error... should not happen *)
      (* gather all constraints from sub-expressions *)
      let constraints = gather_constraints es in
      add_conc_info_m m symb_expr ~constraints
        (EStruct
           {
             fields =
               StructField.Map.of_seq
                 (Seq.zip (List.to_seq fields) (List.to_seq es));
             name;
           })
      |> make_ok
    | EStructAccess { e; name = s; field } -> (
      Message.debug "... it's an EStructAccess";
      propagate_generic_error (evaluate_expr ctx lang e) []
      @@ fun e ->
      match Mark.remove e with
      | EStruct { fields = es; name } ->
        if not (StructName.equal s name) then
          Message.error
            ~extra_pos:["", pos; "", Expr.pos e]
            "Error during struct access: not the same structs (should not \
             happen if the term was well-typed)";
        let field_expr =
          match StructField.Map.find_opt field es with
          | Some e' -> e'
          | None ->
            Message.error ~pos:(Expr.pos e)
              "Invalid field access %a in struct %a (should not happen if the \
               term was well-typed)"
              StructField.format field StructName.format s
        in
        let e_symb = get_symb_expr e in
        let fd_symb = get_symb_expr field_expr in
        let symb_expr =
          make_z3_struct_access ctx s field e_symb fd_symb
          (* TODO catch error... should not happen *)
        in

        Message.debug "EStructAccess symbolic struct access created";
        (* the constraints generated by struct access are only those generated
           by the subcall, as the field expression is already a value *)
        let constraints = get_constraints e in
        add_conc_info_m m symb_expr ~constraints (Mark.remove field_expr)
        |> make_ok
      | _ ->
        Message.error ~pos:(Expr.pos e)
          "The expression %a should be a struct %a but is not (should not \
           happen if the term was well-typed)"
          (Print.expr ()) e StructName.format s)
    | ETuple es ->
      let es = List.map (evaluate_expr ctx lang) es in
      propagate_generic_error_list es [] @@ fun es ->
      let constraints = gather_constraints es in
      let symbolic =
        let symbols = List.map get_symb_expr es in
        if List.for_all
             (function SymbExpr.Symb_z3 _ -> true | _ -> false)
             symbols
        then
          let values = List.map (fun s -> Option.get (z3_of_symb s)) symbols in
          let _, sort =
            find_or_create_tuple_sort ctx (List.map Z3.Expr.get_sort values)
          in
          SymbExpr.mk_z3
            (Z3.Expr.mk_app ctx.ctx_z3 (Z3.Tuple.get_mk_decl sort) values)
        else if
          List.exists
            (function SymbExpr.Symb_incomplete -> true | _ -> false)
            symbols
        then SymbExpr.incomplete
        else SymbExpr.none
      in
      replace_conc_info_e symbolic ~constraints (ETuple es, m) |> make_ok
    | ETupleAccess { e; index; size } ->
      propagate_generic_error (evaluate_expr ctx lang e) [] @@ fun tuple ->
      begin match Mark.remove tuple with
      | ETuple es when List.length es = size ->
        let selected = List.nth es index in
        add_conc_info_m m (get_symb_expr selected)
          ~constraints:(get_constraints tuple) (Mark.remove selected)
        |> make_ok
      | ETuple _ ->
        Message.error ~pos
          "Tuple access expected %d components (should not happen if the term \
           was well-typed)" size
      | _ ->
        Message.error ~pos
          "Tuple access expected a tuple (should not happen if the term was \
           well-typed)"
      end
    | EBad -> assert false
    | EPos _ as e ->
      (* A reified source position.  The plain interpreter lists [EPos] among
         its values ([shared_ast/interpreter.ml]: "these are values"), and it
         is only ever carried along to be read back by an error message ---
         nothing computes with it and nothing branches on it.  So it needs no
         symbolic content of its own beyond something of the right sort:
         [translate_typ_lit] already maps [TPos] to the unit sort, so reuse the
         unit constant, exactly as [z3_of_lit] does for [LUnit].

         Without this every date rule in a port is unreachable, because
         [Date.of_year_month_day] and friends carry a position for the
         "ambiguous date" error they can raise. *)
      Message.debug "... it's an EPos";
      add_conc_info_m m (SymbExpr.mk_z3 (snd ctx.ctx_z3unit)) ~constraints:[] e
    | EInj { name; e; cons } ->
      Message.debug "... it's an EInj";
      propagate_generic_error (evaluate_expr ctx lang e) []
      @@ fun e ->
      let concrete = EInj { name; e; cons } in

      let e_symb = get_symb_expr e in
      let enum_ty =
        match get_type (concrete, m) with
        | Some ty -> ty
        | None when not (EnumName.equal name ConstantNames.option_enum) ->
          (* Enum literals inside homogeneous list literals may lose their
             individual type mark even though [name] still identifies the
             ordinary declared enumeration exactly.  The symbolic injection
             only needs that enum identity in this case.  Option injections
             are deliberately excluded: their erased name does not recover
             the polymorphic payload type. *)
          Mark.add pos (TEnum name)
        | None ->
          Message.error ~pos
            "An enumeration injection has no type during concolic evaluation"
      in
      let symb_expr =
        SymbExpr.app_z3 (make_z3_enum_inj ctx name cons enum_ty) e_symb
      in
      let constraints = get_constraints e in

      add_conc_info_m m symb_expr ~constraints concrete |> make_ok
    | EMatch { e; cases; name } -> (
      Message.debug "... it's an EMatch";
      (* NOTE: The surface keyword [anything] is expanded during desugaring, so
         it makes me generate many cases. See the [enum_wildcard] test for an
         example. TODO issue #130 asks for this feature ; use it once it is
         added. *)
      propagate_generic_error (evaluate_expr ctx lang e) []
      @@ fun e ->
      match Mark.remove e with
      | EInj { e = e1; cons; name = name' } ->
        if not (EnumName.equal name name') then
          Message.error
            ~extra_pos:["", Expr.pos e; "", Expr.pos e1]
            "Error during match: two different enums found (should not happen \
             if the term was well-typed)";
        record_match_origin ctx (Expr.pos e) cons;
        let es_n =
          match EnumConstructor.Map.find_opt cons cases with
          | Some es_n -> es_n
          | None ->
            Message.error ~pos:(Expr.pos e)
              "sum type index error (should not happen if the term was \
               well-typed)"
        in

        (* Here we make sure that the symbolic expression of [e1] (that will be
           sent "down" in a binder) is the accessor of [cons] applied to [e].
           Otherwise it would be the symbolic expression built from the bottom
           up during the evaluation of [e], which may not take into account the
           symbolic value of [e]. *)
        let e_symb = get_symb_expr e in
        let e1_symb =
          match e_symb with
          | Symb_incomplete -> get_symb_expr e1
          | _ ->
            SymbExpr.app_z3 (make_z3_enum_access ctx name cons) e_symb
            (* TODO catch error *)
        in
        let e1_constraints = get_constraints e1 in
        (* Here we have to explicitely "force" the new symbolic value, keep the
           constraints from [e1], and keep the position and type from [e1] *)
        let new_mark = set_conc_info e1_symb e1_constraints (Mark.get e1) in
        let e1 = Mark.set new_mark e1 in

        (* To encode the fact that we are in the [cons] arm of the pattern
           matching, we add a constraint per arm. For the [cons] arm, it encodes
           the fact that [e] is a [cons], and thus is a "true" path branch. For
           every other arm [A], it encodes the fact that [e] is not an [A], and
           thus is a "false" path branch. *)
        let e_constraints = get_constraints e in
        let arm_conditions =
          match e_symb with
          | Symb_incomplete -> []
          | _ -> make_z3_arm_conditions ctx name cons e_symb
        in
        let arm_path_constraints =
          List.map
            (fun (constructor, s, b) ->
              PathConstraint.mk_z3
                ?origin:(origin_for_match ctx (Expr.pos e) constructor cons b)
                (SymbExpr.simplify s) (Expr.pos e) b)
            arm_conditions
        in

        (* then we can evaluate the branch that was taken *)
        let ty =
          EnumConstructor.Map.find cons
            (EnumName.Map.find name ctx.ctx_decl.ctx_enums)
        in
        let new_e = Mark.add m (EApp { f = es_n; args = [e1]; tys = [ty] }) in
        let result = evaluate_expr ctx lang new_e in
        propagate_generic_error result
          (append_constraints arm_path_constraints e_constraints)
        @@ fun result ->
        let r_concrete = Mark.remove result in
        let r_symb = get_symb_expr result in
        let r_constraints = get_constraints result in

        (* the constraints generated by the match when in case [cons] are :
         * - those generated by the evaluation of [e]
         * - the new constraints corresponding to the fact that we are in the [cons] case
         * - those generated by the evaluation of [es_n e1]
         *)
        let constraints =
          concat_constraints
            [r_constraints; arm_path_constraints; e_constraints]
        in

        add_conc_info_m m r_symb ~constraints r_concrete |> make_ok
      | _ ->
        Message.error ~pos:(Expr.pos e)
          "Expected a term having a sum type as an argument to a match (should \
           not happen if the term was well-typed")
    | EIfThenElse { cond; etrue; efalse } -> (
      Message.debug "... it's an EIfThenElse";
      propagate_generic_error (evaluate_expr ctx lang cond) []
      @@ fun cond ->
      let c_symb = get_symb_expr cond in
      let c_constraints = get_constraints cond in
      match Mark.remove cond with
      | ELit (LBool true) ->
        Message.debug "EIfThenElse>true adding %a to constraints"
          SymbExpr.formatter c_symb;
        let c_symb = SymbExpr.simplify c_symb in
        let origin = origin_for_binary ctx (Expr.pos cond) true in
        record_taken_origin ctx origin;
        let c_path_constraint =
          PathConstraint.mk_z3
            ?origin
            c_symb (Expr.pos cond) true
        in
        let etrue = evaluate_expr ctx lang etrue in
        propagate_generic_error etrue (c_path_constraint :: c_constraints)
        @@ fun etrue ->
        let e_symb = get_symb_expr etrue in
        let e_constraints = get_constraints etrue in
        let e_mark = Mark.get etrue in
        let e_concr = Mark.remove etrue in
        (* the constraints generated by the ifthenelse when [cond] is true are :
         * - those generated by the evaluation of [cond]
         * - a new constraint corresponding to [cond] itself
         * - those generated by the evaluation of [etrue]
         *)
        let constraints =
          append_constraints e_constraints
            (c_path_constraint :: c_constraints)
        in
        add_conc_info_m e_mark e_symb ~constraints e_concr |> make_ok
      | ELit (LBool false) ->
        Message.debug "EIfThenElse>false adding %a to constraints"
          SymbExpr.formatter c_symb;
        let not_c_symb =
          SymbExpr.app_z3 (Z3.Boolean.mk_not ctx.ctx_z3) c_symb
        in
        let not_c_symb = SymbExpr.simplify not_c_symb in
        (* TODO catch error... should not happen *)
        let origin = origin_for_binary ctx (Expr.pos cond) false in
        record_taken_origin ctx origin;
        let not_c_path_constraint =
          PathConstraint.mk_z3
            ?origin
            not_c_symb (Expr.pos cond) false
        in
        let efalse = evaluate_expr ctx lang efalse in
        propagate_generic_error efalse (not_c_path_constraint :: c_constraints)
        @@ fun efalse ->
        let e_symb = get_symb_expr efalse in
        let e_constraints = get_constraints efalse in
        let e_mark = Mark.get efalse in
        let e_concr = Mark.remove efalse in
        (* the constraints generated by the ifthenelse when [cond] is false are :
         * - those generated by the evaluation of [cond]
         * - a new constraint corresponding to [cond] itself
         * - those generated by the evaluation of [efalse]
         *)
        let constraints =
          append_constraints e_constraints
            (not_c_path_constraint :: c_constraints)
        in
        add_conc_info_m e_mark e_symb ~constraints e_concr |> make_ok
      | _ ->
        Message.error ~pos:(Expr.pos cond)
          "Expected a boolean literal for the result of this condition (should \
           not happen if the term was well-typed)")
    | EArray es ->
      let es = List.map (evaluate_expr ctx lang) es in
      propagate_generic_error_list es []
      @@ fun es ->
      let constraints = gather_constraints es in
      let es_concr = EArray es in
      let array = es_concr, m in
      let symb =
        match SymbExpr.as_list (get_symb_expr array) with
        | Some list -> SymbExpr.Symb_list list
        | None -> SymbExpr.Symb_list (concrete_symbolic_list ctx es)
      in
      replace_conc_info_e symb ~constraints array |> make_ok
    | EAssert e' ->
      (* TODO CONC REU *)
      propagate_generic_error (evaluate_expr ctx lang e') []
      @@ fun e ->
      begin
        let e_symb = get_symb_expr e in
        let e_constraints = get_constraints e in
        match Mark.remove e with
        | ELit (LBool true) ->
          let concrete = ELit LUnit in
          let e_symb_pc = PathConstraint.mk_z3 e_symb (Expr.pos e') true in
          (* the constraints generated by an assertion when [e] is true are :
           * - those generated by the evaluation of [e]
           * - a new constraint corresponding to [e]
           *)
          (* NOTE that there is no symbolic expression on asserts *)
          let constraints = e_symb_pc :: e_constraints in
          add_conc_info_m m SymbExpr.none ~constraints concrete |> make_ok
        | ELit (LBool false) ->
          (* FIXME use [partially_evaluate_expr_for_assertion_failure_message]
             in error message like in concrete interpreter *)
          let not_e_symb =
            SymbExpr.app_z3 (Z3.Boolean.mk_not ctx.ctx_z3) e_symb
          in
          let not_e_symb_pc =
            PathConstraint.mk_z3 not_e_symb (Expr.pos e') false
          in
          let constraints = not_e_symb_pc :: e_constraints in
          make_error_assertionerror m constraints "Assertion failed"
          (* "Assertion failed:@\n%a" (Print.UserFacing.expr lang) e'
             (partially_evaluate_expr_for_assertion_failure_message ctx lang
             (Expr.skip_wrappers e')) *)
        | _ ->
          Message.error ~pos:(Expr.pos e')
            "Expected a boolean literal for the result of this assertion \
             (should not happen if the term was well-typed)"
      end
    | ECustom _ -> failwith "ECustom not implemented"
    | EEmpty ->
      Message.debug "... it's an EEmptyError";
      make_ok e (* it is a value *)
    | EFatalError _err ->
      failwith "EFatalError not implemented"
      (* raise (Runtime.Error (err, [Expr.pos_to_runtime pos])) *)
    | EErrorOnEmpty e' -> (
      Message.debug "... it's an EErrorOnEmpty";
      propagate_generic_error (evaluate_expr ctx lang e') []
      @@ fun e' ->
      match e' with
      | EEmpty, m ->
        make_error_emptyerror m (get_constraints e')
          "This variable evaluated to an empty term (no rule that defined it \
           applied in this situation)"
      | e -> make_ok e
      (* just pass along the concrete and symbolic values, and the
         constraints *)
      )
    | EDefault
        {
          excepts =
            [
              ((EApp { f = (EAbs _, _) as abs; args = [(ELit LUnit, _)]; _ }, _)
               as except);
            ];
          just = ELit (LBool true), _;
          cons;
        } -> (
      (* failwith "[evaluate_expr] no more thunk" (* FIXME CONTEXT *) *)
      (* FIXME add metadata to find this case instead of this big match *)
      Message.debug "... it's a context variable definition";

      let app = evaluate_expr ctx lang except in
      propagate_generic_error app []
      @@ fun app ->
      let pos = Expr.pos except in
      let abs_symb = get_symb_expr abs in
      let app_constraints =
        get_constraints app (* TODO check that this is always []? *)
      in
      match Mark.remove app with
      | EEmpty ->
        Message.debug "Context>empty";
        let is_empty : PathConstraint.naked_path =
          PathConstraint.mk_reentrant abs_symb ctx.ctx_dummy_const pos true
          |> Option.to_list
        in
        let result = evaluate_expr ctx lang cons in
        propagate_generic_error result
          (append_constraints is_empty app_constraints)
        @@ fun result ->
        let r_symb = get_symb_expr result in
        let r_constraints = get_constraints result in
        (* TODO check that constraints from app should stay as well, just in
           case *)
        let constraints =
          concat_constraints [r_constraints; is_empty; app_constraints]
        in
        add_conc_info_e r_symb ~constraints result |> make_ok
      | _ ->
        Message.debug "Context>non-empty";
        let not_is_empty : PathConstraint.naked_path =
          PathConstraint.mk_reentrant abs_symb ctx.ctx_dummy_const pos false
          |> Option.to_list
        in
        (* the only constraint is the new one encoding the fact that there is a
           reentrant value, and the symbolic expression is that of the
           reentering value *)
        (* TODO check that constraints from app should stay as well, just in
           case *)
        let constraints = append_constraints not_is_empty app_constraints in
        add_conc_info_e SymbExpr.none ~constraints app |> make_ok)
    | EDefault { excepts = [outer]; just = ELit (LBool true), _; cons }
      when SymbExpr.is_reentrant (get_symb_expr outer) -> (
      (* FIXME add metadata to find this case instead of this match? *)
      Message.debug "... it's a context variable definition";

      let outer_symb = get_symb_expr outer in

      Message.debug "context symb %a" SymbExpr.formatter outer_symb;
      let inner =
        match Mark.remove outer with
        | EEmpty -> outer
        | EPureDefault inner -> inner
        | _ -> failwith "no"
      in
      let eval_inner = evaluate_expr ctx lang inner in
      propagate_generic_error eval_inner []
      @@ fun eval_inner ->
      let pos = Expr.pos eval_inner in
      let eval_inner_constraints =
        get_constraints eval_inner (* TODO check that this is always []? *)
      in
      match Mark.remove eval_inner with
      | EEmpty ->
        Message.debug "Context>empty";
        let is_empty : PathConstraint.naked_path =
          PathConstraint.mk_reentrant outer_symb ctx.ctx_reentrant_const pos
            true
          |> Option.to_list
        in
        let result = evaluate_expr ctx lang cons in
        propagate_generic_error result
          (append_constraints is_empty eval_inner_constraints)
        @@ fun result ->
        let r_symb = get_symb_expr result in
        let r_constraints = get_constraints result in
        (* TODO check that constraints from app should stay as well, just in
           case *)
        let constraints =
          concat_constraints [r_constraints; is_empty; eval_inner_constraints]
        in
        add_conc_info_e r_symb ~constraints result |> make_ok
      | _ ->
        Message.debug "Context>non-empty";
        let not_is_empty : PathConstraint.naked_path =
          PathConstraint.mk_reentrant outer_symb ctx.ctx_reentrant_const pos
            false
          |> Option.to_list
        in
        (* the only constraint is the new one encoding the fact that there is a
           reentrant value, and the symbolic expression is that of the
           reentering value *)
        (* TODO check that constraints from app should stay as well, just in
           case *)
        let constraints =
          append_constraints not_is_empty eval_inner_constraints
        in
        add_conc_info_e SymbExpr.none ~constraints eval_inner |> make_ok)
    | EDefault { excepts; just; cons } ->
      Message.debug "... it's an EDefault";

      let count_nonempty_greedy l =
        let l = List.map (evaluate_expr ctx lang) l in
        Message.debug "EDefault using greedy conflict finder";
        let empty_count = List.length (List.filter Concrete.is_empty_error l) in
        let nonempty_count = List.length l - empty_count in
        nonempty_count, l
      in

      let count_nonempty_lazy l =
        Message.debug "EDefault using lazy conflict finder";
        let l = List.map (fun e -> lazy (evaluate_expr ctx lang e)) l in
        let rec aux l seen_nonempty acc =
          match l with
          | [] -> Bool.to_int seen_nonempty, List.rev acc
          | (lazy ex) :: exs ->
            if not (Concrete.is_empty_error ex) then
              if seen_nonempty then 2, List.rev (ex :: acc)
              else aux exs true (ex :: acc)
            else aux exs seen_nonempty (ex :: acc)
        in
        aux l false []
      in

      let count_nonempty =
        if Optimizations.lazy_default ctx.ctx_optims then count_nonempty_lazy
        else count_nonempty_greedy
      in

      let nonempty_count, excepts = count_nonempty excepts in

      Message.debug "EDefault found %n non-empty exceptions!" nonempty_count;
      handle_default ctx lang m (Expr.pos e) nonempty_count excepts just cons
    | EPureDefault _ when SymbExpr.is_reentrant (get_symb_expr e) ->
      Message.debug "... it's an EPureDefault for reentrant";
      e |> make_ok
    | EPureDefault e -> evaluate_expr ctx lang e
    | _ -> .
  in
  (* Message.debug "\teval returns %a | %a"
     (Print.expr ()) ret SymbExpr.formatter (get_symb_expr_r ret); *)

  Message.debug "\teval returns %a" SymbExpr.formatter (get_symb_expr_r ret);
  ret

and handle_default ctx lang m pos nonempty_count excepts just cons =
  propagate_generic_error_list excepts []
  @@ fun excepts ->
  let exc_constraints = gather_constraints excepts in
  match nonempty_count with
  | 0 -> (
    Message.debug "EDefault>no except";
    let just = evaluate_expr ctx lang just in
    propagate_generic_error just exc_constraints
    @@ fun just ->
    let j_symb = get_symb_expr just in
    let j_constraints = get_constraints just in
    match Mark.remove just with
    | EEmpty ->
      (* TODO should be a runtime error *)
      Message.debug "EDefault>empty";
      (* TODO test this case *)
      (* the constraints generated by the default when [just] is empty are :
       * - those generated by the evaluation of the excepts
       * - those generated by the evaluation of [just]
       *)
      let constraints = append_constraints j_constraints exc_constraints in
      add_conc_info_m m SymbExpr.none ~constraints EEmpty
    | ELit (LBool true) ->
      Message.debug "EDefault>true adding %a to constraints" SymbExpr.formatter
        j_symb;
      let j_symb = SymbExpr.simplify j_symb in
      (* TODO catch error... should not happen *)
      (* TODO factorize the simplifications? *)
      let origin = origin_for_binary ctx (Expr.pos just) true in
      record_taken_origin ctx origin;
      let j_path_constraint =
        PathConstraint.mk_z3
          ?origin
          j_symb (Expr.pos just) true
      in
      let cons = evaluate_expr ctx lang cons in
      propagate_generic_error cons
        (j_path_constraint :: append_constraints j_constraints exc_constraints)
      @@ fun cons ->
      let c_symb = get_symb_expr cons in
      let c_constraints = get_constraints cons in
      let c_mark = Mark.get cons in
      let c_concr = Mark.remove cons in
      (* the constraints generated by the default when [just] is true are :
       * - those generated by the evaluation of the excepts
       * - those generated by the evaluation of [just]
       * - a new constraint corresponding to [just] itself
       * - those generated by the evaluation of [cons]
       *)
      let constraints =
        concat_constraints
          [c_constraints; j_path_constraint :: j_constraints; exc_constraints]
      in
      add_conc_info_m c_mark c_symb ~constraints c_concr |> make_ok
    | ELit (LBool false) ->
      let not_j_symb = SymbExpr.app_z3 (Z3.Boolean.mk_not ctx.ctx_z3) j_symb in
      let not_j_symb = SymbExpr.simplify not_j_symb in
      let origin = origin_for_binary ctx (Expr.pos just) false in
      record_taken_origin ctx origin;
      let not_j_path_constraint =
        PathConstraint.mk_z3
          ?origin
          not_j_symb (Expr.pos just) false
      in

      Message.debug "EDefault>false adding %a to constraints" SymbExpr.formatter
        not_j_symb;
      (* the constraints generated by the default when [just] is false are :
       * - those generated by the evaluation of the excepts
       * - those generated by the evaluation of [just]
       * - a new constraint corresponding to [just] itself
       *)
      let constraints =
        not_j_path_constraint
        :: append_constraints j_constraints exc_constraints
      in
      add_conc_info_m m SymbExpr.none ~constraints EEmpty
    | _ ->
      Message.error ~pos
        "Default justification has not been reduced to a boolean at evaluation \
         (should not happen if the term was well-typed)")
  | 1 ->
    Message.debug "EDefault>except";
    let r = List.find (fun sub -> not (Concrete.is_empty_error sub)) excepts in
    (* the constraints generated by the default when exactly one except is raised are :
     * - those generated by the evaluation of the excepts
     *)
    let r_symb = get_symb_expr r in
    let constraints = exc_constraints in
    add_conc_info_e r_symb ~constraints r |> make_ok
  | _ ->
    (* TODO QU Raphaël: discrepancy with standard interpreter? =>> NON à mon
       avis *)
    make_error_conflicterror m exc_constraints
      (List.map
         (fun except ->
           Some "This consequence has a valid justification:", Expr.pos except)
         (List.filter (fun sub -> not (Concrete.is_empty_error sub)) excepts))
      "There is a conflict between multiple valid consequences for assigning \
       the same variable."

(** The following functions gather methods to generate input values for concolic
    execution, be it from a model or from hardcoded default values. *)

let nested_list_key (e : s_expr) = Z3.Expr.to_string e

let rec make_symbolic_input_value ctx name (ty : typ) : SymbExpr.t =
  match Mark.remove ty with
  | TArray element_ty ->
    let len =
      Z3.Expr.mk_const_s ctx.ctx_z3 (name ^ "!len")
        (Z3.Arithmetic.Integer.mk_sort ctx.ctx_z3)
    in
    let list =
      match SymbExpr.mk_list len [] with
      | Symb_list list -> list
      | _ -> assert false
    in
    let rec grow target =
      let target = min target ctx.ctx_max_list_length in
      let capacity = List.length list.elts in
      if capacity < target then begin
        let element =
          make_symbolic_input_value ctx
            (name ^ "!" ^ string_of_int capacity) element_ty
        in
        list.elts <- list.elts @ [element];
        grow target
      end
    in
    Hashtbl.replace ctx.ctx_growable_lists list.id (list, grow);
    grow (min 1 ctx.ctx_max_list_length);
    Symb_list list
  | _ ->
    let _, sort = translate_typ ctx (Mark.remove ty) in
    let symbol = Z3.Expr.mk_const_s ctx.ctx_z3 name sort in
    register_nested_lists ctx name ty (SymbExpr.mk_z3 symbol);
    SymbExpr.mk_z3 symbol

and register_nested_lists ctx name (ty : typ) (symb : SymbExpr.t) : unit =
  match Mark.remove ty, symb with
  | TStruct struct_name, Symb_z3 _ ->
    let fields = StructName.Map.find struct_name ctx.ctx_decl.ctx_structs in
    StructField.Map.iter
      (fun field field_ty ->
        let field_name = Mark.remove (StructField.get_info field) in
        let field_symb =
          make_z3_struct_access ctx struct_name field symb SymbExpr.none
        in
        match Mark.remove field_ty with
        | TArray element_ty ->
          let list =
            match make_symbolic_input_value ctx (name ^ "!" ^ field_name)
                    field_ty with
            | Symb_list list -> list
            | _ -> assert false
          in
          begin match field_symb with
          | Symb_z3 access ->
            let key = nested_list_key access in
            Message.debug "Registering nested symbolic list %s" key;
            Hashtbl.replace ctx.ctx_nested_lists key list
          | _ -> assert false
          end;
          (* [make_symbolic_input_value] recursively registers lists below
             every structure-valued element. *)
          ignore element_ty
        | _ ->
          register_nested_lists ctx (name ^ "!" ^ field_name) field_ty
            field_symb)
      fields
  | _ -> ()

(** Create the mark of an input field from its name [field] and its type [ty].
    Note that this function guarantees that the type information will be present
    when calling [inputs_of_model] *)
let make_input_mark ctx m field (ty : typ) : conc_info mark =
  let name = Mark.remove (StructField.get_info field) in
  let _, sort = translate_typ ctx (Mark.remove ty) in
  let symb_expr =
    match Mark.remove ty with
    | TArrow ([(TLit TUnit, _)], (TDefault _inner_ty, _)) ->
      failwith "[make_input_mark] no more thunks" (* FIXME CONTEXT *)
    | TDefault inner_ty ->
      (* Context variables carry the name of the actual input variable (that is
         the name of the field in the input struct), as well as a symbol used to
         mark the default expression, that can then be used in Z3 when the given
         value is non-empty. See [make_reentrant_input]. *)
      Message.debug "[make_input_mark] reentrant variable <%s> : %a" name
        Print.typ ty;
      let _, inner_sort = translate_typ ctx (Mark.remove inner_ty) in
      let symbol = Z3.Expr.mk_const_s ctx.ctx_z3 name inner_sort in
      SymbExpr.mk_reentrant field symbol
    | TArrow _ ->
      (* proper functions are not allowed as input *)
      Message.error ~pos:(Mark.get ty)
        "This input of the scope is a function. This case is not handled by \
         the concolic interpreter for now. You may want to call this scope \
         from an other scope and provide a specific function as argument."
    | TArray element_ty ->
      ignore element_ty;
      make_symbolic_input_value ctx name ty
    | _ ->
      (* Other variales simply carry a symbol corresponding their name. *)
      let symbol = Z3.Expr.mk_const_s ctx.ctx_z3 name sort in
      register_nested_lists ctx name ty (SymbExpr.mk_z3 symbol);
      SymbExpr.mk_z3 symbol
  in
  let pos = Expr.mark_pos m in
  Custom { pos; custom = { symb_expr; constraints = []; ty = Some ty } }

let soft_constraints_of_input_mark ctx (m : conc_info mark) :
    PathConstraint.pc_expr list =
  let (Custom { custom = { ty; symb_expr; _ }; _ }) = m in
  let ty = Option.get ty in
  (* by construction ty is not None *)
  let naked_ty = Mark.remove ty in
  let pos = Mark.get ty in
  let ctx = ctx.ctx_z3 in
  match naked_ty, symb_expr with
  | TLit TMoney, Symb_z3 var ->
    let zero = Z3.Arithmetic.Integer.mk_numeral_i ctx 0 in
    let money_unit = Z3.Arithmetic.Integer.mk_numeral_i ctx 1_00 in
    let money_ten = Z3.Arithmetic.Integer.mk_numeral_i ctx 10_00 in
    let money_hundred = Z3.Arithmetic.Integer.mk_numeral_i ctx 100_00 in
    let non_negative = Z3.Arithmetic.mk_ge ctx var zero in
    let round_unit =
      Z3.Boolean.mk_eq ctx
        (Z3.Arithmetic.Integer.mk_mod ctx var money_unit)
        zero
    in
    let round_ten =
      Z3.Boolean.mk_eq ctx (Z3.Arithmetic.Integer.mk_mod ctx var money_ten) zero
    in
    let round_hundred =
      Z3.Boolean.mk_eq ctx
        (Z3.Arithmetic.Integer.mk_mod ctx var money_hundred)
        zero
    in
    List.map
      (fun (x, id) ->
        let x = SymbExpr.mk_z3 x in
        (PathConstraint.mk_soft x 1 (Some id) pos false).expr)
      [
        non_negative, "3non-negative";
        round_unit, "2unit";
        round_ten, "1ten";
        round_hundred, "0hundred";
      ]
  | _ -> []

let make_soft_constraints ctx (input_marks : conc_info mark StructField.Map.t) :
    PathConstraint.pc_expr list =
  StructField.Map.fold
    (fun _ m acc -> append_constraints (soft_constraints_of_input_mark ctx m) acc)
    input_marks []

let make_list_bounds ctx (input_marks : conc_info mark StructField.Map.t) =
  let z3 = ctx.ctx_z3 in
  let int n = Z3.Arithmetic.Integer.mk_numeral_i z3 n in
  let seen = Hashtbl.create 31 in
  let rec add symb_expr acc =
    match SymbExpr.as_list symb_expr with
    | None -> acc
    | Some list ->
      let key = list.id in
      if Hashtbl.mem seen key then acc
      else begin
        Hashtbl.add seen key ();
        let lower = Z3.Arithmetic.mk_ge z3 list.len (int 0) in
        let upper =
          Z3.Arithmetic.mk_le z3 list.len (int (list_capacity ctx list))
        in
        List.fold_left (fun acc elt -> add elt acc)
          (PathConstraint.Pc_z3 lower :: PathConstraint.Pc_z3 upper :: acc)
          list.elts
      end
  in
  let bounds =
    StructField.Map.fold
      (fun _ mark acc ->
        let (Custom { custom = { symb_expr; _ }; _ }) = mark in
        add symb_expr acc)
      input_marks []
  in
  Hashtbl.fold (fun _ list acc -> add (SymbExpr.Symb_list list) acc)
    ctx.ctx_nested_lists bounds

let source_date_boundaries (root : conc_expr) =
  let rec collect acc (e : conc_expr) =
    let acc =
      match Mark.remove e with
      | ELit (LDate date) -> DateEncoding.date_to_bigint date :: acc
      | _ -> acc
    in
    Expr.shallow_fold (fun child acc -> collect acc child) e acc
  in
  collect [] root |> List.sort_uniq Z.compare

let input_date_symbols ctx (input_marks : conc_info mark StructField.Map.t) =
  let rec collect ty (symb : SymbExpr.t) acc =
    match Mark.remove ty, symb with
    | TLit TDate, Symb_z3 date -> (date, Mark.get ty) :: acc
    | TStruct name, Symb_z3 _ ->
      let fields = StructName.Map.find name ctx.ctx_decl.ctx_structs in
      StructField.Map.fold
        (fun field field_ty acc ->
          let field_symb =
            make_z3_struct_access ctx name field symb SymbExpr.none
          in
          collect field_ty field_symb acc)
        fields acc
    | TArray element_ty, Symb_list list ->
      List.fold_left (fun acc element -> collect element_ty element acc)
        acc list.elts
    | TDefault inner_ty, Symb_reentrant { symbol; _ } ->
      collect inner_ty (SymbExpr.mk_z3 symbol) acc
    | _ -> acc
  in
  StructField.Map.fold
    (fun _ mark acc ->
      let (Custom { custom = { ty; symb_expr; _ }; _ }) = mark in
      match ty with None -> acc | Some ty -> collect ty symb_expr acc)
    input_marks []

let rec z3_contains expression needle =
  Z3.Expr.equal expression needle
  || List.exists (fun child -> z3_contains child needle)
       (Z3.Expr.get_args expression)

let temporal_seeds ctx date_symbols boundaries pc =
  match PathConstraint.origin pc, pc.PathConstraint.expr with
  | Some _, PathConstraint.Pc_z3 condition ->
    let relevant_symbols =
      List.filter (fun (symbol, _) -> z3_contains condition symbol) date_symbols
    in
    let relevant_boundaries =
      List.filter
        (fun boundary ->
          z3_contains condition (z3_int_of_bigint ctx.ctx_z3 boundary))
        boundaries
    in
    List.concat_map
      (fun (symbol, pos) ->
        List.concat_map
          (fun boundary ->
            [-1; 0; 1]
            |> List.map (fun offset ->
                 let value = Z.add boundary (Z.of_int offset) in
                 let equality =
                   Z3.Boolean.mk_eq ctx.ctx_z3 symbol
                     (z3_int_of_bigint ctx.ctx_z3 value)
                 in
                 (* Scheduler candidates negate their stored expression. Store
                    [not (date = boundary)] so selecting this synthetic edge
                    submits the desired equality through the ordinary solver. *)
                 PathConstraint.mk_z3
                   (SymbExpr.mk_z3
                      (Z3.Boolean.mk_not ctx.ctx_z3 equality))
                   pos false))
          relevant_boundaries)
      relevant_symbols
    |> List.sort_uniq (fun left right ->
         String.compare
           (Format.asprintf "%a" PathConstraint.Print.naked_path [left])
           (Format.asprintf "%a" PathConstraint.Print.naked_path [right]))
  | _ -> []

(** Evaluation *)

(** Do a "pre-evaluation" of the program. It compiles the target scope to a
    function that takes the input struct of the scope and returns its output
    struct *)
let simplify_program ?on_expr ctx (p : (dcalc, 'm) gexpr program) s : conc_expr =
  Message.debug "[CONC] Make program expression concolic";
  let e = Expr.unbox (Program.to_expr p s) in

  Message.debug "[CONC] Pre-compute program concretely";
  let result = Concrete.evaluate_expr ?on_expr ctx.ctx_decl p.lang e in
  init_conc_expr result

(** Evaluate pre-compiled scope [e] with its input struct [name] populated with
    [fields] *)
let eval_conc_with_input
    ctx
    lang
    (name : StructName.t)
    (e : conc_expr)
    (mark : conc_info mark)
    (fields : conc_boxed_expr StructField.Map.t) : conc_result =
  let to_interpret =
    Expr.eapp
      ~f:(Expr.box e)
        (* box instead of rebox because the term is supposed to be closed *)
      ~args:[Expr.estruct ~name ~fields mark]
      ~tys:[Option.get (get_type e)] (* these are supposed to be typed?? *)
      (set_conc_info SymbExpr.none [] (Mark.get e))
  in
  Message.debug "...inputs applied...";
  evaluate_expr ctx lang (Expr.unbox to_interpret)

(** Constraint solving *)
module Solver (Settings : sig
  val optims : Optimizations.flag list
end) =
struct
  type unknown_info = {
    z3reason : string;
    z3stats : Z3.Statistics.statistics;
    z3solver_string : string;
    z3assertions : s_expr list;
  }

  type z3_solver_result =
    | Z3Sat of Z3.Model.model option
    | Z3Unsat
    | Z3Unknown of unknown_info

  (* FIXME this is ugly *)
  let num_unsat = ref 0
  let num_soft_unsat = ref 0
  let num_soft_sat = ref 0

  module StringMap = Map.Make (String)

  let soft_sats = ref StringMap.empty
  let soft_unsats = ref StringMap.empty

  let incr_sat group =
    soft_sats :=
      StringMap.update group
        (fun n -> Some (Option.value ~default:0 n + 1))
        !soft_sats

  let incr_unsat group =
    soft_unsats :=
      StringMap.update group
        (fun n -> Some (Option.value ~default:0 n + 1))
        !soft_unsats

  let print_soft_sats () =
    let open Format in
    let seq = StringMap.to_seq !soft_sats in
    asprintf "sat groups:@[<v>@,%a@]"
      (pp_print_seq ~pp_sep:pp_print_cut (fun fmt (name, n) ->
           fprintf fmt "%n %s sat group" n name))
      seq

  let print_soft_unsats () =
    let open Format in
    let seq = StringMap.to_seq !soft_unsats in
    asprintf "unsat groups:@[<v>@,%a@]"
      (pp_print_seq ~pp_sep:pp_print_cut (fun fmt (name, n) ->
           fprintf fmt "%n %s unsat group" n name))
      seq

  module type Z3SolverModuleType = sig
    type t

    val make : Z3.context -> t
    val add : t -> s_expr list -> unit
    val push : t -> unit
    val pop : t -> unit
    val check : t -> s_expr list -> Z3.Solver.status
    val get_model : t -> Z3.Model.model option
    val get_reason_unknown : t -> string
    val get_statistics : t -> Z3.Statistics.statistics
    val to_string : t -> string
    val get_assertions : t -> s_expr list
  end

  module Z3SolverModule_Solver : Z3SolverModuleType = struct
    type t = Z3.Solver.solver

    let make ctx =
      let solver = Z3.Solver.mk_solver ctx None in
      if Optimizations.timeout Settings.optims then begin
        (* Unix alarms cannot reliably interrupt a long-running native Z3
           call. Give Z3 its own millisecond timeout as well, so a difficult
           candidate yields UNKNOWN and the remaining worklist can proceed. *)
        let params = Z3.Params.mk_params ctx in
        Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") 1000;
        Z3.Solver.set_parameters solver params
      end;
      solver
    let add s l = Z3.Solver.add s l

    (* let add_soft _ _ l = if l <> [] then Message.error ~internal:true "Tried
       to add a soft constraint on an incompatible solver. Try activating the
       soft constraint option." *)
    let push = Z3.Solver.push
    let pop s = Z3.Solver.pop s 1
    let check s cs = Z3.Solver.check s cs
    let get_model = Z3.Solver.get_model
    let get_reason_unknown = Z3.Solver.get_reason_unknown
    let get_statistics = Z3.Solver.get_statistics
    let to_string = Z3.Solver.to_string
    let get_assertions = Z3.Solver.get_assertions
  end

  module type Z3SolverType = sig
    val solve :
      Z3.context -> s_expr list -> PathConstraint.soft list -> z3_solver_result

    val push : Z3.context -> s_expr -> unit
    val pop : Z3.context -> unit -> unit
    val reset : unit -> unit
  end

  module SimpleZ3Solver (S : Z3SolverModuleType) : Z3SolverType = struct
    let solve ctx (constraints : s_expr list) (_ : PathConstraint.soft list) :
        z3_solver_result =
      let solver = S.make ctx in
      S.add solver constraints;

      Message.debug "Solver is\n%s" (S.to_string solver);
      match S.check solver [] with
      | SATISFIABLE -> Z3Sat (S.get_model solver)
      | UNSATISFIABLE -> Z3Unsat
      | UNKNOWN ->
        Z3Unknown
          {
            z3reason = S.get_reason_unknown solver;
            z3stats = S.get_statistics solver;
            z3solver_string = S.to_string solver;
            z3assertions = S.get_assertions solver;
          }

    let push _ _ = ()
    let pop _ () = ()
    let reset () = ()
  end

  module IncrementalZ3Solver (S : Z3SolverModuleType) : Z3SolverType = struct
    let solver = ref None

    let get_solver (ctx : Z3.context) =
      match !solver with
      | None ->
        let s = S.make ctx in
        solver := Some s;
        s
      | Some s -> s

    let _solve ctx (local_constraints : s_expr list) : z3_solver_result =
      let solver = get_solver ctx in
      Message.debug "Using incremental Z3 solver";
      S.push solver;
      S.add solver local_constraints;
      let status = S.check solver local_constraints in

      Message.debug "Solver is\n%s" (S.to_string solver);
      let result =
        match status with
        | SATISFIABLE -> Z3Sat (S.get_model solver)
        | UNSATISFIABLE -> Z3Unsat
        | UNKNOWN ->
          Z3Unknown
            {
              z3reason = S.get_reason_unknown solver;
              z3stats = S.get_statistics solver;
              z3solver_string = S.to_string solver;
              z3assertions = S.get_assertions solver;
            }
      in
      S.pop solver;
      result

    module StringMap = String.Map

    let group_softs (softs : PathConstraint.soft list) :
        PathConstraint.soft list StringMap.t =
      List.fold_left
        (fun acc (s : PathConstraint.soft) ->
          StringMap.update s.id
            (function None -> Some [s] | Some l -> Some (s :: l))
            acc)
        StringMap.empty softs

    let fold_softs ctx name group acc =
      match acc with
      | Some _ -> acc
      | None -> begin
        Message.debug "Trying soft group %s" name;
        let soft_exprs =
          List.map (fun (s : PathConstraint.soft) -> s.symb) group
        in
        let result_soft = _solve ctx soft_exprs in
        match result_soft with
        | Z3Sat _ ->
          incr num_soft_sat;
          incr_sat name;
          Some result_soft
        | Z3Unsat ->
          incr num_soft_unsat;
          incr_unsat name;
          None
        | Z3Unknown _ as r -> Some r
      end

    let solve ctx _ (softs : PathConstraint.soft list) : z3_solver_result =
      Message.debug "Trying solver without softs...";
      let result = _solve ctx [] in
      match result with
      | Z3Sat _ ->
        if softs = [] then result
        else begin
          Message.debug "Sat without softs, so trying solver with softs";
          let groups = group_softs softs in
          (* Message.result "%s" (StringMap.to_seq groups |> List.of_seq |>
             List.map fst |> List.hd); *)
          let try_softs = StringMap.fold (fold_softs ctx) groups None in
          Option.value try_softs ~default:result
        end
      | _ ->
        incr num_unsat;
        result

    let push ctx e =
      let t = Sys.time () in
      let solver = get_solver ctx in
      S.push solver;
      S.add solver [e];

      Message.debug "after_push %f" (Sys.time () -. t)

    let pop ctx () =
      let t = Sys.time () in
      let solver = get_solver ctx in
      S.pop solver;

      Message.debug "after_pop %f" (Sys.time () -. t)

    let reset () = solver := None
  end

  let z3Solver =
    let module SM = Z3SolverModule_Solver in
    if Optimizations.incremental_solver Settings.optims then
      (module IncrementalZ3Solver (SM) : Z3SolverType)
    else (module SimpleZ3Solver (SM) : Z3SolverType)

  module Z3Solver = (val z3Solver)

  type input = PathConstraint.pc_expr list

  type model = {
    model_z3 : Z3.Model.model;
    model_empty_reentrants : StructField.Set.t;
  }

  (* TODO make formatter *)
  let string_of_model m =
    let z3_string = Z3.Model.to_string m.model_z3 in
    let empty_reentrants_list =
      List.of_seq @@ StructField.Set.to_seq m.model_empty_reentrants
    in
    let empty_reentrants_strings =
      List.map
        (fun f -> Mark.remove (StructField.get_info f))
        empty_reentrants_list
    in
    let empty_reentrants_string =
      List.fold_left (fun x acc -> x ^ ", " ^ acc) "" empty_reentrants_strings
    in
    "z3: " ^ z3_string ^ "\nreentrant: " ^ empty_reentrants_string

  let fmt_unknown_info (fmt : Format.formatter) (info : unknown_info) =
    let open Format in
    fprintf fmt "Reason: %s" info.z3reason;
    pp_print_newline fmt ();
    fprintf fmt "Statistics:@.%s" (Z3.Statistics.to_string info.z3stats);
    pp_print_newline fmt ();
    fprintf fmt "Solver:@.%s" info.z3solver_string;
    pp_print_newline fmt ();
    fprintf fmt "Assertions:@.  @[<v>%a@]"
      (Format.pp_print_list Format.pp_print_string)
      (List.map Z3.Expr.to_string info.z3assertions)

  type solver_result =
    | Sat of model option
    | Unsat
    | Unknown of unknown_info
    | SolverTimeout

  let split_input (l : input) :
      s_expr list * PathConstraint.soft list * StructField.Set.t =
    let rec aux
        l
        (acc_z3 : s_expr list)
        (acc_soft : PathConstraint.soft list)
        (acc_reentrant : StructField.Set.t) =
      let open PathConstraint in
      match l with
      | [] -> acc_z3, acc_soft, acc_reentrant
      | Pc_z3 e :: l' -> aux l' (e :: acc_z3) acc_soft acc_reentrant
      | Pc_soft s :: l' -> aux l' acc_z3 (s :: acc_soft) acc_reentrant
      | Pc_reentrant e :: l' ->
        aux l' acc_z3 acc_soft
          (if e.is_empty then StructField.Set.add e.symb.name acc_reentrant
           else acc_reentrant)
      | Pc_incomplete :: _ ->
        Message.error ~internal:true
          "[Solver.split_input] should not get Pc_incomplete as argument"
    in
    aux l [] [] StructField.Set.empty

  (* https://discuss.ocaml.org/t/computation-with-time-constraint/5548/9 *)
  exception Timeout

  let delayed_fun f timeout =
    if not @@ Optimizations.timeout Settings.optims then f ()
    else
      let _ =
        Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Timeout))
      in
      ignore (Unix.alarm timeout);
      try
        let r = f () in
        ignore (Unix.alarm 0);
        r
      with e ->
        ignore (Unix.alarm 0);
        raise e

  let solve (ctx : context) (constraints : input) =
    if Optimizations.check_easy_unsat Settings.optims ctx.ctx_z3 constraints
    then Unsat
    else
      let rec aux retry ctx constraints =
        let z3_constraints, z3_soft_constraints, model_empty_reentrants =
          split_input constraints
        in
        try
          let status =
            delayed_fun
              (fun () ->
                Z3Solver.solve ctx.ctx_z3 z3_constraints z3_soft_constraints)
              1
          in
          begin match status with
          | Z3Sat (Some model_z3) ->
            Sat (Some { model_z3; model_empty_reentrants })
          | Z3Sat None -> Sat None
          | Z3Unsat -> Unsat
          | Z3Unknown info -> Unknown info
          end
        with Timeout ->
          if retry then begin
            Message.warning "Concolic execution solver timed out once";
            Message.warning "Trying to solve again...";
            aux false ctx constraints
          end
          else SolverTimeout
      in
      aux (Optimizations.timeout_retry Settings.optims) ctx constraints

  let push ctx (pc : PathConstraint.pc_expr) =
    match pc with
    | Pc_z3 pc -> Z3Solver.push ctx.ctx_z3 pc
    | Pc_soft _ -> () (* Z3Solver.push_soft ctx.ctx_z3 sc *)
    | Pc_reentrant _ -> ()
    | Pc_incomplete ->
      Message.error ~internal:true
        "[Solver.push] should not get Pc_incomplete as argument"

  let pop ctx (pc : PathConstraint.pc_expr) =
    match pc with
    | Pc_z3 _ | Pc_soft _ -> Z3Solver.pop ctx.ctx_z3 ()
    | Pc_reentrant _ -> ()
    | Pc_incomplete ->
      Message.error ~internal:true
        "[Solver.pop] should not get Pc_incomplete as argument"

  let reset () = Z3Solver.reset ()

  (** Create a dummy concolic mark with a position and a type. It has no
      symbolic expression or constraints, and is used for subexpressions inside
      of input structs whose mark is a single symbol. *)
  let dummy_mark pos ty : conc_info mark =
    Custom
      {
        pos;
        custom = { symb_expr = SymbExpr.none; constraints = []; ty = Some ty };
      }

  (** Get a default literal value from a literal type *)
  let default_lit_of_tlit t : lit =
    match t with
    | TBool -> LBool true
    | TInt -> LInt (Z.of_int 0)
    | TMoney -> LMoney (Runtime.money_of_units_int 0)
    | TUnit | TPos -> LUnit
    | TRat -> LRat (Runtime.decimal_of_string "0")
    | TDate -> LDate DateEncoding.default_date
    | TDuration -> LDuration DateEncoding.default_duration

  (** Get a default concolic expression from a type. The concolic [mark] is
      given by the caller, and this function gives a default concrete value.
      This function is expected to be called from [inputs_of_model] when Z3 has
      not given a value for an input field. *)
  let rec default_expr_of_typ ctx mark ty : conc_boxed_expr =
    match Mark.remove ty with
    | TLit t -> Expr.elit (default_lit_of_tlit t) mark
    | TArrow ([(TLit TUnit, _)], (TDefault _, _)) ->
      (* context variable *)
      Message.error ~pos:(Expr.mark_pos mark)
        "[default_expr_of_typ] should not be called on a context variable. \
         This should not happen if context variables were handled properly."
    | TArrow _ ->
      (* functions *)
      Message.error ~pos:(Expr.mark_pos mark)
        "[default_expr_of_typ] should not be called on a function. This should \
         not happen if functions were handled properly."
    | TTuple tys ->
      let pos = Expr.mark_pos mark in
      Expr.etuple
        (List.map (fun ty -> default_expr_of_typ ctx (dummy_mark pos ty) ty) tys)
        mark
    | TStruct name ->
      (* When a field of the input structure is a struct itself, its fields will
         only be evaluated for their concrete values, as their symbolic value
         will be accessed symbolically from the symbol of the input structure
         field. Thus we can safely give a dummy mark, one with position and type
         for printing, but no symbolic expression or constraint *)
      let pos = Expr.mark_pos mark in
      let fields_typ = StructName.Map.find name ctx.ctx_decl.ctx_structs in
      let fields_expr =
        StructField.Map.map
          (fun ty -> default_expr_of_typ ctx (dummy_mark pos ty) ty)
          fields_typ
      in
      Expr.estruct ~name ~fields:fields_expr mark
    | TEnum name ->
      (* Catala enums always have at least one case, so we can take the first
         one we find and use it as the default case *)
      let pos = Expr.mark_pos mark in
      let constructors = EnumName.Map.find name ctx.ctx_decl.ctx_enums in
      let cstr_name, cstr_ty =
        List.hd (EnumConstructor.Map.bindings constructors)
      in
      let cstr_e = default_expr_of_typ ctx (dummy_mark pos cstr_ty) cstr_ty in
      Expr.einj ~name ~cons:cstr_name ~e:cstr_e mark
    | TOption _ ->
      let pos = Expr.mark_pos mark in
      let unit_ty = TLit TUnit, pos in
      let payload = Expr.elit LUnit (dummy_mark pos unit_ty) in
      Expr.einj ~name:ConstantNames.option_enum
        ~cons:ConstantNames.none_constr ~e:payload mark
    | TArray _ -> Expr.earray [] mark
    | TDefault _ -> failwith "[default_expr_of_typ] TDefault not implemented"
    | TForAll _ -> failwith "[default_expr_of_typ] TForAll not implemented"
    | TVar _ -> failwith "[default_expr_of_typ] TVar not implemented"
    | TAbstract _ -> failwith "[default_expr_of_typ] TAbstract not implemented"
    | TError -> failwith "[default_expr_of_typ] TError not implemented"
    | TClosureEnv ->
      failwith "[default_expr_of_typ] TClosureEnv not implemented"

  (** Get the Z3 expression corresponding to the value of Z3 symbol constant [v]
      in Z3 model [m]. [None] if [m] has not given a value. TODO CONC check that
      the following hypothesis is correct : "get_const_interp_e only returns
      None if the symbol constant can take any value" *)
  let interp_in_model (m : Z3.Model.model) (v : s_expr) : s_expr option =
    Z3.Model.get_const_interp_e m v

  let value_of_symb_expr_lit tl e =
    match tl with
    | TInt -> LInt (integer_of_symb_expr e)
    | TBool -> LBool (bool_of_symb_expr e)
    | TMoney ->
      let cents = integer_of_symb_expr e in
      let money = Runtime.money_of_cents_integer cents in
      LMoney money
    | TRat -> LRat (decimal_of_symb_expr e)
    | TPos | TUnit ->
      LUnit (* TODO maybe check that the Z3 value is indeed unit? *)
    | TDate -> LDate (DateEncoding.decode_date e)
    | TDuration -> LDuration (DateEncoding.decode_duration e)

  (** Make a Catala value from a Z3 expression. The concolic [mark] is given by
      the caller, and this function gives a concrete value corresponding to
      symbolic value [e]. This function is expected to be called from
      [inputs_of_model] when Z3 has given a value for an input field. *)
  let rec value_of_symb_expr ctx model mark ty (origin : s_expr) (e : s_expr) =
    match Mark.remove ty with
    | TLit tl ->
      let lit = value_of_symb_expr_lit tl e in
      Expr.elit lit mark
    | TForAll _ -> failwith "[value_of_symb_expr] TForAll not implemented"
    | TVar _ -> failwith "[value_of_symb_expr] TVar not implemented"
    | TAbstract _ -> failwith "[value_of_symb_expr] TAbstract not implemented"
    | TError -> failwith "[value_of_symb_expr] TError not implemented"
    | TClosureEnv -> failwith "[value_of_symb_expr] TClosureEnv not implemented"
    | TTuple tys ->
      let pos = Expr.mark_pos mark in
      let sort = Z3.Expr.get_sort e in
      let accessors = Z3.Tuple.get_field_decls sort in
      let elements =
        List.map2
          (fun accessor ty ->
            let concrete_access = Z3.Expr.mk_app ctx.ctx_z3 accessor [e] in
            let symbolic_access = Z3.Expr.mk_app ctx.ctx_z3 accessor [origin] in
            let value = Option.get (Z3.Model.eval model concrete_access true) in
            value_of_symb_expr ctx model (dummy_mark pos ty) ty symbolic_access
              value)
          accessors tys
      in
      Expr.etuple elements mark
    | TStruct name ->
      (* To get the values of fields inside a Z3 struct and reconstruct a Catala
         struct out of those, evaluate a Z3 "accessor" to the corresponding
         field in the model *)
      let pos = Expr.mark_pos mark in
      let fields_typ = StructName.Map.find name ctx.ctx_decl.ctx_structs in
      let expr_of_fd fd ty =
        let concrete_access =
          make_z3_struct_access ctx name fd (SymbExpr.mk_z3 e) SymbExpr.none
        in
        let symbolic_access =
          make_z3_struct_access ctx name fd (SymbExpr.mk_z3 origin)
            SymbExpr.none
        in
        match concrete_access, symbolic_access, Mark.remove ty with
        | Symb_z3 _, Symb_list list, TArray _ ->
          value_of_symb_value ctx model (dummy_mark pos ty) ty
            (SymbExpr.Symb_list list)
        | Symb_z3 access, Symb_z3 symbolic_access, _ ->
          (* TODO check that there is no reentrant here *)
          let ev = Option.get (Z3.Model.eval model access true) in
          (* TODO catch error *)
          value_of_symb_expr ctx model (dummy_mark pos ty) ty symbolic_access ev
        (* See [default_expr_of_typ] for an explanation on the dummy mark *)
        | _ ->
          failwith
            "[value_of_symb_expr] access expression is not Z3, this should not \
             happen"
        (* TODO make better error handling here *)
      in
      let fields_expr = StructField.Map.mapi expr_of_fd fields_typ in
      Expr.estruct ~name ~fields:fields_expr mark
    | TEnum name ->
      let pos = Expr.mark_pos mark in
      (* create a mapping of Z3 constructors to the Catala constructors of this
         enum and their types *)
      let sort = EnumName.Map.find name ctx.ctx_z3enums in
      let z3_constructors = Z3.Datatype.get_constructors sort in
      let constructors = EnumName.Map.find name ctx.ctx_decl.ctx_enums in
      let mapping =
        combine_exact "enumeration model constructor" z3_constructors
          (EnumConstructor.Map.bindings constructors)
      in
      (* get the Z3 constructor used in [e] *)
      let e_constructor = Z3.Expr.get_func_decl e in
      (* recover the constructor corresponding to the Z3 constructor *)
      let _, (cstr_name, cstr_ty) =
        try
          List.find
            (fun (cons1, _) -> Z3.FuncDecl.equal e_constructor cons1)
            mapping
        with Not_found ->
          failwith
            "value_of_symb_expr could not find what case of an enum was used. \
             This should not happen."
        (* TODO make better error *)
      in
      let e_arg = List.hd (Z3.Expr.get_args e) in
      let arg =
        value_of_symb_expr ctx model (dummy_mark pos cstr_ty) cstr_ty e_arg
          e_arg
      in
      Expr.einj ~name ~cons:cstr_name ~e:arg mark
    | TArrow _ ->
      Message.error ~pos:(Expr.mark_pos mark)
        "[value_of_symb_expr] should not be called on a context variable or a \
         function. This should not happen if they were handled properly"
    | TOption payload_ty ->
      let pos = Expr.mark_pos mark in
      let sort = Z3.Expr.get_sort e in
      let constructors = Z3.Datatype.get_constructors sort in
      let e_constructor = Z3.Expr.get_func_decl e in
      begin match constructors with
      | [none_constructor; _some_constructor]
        when Z3.FuncDecl.equal e_constructor none_constructor ->
        let unit_ty = TLit TUnit, pos in
        let payload = Expr.elit LUnit (dummy_mark pos unit_ty) in
        Expr.einj ~name:ConstantNames.option_enum
          ~cons:ConstantNames.none_constr ~e:payload mark
      | [_; some_constructor]
        when Z3.FuncDecl.equal e_constructor some_constructor ->
        let payload_value = List.hd (Z3.Expr.get_args e) in
        let payload =
          value_of_symb_expr ctx model (dummy_mark pos payload_ty) payload_ty
            payload_value payload_value
        in
        Expr.einj ~name:ConstantNames.option_enum
          ~cons:ConstantNames.some_constr ~e:payload mark
      | _ ->
        failwith
          "[value_of_symb_expr] option value has an unknown constructor"
      end
    | TArray _ -> failwith "[value_of_symb_expr] TArray not implemented"
    | TDefault _ -> failwith "[value_of_symb_expr] TDefault not implemented"

  and value_of_symb_value ctx model mark ty symb =
    match symb with
    | SymbExpr.Symb_z3 symbol ->
      let value = interp_in_model model symbol in
      begin match value, Mark.remove ty with
      | Some value, _ -> value_of_symb_expr ctx model mark ty symbol value
      | None, TStruct _ ->
        (* A constraint may mention only a separately encoded list field, so
           Z3 can leave the enclosing structure itself uninterpreted. Build a
           completed default structure while still materialising its nested
           symbolic lists from their own length and element symbols. *)
        let value = Option.get (Z3.Model.eval model symbol true) in
        value_of_symb_expr ctx model mark ty symbol value
      | None, _ -> default_expr_of_typ ctx mark ty
      end
    | SymbExpr.Symb_list list -> value_of_symb_list ctx model mark ty list
    | _ -> failwith "[value_of_symb_value] unsupported symbolic input"

  and value_of_symb_list ctx model mark ty (list : SymbExpr.symb_list) =
    match Mark.remove ty with
    | TArray element_ty ->
      let n =
        match interp_in_model model list.len with
        | None -> 0
        | Some value ->
          integer_of_symb_expr value |> Z.to_int
          |> max 0 |> min ctx.ctx_max_list_length
      in
      let rec take n xs =
        match n, xs with
        | 0, _ | _, [] -> []
        | n, x :: xs -> x :: take (n - 1) xs
      in
      let symbols = take n list.elts in
      let pos = Expr.mark_pos mark in
      let elements =
        List.map
          (fun symbol ->
            let emark =
              Custom
                {
                  pos;
                  custom =
                    { symb_expr = symbol; constraints = [];
                      ty = Some element_ty };
                }
            in
            value_of_symb_value ctx model emark element_ty symbol)
          symbols
      in
      let list_mark =
        map_conc_mark
          ~symb_expr_f:(fun _ -> SymbExpr.Symb_list { list with elts = symbols })
          mark
      in
      Expr.earray elements list_mark
    | _ -> failwith "[value_of_symb_list] symbolic list has a non-list type"

  let make_term ctx z3_model mk ty symb_expr =
    value_of_symb_value ctx z3_model mk ty (SymbExpr.mk_z3 symb_expr)

  let make_reentrant_input ctx name z3_model empty_reentrants mk ty symb_expr :
      conc_boxed_expr =
    (* See [make_input_mark] for a general description of the Symb_reentrant
       symbolic expression. *)
    if StructField.Set.mem name empty_reentrants then (
      (* If the context variable must evaluate to its default value (as defined
         in the scope), then we make an empty term. During evaluation, the
         [name] of the variable will be used to generate a constraint encoding
         whether it is empty, but the symbolic expression on the (empty) innner
         term will not be used. *)
      Message.debug "[make_reentrant_input] empty";
      Expr.eempty mk)
    else (
      (* If the context variable must evaluate to a specific value computed by
         the Z3 model, then we make this inner term and encapsulate it. The mark
         on the inner term (inside the default) is the symbol in the
         Symb_reentrant structure, and will be be used during evaluation. The
         mark on the outer term (the default term itself) will be used only for
         its [name] field and will be used to generate a constraint encoding
         whether it is empty. *)
      Message.debug "[make_reentrant_input] non empty";
      match Mark.remove ty with
      | TArrow ([(TLit TUnit, _)], (TDefault _inner_ty, _)) ->
        failwith "[make_reentrant_input] no more thunk" (* FIXME CONTEXT *)
      | TDefault inner_ty ->
        let inner_mk =
          map_conc_mark ~symb_expr_f:(fun _ -> Symb_z3 symb_expr) mk
        in
        let term = make_term ctx z3_model inner_mk inner_ty symb_expr in
        let (Custom { custom; _ }) = Mark.get term in

        Message.debug "[make_reentrant_input] non empty inner: %a"
          SymbExpr.formatter_typed custom.symb_expr;
        let term = Expr.epuredefault term mk in
        let (Custom { custom; _ }) = Mark.get term in

        Message.debug "[make_reentrant_input] non empty thunked: %a"
          SymbExpr.formatter_typed custom.symb_expr;
        term
      | _ -> failwith "[make_reentrant_input] did not get an arrow type")

  (** Get Catala values from a Z3 model, possibly using default values *)
  let inputs_of_model
      ctx
      (m : model)
      (input_marks : conc_info mark StructField.Map.t) :
      conc_boxed_expr StructField.Map.t =
    let f _ (mk : conc_info mark) : conc_boxed_expr =
      let (Custom { custom; _ }) = mk in
      let ty =
        Option.get custom.ty
        (* should not fail because [make_input_mark] always adds a ty *)
      in
      let symb_expr = custom.symb_expr in
      let t =
        match symb_expr with
        | Symb_reentrant { name; symbol } ->
          (* Context variable *)
          make_reentrant_input ctx name m.model_z3 m.model_empty_reentrants mk
            ty symbol
        | Symb_z3 s ->
          (* Input variable *)
          make_term ctx m.model_z3 mk ty s
        | Symb_list list -> begin
          value_of_symb_list ctx m.model_z3 mk ty list
        end
        | Symb_none ->
          failwith "[inputs_of_model] input mark should not be none"
        | Symb_incomplete ->
          failwith "[inputs_of_model] input mark should not be incomplete"
          (* TODO INC *)
        | Symb_abs ->
          failwith
            "[inputs_of_model] input mark should not be abs" (* TODO INC *)
        | Symb_error _ ->
          failwith "[inputs_of_model] input mark should not be an error"
      in
      let (Custom { custom; _ }) = Mark.get t in

      Message.debug "[inputs_of_model] input has symb? %a" SymbExpr.formatter
        custom.symb_expr;
      t
    in
    StructField.Map.mapi f input_marks
end

(** Remove marks from an annotated path, to get a list of path constraints to
    feed in the solver. In doing so, actually negate constraints marked as
    Negated. This function shall be called on an output of
    [PathConstraint.make_expected_path]. *)
let pc_expr_of_apc ctx (apc : PathConstraint.annotated_pc) :
    PathConstraint.pc_expr (* FIXME Solver.input *) =
  let open PathConstraint in
  match apc with
  | Normal c -> c.expr
  | Done c -> c.expr
  | Negated c -> begin
    match c.expr with
    | Pc_z3 e -> Pc_z3 (Z3.Boolean.mk_not ctx.ctx_z3 e)
    | Pc_soft _ ->
      failwith "[pc_expr_of_apc] negation of soft constraint should not happen"
    | Pc_reentrant e -> Pc_reentrant { e with is_empty = not e.is_empty }
    | Pc_incomplete ->
      Message.error ~internal:true
        "[pc_expr_of_apc] should not get Pc_incomplete as argument"
  end

let constraint_list_of_path ctx (path : PathConstraint.annotated_path) :
    PathConstraint.pc_expr list (* FIXME Solver.input? *) =
  List.rev (List.rev_map (pc_expr_of_apc ctx) path)

let apply_diff
    ctx
    f_push
    f_pop
    (diff : PathConstraint.incremental_annotated_pc list) : unit =
  Message.debug "apply_diff";
  let f = function
    | PathConstraint.IncrPush apc ->
      let expr = pc_expr_of_apc ctx apc in
      f_push ctx expr
    | PathConstraint.IncrPop apc ->
      let expr = pc_expr_of_apc ctx apc in
      f_pop ctx expr
  in
  List.iter f diff

let print_fields (prefix : string) fields =
  let ordered_fields =
    List.sort (fun ((v1, _), _) ((v2, _), _) -> String.compare v1 v2) fields
  in
  List.iter
    (fun ((var, _), value) ->
      Message.result "%s@[<hov 2>%s@ =@ %a@]%s" prefix var (Print.expr ()) value
        (if Global.options.debug then
           " | " ^ SymbExpr.to_string (_get_symb_expr_unsafe value)
         else ""))
    ordered_fields

module Stats = struct
  (* TODO: quel temps manque ? compter le nombre d'evals *)
  (* GC: pic mémoire alloué ? Z3 incrémental le dit ? *)
  type time = float
  type period = { start : time; stop : time }
  type step = string * period

  type execution = {
    steps : step list;
    total_time : period;
    num_constraints : int;
  }

  type t = {
    total_time : period;
    steps : step list;
    executions : execution list;
  }

  let start_period () : period =
    let start = Sys.time () in
    { start; stop = nan }

  let stop_period p : period =
    let stop = Sys.time () in
    { p with stop }

  let init () : t =
    let total_time = start_period () in
    { total_time; steps = []; executions = [] }

  let start_step message : step = message, start_period ()
  let stop_step ((msg, p) : step) : step = msg, stop_period p

  let start_exec num_constraints : execution =
    let total_time = start_period () in
    { steps = []; total_time; num_constraints }

  let add_exec_step (e : execution) step : execution =
    { e with steps = step :: e.steps }

  let stop_exec (e : execution) : execution =
    let total_time = stop_period e.total_time in
    { e with total_time }

  let add_stat_step (stats : t) (step : step) : t =
    { stats with steps = step :: stats.steps }

  let add_stat_exec (stats : t) (e : execution) : t =
    { stats with executions = e :: stats.executions }

  let stop stats : t =
    let total_time = stop_period stats.total_time in
    { stats with total_time }

  let running_period stats : period = stop_period stats.total_time
  let elapsed stats : float = Sys.time () -. stats.total_time.start

  let fold_execs (execs : execution list) : step list =
    let f (steps : step list) (exec : execution) =
      List.map2
        (fun (s, p) (s', p') ->
          assert (String.equal s s');
          s, { p with stop = p.stop +. p'.stop -. p'.start })
        steps exec.steps
    in
    match execs with
    | [] -> []
    | { steps; _ } :: execs -> List.fold_left f steps execs

  module Print = struct
    open Format

    (* let ms (fmt : formatter) (t : time) = *)
    (*   let milli : int = int_of_float (t *. 1000.) in *)
    (*   pp_print_int fmt milli; *)
    (*   pp_print_string fmt " ms" *)

    let sec (fmt : formatter) (t : time) =
      fprintf fmt "%.3f" t;
      pp_print_string fmt " s"

    let period (fmt : formatter) (p : period) = sec fmt (p.stop -. p.start)

    let step (fmt : formatter) ((msg, p) : step) =
      fprintf fmt "%s: %a" msg period p

    (* let itemize (bullet : string) (ppf : formatter -> 'a -> unit) (fmt :
       formatter) (x : 'a) = fprintf fmt "%s %a" bullet ppf x *)

    let steps (fmt : formatter) (l : step list) =
      let l = List.rev l in
      pp_print_list ~pp_sep:pp_print_cut step fmt l

    let executions (fmt : formatter) (execs : execution list) =
      let folded = fold_execs execs |> List.rev in
      let max_constraints =
        List.fold_left (fun acc exe -> max acc exe.num_constraints) 0 execs
      in
      pp_print_list ~pp_sep:pp_print_cut step fmt folded;
      pp_print_cut fmt ();
      fprintf fmt "max constraints: %n" max_constraints
  end

  let print (fmt : Format.formatter) (stats : t) =
    let open Format in
    fprintf fmt "General steps:@\n@[<v 2>  %a@]@\n" Print.steps stats.steps;
    fprintf fmt "After %n execution steps:@\n@[<v 2>  %a@]@\n"
      (List.length stats.executions)
      Print.executions stats.executions;
    fprintf fmt "Total concolic time: %a" Print.period stats.total_time
end

(** Main function *)
let enumerate_branch_objectives
    (type m)
    (max_list_length : int)
    (p : (dcalc, m) gexpr program)
    s : string list =
  if max_list_length < 0 then
    Message.error "The maximum BOBCat list length must be non-negative";
  let ctx = make_empty_context p.decl_ctx [] max_list_length |> init_context in
  let scope_e = simplify_program ctx p s in
  index_source_branches ctx scope_e;
  let objectives =
    Hashtbl.fold (fun _ pair pairs -> pair :: pairs) ctx.ctx_branch_pairs []
    |> List.sort_uniq String.compare
  in
  print_json_string_list "BOBCAT_BRANCH_MANIFEST" objectives;
  Format.pp_print_flush Format.std_formatter ();
  objectives

exception Unsupported_goal of string

let expose_entry_scope (program : typed Dcalc.Ast.expr) =
  let rec expose definitions seen (e : typed Dcalc.Ast.expr) =
    match Mark.remove e with
    | EApp { f = (EAbs { binder; _ }, _); args; _ }
      when Bindlib.mbinder_arity binder = List.length args ->
      let vars, body = Bindlib.unmbind binder in
      let definitions =
        List.fold_left2
          (fun definitions var definition ->
            Var.Map.add var definition definitions)
          definitions (Array.to_list vars) args
      in
      expose definitions seen body
    | EVar var ->
      if Var.Set.mem var seen then
        raise (Unsupported_goal "cyclic top-level definition while locating scope")
      else
        begin match Var.Map.find_opt var definitions with
        | Some definition ->
          expose definitions (Var.Set.add var seen) definition
        | None ->
          raise
            (Unsupported_goal
               "unbound top-level variable while locating entry scope")
        end
    | EAbs _ -> Var.Map.bindings definitions, e
    | _ ->
      raise
        (Unsupported_goal
           "the compiled entry scope is not a function after lazy unfolding")
  in
  expose Var.Map.empty Var.Set.empty program


let print_goal_result objective status fields =
  let json =
    `Assoc
      (("objective", `String objective) :: ("status", `String status) :: fields)
  in
  Message.result "BOBCAT_OBJECTIVE %s" (Yojson.Safe.to_string json)

let replay_model ctx p scope input =
  let hits = Hashtbl.create 32 in
  let on_result original result =
    match Mark.remove original with
    | EAppOp { op = Tag ((Branching _ | Exception _) as tag), _; _ } ->
      let taken =
        match tag, Mark.remove result with
        | Branching _, _ -> true
        | Exception _, ELit (LBool true) -> true
        | Exception _, _ -> false
        | _ -> false
      in
      if taken then
        let key = outcome_key tag (Expr.pos original) in
        Option.iter
          (fun branch -> Hashtbl.replace hits branch ())
          (Hashtbl.find_opt ctx.ctx_branch_pairs key)
    | EApp { f = ((EAbs _, _) as selected_arm); _ } ->
      (* The concrete interpreter turns a selected match arm into an
         application of that arm lambda.  Recording its source position also
         covers compiler-generated matches whose arm has no surviving Tag
         node (for example `minimum ... or if list empty ...`). *)
      let key = outcome_key (Branching None) (Expr.pos selected_arm) in
      Option.iter
        (fun branch -> Hashtbl.replace hits branch ())
        (Hashtbl.find_opt ctx.ctx_branch_pairs key)
    | _ -> ()
  in
  try
    let outputs =
      Concrete.interpret_program_dcalc ~input ~on_result
        ~raise_on_error:true ~disable_trace:true p scope
    in
    let branches = sorted_table_keys hits in
    begin
      let outputs =
        `Assoc
          (List.map
             (fun ((name, _), value) ->
               name, `String (Format.asprintf "%a" (Print.expr ()) value))
             outputs)
      in
      Ok (branches, outputs)
    end
  with
  | Stack_overflow ->
    Error ("concrete replay exhausted the OCaml stack", sorted_table_keys hits)
  | (Runtime.Error _ | Failure _ | Invalid_argument _) as exn ->
    let backtrace = Printexc.get_backtrace () in
    Error
      ( (Printexc.to_string exn
         ^ if String.equal backtrace "" then "" else "\n" ^ backtrace),
        sorted_table_keys hits )

let solve_branch_objectives
    (max_list_length : int)
    (optimization_timeout_ms : int)
    (solver_timeout_ms : int)
    (solver_timeout_max_ms : int)
    (print_timings : bool)
    (p : (dcalc, typed) gexpr program)
  s : unit =
  if solver_timeout_ms <= 0 then
    Message.error "The initial BOBCat solver timeout must be positive";
  if optimization_timeout_ms < 0 then
    Message.error "The BOBCat MaxSAT timeout must be non-negative";
  if solver_timeout_max_ms < solver_timeout_ms then
    Message.error
      "The maximum BOBCat solver timeout must be at least the initial timeout";
  let output_mutex = Mutex.create () in
  let synchronized mutex action =
    Mutex.lock mutex;
    Fun.protect ~finally:(fun () -> Mutex.unlock mutex) action
  in
  let emit_timing ?list_bound phase objectives cpu_seconds =
    if print_timings then begin
      let metadata =
        match list_bound with
        | None -> []
        | Some bound -> ["list_bound", `Int bound]
      in
      let json =
        `Assoc
          ([ "phase", `String phase;
             "objectives", `List (List.map (fun x -> `String x) objectives);
             "cpu_ms", `Float (cpu_seconds *. 1000.) ]
          @ metadata)
      in
      synchronized output_mutex (fun () ->
        Message.result "BOBCAT_TIMING %s" (Yojson.Safe.to_string json);
        Format.pp_print_flush Format.std_formatter ())
    end
  in
  let timed ?list_bound phase objectives action =
    let started = Sys.time () in
    Fun.protect
      ~finally:(fun () ->
        emit_timing ?list_bound phase objectives (Sys.time () -. started))
      action
  in
  let ctx = make_empty_context p.decl_ctx [] max_list_length |> init_context in
  (* The inherited concolic engine first evaluated the closed program to
     precompute a residual scope. On large whole-program inputs that eager
     beta-reduction duplicates shared definitions exponentially before BOBCat
     even reaches Z3. A backward engine needs the typed DCalc graph itself: it
     follows applications on demand and retains the program's binders as
     sharing points. *)
  let typed_program_e = Program.to_expr p s |> Expr.unbox in
  let definitions, typed_scope_e = expose_entry_scope typed_program_e in
  let input_var, input_ty, body =
    match Mark.remove typed_scope_e with
    | EAbs { binder; tys = [input_ty]; _ } ->
      let vars, body = Bindlib.unmbind binder in
      if Array.length vars <> 1 then
        raise (Unsupported_goal "the entry scope does not have one input");
      vars.(0), input_ty, body
    | _ ->
      raise
        (Unsupported_goal "the compiled entry scope is not a function")
  in
  let indexed_definitions =
    List.fold_left
      (fun env (var, definition) -> Var.Map.add var definition env)
      Var.Map.empty definitions
  in
  let rec largest_literal_list e =
    let here =
      match Mark.remove e with EArray values -> List.length values | _ -> 0
    in
    Expr.shallow_fold
      (fun child largest -> max largest (largest_literal_list child))
      e here
  in
  let array_capacity =
    List.fold_left
      (fun largest (_, definition) ->
        max largest (largest_literal_list definition))
      (max max_list_length (largest_literal_list body)) definitions
  in
  timed "manifest_index" [] (fun () ->
    index_source_branches ~definitions:indexed_definitions ctx body);
  let indexed_objectives =
    Hashtbl.fold (fun _ pair pairs -> pair :: pairs) ctx.ctx_branch_pairs []
    |> List.sort_uniq String.compare
  in
  let objective_of_tag tag pos =
    Hashtbl.find_opt ctx.ctx_branch_pairs (outcome_key tag pos)
  in
  let objectives =
    indexed_objectives
    |> List.sort (fun left right ->
         let root_file = Pos.get_file (Expr.pos body) in
         let contains haystack needle =
           let haystack_length = String.length haystack in
           let needle_length = String.length needle in
           let rec loop offset =
             offset + needle_length <= haystack_length
             && (String.equal needle
                   (String.sub haystack offset needle_length)
                 || loop (offset + 1))
           in
           needle_length = 0 || loop 0
         in
         let rank objective =
           let local = contains objective ("@" ^ root_file ^ ":") in
           let kind =
             if String.starts_with ~prefix:"if@" objective then 0
             else if String.starts_with ~prefix:"default@" objective then 1
             else 2
           in
           (if local then 0 else 1), kind
         in
         match compare (rank left) (rank right) with
         | 0 -> String.compare left right
         | order -> order)
  in
  (* Emit the denominator before building potentially expensive Z3 formulas.
     A process-level budget may stop compilation or solving, but it must never
     make uncovered source outcomes disappear from the coverage metric. *)
  print_json_string_list "BOBCAT_BRANCH_MANIFEST" objectives;
  Format.pp_print_flush Format.std_formatter ();
  let state_mutex = Mutex.create () in
  let replay_mutex = Mutex.create () in
  let final_results = Hashtbl.create (List.length indexed_objectives) in
  let leased = Hashtbl.create (List.length indexed_objectives) in
  let is_final objective =
    synchronized state_mutex (fun () -> Hashtbl.mem final_results objective)
  in
  let uncovered_snapshot () =
    synchronized state_mutex (fun () ->
      List.filter
        (fun objective -> not (Hashtbl.mem final_results objective))
        objectives)
  in
  let finalize objective status fields =
    let added =
      synchronized state_mutex (fun () ->
        if Hashtbl.mem final_results objective then false
        else begin
          Hashtbl.replace final_results objective (status, fields);
          true
        end)
    in
    if added then
      synchronized output_mutex (fun () ->
        print_goal_result objective status fields;
        Format.pp_print_flush Format.std_formatter ())
  in
  let lease objectives =
    synchronized state_mutex (fun () ->
      objectives
      |> List.filter (fun objective ->
           not (Hashtbl.mem final_results objective)
           && not (Hashtbl.mem leased objective))
      |> List.map (fun objective ->
           Hashtbl.replace leased objective ();
           objective))
  in
  let release objectives =
    synchronized state_mutex (fun () ->
      List.iter (Hashtbl.remove leased) objectives)
  in
  let run_worker _worker_id =
  let solver_session =
    Verification.Z3backend.create_direct_session p.decl_ctx ~input_var
      ~input_ty ~max_list_length ~array_capacity ~solver_timeout_ms
  in
  let compiled = Hashtbl.create (List.length indexed_objectives) in
  let pending_from candidates =
    List.filter
      (fun objective ->
        Hashtbl.mem compiled objective
        && not (is_final objective))
      candidates
  in
  let divergences = ref 0 in
  let max_divergences = max 32 (4 * List.length objectives) in
  let replay_and_validate model predicted =
    synchronized replay_mutex (fun () ->
    Message.debug "BOBCat candidate input: %s" (Yojson.Safe.to_string model);
    match timed "concrete_replay" predicted (fun () -> replay_model ctx p s model) with
    | Error (reason, observed_before_error) ->
      incr divergences;
      Verification.Z3backend.block_last_input solver_session;
      let json =
        `Assoc
          [ "input", model;
            "predicted",
            `List (List.map (fun x -> `String x) predicted);
            "observed_before_error",
            `List (List.map (fun x -> `String x) observed_before_error);
            "reason", `String reason ]
      in
      synchronized output_mutex (fun () ->
        Message.result "BOBCAT_REFINEMENT %s" (Yojson.Safe.to_string json);
        Message.warning "BOBCat rejected symbolic input %s: %s"
          (Yojson.Safe.to_string model) reason);
      false
    | Ok (observed, outputs) ->
      let newly_covered =
        List.filter
          (fun objective ->
            List.mem objective observed
            && not (is_final objective))
          objectives
      in
      (* Every successfully replayed model is a valid concrete test, even when
         it does not witness the symbolic objective that produced it.  Keep
         the complete corpus; coverage credit remains based exclusively on
         the outcomes observed by the concrete interpreter. *)
      let replay_json =
        `Assoc
          [ "objectives",
            `List (List.map (fun x -> `String x) predicted);
            "input", model;
            "outputs", outputs;
            "branches",
            `List (List.map (fun b -> `String b) observed) ]
      in
      synchronized output_mutex (fun () ->
        Message.result "BOBCAT_REPLAY %s" (Yojson.Safe.to_string replay_json));
      if newly_covered = [] then begin
        incr divergences;
        Verification.Z3backend.block_last_input solver_session;
        let json =
          `Assoc
            [ "input", model;
              "predicted",
              `List (List.map (fun x -> `String x) predicted);
              "observed",
              `List (List.map (fun x -> `String x) observed);
              "reason", `String "predicted objective was not observed" ]
        in
        synchronized output_mutex (fun () ->
          Message.result "BOBCAT_REFINEMENT %s" (Yojson.Safe.to_string json));
        false
      end else begin
        List.iter
          (fun objective ->
            finalize objective "sat"
              ["input", model; "validated", `Bool true])
          newly_covered;
        true
      end)
  in
  let split values =
    let left_count = max 1 (List.length values / 2) in
    let rec take_drop n taken rest =
      if n = 0 then List.rev taken, rest
      else match rest with
        | [] -> List.rev taken, []
        | value :: tail -> take_drop (n - 1) (value :: taken) tail
    in
    take_drop left_count [] values
  in
  let max_refinements_per_group = 3 in
  let rec solve_group
      ?(refinements = 0)
      ~(list_bound : int)
      ~finalize_failures timeout_ms candidates =
    let candidates = pending_from candidates in
    if candidates = [] || !divergences >= max_divergences then ()
    else begin
      Verification.Z3backend.set_solver_timeout solver_session timeout_ms;
      match
        timed ~list_bound "z3_check_and_decode" candidates (fun () ->
          let maximize_objectives =
            uncovered_snapshot ()
            |> List.filter (fun objective -> Hashtbl.mem compiled objective)
          in
          Verification.Z3backend.solve_uncovered solver_session ~list_bound
            ~optimization_timeout_ms:
              (if optimization_timeout_ms = 0 then 0
               else min timeout_ms optimization_timeout_ms)
            ~maximize_objectives candidates)
      with
      | Coverage_unsat ->
        if list_bound < max_list_length then
          solve_group ~list_bound:(list_bound + 1) ~finalize_failures
            solver_timeout_ms candidates
        else if finalize_failures then
          List.iter (fun objective -> finalize objective "unsat" []) candidates
      | Coverage_sat (model, predicted) ->
        let made_progress = replay_and_validate model predicted in
        let remaining = pending_from candidates in
        if remaining <> [] && made_progress && (!divergences < max_divergences)
        then
          (* A valid replay can cover only part of an OR-batch. A rejected
             replay adds a counterexample refinement. In both cases the next
             query is strictly different: an objective disappeared or the
             exact spurious model was excluded. *)
          solve_group ~list_bound ~finalize_failures solver_timeout_ms remaining
        else if remaining <> [] && not made_progress && finalize_failures then
          if refinements + 1 >= max_refinements_per_group then
            List.iter
              (fun objective ->
                finalize objective "unknown"
                  [ "reason",
                    `String
                      "repeated symbolic/concrete divergence after abstract \
                       input refinement";
                    "refinements", `Int (refinements + 1) ])
              remaining
          else
            solve_group ~refinements:(refinements + 1) ~list_bound
              ~finalize_failures solver_timeout_ms remaining
      | Coverage_unknown reason ->
        begin match candidates with
        | [_] when timeout_ms < solver_timeout_max_ms ->
          let next_timeout =
            min solver_timeout_max_ms (max (timeout_ms + 1) (timeout_ms * 5))
          in
          solve_group ~list_bound ~finalize_failures next_timeout candidates
        | [_] ->
          if list_bound < max_list_length then
            solve_group ~list_bound:(list_bound + 1) ~finalize_failures
              solver_timeout_ms candidates
          else if finalize_failures then
            List.iter
              (fun objective ->
                finalize objective "unknown"
                  [ "reason", `String reason;
                    "timeout_ms", `Int timeout_ms ])
              candidates
        | _ ->
          (* UNKNOWN for A OR B says nothing about A or B individually. Split
             until the expensive objective is isolated so its siblings still
             get a definitive result. *)
          let left, right = split candidates in
          solve_group ~list_bound ~finalize_failures timeout_ms left;
          solve_group ~list_bound ~finalize_failures timeout_ms right
        end
    end
  in
  let streamed = Hashtbl.create (List.length objectives) in
  let on_objective objective =
    Hashtbl.replace compiled objective ();
    if not (Hashtbl.mem streamed objective) then begin
      Hashtbl.replace streamed objective ();
      (* Solve a newly available leaf immediately. UNSAT/UNKNOWN is provisional
         because another dynamic instance of the same source outcome may be
         discovered later; SAT is already safe after concrete replay. *)
      match lease [objective] with
      | [] -> ()
      | claimed ->
        Fun.protect ~finally:(fun () -> release claimed) (fun () ->
          solve_group ~list_bound:0 ~finalize_failures:false solver_timeout_ms
            claimed)
    end
  in
  Printexc.record_backtrace true;
  begin
    try
      timed "shared_compilation" objectives (fun () ->
        Verification.Z3backend.compile_reachability solver_session
          ~on_objective ~objective_of_tag ~definitions body)
    with
    | Stack_overflow ->
      Message.warning "BOBCat shared compilation exhausted the OCaml stack:\n%s"
        (Printexc.get_backtrace ())
    | (Failure _ | Invalid_argument _ | Z3.Error _) as exn ->
      Message.warning "BOBCat shared compilation stopped: %s"
        (Printexc.to_string exn)
  end;
  List.iter
    (fun objective -> Hashtbl.replace compiled objective ())
    (Verification.Z3backend.compiled_objectives solver_session);
  List.iter
    (fun (objective, reason) ->
      if not (Hashtbl.mem compiled objective) then
        finalize objective "unknown" ["reason", `String reason])
    (Verification.Z3backend.unknown_objectives solver_session);
  List.iter
    (fun objective ->
      if not (Hashtbl.mem compiled objective)
         && not (is_final objective)
      then
        finalize objective "unknown"
          [ "reason",
            `String "objective tag has no executable guarded instance" ])
    objectives;
  let rec take n = function
    | _ when n <= 0 -> []
    | [] -> []
    | x :: xs -> x :: take (n - 1) xs
  in
  let rec cover () =
    let uncovered = pending_from objectives in
    match uncovered with
    | [] -> ()
    | _ ->
      let candidates = lease (take 8 uncovered) in
      if candidates = [] then ()
      else begin
        Fun.protect ~finally:(fun () -> release candidates) (fun () ->
          if !divergences >= max_divergences then
            List.iter
              (fun objective ->
                finalize objective "unknown"
                  [ "reason",
                    `String "concrete replay divergence budget exhausted" ])
              candidates
          else
            solve_group ~list_bound:0 ~finalize_failures:true solver_timeout_ms
              candidates);
        cover ()
      end
  in
  cover ();
  ()
  in
  run_worker 0;
  List.iter
    (fun objective ->
      if not (is_final objective) then
        finalize objective "unknown"
          ["reason", `String "objective was not classified"])
    objectives;
  synchronized output_mutex (fun () ->
    Message.result "BOBCAT_DONE %d" (List.length objectives);
    Format.pp_print_flush Format.std_formatter ())

let interpret_program_concolic
    (type m)
    (print_stats : bool)
    (optims : Optimizations.flag list)
    (mutation_seed : int option)
    (max_list_length : int)
    (code_coverage : bool)
    (coverage_priority_burst : int)
    (p : (dcalc, m) gexpr program)
    s : (Uid.MarkedString.info * conc_expr) list =
  Message.debug "=== Start concolic interpretation... ===";
  if max_list_length < 0 then
    Message.error "The maximum concolic list length must be non-negative";
  if coverage_priority_burst < 0 then
    Message.error "The coverage-priority burst must be non-negative";
  Optimizations.check_optims_coherent optims;

  (* output_name, out_fmt : string * Format.formatter) *)
  let stats = Stats.init () in

  let s_context_creation = Stats.start_step "create context" in
  let decl_ctx = p.decl_ctx in
  Message.debug "[CONC] Create empty context";
  let ctx = make_empty_context decl_ctx optims max_list_length in
  Message.debug "[CONC] Initialize context";
  let ctx = init_context ctx in
  let stats = Stats.stop_step s_context_creation |> Stats.add_stat_step stats in

  let s_simplify = Stats.start_step "simplify" in
  let scope_e = simplify_program ctx p s in

  let ast_stats = Mutation.get_stats scope_e in

  if Optimizations.mutation optims then Mutation.init mutation_seed;

  let scope_e =
    if Optimizations.random_mutations optims then begin
      let mutations =
        List.filter_map
          (fun (o, f, p) -> if o optims then Some (f, p) else None)
          [
            Optimizations.mutation_remove, Mutation.remove_excepts 0.3, 0.3;
            Optimizations.mutation_duplicate, Mutation.duplicate_excepts, 0.3;
            Optimizations.mutation_negate_justs, Mutation.negate_justs, 0.1;
          ]
      in

      Message.debug "Before random mutations:\n%a" (Print.expr ()) scope_e;
      let mutated_scope_e =
        Mutation.apply_mutations mutations scope_e |> Expr.unbox
      in

      Message.debug "\nAfter random mutations:\n%a" (Print.expr ())
        mutated_scope_e;
      mutated_scope_e
    end
    else if Optimizations.mutation_one_conflict optims then begin
      Message.debug "Before one mutation:\n%a" (Print.expr ()) scope_e;
      let mutated_scope_e =
        Mutation.create_one_conflict scope_e |> Expr.unbox
      in

      Message.debug "\nAfter one mutation:\n%a" (Print.expr ()) mutated_scope_e;
      mutated_scope_e
    end
    else scope_e
  in

  let scope_e = Optimizations.optimize_expr optims scope_e in

  if code_coverage then index_source_branches ctx scope_e;

  if Optimizations.ast_stats optims then begin
    Message.result "%a" Mutation.pprint_ast_stats (Mutation.get_stats scope_e);
    exit 0
  end;

  let stats = Stats.stop_step s_simplify |> Stats.add_stat_step stats in
  match scope_e with
  | EAbs { tys = [((TStruct s_in, _) as _targs)]; _ }, mark_e -> begin
    (* [taus] contain the types of the scope arguments. For [context] arguments,
       we can provide an empty thunked term. For [input] arguments of another
       type, we provide an empty value. *)
    (* first set of inputs *)
    let taus = StructName.Map.find s_in ctx.ctx_decl.ctx_structs in

    (* TODO CONC should it be [mark_e] or something else? *)
    let input_marks = StructField.Map.mapi (make_input_mark ctx mark_e) taus in
    let date_boundaries = source_date_boundaries scope_e in
    let date_symbols = input_date_symbols ctx input_marks in
    let hard_constraints = ref (make_list_bounds ctx input_marks) in
    let soft_constraints =
      if Optimizations.soft_constraints optims then
        make_soft_constraints ctx input_marks
      else []
    in

    Message.debug "Initial soft constraints: %a\n"
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ")
         PathConstraint.Print.pc_expr)
      soft_constraints;

    let total_tests = ref 0 in

    let branch_manifest =
      Hashtbl.fold
        (fun _ pair pairs -> pair :: pairs)
        ctx.ctx_branch_pairs []
      |> List.sort_uniq String.compare
    in
    if code_coverage then
      print_json_string_list "CONCOLIC_BRANCH_MANIFEST" branch_manifest;

    let module Solver = Solver (struct
      let optims = optims
    end) in
    (* add soft constraints to solver if it is incremental *)
    List.iter (Solver.push ctx)
      (append_constraints !hard_constraints soft_constraints);

    let rebuild_incremental_solver path =
      Solver.reset ();
      hard_constraints := make_list_bounds ctx input_marks;
      List.iter (Solver.push ctx)
        (concat_constraints
           [!hard_constraints; soft_constraints; constraint_list_of_path ctx path])
    in

    let found_incomplete = ref false in
    let covered_outcomes = Hashtbl.create 257 in
    let scheduler =
      PathConstraint.Scheduler.create
        ~priority_burst:coverage_priority_burst
    in
    let is_novel pc =
      match PathConstraint.origin pc with
      | None -> false
      | Some origin ->
        List.exists
          (fun outcome -> not (Hashtbl.mem covered_outcomes outcome))
          origin.may_reach_when_flipped
    in
    let record_covered_outcomes () =
      Hashtbl.iter
        (fun outcome () -> Hashtbl.replace covered_outcomes outcome ())
        ctx.ctx_branch_hits
    in
    let report_branch_progress stats path_index =
      if code_coverage then
        Message.result "CONCOLIC_BRANCH_PROGRESS %d %.6f %d %d" path_index
          (Stats.elapsed stats)
          (Hashtbl.length covered_outcomes)
          (List.length branch_manifest)
    in
    let validate_prediction candidate =
      match PathConstraint.origin (PathConstraint.Scheduler.pc candidate) with
      | None -> ()
      | Some origin ->
        let observed = sorted_table_keys ctx.ctx_branch_hits in
        if origin.may_reach_when_flipped <> []
           && not
                (List.exists
                   (fun outcome -> Hashtbl.mem ctx.ctx_branch_hits outcome)
                   origin.may_reach_when_flipped)
        then begin
          found_incomplete := true;
          Message.warning
            "Coverage-directed prediction for %s did not match concrete replay. \
             Predicted one of [%s], observed [%s]; retaining the test and \
             continuing with concrete coverage."
            origin.decision_id
            (String.concat ", " origin.may_reach_when_flipped)
            (String.concat ", " observed)
        end
    in

    let rec continue_with_next current exec stats =
      let s_new_pc = Stats.start_step "choose new path constraints" in
      let coverage_saturated =
        code_coverage
        && Hashtbl.length covered_outcomes >= List.length branch_manifest
      in
      let next =
        if coverage_saturated then begin
          Message.debug
            "All source branch outcomes are covered; stopping bounded search";
          None
        end
        else PathConstraint.Scheduler.next scheduler ~is_novel
      in
      let exec = Stats.stop_step s_new_pc |> Stats.add_exec_step exec in
      let s_diff = Stats.start_step "apply diff" in
      Option.iter
        (fun next ->
          PathConstraint.Scheduler.switch_diff current next
          |> apply_diff ctx Solver.push Solver.pop)
        next;
      let exec = Stats.stop_step s_diff |> Stats.add_exec_step exec in
      let stats = Stats.stop_exec exec |> Stats.add_stat_exec stats in
      match next with
      | None -> stats
      | Some next -> concolic_loop (Some next) stats

    and concolic_loop
        (current : PathConstraint.Scheduler.candidate option)
        stats : Stats.t =
      let previous_path =
        Option.fold ~none:[] ~some:PathConstraint.Scheduler.annotated_path
          current
      in
      if Optimizations.tests_vs_time optims then
        Message.result "time of step: %a" Stats.Print.period
          (Stats.running_period stats);
      let exec = Stats.start_exec (List.length previous_path) in
      let s_print_pc = Stats.start_step "print path constraints" in
      Message.debug "";

      Message.debug "Trying new path constraints:@ @[<v>%a@]"
        PathConstraint.Print.annotated_path previous_path;
      let exec = Stats.stop_step s_print_pc |> Stats.add_exec_step exec in
      let s_extract_constraints =
        Stats.start_step "extract solver constraints"
      in
      let solver_constraints = constraint_list_of_path ctx previous_path in
      let solver_constraints =
        concat_constraints
          [!hard_constraints; soft_constraints; solver_constraints]
      in
      let exec =
        Stats.stop_step s_extract_constraints |> Stats.add_exec_step exec
      in

      let s_solve = Stats.start_step "solve" in
      let solver_result = Solver.solve ctx solver_constraints in
      let exec = Stats.stop_step s_solve |> Stats.add_exec_step exec in

      match solver_result with
      | Solver.Sat (Some m) ->
        Message.debug "Solver returned a model";

        Message.debug "model:\n%s" (Solver.string_of_model m);

        let s_inputs = Stats.start_step "get inputs from model" in
        let inputs = Solver.inputs_of_model ctx m input_marks in

        if not Global.options.debug then Message.result "";
        if Optimizations.tests_vs_time optims then
          Message.result "time of test: %a" Stats.Print.period
            (Stats.running_period stats);
        Message.result "Evaluating with inputs:";
        let inputs_list =
          List.map
            (fun (fld, e) -> StructField.get_info fld, Expr.unbox e)
            (StructField.Map.bindings inputs)
        in
        print_fields ". " inputs_list;

        let exec = Stats.stop_step s_inputs |> Stats.add_exec_step exec in

        let s_eval = Stats.start_step "eval" in
        Hashtbl.clear ctx.ctx_lengths_demanded;
        Hashtbl.clear ctx.ctx_list_length_guards;
        Hashtbl.clear ctx.ctx_branch_hits;
        let res =
          try
            Ok (eval_conc_with_input ctx p.lang s_in scope_e mark_e inputs)
          with
          | Stack_overflow ->
            Error "concrete evaluation exhausted the OCaml stack"
          | (Runtime.Error _ | Failure _ | Invalid_argument _ | Z3.Error _)
              as exn ->
            Error (Printexc.to_string exn)
        in
        let exec = Stats.stop_step s_eval |> Stats.add_exec_step exec in

        begin match res with
        | Error message ->
          found_incomplete := true;
          Message.result "Output of scope after evaluation:";
          Message.result "Found error internal concolic failure: %s at %s"
            message (Pos.to_string_short (Expr.pos scope_e));
          if code_coverage then
            print_json_string_list
              (Printf.sprintf "CONCOLIC_BRANCH_PATH %d" !total_tests)
              (sorted_table_keys ctx.ctx_branch_hits);
          incr total_tests;
          record_covered_outcomes ();
          report_branch_progress stats (!total_tests - 1);
          Message.warning
            "Concolic evaluation failed for one candidate (%s); retaining its \
             concrete branch trace and continuing with the remaining worklist."
            message;
          continue_with_next current exec stats
        | Ok res ->
        Message.result "Output of scope after evaluation:";

        begin match Mark.remove res with
        | EStruct { fields; _ } ->
          let outputs_list =
            List.map
              (fun (fld, e) -> StructField.get_info fld, e)
              (StructField.Map.bindings fields)
          in
          print_fields ". " outputs_list
        | EGenericError ->
          (* TODO better error messages *)
          (* TODO test the different cases *)
          Message.result "Found error %a at %s" SymbExpr.formatter
            (get_symb_expr_r res)
            (Pos.to_string_short (Expr.pos res))
        | _ ->
          Message.error ~pos:(Expr.pos scope_e)
            "The concolic interpretation of a program should always yield a \
             struct corresponding to the scope variables"
        end;
        if code_coverage then
          print_json_string_list
            (Printf.sprintf "CONCOLIC_BRANCH_PATH %d" !total_tests)
            (sorted_table_keys ctx.ctx_branch_hits);
        incr total_tests;
        record_covered_outcomes ();
        report_branch_progress stats (!total_tests - 1);
        Option.iter validate_prediction current;

        let incomplete =
          List.exists PathConstraint.is_incomplete (get_constraints_r res)
        in

        if incomplete then begin
          found_incomplete := true;
          Message.warning
            "Concolic evaluation found an expression that cannot be encoded (a \
             list or a date). The current\n\
            \                           path will be dropped.";
          continue_with_next current exec stats
        end
        else begin
          let res_path_constraints = get_constraints_r res in

          let res_path_constraints =
            Optimizations.remove_trivial_constraints optims res_path_constraints
          in

          Message.debug "Path constraints after evaluation:@.@[<v>%a@]"
            PathConstraint.Print.naked_path res_path_constraints;

          let concrete_path = List.rev res_path_constraints in
          let requested_flip_was_observed candidate =
            let requested = PathConstraint.Scheduler.pc candidate in
            List.exists
              (fun observed ->
                PathConstraint.path_constraint_same_site requested observed
                && requested.branch <> observed.branch)
              concrete_path
          in
          begin match PathConstraint.compare_paths previous_path concrete_path with
          | None
            when Option.fold ~none:false
                   ~some:(fun candidate ->
                     not (PathConstraint.Scheduler.synthetic candidate)
                     && not (requested_flip_was_observed candidate))
                   current ->
            found_incomplete := true;
            Message.warning
              "Concrete execution diverged from the predicted symbolic path; \
               keeping this test and dropping the stale candidate.";
          | None | Some _ -> ()
          end;
          PathConstraint.Scheduler.observe scheduler ~from:current ~is_novel
            ~seeds:(temporal_seeds ctx date_symbols date_boundaries)
            concrete_path;
          continue_with_next current exec stats
        end
        end
      | Solver.Unsat -> begin
        Message.debug "Solver returned Unsat";
        match current with
        | None -> failwith "[CONC] Failed to solve without constraints"
        | Some candidate
          when Option.fold ~none:false ~some:(request_list_growth ctx)
                 (PathConstraint.growth_request
                    (PathConstraint.Scheduler.pc candidate)) ->
          Message.debug "Growing symbolic list and restarting DFS from root";
          (* Materialising a new element can introduce an earlier decision or
             change short-circuit evaluation, so every annotation in the old
             traversal belongs to an obsolete path tree. Start a fresh DFS
             under the enlarged bounds instead of replaying that path. *)
          PathConstraint.Scheduler.reset scheduler;
          rebuild_incremental_solver [];
          concolic_loop None stats
        | Some _ ->
          (* add empty steps for stats *)
          let exec =
            Stats.start_step "get inputs from model"
            |> Stats.stop_step
            |> Stats.add_exec_step exec
          in
          let exec =
            Stats.start_step "eval"
            |> Stats.stop_step
            |> Stats.add_exec_step exec
          in
          continue_with_next current exec stats
      end
      | Solver.Sat None ->
        failwith "[CONC] Constraints satisfiable but no model was produced"
      | Solver.Unknown info ->
        found_incomplete := true;
        Message.warning
          "Z3 returned unknown for one concolic candidate; dropping that \
           candidate and continuing. Debug info:@.%a@."
          Solver.fmt_unknown_info info;
        continue_with_next current exec stats
      | Solver.SolverTimeout ->
        found_incomplete := true;
        Message.warning
          "Z3 timed out for one concolic candidate; dropping that candidate \
           and continuing with the remaining worklist.";
        continue_with_next current exec stats
    in

    let s_loop = Stats.start_step "total loop time" in
    let stats = concolic_loop None stats in
    let stats = Stats.stop_step s_loop |> Stats.add_stat_step stats in
    Message.result "";

    Message.result "Concolic interpreter done";
    if !found_incomplete then
      Message.warning
        "Please note that the concolic execution may be incomplete: it could \
         systematically explore the whole program.";

    let stats = Stats.stop stats in
    if print_stats then
      Message.result
        "=== Concolic execution statistics ===\n%a\n%d tests\n%s%s======"
        Stats.print stats !total_tests
        (* FIXME ugly *)
        (if Optimizations.soft_constraints optims then
           "Soft constraints:\n"
           ^ "  "
           ^ string_of_int !Solver.num_unsat
           ^ " hard unsat\n"
           ^ "  "
           ^ string_of_int !Solver.num_soft_unsat
           ^ " soft unsat\n"
           ^ "  "
           ^ string_of_int !Solver.num_soft_sat
           ^ " soft sat\n"
           ^ "  "
           ^ Solver.print_soft_sats ()
           ^ "\n"
           ^ "  "
           ^ Solver.print_soft_unsats ()
           ^ "\n"
         else "")
        (if Optimizations.mutation optims then
           "Mutations:\n"
           ^ "  out of "
           ^ string_of_int ast_stats.defaults
           ^ " defaults"
           ^ " ("
           ^ string_of_int ast_stats.defaults_with_excepts
           ^ " non-empty)"
           ^ " and "
           ^ string_of_int (List.fold_left ( + ) 0 ast_stats.excepts_sizes)
           ^ " excepts...\n"
           ^ "  "
           ^ string_of_int !Mutation.remove_excepts_n
           ^ " excepts removed\n"
           ^ "  "
           ^ string_of_int !Mutation.duplicate_excepts_n
           ^ " excepts duplicated\n"
           ^ "  "
           ^ string_of_int !Mutation.negate_justs_n
           ^ " justs negated\n"
         else "");
    (* XXX BROKEN output *)
    []
  end
  | _ ->
    Message.error ~pos:(Expr.pos scope_e)
      "The interpreter can only interpret terms starting with functions having \
       thunked arguments"
