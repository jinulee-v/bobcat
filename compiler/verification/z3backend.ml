(* This file is part of the Catala compiler, a specification language for tax
   and social benefits computation rules. Copyright (C) 2022 Inria, contributor:
   Aymeric Fromherz <aymeric.fromherz@inria.fr>

   Licensed under the Apache License, Version 2.0 (the "License"); you may not
   use this file except in compliance with the License. You may obtain a copy of
   the License at

   http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
   License for the specific language governing permissions and limitations under
   the License. *)

open Catala_utils
open Shared_ast
open Dcalc
open Ast
open Z3
module StringMap = String.Map
module Runtime = Catala_runtime

type array_encoding = {
  array_sort : Sort.sort;
  array_make : FuncDecl.func_decl;
  array_length : FuncDecl.func_decl;
  array_elements : FuncDecl.func_decl list;
}

module ExpressionIdentity = Hashtbl.Make(struct
  type t = typed expr
  let equal a b = a == b
  let hash e =
    let pos = Shared_ast.Expr.pos e in
    let variable = match Mark.remove e with EVar v -> Bindlib.uid_of v | _ -> -1 in
    Hashtbl.hash (Pos.get_file pos, Pos.get_start_line pos,
                  Pos.get_start_column pos, Pos.get_end_line pos, variable)
end)

type named_function_type = FunctionStruct of StructName.t | FunctionEnum of EnumName.t

type context = {
  ctx_z3 : Z3.context;
  (* The Z3 context, used to create symbols and expressions *)
  ctx_decl : decl_ctx;
  ctx_function_types : (named_function_type, unit) Hashtbl.t;
  (* The declaration context from the Catala program, containing information to
     precisely pretty print Catala expressions *)
  ctx_funcdecl : (typed expr, FuncDecl.func_decl) Var.Map.t;
  (* A map from Catala function names (represented as variables) to Z3 function
     declarations, used to only define once functions in Z3 queries *)
  ctx_z3vars : (typed expr Var.t * typ) StringMap.t;
  (* A map from strings, corresponding to Z3 symbol names, to the Catala
     variable they represent. Used when to pretty-print Z3 models when a
     counterexample is generated *)
  ctx_z3datatypes : Sort.sort EnumName.Map.t;
  (* A map from Catala enumeration names to the corresponding Z3 sort, from
     which we can retrieve constructors and accessors *)
  ctx_z3matchsubsts : (typed expr, Expr.expr) Var.Map.t;
  (* A map from Catala temporary variables, generated when translating a match,
     to the corresponding enum accessor call as a Z3 expression *)
  ctx_z3structs : Sort.sort StructName.Map.t;
  (* A map from Catala struct names to the corresponding Z3 sort, from which we
     can retrieve the constructor and the accessors *)
  ctx_z3types : (int * Sort.sort) list;
  ctx_head_values : (int, typed expr * typed expr * (typed expr, typed expr) Var.Map.t) Hashtbl.t;
  ctx_z3unit : Sort.sort * Expr.expr;
  ctx_z3duration : Sort.sort;
  ctx_z3defaults :
    (Sort.sort * FuncDecl.func_decl * FuncDecl.func_decl list) StringMap.t;
  ctx_z3options : Sort.sort StringMap.t;
  ctx_z3arrays : array_encoding StringMap.t;
  ctx_z3tuples : Sort.sort StringMap.t;
  ctx_max_list_length : int;
  ctx_symbolic_list_bound : int;
  ctx_allow_fatal_dummy : bool;
  ctx_z3definitions : (typed expr, typed expr) Var.Map.t;
  ctx_z3valuecache :
    (typed expr, Expr.expr * Expr.expr list) Var.Map.t;
  (* Shared translations of named value definitions. The saved constraints
     are reintroduced at each guarded use, so caching preserves both DAG
     sharing and the guard under which partial operations are valid. *)
  ctx_capacity_limited : bool ref;
  ctx_z3bounds : (int, int) Hashtbl.t;
  ctx_calendar_pending : Expr.expr list ref;
  ctx_environment_ids : (string, int) Hashtbl.t;
  ctx_expression_ids : int ExpressionIdentity.t;
  ctx_pending_relations : (Expr.expr * Expr.expr list * (context -> context * Expr.expr list)) Queue.t;
  ctx_abstract_symbols : (int, unit) Hashtbl.t;
  ctx_relation_graph : (int, int list list) Hashtbl.t;
  ctx_abstract_calls : (string, Expr.expr * Expr.expr) Hashtbl.t;
  ctx_lazy_relations : bool;
  ctx_summary_cache : (string, Expr.expr * Expr.expr * int * Expr.expr list) Hashtbl.t;
  ctx_z3resolving : (typed expr) Var.Set.t;
  (* Definitions are followed by [translate_expr]. This set rejects an
     accidental recursive definition instead of silently replacing it with an
     unconstrained Z3 constant. Catala programs are recursion-free. *)
  ctx_z3freevars : (typed expr) Var.Set.t;
  (* Variables which genuinely denote symbolic inputs. In BOBCat direct mode,
     every other unresolved variable is a malformed encoding, not a license to
     invent an unconstrained value. *)
  (* Lifted default values are encoded as
     [Default(defined, conflict, value)].  Keeping this distinct from the
     underlying value is what lets BOBCat reason about EEmpty,
     EPureDefault, ordered exceptions, and ErrorOnEmpty instead of either
     rejecting them or silently treating an empty value as an arbitrary one. *)
  (* A pair containing the Z3 encodings of the unit type, encoded as a tuple of
     0 elements, and the unit value *)
  ctx_z3constraints : Expr.expr list;
      (* A list of constraints about the created Z3 expressions accumulated
         during their initialization, for instance, that the length of an array
         is an integer which always is greater than 0 *)
}
(** The context contains all the required information to encode a VC represented
    as a Catala term to Z3. The field [ctx_decl] is computed before starting the
    translation to Z3, and are thus unmodified throughout the translation. The
    [ctx_z3] context is an OCaml abstraction on top of an underlying C++
    imperative implementation, it is therefore only created once. Unfortunately,
    the maps [ctx_funcdecl], [ctx_z3vars], [ctx_z3datatypes],
    [ctx_z3matchsubsts], [ctx_z3structs], and [ctx_z3constraints] are computed
    dynamically during the translation requiring us to pass the context around
    in a functional way **)

(** [add_funcdecl] adds the mapping between the Catala variable [v] and the Z3
    function declaration [fd] to the context **)
let add_funcdecl
    (v : typed expr Var.t)
    (fd : FuncDecl.func_decl)
    (ctx : context) : context =
  { ctx with ctx_funcdecl = Var.Map.add v fd ctx.ctx_funcdecl }

(** [add_z3var] adds the mapping between [name] and the Catala variable [v] and
    its typ [ty] to the context **)
let add_z3var (name : string) (v : typed expr Var.t) (ty : typ) (ctx : context)
    : context =
  { ctx with ctx_z3vars = StringMap.add name (v, ty) ctx.ctx_z3vars }

(** [add_z3enum] adds the mapping between the Catala enumeration [enum] and the
    corresponding Z3 datatype [sort] to the context **)
let add_z3enum (enum : EnumName.t) (sort : Sort.sort) (ctx : context) : context
    =
  { ctx with ctx_z3datatypes = EnumName.Map.add enum sort ctx.ctx_z3datatypes }

let rec known_value_bound ctx value =
  match Hashtbl.find_opt ctx.ctx_z3bounds (Z3.AST.get_id (Expr.ast_of_expr value)) with
  | Some bound -> Some bound
  | None when Z3.AST.get_ast_kind (Expr.ast_of_expr value) = Z3enums.APP_AST
      && FuncDecl.get_decl_kind (Expr.get_func_decl value) = Z3enums.OP_DT_ACCESSOR ->
    begin match Expr.get_args value with
    | [parent] -> known_value_bound ctx parent
    | _ -> None
    end
  | None -> None

(** [add_z3matchsubst] adds the mapping between temporary variable [v] and the
    Z3 expression [e] representing an accessor application to the context **)
let add_z3matchsubst (v : typed expr Var.t) (e : Expr.expr) (ctx : context) :
    context =
  Option.iter (fun bound ->
    Hashtbl.replace ctx.ctx_z3bounds (Z3.AST.get_id (Expr.ast_of_expr e)) bound)
    (known_value_bound ctx e);
  { ctx with ctx_z3matchsubsts = Var.Map.add v e ctx.ctx_z3matchsubsts }

(** [add_z3struct] adds the mapping between the Catala struct [s] and the
    corresponding Z3 datatype [sort] to the context **)
let add_z3struct (s : StructName.t) (sort : Sort.sort) (ctx : context) : context
    =
  { ctx with ctx_z3structs = StructName.Map.add s sort ctx.ctx_z3structs }

let add_z3constraint (e : Expr.expr) (ctx : context) : context =
  { ctx with ctx_z3constraints = e :: ctx.ctx_z3constraints }

(** For the Z3 encoding of Catala programs, we define the "day 0" as Jan 1, 1900
    **)
let base_day = Runtime.date_of_numbers 1900 1 1

(** [unique_name] returns the full, unique name corresponding to variable [v],
    as given by Bindlib **)
let unique_name (v : 'e Var.t) : string =
  Format.asprintf "%s_%d" (Bindlib.name_of v) (Bindlib.uid_of v)

(** [date_to_int] translates [date] to an integer corresponding to the number of
    days since Jan 1, 1900 **)
let date_to_int (d : Runtime.date) : int =
  (* Alternatively, could expose this from Runtime as a (noop) coercion, but
     would allow to break abstraction more easily elsewhere *)
  let period = Runtime.Oper.o_sub_dat_dat d base_day in
  let y, m, d = Runtime.duration_to_years_months_days period in
  assert (y = 0 && m = 0);
  d

module DateEncoding = struct
  let int ctx n = Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 n
  let add ctx xs = Arithmetic.mk_add ctx.ctx_z3 xs
  let sub ctx xs = Arithmetic.mk_sub ctx.ctx_z3 xs
  let mul ctx xs = Arithmetic.mk_mul ctx.ctx_z3 xs
  let div ctx a b = Arithmetic.mk_div ctx.ctx_z3 a b
  let modulo ctx a b = Arithmetic.Integer.mk_mod ctx.ctx_z3 a b
  let ite ctx c a b = Boolean.mk_ite ctx.ctx_z3 c a b

  (* Howard Hinnant's proleptic-Gregorian civil/serial conversion.  BOBCat's
     integer date zero is 1900-01-01, whose absolute civil day is 693901. *)
  let civil_to_date ctx year month day =
    let year =
      sub ctx
        [ year;
          ite ctx (Arithmetic.mk_le ctx.ctx_z3 month (int ctx 2))
            (int ctx 1) (int ctx 0) ]
    in
    let era = div ctx year (int ctx 400) in
    let yoe = sub ctx [year; mul ctx [era; int ctx 400]] in
    let mp =
      add ctx
        [ month;
          ite ctx (Arithmetic.mk_gt ctx.ctx_z3 month (int ctx 2))
            (int ctx (-3)) (int ctx 9) ]
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
          Arithmetic.mk_unary_minus ctx.ctx_z3 (div ctx yoe (int ctx 100));
          doy ]
    in
    sub ctx [add ctx [mul ctx [era; int ctx 146097]; doe]; int ctx 693901]

  let is_leap ctx year =
    let eq0 x = Boolean.mk_eq ctx.ctx_z3 x (int ctx 0) in
    Boolean.mk_or ctx.ctx_z3
      [ eq0 (modulo ctx year (int ctx 400));
        Boolean.mk_and ctx.ctx_z3
          [ eq0 (modulo ctx year (int ctx 4));
            Boolean.mk_not ctx.ctx_z3
              (eq0 (modulo ctx year (int ctx 100))) ] ]

  let days_in_month ctx year month =
    let eq n = Boolean.mk_eq ctx.ctx_z3 month (int ctx n) in
    ite ctx (eq 2) (ite ctx (is_leap ctx year) (int ctx 29) (int ctx 28))
      (ite ctx
         (Boolean.mk_or ctx.ctx_z3 [eq 4; eq 6; eq 9; eq 11])
         (int ctx 30) (int ctx 31))

  let valid_ymd ctx year month day =
    Boolean.mk_and ctx.ctx_z3
      [ Arithmetic.mk_ge ctx.ctx_z3 month (int ctx 1);
        Arithmetic.mk_le ctx.ctx_z3 month (int ctx 12);
        Arithmetic.mk_ge ctx.ctx_z3 day (int ctx 1);
        Arithmetic.mk_le ctx.ctx_z3 day (days_in_month ctx year month) ]

  let date_to_civil ctx date =
    (* Exact ground instances of canonical calendar coordinates. The function
       applications remain substitutable in reusable symbolic templates. *)
    let integer = Arithmetic.Integer.mk_sort ctx.ctx_z3 in
    let coordinate name =
      let fn = FuncDecl.mk_func_decl_s ctx.ctx_z3 name [integer] integer in
      Expr.mk_app ctx.ctx_z3 fn [date] in
    let year = coordinate "bobcat_calendar_year" in
    let month = coordinate "bobcat_calendar_month" in
    let day = coordinate "bobcat_calendar_day" in
    let relation = Boolean.mk_and ctx.ctx_z3
        [valid_ymd ctx year month day;
         Boolean.mk_eq ctx.ctx_z3 date (civil_to_date ctx year month day)] in
    ctx.ctx_calendar_pending := relation :: !(ctx.ctx_calendar_pending);
    year, month, day

  let duration_parts ctx duration =
    match Tuple.get_field_decls ctx.ctx_z3duration with
    | [years; months; days] ->
      let get accessor = Expr.mk_app ctx.ctx_z3 accessor [duration] in
      get years, get months, get days
    | _ -> assert false

  let make_duration ctx years months days =
    Expr.mk_app ctx.ctx_z3 (Tuple.get_mk_decl ctx.ctx_z3duration)
      [years; months; days]

  let requires_rounding ctx date duration =
    let years, months, _ = duration_parts ctx duration in
    let year, month, day = date_to_civil ctx date in
    let total_month = add ctx [month; months; int ctx (-1)] in
    let new_year = add ctx [year; years; div ctx total_month (int ctx 12)] in
    let new_month = add ctx [modulo ctx total_month (int ctx 12); int ctx 1] in
    Arithmetic.mk_gt ctx.ctx_z3 day (days_in_month ctx new_year new_month)

  let add_dat_dur ctx round date duration =
    let years, months, days = duration_parts ctx duration in
    let year, month, day = date_to_civil ctx date in
    let total_month = add ctx [month; months; int ctx (-1)] in
    let new_year = add ctx [year; years; div ctx total_month (int ctx 12)] in
    let new_month = add ctx [modulo ctx total_month (int ctx 12); int ctx 1] in
    let last = days_in_month ctx new_year new_month in
    let invalid = Arithmetic.mk_gt ctx.ctx_z3 day last in
    let rounded_year, rounded_month, rounded_day =
      match round with
      | Dates_calc.RoundDown | Dates_calc.AbortOnRound ->
        new_year, new_month, ite ctx invalid last day
      | Dates_calc.RoundUp ->
        let next_total = new_month in
        ( ite ctx invalid
            (add ctx [new_year; div ctx next_total (int ctx 12)]) new_year,
          ite ctx invalid
            (add ctx [modulo ctx next_total (int ctx 12); int ctx 1]) new_month,
          ite ctx invalid (int ctx 1) day )
    in
    add ctx [civil_to_date ctx rounded_year rounded_month rounded_day; days]

  let minus_dur ctx duration =
    let years, months, days = duration_parts ctx duration in
    make_duration ctx
      (Arithmetic.mk_unary_minus ctx.ctx_z3 years)
      (Arithmetic.mk_unary_minus ctx.ctx_z3 months)
      (Arithmetic.mk_unary_minus ctx.ctx_z3 days)

  let add_dur_dur ctx left right =
    let ly, lm, ld = duration_parts ctx left in
    let ry, rm, rd = duration_parts ctx right in
    make_duration ctx (add ctx [ly; ry]) (add ctx [lm; rm]) (add ctx [ld; rd])

  let sub_dur_dur ctx left right = add_dur_dur ctx left (minus_dur ctx right)
  let sub_dat_dat ctx left right =
    make_duration ctx (int ctx 0) (int ctx 0) (sub ctx [left; right])

  let mult_dur_int ctx duration factor =
    let years, months, days = duration_parts ctx duration in
    make_duration ctx (mul ctx [years; factor]) (mul ctx [months; factor])
      (mul ctx [days; factor])

  let duration_comparison ctx comparison left right =
    let ly, lm, ld = duration_parts ctx left in
    let ry, rm, rd = duration_parts ctx right in
    let zero = int ctx 0 in
    let eq0 value = Boolean.mk_eq ctx.ctx_z3 value zero in
    let calendar_mode = Boolean.mk_and ctx.ctx_z3 [eq0 ld; eq0 rd] in
    let day_mode =
      Boolean.mk_and ctx.ctx_z3 [eq0 ly; eq0 lm; eq0 ry; eq0 rm]
    in
    let valid = Boolean.mk_or ctx.ctx_z3 [calendar_mode; day_mode] in
    let months years months = add ctx [mul ctx [int ctx 12; years]; months] in
    let calendar_result = comparison (months ly lm) (months ry rm) in
    let day_result = comparison ld rd in
    valid, ite ctx calendar_mode calendar_result day_result

  let duration_equality ctx left right =
    let structural = Boolean.mk_eq ctx.ctx_z3 left right in
    let comparable, numerical =
      duration_comparison ctx (Boolean.mk_eq ctx.ctx_z3) left right
    in
    ( Boolean.mk_or ctx.ctx_z3 [structural; comparable],
      Boolean.mk_or ctx.ctx_z3 [structural; numerical] )

  let div_dur_dur ctx left right =
    let ly, lm, ld = duration_parts ctx left in
    let ry, rm, rd = duration_parts ctx right in
    let zero = int ctx 0 in
    let eq0 value = Boolean.mk_eq ctx.ctx_z3 value zero in
    let valid =
      Boolean.mk_and ctx.ctx_z3
        [eq0 ly; eq0 lm; eq0 ry; eq0 rm;
         Boolean.mk_not ctx.ctx_z3 (eq0 rd)]
    in
    let numerator = Arithmetic.Integer.mk_int2real ctx.ctx_z3 ld in
    valid, Arithmetic.mk_div ctx.ctx_z3 numerator rd
end

let z3_round ctx value =
  let zero = Arithmetic.Real.mk_numeral_i ctx.ctx_z3 0 in
  let half = Arithmetic.Real.mk_numeral_nd ctx.ctx_z3 1 2 in
  let positive = Arithmetic.mk_ge ctx.ctx_z3 value zero in
  let round_positive =
    Arithmetic.Real.mk_real2int ctx.ctx_z3
      (Arithmetic.mk_add ctx.ctx_z3 [value; half])
  in
  let round_negative =
    Arithmetic.mk_unary_minus ctx.ctx_z3
      (Arithmetic.Real.mk_real2int ctx.ctx_z3
         (Arithmetic.mk_add ctx.ctx_z3
            [Arithmetic.mk_unary_minus ctx.ctx_z3 value; half]))
  in
  Boolean.mk_ite ctx.ctx_z3 positive round_positive round_negative

let z3_force_real ctx value =
  Arithmetic.Integer.mk_int2real ctx.ctx_z3 value

(** [date_of_year] translates a [year], represented as an integer into an OCaml
    date corresponding to Jan 1st of the same year *)
let _date_of_year (year : int) = Runtime.date_of_numbers year 1 1

(** Returns the date (as a string) corresponding to nb days after the base day,
    defined here as Jan 1, 1900 **)
let nb_days_to_date (nb : int) : string =
  let dummy_pos =
    {
      Runtime.filename = "";
      start_line = 0;
      start_column = 0;
      end_line = 0;
      end_column = 0;
      law_headings = [];
    }
  in
  Runtime.date_to_string
    (Runtime.Oper.o_add_dat_dur AbortOnRound dummy_pos base_day
       (Runtime.duration_of_numbers 0 0 nb))

(** [print_z3model_expr] pretty-prints the value [e] given by a Z3 model
    according to the Catala type [ty], corresponding to [e] **)
let rec print_z3model_expr (ctx : context) (ty : typ) (e : Expr.expr) : string =
  let print_lit (ty : typ_lit) =
    match ty with
    (* TODO: Print boolean according to current language *)
    | TBool -> Expr.to_string e
    (* TUnit is only used for the absence of an enum constructor argument.
       Hence, when pretty-printing, we print nothing to remain closer from
       Catala sources *)
    | TUnit -> ""
    | TInt -> Expr.to_string e
    | TRat -> Arithmetic.Real.to_decimal_string e Global.options.max_prec_digits
    (* TODO: Print the right money symbol according to language *)
    | TMoney ->
      let z3_str = Expr.to_string e in
      (* The Z3 model returns an integer corresponding to the amount of cents.
         We reformat it as dollars *)
      let to_dollars s =
        Runtime.money_to_string (Runtime.money_of_cents_string s)
      in
      if String.contains z3_str '-' then
        Format.asprintf "-%s $"
          (to_dollars (String.sub z3_str 3 (String.length z3_str - 4)))
      else Format.asprintf "%s $" (to_dollars z3_str)
    (* The Z3 date representation corresponds to the number of days since Jan 1,
       1900. We pretty-print it as the actual date *)
    (* TODO: Use differnt dates conventions depending on the language ? *)
    | TDate -> nb_days_to_date (int_of_string (Expr.to_string e))
    | TDuration -> Format.asprintf "%s days" (Expr.to_string e)
    | TPos -> ""
  in

  match Mark.remove ty with
  | TLit ty -> print_lit ty
  | TStruct name ->
    let s = StructName.Map.find name ctx.ctx_decl.ctx_structs in
    let get_fieldname (fn : StructField.t) : string =
      StructField.to_string fn
    in
    let fields =
      List.map2
        (fun (fn, ty) e ->
          Format.asprintf "-- %s : %s" (get_fieldname fn)
            (print_z3model_expr ctx ty e))
        (StructField.Map.bindings s)
        (Expr.get_args e)
    in

    let fields_str = String.concat " " fields in

    Format.asprintf "%s { %s }" (StructName.base name) fields_str
  | TTuple _ ->
    failwith "[Z3 model]: Pretty-printing of unnamed structs not supported"
  | TEnum name ->
    (* The value associated to the enum is a single argument *)
    let e' = List.hd (Expr.get_args e) in
    let fd = Expr.get_func_decl e in
    let fd_name = Symbol.to_string (FuncDecl.get_name fd) in

    let enum_ctrs = EnumName.Map.find name ctx.ctx_decl.ctx_enums in
    let case =
      List.find
        (fun (ctr, _) ->
          (* FIXME: don't match on strings *)
          String.equal fd_name (EnumConstructor.to_string ctr))
        (EnumConstructor.Map.bindings enum_ctrs)
    in

    Format.asprintf "%s (%s)" fd_name (print_z3model_expr ctx (snd case) e')
  | TAbstract _ ->
    failwith "[Z3 model]: Pretty-printing of abstract types not supported"
  | TOption _ -> failwith "[Z3 model]: Pretty-printing of options not supported"
  | TArrow _ -> failwith "[Z3 model]: Pretty-printing of arrows not supported"
  | TArray _ ->
    (* For now, only the length of arrays is modeled *)
    Format.asprintf "(length = %s)" (Expr.to_string e)
  | TForAll _ | TVar _ ->
    failwith "[Z3 model]: Pretty-printing of Any not supported"
  | TClosureEnv ->
    failwith "[Z3 model]: Pretty-printing of closure_env not supported"
  | TDefault _ ->
    failwith "[Z3 model]: Pretty-printing of default terms not supported"
  | TError -> assert false

(** [print_model] pretty prints a Z3 model, used to exhibit counter examples
    where verification conditions are not satisfied. The context [ctx] is useful
    to retrieve the mapping between Z3 variables and Catala variables, and to
    retrieve type information about the variables that was lost during the
    translation (e.g., by translating a date to an integer) **)
let print_model (ctx : context) (model : Model.model) : string =
  let decls = Model.get_decls model in
  Format.asprintf "%a"
    (Format.pp_print_list
       ~pp_sep:(fun fmt () -> Format.fprintf fmt "")
       (fun fmt d ->
         if FuncDecl.get_arity d = 0 then
           (* Constant case *)
           match Model.get_const_interp model d with
           (* TODO: Better handling of this case *)
           | None ->
             failwith
               "[Z3 model]: A variable does not have an associated Z3 solution"
           (* Print "name : value\n" *)
           | Some e -> (
             let symbol_name = Symbol.to_string (FuncDecl.get_name d) in
             match StringMap.find_opt symbol_name ctx.ctx_z3vars with
             | None -> ()
             | Some (v, ty) ->
               Format.fprintf fmt "@{<blue>-->@} @{<yellow>%s@} : %s\n"
                 (Bindlib.name_of v)
                 (print_z3model_expr ctx ty e))
         else
           (* Declaration d is a function *)
           match Model.get_func_interp model d with
           (* TODO: Better handling of this case *)
           | None ->
             failwith
               "[Z3 model]: A variable does not have an associated Z3 solution"
           (* Print "name : value\n" *)
           | Some f ->
             let symbol_name = Symbol.to_string (FuncDecl.get_name d) in
             let v, _ = StringMap.find symbol_name ctx.ctx_z3vars in
             Format.fprintf fmt "@{<blue>-->@} @{<yellow>%s@} : %s\n"
               (Bindlib.name_of v)
               (* TODO: Model of a Z3 function should be pretty-printed *)
               (Model.FuncInterp.to_string f)))
    decls

let integer_string (e : Expr.expr) =
  let s = Expr.to_string e in
  let len = String.length s in
  if len > 4 && String.starts_with ~prefix:"(- " s
     && Char.equal s.[len - 1] ')'
  then "-" ^ String.sub s 3 (len - 4)
  else s

let first_n n xs =
  let rec loop n reversed = function
    | _ when n <= 0 -> List.rev reversed
    | [] -> List.rev reversed
    | x :: xs -> loop (n - 1) (x :: reversed) xs
  in
  loop n [] xs

let rational_string (e : Expr.expr) =
  let decimal () =
    let value = Arithmetic.Real.to_decimal_string e 30 |> String.trim in
    let len = String.length value in
    if len > 0 && Char.equal value.[len - 1] '?'
    then String.sub value 0 (len - 1)
    else value
  in
  let rec normalize s =
    let s = String.trim s in
    let len = String.length s in
    if len > 4 && String.starts_with ~prefix:"(- " s
       && Char.equal s.[len - 1] ')'
    then "-" ^ normalize (String.sub s 3 (len - 4))
    else if len > 5 && String.starts_with ~prefix:"(/ " s
            && Char.equal s.[len - 1] ')'
    then
      let body = String.sub s 3 (len - 4) in
      match String.split_on_char ' ' body with
      | [_num; _den] -> decimal ()
      | _ -> decimal ()
    else s
  in
  normalize (Expr.to_string e)

let rec default_json (ctx : context) (ty : typ) : Yojson.Safe.t =
  match Mark.remove ty with
  | TLit TBool -> `Bool false
  | TLit TInt -> `Int 0
  | TLit TRat | TLit TMoney -> `String "0"
  | TLit TDate -> `String "1900-01-01"
  | TLit TDuration ->
    `Assoc ["years", `Int 0; "months", `Int 0; "days", `Int 0]
  | TLit TUnit | TLit TPos -> `Assoc []
  | TStruct name ->
    let fields = StructName.Map.find name ctx.ctx_decl.ctx_structs in
    `Assoc
      (StructField.Map.bindings fields
       |> List.filter_map (fun (field, ty) ->
            match Mark.remove ty with
            | TOption _ -> None
            | _ ->
              Some
                (StructField.original_string field, default_json ctx ty)))
  | TEnum name ->
    let cons, payload =
      EnumName.Map.find name ctx.ctx_decl.ctx_enums
      |> EnumConstructor.Map.min_binding
    in
    let cons = EnumConstructor.original_string cons in
    begin match Mark.remove payload with
    | TLit TUnit -> `String cons
    | _ -> `Assoc [cons, default_json ctx payload]
    end
  | TOption _ -> `Null
  | TArray _ -> `List []
  | TTuple tys -> `List (List.map (default_json ctx) tys)
  | TDefault ty -> default_json ctx ty
  | TAbstract _ | TArrow _ | TVar _ | TForAll _ | TClosureEnv | TError ->
    `Null

let eval_model model e =
  match Model.eval model e true with Some value -> value | None -> e

let rec json_of_z3model_expr
    (ctx : context)
    (model : Model.model)
    ?(scope_input = false)
    (ty : typ)
    (e : Expr.expr) : Yojson.Safe.t =
  let e = eval_model model e in
  match Mark.remove ty with
  | TLit TBool -> `Bool (Boolean.is_true e)
  | TLit TInt -> `String (integer_string e)
  | TLit TRat -> `String (rational_string e)
  | TLit TMoney ->
    let cents = Z.of_string (integer_string e) in
    `String (Q.(of_bigint cents / of_int 100 |> to_string))
  | TLit TDate ->
    (* Use the schema's object form. It is total over the admitted year
       domain, including year 0000, whereas the runtime string formatter and
       parser historically disagreed on zero-padding at that boundary. *)
    (* Decode the solved serial value independently of any calendar selectors
       mentioned by the query: unused selector applications are unconstrained. *)
    let absolute = int_of_string (integer_string e) + 693901 in
    let era = (if absolute < 0 then absolute - 146096 else absolute) / 146097 in
    let doe = absolute - era * 146097 in
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 in
    let year = yoe + era * 400 in
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100) in
    let mp = (5 * doy + 2) / 153 in
    let day = doy - (153 * mp + 2) / 5 + 1 in
    let month = mp + (if mp < 10 then 3 else -9) in
    let year = year + (if month <= 2 then 1 else 0) in
    `Assoc ["year", `Int year; "month", `Int month; "day", `Int day]
  | TLit TDuration ->
    let years, months, days = DateEncoding.duration_parts ctx e in
    let component value =
      value |> eval_model model |> integer_string |> int_of_string
    in
    `Assoc
      [ "years", `Int (component years);
        "months", `Int (component months);
        "days", `Int (component days) ]
  | TLit TUnit | TLit TPos -> `Assoc []
  | TStruct name ->
    let fields = StructName.Map.find name ctx.ctx_decl.ctx_structs in
    let struct_sort = StructName.Map.find name ctx.ctx_z3structs in
    let accessors = List.hd (Datatype.get_accessors struct_sort) in
    `Assoc
      (List.map2
         (fun (field, field_ty) accessor ->
           let field_name = StructField.original_string field in
           let field_name =
             if scope_input && String.ends_with ~suffix:"_in" field_name
                && String.length field_name > 3
             then String.sub field_name 0 (String.length field_name - 3)
             else field_name
           in
           let value = Expr.mk_app ctx.ctx_z3 accessor [e] in
           field_name,
           json_of_z3model_expr ctx model field_ty value)
         (StructField.Map.bindings fields) accessors
       |> List.filter (fun (_, value) -> not (value = `Null)))
  | TEnum name ->
    let fd = Expr.get_func_decl e in
    let fd_name = Symbol.to_string (FuncDecl.get_name fd) in
    let constructor, payload_ty =
      EnumName.Map.find name ctx.ctx_decl.ctx_enums
      |> EnumConstructor.Map.bindings
      |> List.find (fun (constructor, _) ->
           String.equal fd_name (EnumConstructor.to_string constructor))
    in
    let constructor = EnumConstructor.original_string constructor in
    begin match Mark.remove payload_ty with
    | TLit TUnit -> `String constructor
    | _ ->
      let payload = List.hd (Expr.get_args e) in
      `Assoc
        [ constructor, json_of_z3model_expr ctx model payload_ty payload ]
    end
  | TArray element_ty ->
    let accessors = List.hd (Datatype.get_accessors (Expr.get_sort e)) in
    begin match accessors with
    | length_accessor :: element_accessors ->
      let length =
        Expr.mk_app ctx.ctx_z3 length_accessor [e]
        |> eval_model model |> integer_string |> int_of_string
        |> max 0 |> min (List.length element_accessors)
      in
      `List
        (first_n length element_accessors
         |> List.map (fun accessor ->
              json_of_z3model_expr ctx model element_ty
                (Expr.mk_app ctx.ctx_z3 accessor [e])))
    | [] -> `List []
    end
  | TTuple tys ->
    `List
      (List.map2 (json_of_z3model_expr ctx model) tys (Expr.get_args e))
  | TOption payload_ty ->
    let option_sort = Expr.get_sort e in
    let recognizers = Datatype.get_recognizers option_sort in
    let accessors = Datatype.get_accessors option_sort in
    begin match recognizers, accessors with
    | _absent :: present :: _, _ :: (_present_value :: _) :: _ ->
      if Boolean.is_true
           (eval_model model (Expr.mk_app ctx.ctx_z3 present [e]))
      then
        json_of_z3model_expr ctx model payload_ty
          (Expr.mk_app ctx.ctx_z3 _present_value [e])
      else `Null
    | _ -> `Null
    end
  | TDefault inner_ty ->
    let _, _, accessors =
      let default_sort = Sort.to_string (Expr.get_sort e) in
      StringMap.bindings ctx.ctx_z3defaults
      |> List.find_map (fun (_, ((sort, _, _) as encoding)) ->
           if String.equal default_sort (Sort.to_string sort)
           then Some encoding
           else None)
      |> Option.get
    in
    let defined, conflict, value =
      match accessors with
      | [defined; conflict; value] -> defined, conflict, value
      | _ -> assert false
    in
    if Boolean.is_true (eval_model model (Expr.mk_app ctx.ctx_z3 defined [e]))
       && not
            (Boolean.is_true
               (eval_model model (Expr.mk_app ctx.ctx_z3 conflict [e])))
    then
      json_of_z3model_expr ctx model inner_ty
        (Expr.mk_app ctx.ctx_z3 value [e])
    else `Null
  | TAbstract _ | TArrow _ | TVar _ | TForAll _ | TClosureEnv | TError ->
    `Null

(** [translate_typ_lit] returns the Z3 sort corresponding to the Catala literal
    type [t] **)
let translate_typ_lit (ctx : context) (t : typ_lit) : Sort.sort =
  match t with
  | TBool -> Boolean.mk_sort ctx.ctx_z3
  | TUnit -> fst ctx.ctx_z3unit
  | TInt -> Arithmetic.Integer.mk_sort ctx.ctx_z3
  | TRat -> Arithmetic.Real.mk_sort ctx.ctx_z3
  | TMoney -> Arithmetic.Integer.mk_sort ctx.ctx_z3
  (* Dates are encoded as integers, corresponding to the number of days since
     Jan 1, 1900 *)
  | TDate -> Arithmetic.Integer.mk_sort ctx.ctx_z3
  | TDuration -> ctx.ctx_z3duration
  | TPos -> fst ctx.ctx_z3unit

(** [translate_typ] returns the Z3 sort correponding to the Catala type [t] **)
let rec translate_typ (ctx : context) (t : naked_typ) : context * Sort.sort =
  match t with
  | TLit t -> ctx, translate_typ_lit ctx t
  | TStruct name -> find_or_create_struct ctx name
  | TTuple tys -> find_or_create_tuple ctx tys
  | TEnum e -> find_or_create_enum ctx e
  | TAbstract _ -> failwith "[Z3 encoding] TAbstract type not supported"
  | TOption ty -> find_or_create_option ctx ty
  | TDefault ty ->
    let ctx, (sort, _, _) = find_or_create_default ctx ty in
    ctx, sort
  | TArrow _ -> ctx, fst ctx.ctx_z3unit
  | TArray ty -> find_or_create_array ctx ty
  | TVar var ->
    ctx, (match List.assoc_opt (Bindlib.uid_of var) ctx.ctx_z3types with
      | Some sort -> sort
      | None -> Sort.mk_uninterpreted_s ctx.ctx_z3
          ("bobcat_type_" ^ Bindlib.name_of var
           ^ string_of_int (Bindlib.uid_of var)))
  | TForAll binder ->
    let vars, _ = Bindlib.unmbind binder in
    let suffix =
      Array.to_list vars
      |> List.map (fun var ->
           Bindlib.name_of var ^ string_of_int (Bindlib.uid_of var))
      |> String.concat "_"
    in
    ctx, Sort.mk_uninterpreted_s ctx.ctx_z3 ("bobcat_forall_" ^ suffix)
  | TClosureEnv -> failwith "[Z3 encoding] TClosureEnv type not supported"
  | TError -> failwith "[Z3 encoding] TError type not supported"

(** [find_or_create_enum] attempts to retrieve the Z3 sort corresponding to the
    Catala enumeration [enum]. If no such sort exists yet, it constructs it by
    creating a Z3 constructor for each Catala constructor of [enum], and adds it
    to the context *)
and find_or_create_enum (ctx : context) (enum : EnumName.t) :
    context * Sort.sort =
  (* Creates a Z3 constructor corresponding to the Catala constructor [c] *)
  let create_constructor (name : EnumConstructor.t) (ty : typ) (ctx : context) :
      context * Datatype.Constructor.constructor =
    let name = EnumConstructor.to_string name in
    let ctx, arg_z3_ty = translate_typ ctx (Mark.remove ty) in

    (* The mk_constructor_s Z3 function is not so well documented. From my
       understanding, its argument are: - a string corresponding to the name of
       the constructor - a recognizer as a symbol corresponding to the name
       (unsure why) - a list of symbols corresponding to the arguments of the
       constructor - a list of types, that must be of the same length as the
       list of arguments - a list of sort_refs, of the same length as the list
       of arguments. I'm unsure what this corresponds to *)
    ( ctx,
      Datatype.mk_constructor_s ctx.ctx_z3 name
        (Symbol.mk_string ctx.ctx_z3 name)
        (* We need a name for the argument of the constructor, we arbitrary pick
           the name of the constructor to which we append the special character
           "!" and the integer 0 *)
        [Symbol.mk_string ctx.ctx_z3 (name ^ "!0")]
        (* The type of the argument, translated to a Z3 sort *)
        [Some arg_z3_ty]
        [Sort.get_id arg_z3_ty] )
  in

  match EnumName.Map.find_opt enum ctx.ctx_z3datatypes with
  | Some e -> ctx, e
  | None ->
    let ctrs = EnumName.Map.find enum ctx.ctx_decl.ctx_enums in
    let ctx, z3_ctrs =
      EnumConstructor.Map.fold
        (fun ctr ty (ctx, ctrs) ->
          let ctx, ctr = create_constructor ctr ty ctx in
          ctx, ctr :: ctrs)
        ctrs (ctx, [])
    in
    (* Datatype sort names share one global Z3 namespace. Under whole-program
       compilation, distinct modules may legitimately declare the same source
       basename (the public wrapper and the wrapped law both have [Enfant],
       for example), so retain Catala's qualified identity here. *)
    let z3_enum =
      Datatype.mk_sort_s ctx.ctx_z3
        ("enum!" ^ EnumName.to_string enum) (List.rev z3_ctrs)
    in
    add_z3enum enum z3_enum ctx, z3_enum

and find_or_create_option (ctx : context) (payload_ty : typ) :
    context * Sort.sort =
  let ctx, payload_sort = translate_typ ctx (Mark.remove payload_ty) in
  find_or_create_option_sort ctx payload_sort

and find_or_create_tuple (ctx : context) (tys : typ list) :
    context * Sort.sort =
  let ctx, sorts =
    List.fold_left_map
      (fun ctx ty -> translate_typ ctx (Mark.remove ty))
      ctx tys
  in
  let key = String.concat "#" (List.map Sort.to_string sorts) in
  match StringMap.find_opt key ctx.ctx_z3tuples with
  | Some sort -> ctx, sort
  | None ->
    let suffix = Digest.(to_hex (string key)) in
    let field_names =
      List.mapi
        (fun index _ ->
          Symbol.mk_string ctx.ctx_z3
            (Printf.sprintf "tuple_%d_%s" index suffix))
        sorts
    in
    let sort =
      Tuple.mk_sort ctx.ctx_z3
        (Symbol.mk_string ctx.ctx_z3 ("bobcat_tuple_" ^ suffix))
        field_names sorts
    in
    { ctx with ctx_z3tuples = StringMap.add key sort ctx.ctx_z3tuples }, sort

and find_or_create_option_sort (ctx : context) (payload_sort : Sort.sort) :
    context * Sort.sort =
  let key = Sort.to_string payload_sort in
  match StringMap.find_opt key ctx.ctx_z3options with
  | Some sort -> ctx, sort
  | None ->
    let suffix = Digest.(to_hex (string key)) in
    let constructor name payload =
      Datatype.mk_constructor_s ctx.ctx_z3
        ("bobcat_option_" ^ name ^ "_" ^ suffix)
        (Symbol.mk_string ctx.ctx_z3
           ("is_bobcat_option_" ^ name ^ "_" ^ suffix))
        [Symbol.mk_string ctx.ctx_z3 (name ^ "_value_" ^ suffix)]
        [Some payload] [Sort.get_id payload]
    in
    let sort =
      Datatype.mk_sort_s ctx.ctx_z3 ("bobcat_option_sort_" ^ suffix)
        [ constructor "Absent" (fst ctx.ctx_z3unit);
          constructor "Present" payload_sort ]
    in
    { ctx with ctx_z3options = StringMap.add key sort ctx.ctx_z3options }, sort

and find_or_create_array_sort (ctx : context) (element_sort : Sort.sort) :
    context * Sort.sort =
  let key =
    Sort.to_string element_sort ^ "#" ^ string_of_int ctx.ctx_max_list_length
  in
  match StringMap.find_opt key ctx.ctx_z3arrays with
  | Some encoding -> ctx, encoding.array_sort
  | None ->
    let suffix = Digest.(to_hex (string key)) in
    let int_sort = Arithmetic.Integer.mk_sort ctx.ctx_z3 in
    let element_names =
      List.init ctx.ctx_max_list_length (fun index ->
        Symbol.mk_string ctx.ctx_z3
          (Printf.sprintf "element_%d_%s" index suffix))
    in
    let constructor =
      Datatype.mk_constructor_s ctx.ctx_z3
        ("bobcat_array_" ^ suffix)
        (Symbol.mk_string ctx.ctx_z3 ("is_bobcat_array_" ^ suffix))
        (Symbol.mk_string ctx.ctx_z3 ("length_" ^ suffix) :: element_names)
        (Some int_sort
         :: List.init ctx.ctx_max_list_length (fun _ -> Some element_sort))
        (Sort.get_id int_sort
         :: List.init ctx.ctx_max_list_length (fun _ -> Sort.get_id element_sort))
    in
    let sort =
      Datatype.mk_sort_s ctx.ctx_z3 ("bobcat_array_sort_" ^ suffix)
        [constructor]
    in
    let make = List.hd (Datatype.get_constructors sort) in
    let accessors = List.hd (Datatype.get_accessors sort) in
    let length, elements =
      match accessors with
      | length :: elements -> length, elements
      | [] -> assert false
    in
    let encoding =
      { array_sort = sort; array_make = make; array_length = length;
        array_elements = elements }
    in
    { ctx with ctx_z3arrays = StringMap.add key encoding ctx.ctx_z3arrays },
    sort

and find_or_create_array (ctx : context) (element_ty : typ) :
    context * Sort.sort =
  let ctx, element_sort = translate_typ ctx (Mark.remove element_ty) in
  find_or_create_array_sort ctx element_sort

(** [find_or_create_struct] attemps to retrieve the Z3 sort corresponding to the
    struct [s]. If no such sort exists yet, we construct it as a datatype with
    one constructor taking all the fields as arguments, and add it to the
    context *)
and find_or_create_struct (ctx : context) (s : StructName.t) :
    context * Sort.sort =
  match StructName.Map.find_opt s ctx.ctx_z3structs with
  | Some s -> ctx, s
  | None ->
    let s_name = "struct!" ^ StructName.to_string s in
    let fields = StructName.Map.find s ctx.ctx_decl.ctx_structs in
    let z3_fieldnames =
      List.map
        (fun f -> StructField.to_string f |> Symbol.mk_string ctx.ctx_z3)
        (StructField.Map.keys fields)
    in
    let ctx, z3_fieldtypes_rev =
      StructField.Map.fold
        (fun _ ty (ctx, ftypes) ->
          let ctx, ftype = translate_typ ctx (Mark.remove ty) in
          ctx, ftype :: ftypes)
        fields (ctx, [])
    in
    let z3_fieldtypes = List.rev z3_fieldtypes_rev in
    let z3_sortrefs = List.map Sort.get_id z3_fieldtypes in
    let mk_struct_s = "mk!" ^ s_name in
    let z3_mk_struct =
      Datatype.mk_constructor_s ctx.ctx_z3 mk_struct_s
        (Symbol.mk_string ctx.ctx_z3 mk_struct_s)
        z3_fieldnames
        (List.map (fun x -> Some x) z3_fieldtypes)
        z3_sortrefs
    in

    let z3_struct = Datatype.mk_sort_s ctx.ctx_z3 s_name [z3_mk_struct] in
    add_z3struct s z3_struct ctx, z3_struct

and find_or_create_default_sort (ctx : context) (value_sort : Sort.sort) :
    context * (Sort.sort * FuncDecl.func_decl * FuncDecl.func_decl list) =
  let key = Sort.to_string value_sort in
  match StringMap.find_opt key ctx.ctx_z3defaults with
  | Some encoding -> ctx, encoding
  | None ->
    let suffix = string_of_int (Sort.get_id value_sort) in
    let constructor =
      Datatype.mk_constructor_s ctx.ctx_z3 ("bobcat_default_" ^ suffix)
        (Symbol.mk_string ctx.ctx_z3 ("is_bobcat_default_" ^ suffix))
        [ Symbol.mk_string ctx.ctx_z3 ("defined_" ^ suffix);
          Symbol.mk_string ctx.ctx_z3 ("conflict_" ^ suffix);
          Symbol.mk_string ctx.ctx_z3 ("value_" ^ suffix) ]
        [ Some (Boolean.mk_sort ctx.ctx_z3);
          Some (Boolean.mk_sort ctx.ctx_z3);
          Some value_sort ]
        [ Sort.get_id (Boolean.mk_sort ctx.ctx_z3);
          Sort.get_id (Boolean.mk_sort ctx.ctx_z3);
          Sort.get_id value_sort ]
    in
    let sort =
      Datatype.mk_sort_s ctx.ctx_z3 ("bobcat_default_sort_" ^ suffix)
        [constructor]
    in
    let mk = List.hd (Datatype.get_constructors sort) in
    let accessors = List.hd (Datatype.get_accessors sort) in
    let encoding = sort, mk, accessors in
    { ctx with
      ctx_z3defaults = StringMap.add key encoding ctx.ctx_z3defaults },
    encoding

and find_or_create_default (ctx : context) (ty : typ) :
    context * (Sort.sort * FuncDecl.func_decl * FuncDecl.func_decl list) =
  let ctx, value_sort = translate_typ ctx (Mark.remove ty) in
  find_or_create_default_sort ctx value_sort

(* Instantiate a polymorphic formal's type from its concrete SMT argument.
   Bindings are lexical and are restored when leaving the application. *)
let rec bind_type_sort ctx ty sort =
  let fields sort = List.hd (Datatype.get_accessors sort) in
  match Mark.remove ty with
  | TVar var -> { ctx with ctx_z3types =
      (Bindlib.uid_of var, sort) :: List.remove_assoc (Bindlib.uid_of var) ctx.ctx_z3types }
  | TArray ty -> bind_type_sort ctx ty (FuncDecl.get_range (List.nth (fields sort) 1))
  | TOption ty -> bind_type_sort ctx ty
      (FuncDecl.get_range (List.hd (List.nth (Datatype.get_accessors sort) 1)))
  | TDefault ty -> bind_type_sort ctx ty (FuncDecl.get_range (List.nth (fields sort) 2))
  | TTuple tys -> List.fold_left2 (fun ctx ty accessor ->
      bind_type_sort ctx ty (FuncDecl.get_range accessor)) ctx tys (fields sort)
  | _ -> ctx

(** [translate_lit] returns the Z3 expression as a literal corresponding to
    [lit] **)
let translate_lit (ctx : context) (l : lit) : Expr.expr =
  match l with
  | LBool b ->
    if b then Boolean.mk_true ctx.ctx_z3 else Boolean.mk_false ctx.ctx_z3
  | LInt n ->
    Arithmetic.Integer.mk_numeral_s ctx.ctx_z3 (Z.to_string n)
  | LRat r ->
    Arithmetic.Real.mk_numeral_s ctx.ctx_z3
      (Q.to_string r)
  | LMoney m ->
    let z3_m = Runtime.money_to_cents m in
    Arithmetic.Integer.mk_numeral_s ctx.ctx_z3 (Z.to_string z3_m)
  | LUnit -> snd ctx.ctx_z3unit
  (* Encoding a date as an integer corresponding to the number of days since Jan
     1, 1900 *)
  | LDate d -> Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 (date_to_int d)
  | LDuration d ->
    let y, m, d = Runtime.duration_to_years_months_days d in
    DateEncoding.make_duration ctx (DateEncoding.int ctx y)
      (DateEncoding.int ctx m) (DateEncoding.int ctx d)

(** [find_or_create_funcdecl] attempts to retrieve the Z3 function declaration
    corresponding to the variable [v] and its type [ty]. If no such function
    declaration exists yet, we construct it and add it to the context, thus
    requiring to return a new context *)
let find_or_create_funcdecl (ctx : context) (v : typed expr Var.t) (ty : typ) :
    context * FuncDecl.func_decl =
  match Var.Map.find_opt v ctx.ctx_funcdecl with
  | Some fd -> ctx, fd
  | None -> (
    match Mark.remove ty with
    | TArrow (t1, t2) ->
      let ctx, z3_t1 =
        List.fold_left_map translate_typ ctx (List.map Mark.remove t1)
      in
      let ctx, z3_t2 = translate_typ ctx (Mark.remove t2) in
      let name = unique_name v in
      let fd = FuncDecl.mk_func_decl_s ctx.ctx_z3 name z3_t1 z3_t2 in
      let ctx = add_funcdecl v fd ctx in
      let ctx = add_z3var name v ty ctx in
      ctx, fd
    | TVar _ | TForAll _ ->
      failwith
        "[Z3 Encoding] A function being applied has type TForAll, the type was \
         not fully inferred"
    | _ ->
      failwith
        "[Z3 Encoding] Ill-formed VC, a function application does not have a \
         function type")

let bounded_array_components ?limit ctx array =
  match List.hd (Datatype.get_accessors (Expr.get_sort array)) with
  | length :: elements ->
    ( (match limit with
       | Some 0 -> Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 0
       | _ -> Expr.mk_app ctx.ctx_z3 length [array]),
      List.map
        (fun accessor -> Expr.mk_app ctx.ctx_z3 accessor [array])
        (match limit with None -> elements | Some n -> first_n n elements) )
  | [] -> failwith "[Z3 encoding] malformed bounded-list datatype"

(* Structural abstract interpretation. A size records an upper bound for every
   nested list in a value. Functions and records retain their structure so
   higher-order calls and record projections do not lose list growth. *)
type size_value =
  | Size of int
  | SizeArray of int * size_value
  | SizeFunction of int * (size_value list -> size_value)
  | SizeStruct of size_value StructField.Map.t
  | SizeTuple of size_value list

let rec size_max = function
  | Size n -> n
  | SizeArray (n, element) -> max n (size_max element)
  | SizeFunction _ -> 0
  | SizeStruct fields -> StructField.Map.fold (fun _ v n -> max n (size_max v)) fields 0
  | SizeTuple values -> List.fold_left (fun n v -> max n (size_max v)) 0 values

let required_array_capacity ?(literals_only = false) ~decl_ctx ~input_ty ~input_bound ~input_var ~definitions body =
  let maximum = ref (max 1 input_bound) in
  (* Literal storage is independent of the input bound, including literals
     in callbacks that become reachable only after an input list grows. *)
  let named = List.fold_left (fun m (v, e) -> Var.Map.add v e m) Var.Map.empty definitions in
  let seen = ref Var.Set.empty in
  let rec literals e =
    let children = match Mark.remove e with
      | EVar v when not (Var.Set.mem v !seen) ->
        seen := Var.Set.add v !seen; Option.to_list (Var.Map.find_opt v named)
      | EAbs { binder; _ } -> let _, body = Bindlib.unmbind binder in [body]
      | EArray xs -> maximum := max !maximum (List.length xs); xs
      | EApp { f; args; _ } -> f :: args
      | EAppOp { args; _ } | ETuple args -> args
      | EIfThenElse { cond; etrue; efalse } -> [cond; etrue; efalse]
      | EStruct { fields; _ } -> StructField.Map.values fields
      | EStructAccess { e; _ } | ETupleAccess { e; _ } | EInj { e; _ }
      | EAssert e | EPureDefault e | EErrorOnEmpty e -> [e]
      | EMatch { e; cases; _ } -> e :: EnumConstructor.Map.values cases
      | EDefault { excepts; just; cons } -> just :: cons :: excepts
      | _ -> [] in
    List.iter literals children
  in
  literals body;
  if literals_only then !maximum else
  let serial = ref 0 in
  let remember value = maximum := max !maximum (size_max value); value in
  let rec key = function
    | Size n -> "s" ^ string_of_int n
    | SizeArray (n, element) -> "a" ^ string_of_int n ^ "[" ^ key element ^ "]"
    | SizeFunction (id, _) -> "f" ^ string_of_int id
    | SizeTuple xs -> "(" ^ String.concat "," (List.map key xs) ^ ")"
    | SizeStruct fs -> "{" ^ String.concat ","
        (List.map (fun (_, v) -> key v) (StructField.Map.bindings fs)) ^ "}" in
  let rec join a b = match a, b with
    | Size 0, value | value, Size 0 -> value
    | SizeArray (n, a), SizeArray (m, b) -> SizeArray (max n m, join a b)
    | SizeTuple a, SizeTuple b when List.length a = List.length b ->
      SizeTuple (List.map2 join a b)
    | SizeFunction (_, f), SizeFunction (_, g) ->
      incr serial; SizeFunction (!serial, fun xs -> join (f xs) (g xs))
    | SizeStruct a, SizeStruct b when StructField.Map.equal (fun _ _ -> true) a b -> SizeStruct (StructField.Map.mapi
        (fun field a -> match StructField.Map.find_opt field b with
          | Some b -> join a b | None -> a) a)
    | _ -> Size (max (size_max a) (size_max b)) in
  let rec input_shape ty = match Mark.remove ty with
    | TArray element -> SizeArray (input_bound, input_shape element)
    | TStruct name -> SizeStruct (StructField.Map.map input_shape
        (StructName.Map.find name decl_ctx.ctx_structs))
    | TTuple tys -> SizeTuple (List.map input_shape tys)
    | TOption ty | TDefault ty -> input_shape ty
    | TEnum name -> EnumConstructor.Map.fold (fun _ ty acc ->
        join acc (input_shape ty)) (EnumName.Map.find name decl_ctx.ctx_enums) (Size 0)
    | TVar _ | TForAll _ -> Size input_bound
    | _ -> Size 0 in
  let array = function
    | SizeArray (n, element) -> n, element
    | value -> let n = size_max value in n, Size n in
  let apply fn args = match fn with
    | SizeFunction (_, f) -> f args
    | _ -> Size (List.fold_left (fun n x -> max n (size_max x)) (size_max fn) args) in
  let rec eval env expression = remember (match Mark.remove expression with
    | EVar var -> (match Var.Map.find_opt var env with Some v -> Lazy.force v | None -> input_shape (Shared_ast.Expr.ty expression))
    | EAbs { binder; _ } ->
      incr serial;
      let id = !serial in
      let memo = Hashtbl.create 7 in
      SizeFunction (id, fun args ->
        let signature = String.concat ";" (List.map key args) in
        match Hashtbl.find_opt memo signature with
        | Some v -> v
        | None ->
          let vars, body = Bindlib.unmbind binder in
          let env = List.fold_left2 (fun env var value -> Var.Map.add var (lazy value) env)
              env (Array.to_list vars) args in
          let value = eval env body in
          Hashtbl.add memo signature value; value)
    | EApp { f; args; _ } -> apply (eval env f) (List.map (eval env) args)
    | EStruct { fields; _ } -> SizeStruct (StructField.Map.map (eval env) fields)
    | EStructAccess { e; field; _ } -> (match eval env e with
        | SizeStruct fs -> StructField.Map.find field fs | v -> Size (size_max v))
    | ETuple xs -> SizeTuple (List.map (eval env) xs)
    | ETupleAccess { e; index; _ } -> (match eval env e with
        | SizeTuple xs -> List.nth xs index | v -> Size (size_max v))
    | EArray xs -> SizeArray (List.length xs,
        List.fold_left (fun acc x -> join acc (eval env x)) (Size 0) xs)
    | EAppOp { op = (Concat, _); args = [a;b]; _ } ->
      let n, a = array (eval env a) and m, b = array (eval env b) in
      if n > max_int - m then failwith "list capacity overflow";
      SizeArray (n + m, join a b)
    | EAppOp { op = ((Map | Filter | Find) as op, _); args = [fn; xs]; _ } ->
      let n, element = array (eval env xs) in
      let f = eval env fn in
      let mapped = if n = 0 then Size 0 else apply f [element] in
      (match op with
       | Map -> SizeArray (n, mapped)
       | Filter -> SizeArray (n, element)
       | Find -> element
       | _ -> assert false)
    | EAppOp { op = (Fold, _); args = [fn; init; xs]; _ } ->
      let n, element = array (eval env xs) in
      let f = eval env fn in
      let value = ref (eval env init) in
      for _ = 1 to n do value := join !value (apply f [!value; element]) done;
      !value
    | EAppOp { op = (Reduce, _); args = [fn; xs]; _ } ->
      let n, element = array (eval env xs) in
      let f = eval env fn in
      let value = ref element in
      for _ = 2 to n do value := join !value (apply f [!value; element]) done;
      !value
    | EIfThenElse { cond; etrue; efalse } ->
      ignore (eval env cond); join (eval env etrue) (eval env efalse)
    | EMatch { e; cases; _ } ->
      let subject = eval env e in
      EnumConstructor.Map.fold (fun _ arm result -> join result (apply (eval env arm) [subject])) cases (Size 0)
    | EInj { e; _ } | EPureDefault e | EErrorOnEmpty e -> eval env e
    | EDefault { excepts; just; cons } ->
      ignore (eval env just);
      List.fold_left (fun value e -> join value (eval env e)) (eval env cons) excepts
    | EAssert e -> ignore (eval env e); Size 0
    | EAppOp { op = (ArrayAccess _, _); args = [xs]; _ } ->
      snd (array (eval env xs))
    | EAppOp { op = (Tag _, _); args = [inner]; _ } -> eval env inner
    | EAppOp { args; _ } ->
      let arguments = List.map (eval env) args in
      let result = input_shape (Shared_ast.Expr.ty expression) in
      (match result with Size 0 -> Size 0
       | _ -> List.fold_left join result arguments)
    | _ -> Size 0)
  in
  let all_definitions = ref Var.Map.empty in
  let env = List.fold_left (fun env (var, definition) ->
      Var.Map.add var (lazy (eval !all_definitions definition)) env)
      (Var.Map.singleton input_var (lazy (input_shape input_ty))) definitions in
  all_definitions := env;
  ignore (eval env body);
  !maximum

(* Least fixed point of "contains a function" over the declaration graph.
   Reverse edges propagate each positive fact once, including through cycles.
   Repeated queries no longer unfold the same shared type DAG. *)
let function_type_closure decl =
  let positive = Hashtbl.create 127 in
  let parents = Hashtbl.create 127 in
  let pending = Queue.create () in
  let mark node = if not (Hashtbl.mem positive node) then begin
    Hashtbl.add positive node (); Queue.add node pending
  end in
  let rec visit parent ty = match Mark.remove ty with
    | TArrow _ -> mark parent
    | TStruct name -> edge parent (FunctionStruct name)
    | TEnum name -> edge parent (FunctionEnum name)
    | TOption ty | TDefault ty | TArray ty -> visit parent ty
    | TTuple tys -> List.iter (visit parent) tys
    | _ -> ()
  and edge parent child =
    Hashtbl.replace parents child
      (parent :: Option.value ~default:[] (Hashtbl.find_opt parents child)) in
  StructName.Map.iter (fun name fields ->
    StructField.Map.iter (fun _ ty -> visit (FunctionStruct name) ty) fields)
    decl.ctx_structs;
  EnumName.Map.iter (fun name cases ->
    EnumConstructor.Map.iter (fun _ ty -> visit (FunctionEnum name) ty) cases)
    decl.ctx_enums;
  while not (Queue.is_empty pending) do
    let child = Queue.take pending in
    List.iter mark (Option.value ~default:[] (Hashtbl.find_opt parents child))
  done;
  positive

let rec type_contains_function ctx ty = match Mark.remove ty with
  | TArrow _ -> true
  | TStruct name -> Hashtbl.mem ctx.ctx_function_types (FunctionStruct name)
  | TEnum name -> Hashtbl.mem ctx.ctx_function_types (FunctionEnum name)
  | TOption ty | TDefault ty | TArray ty -> type_contains_function ctx ty
  | TTuple tys -> List.exists (type_contains_function ctx) tys
  | _ -> false


let bounded_array_constructor array =
  List.hd (Datatype.get_constructors (Expr.get_sort array))

let enum_z3_members ctx enum sort =
  let constructors =
    EnumName.Map.find enum ctx.ctx_decl.ctx_enums
    |> EnumConstructor.Map.keys
  in
  let recognizers = Datatype.get_recognizers sort in
  let accessors = Datatype.get_accessors sort in
  let z3_constructors = Datatype.get_constructors sort in
  if
    List.length constructors <> List.length recognizers
    || List.length constructors <> List.length accessors
    || List.length constructors <> List.length z3_constructors
  then
    failwith
      "[Z3 encoding] enum declaration and datatype have different arities";
  List.map2
    (fun constructor (z3_constructor, (recognizer, accessors)) ->
      constructor, z3_constructor, recognizer, accessors)
    constructors
    (List.combine z3_constructors (List.combine recognizers accessors))

let external_runtime_name name =
  let path =
    match Mark.remove name with
    | External_value topdef -> TopdefName.path topdef
    | External_scope scope -> ScopeName.path scope
  in
  ( ModuleName.to_string (Option.get (Uid.Path.last_member path)),
    match Mark.remove name with
    | External_value topdef -> TopdefName.base topdef
    | External_scope scope -> ScopeName.base scope )

let _is_leap_year = Runtime.is_leap_year
(* Replace with [Dates_calc.Dates.is_leap_year] when existing *)

let expression_identity ctx expression =
  match ExpressionIdentity.find_opt ctx.ctx_expression_ids expression with
  | Some id -> id
  | None ->
    let id = ExpressionIdentity.length ctx.ctx_expression_ids in
    ExpressionIdentity.add ctx.ctx_expression_ids expression id; id

let symbolic_environment_key ctx definition =
  (* Hash-cons the environment graph rather than serializing its transitive
     closure at every call. Structural equality, not a digest, decides reuse. *)
  let intern key = match Hashtbl.find_opt ctx.ctx_environment_ids key with
    | Some id -> id
    | None -> let id = Hashtbl.length ctx.ctx_environment_ids in
      Hashtbl.add ctx.ctx_environment_ids key id; id in
  let memo = Hashtbl.create 31 in
  let rec variable var =
    let uid = Bindlib.uid_of var in
    match Hashtbl.find_opt memo uid with
    | Some id -> id
    | None ->
      Hashtbl.add memo uid (intern ("cycle:" ^ string_of_int uid));
      let tail = match Var.Map.find_opt var ctx.ctx_z3matchsubsts with
        | Some value -> "value:" ^ string_of_int (Z3.AST.get_id (Expr.ast_of_expr value))
        | None -> match Var.Map.find_opt var ctx.ctx_z3definitions with
          | None -> "free"
          | Some e -> "definition:" ^ string_of_int (expression_identity ctx e)
            ^ ":" ^ expression e in
      let id = intern (string_of_int uid ^ ":" ^ tail) in
      Hashtbl.replace memo uid id; id
  and expression e =
    Shared_ast.Expr.free_vars e |> Var.Set.elements
    |> List.map (fun var -> string_of_int (variable var)) |> String.concat "," in
  string_of_int (intern ("environment:" ^ expression definition))

let canonical_padding ctx sort =
  Expr.mk_const_s ctx.ctx_z3
    ("bobcat_padding_" ^ Digest.(to_hex (string (Sort.to_string sort)))) sort

(* Commuting conversions for elimination of a computed value. Applying a
   function or selecting a record field distributes through its control-flow
   and default contexts, retaining the same guards and source branch tags. *)
let rec map_computed_result transform new_ty (e : typed expr) : typed expr =
  let mark = match Mark.get e with Typed { pos; _ } -> Typed { pos; ty = new_ty } in
  let recur = map_computed_result transform in
  match Mark.remove e with
  | EIfThenElse { cond; etrue; efalse } ->
    EIfThenElse { cond; etrue = recur new_ty etrue; efalse = recur new_ty efalse }, mark
  | EMatch { e = subject; cases; name } ->
    let cases = EnumConstructor.Map.map (fun arm -> match Mark.remove arm with
      | EAbs { binder; pos; tys } ->
        let vars, body = Bindlib.unmbind binder in
        let body = recur new_ty body in
        let binder = Bindlib.unbox (Bindlib.bind_mvar vars (Shared_ast.Expr.Box.lift (Shared_ast.Expr.rebox body))) in
        let ty = TArrow (tys, new_ty), Mark.get new_ty in
        let arm_mark = match Mark.get arm with Typed { pos; _ } -> Typed { pos; ty } in
        EAbs { binder; pos; tys }, arm_mark
      | _ -> failwith "computed result match requires lambda arms") cases in
    EMatch { e = subject; cases; name }, mark
  | EErrorOnEmpty inner ->
    EErrorOnEmpty (recur (TDefault new_ty, Mark.get new_ty) inner), mark
  | EPureDefault inner ->
    let payload = match Mark.remove new_ty with TDefault ty -> ty | _ -> assert false in
    EPureDefault (recur payload inner), mark
  | EDefault { excepts; just; cons } ->
    EDefault { excepts = List.map (recur new_ty) excepts; just; cons = recur new_ty cons }, mark
  | EEmpty -> EEmpty, mark
  | EAppOp { op = (Tag _, _) as op; args = [inner]; tys } ->
    EAppOp { op; args = [recur new_ty inner]; tys }, mark
  | _ -> transform new_ty e

let computed_context (e : typed expr) = match Mark.remove e with
  | EIfThenElse _ | EMatch _ | EErrorOnEmpty _ | EPureDefault _ | EDefault _ | EEmpty -> true
  | EAppOp { op = (Tag _, _); _ } -> true
  | _ -> false

let project_computed base field name result_ty =
  map_computed_result (fun ty e -> match Mark.remove e with
    | EStruct { fields; _ } -> StructField.Map.find field fields
    | _ -> let mark = match Mark.get e with Typed { pos; _ } -> Typed { pos; ty } in
      EStructAccess { e; field; name }, mark) result_ty base

let apply_computed head args result_ty =
  map_computed_result (fun ty f ->
    let mark = match Mark.get f with Typed { pos; _ } -> Typed { pos; ty } in
    EApp { f; args; tys = [] }, mark) result_ty head

(* Call-by-need head normalization. Bindlib gives lexical bindings unique
   identities; each named definition is reduced once, together with the
   environment needed by the resulting closure. No whole-body substitution. *)
let resolve_value_head initial expression =
  let state = ref initial in
  let rec resolve seen e = match Mark.remove e with
    | EVar var when not (Var.Set.mem var seen) ->
      begin match Var.Map.find_opt var (!state).ctx_z3definitions with
      | None -> e
      | Some definition ->
        begin match Hashtbl.find_opt (!state).ctx_head_values (Bindlib.uid_of var) with
        | Some (original, value, environment) when original == definition ->
          state := { !state with ctx_z3definitions =
            Var.Map.union (fun _ current _ -> Some current) (!state).ctx_z3definitions environment };
          value
        | _ ->
          let value = resolve (Var.Set.add var seen) definition in
          Hashtbl.replace (!state).ctx_head_values (Bindlib.uid_of var)
            (definition, value, (!state).ctx_z3definitions);
          value
        end
      end
    | EAppOp { op = (Tag _, _); args = [inner]; _ } -> resolve seen inner
    | EApp { f; args; _ } ->
      begin match Mark.remove (resolve seen f) with
      | EAbs { binder; _ } when Bindlib.mbinder_arity binder = List.length args ->
        let vars, body = Bindlib.unmbind binder in
        state := List.fold_left2 (fun ctx var arg ->
          { ctx with ctx_z3definitions = Var.Map.add var arg ctx.ctx_z3definitions })
          !state (Array.to_list vars) args;
        resolve seen body
      | _ -> e
      end
    | EStructAccess { e = base; field; name } ->
      let base = resolve seen base in
      begin match Mark.remove base with
      | EStruct { fields; _ } -> resolve seen (StructField.Map.find field fields)
      | _ when computed_context base -> project_computed base field name (Shared_ast.Expr.ty e)
      | _ -> e
      end
    | _ -> e in
  let value = resolve Var.Set.empty expression in
  !state, value

let expression_list_bound ctx expression =
  let rec has_lists seen ty = match Mark.remove ty with
    | TArray _ -> true
    | TStruct name when not (List.mem ("s" ^ StructName.to_string name) seen) ->
      let seen = ("s" ^ StructName.to_string name) :: seen in
      StructField.Map.exists (fun _ ty -> has_lists seen ty)
        (StructName.Map.find name ctx.ctx_decl.ctx_structs)
    | TEnum name when not (List.mem ("e" ^ EnumName.to_string name) seen) ->
      let seen = ("e" ^ EnumName.to_string name) :: seen in
      EnumConstructor.Map.exists (fun _ ty -> has_lists seen ty)
        (EnumName.Map.find name ctx.ctx_decl.ctx_enums)
    | TOption ty | TDefault ty -> has_lists seen ty
    | TTuple tys -> List.exists (has_lists seen) tys
    | TVar _ | TForAll _ -> true
    | _ -> false in
  let rec bound ctx seen expression =
    let (Typed { ty; _ }) = Mark.get expression in
    if not (has_lists [] ty) then 0 else
    match Mark.remove expression with
    | EArray values ->
      List.fold_left (fun n e -> max n (bound ctx seen e)) (List.length values) values
    | EVar var when not (Var.Set.mem var seen) ->
      begin match Var.Map.find_opt var ctx.ctx_z3matchsubsts with
      | Some value -> Option.value ~default:ctx.ctx_max_list_length
          (known_value_bound ctx value)
      | None -> match Var.Map.find_opt var ctx.ctx_z3valuecache with
        | Some (value, _) -> Option.value ~default:ctx.ctx_max_list_length
            (known_value_bound ctx value)
        | None -> match Var.Map.find_opt var ctx.ctx_z3definitions with
        | Some definition -> bound ctx (Var.Set.add var seen) definition
        | None when Var.Set.mem var ctx.ctx_z3freevars -> ctx.ctx_symbolic_list_bound
        | None -> ctx.ctx_max_list_length
      end
    | EStructAccess { e; _ } ->
      let next, head = resolve_value_head ctx expression in
      if head != expression then bound next seen head else bound ctx seen e
    | EApp _ ->
      let next, head = resolve_value_head ctx expression in
      if head != expression then bound next seen head else ctx.ctx_max_list_length
    | ETupleAccess { e; _ }
    | EInj { e; _ } | EErrorOnEmpty e | EPureDefault e -> bound ctx seen e
    | EAppOp { op = (Tag _, _); args = [e]; _ } -> bound ctx seen e
    | EStruct { fields; _ } ->
      StructField.Map.fold (fun _ e n -> max n (bound ctx seen e)) fields 0
    | ETuple values -> List.fold_left (fun n e -> max n (bound ctx seen e)) 0 values
    | EAppOp { op = (Filter, _); args = [_; list]; _ } -> bound ctx seen list
    | EAppOp { op = (Map, _); args = [_; list]; _ } ->
      (match Mark.remove ty with
       | TArray element_ty when not (has_lists [] element_ty) -> bound ctx seen list
       | _ -> ctx.ctx_max_list_length)
    | EAppOp { op = (Concat, _); args = [left; right]; _ } ->
      bound ctx seen left + bound ctx seen right
    | EIfThenElse { etrue; efalse; _ } -> max (bound ctx seen etrue) (bound ctx seen efalse)
    | EDefault { excepts; cons; _ } ->
      List.fold_left (fun n e -> max n (bound ctx seen e)) (bound ctx seen cons) excepts
    | EEmpty -> 0
    | _ -> ctx.ctx_max_list_length
  in
  min ctx.ctx_max_list_length (max 0 (bound ctx Var.Set.empty expression))

let encoded_list_bound ctx expression array =
  min (expression_list_bound ctx expression)
    (Option.value ~default:ctx.ctx_max_list_length
       (known_value_bound ctx array))

let guard_new_constraints ctx previous guard =
  let rec delta = function
    | tail when tail == previous -> []
    | c :: rest -> Boolean.mk_implies ctx.ctx_z3 guard c :: delta rest
    | [] -> failwith "guarded constraint accumulator lost its tail" in
  { ctx with ctx_z3constraints = delta ctx.ctx_z3constraints @ previous }

(** [translate_op] returns the Z3 expression corresponding to the application of
    [op] to the arguments [args] **)
let rec translate_op :
    context -> dcalc operator Mark.pos -> 'm expr list -> context * Expr.expr =
 fun ctx (op, pos) args ->
  let ill_formed () =
    Format.kasprintf failwith
      "[Z3 encoding] Ill-formed operator application: %a" Shared_ast.Expr.format
      (Shared_ast.Expr.eappop ~op:(op, pos)
         ~args:(List.map Shared_ast.Expr.untype args)
         ~tys:[]
         (Untyped { pos })
      |> Shared_ast.Expr.unbox)
  in
  let app f =
    let ctx, args = List.fold_left_map translate_expr ctx args in
    ctx, f ctx.ctx_z3 args
  in
  let app1 f =
    app (fun ctx -> function [a] -> f ctx a | _ -> ill_formed ())
  in
  let app2 f =
    app (fun ctx -> function [a; b] -> f ctx a b | _ -> ill_formed ())
  in
  let has_duration_type e =
    let (Typed { ty; _ }) = Mark.get e in
    match Mark.remove ty with TLit TDuration -> true | _ -> false
  in
  match op, args with
  | Fold, _ ->
    failwith "[Z3 encoding] ternary operator application not supported"
  | Add_dat_dur round, [date; duration] ->
    let ctx, date = translate_expr ctx date in
    let ctx, duration = translate_expr ctx duration in
    let ctx =
      match round with
      | Dates_calc.AbortOnRound ->
        add_z3constraint
          (Boolean.mk_not ctx.ctx_z3
             (DateEncoding.requires_rounding ctx date duration))
          ctx
      | Dates_calc.RoundDown | Dates_calc.RoundUp -> ctx
    in
    ctx, DateEncoding.add_dat_dur ctx round date duration
  | Sub_dat_dur round, [date; duration] ->
    let ctx, date = translate_expr ctx date in
    let ctx, duration = translate_expr ctx duration in
    let duration = DateEncoding.minus_dur ctx duration in
    let ctx =
      match round with
      | Dates_calc.AbortOnRound ->
        add_z3constraint
          (Boolean.mk_not ctx.ctx_z3
             (DateEncoding.requires_rounding ctx date duration))
          ctx
      | Dates_calc.RoundDown | Dates_calc.RoundUp -> ctx
    in
    ctx, DateEncoding.add_dat_dur ctx round date duration
  | Add_dur_dur, [left; right] ->
    let ctx, left = translate_expr ctx left in
    let ctx, right = translate_expr ctx right in
    ctx, DateEncoding.add_dur_dur ctx left right
  | Sub_dur_dur, [left; right] ->
    let ctx, left = translate_expr ctx left in
    let ctx, right = translate_expr ctx right in
    ctx, DateEncoding.sub_dur_dur ctx left right
  | Sub_dat_dat, [left; right] ->
    let ctx, left = translate_expr ctx left in
    let ctx, right = translate_expr ctx right in
    ctx, DateEncoding.sub_dat_dat ctx left right
  | Mult_dur_int, [duration; factor] ->
    let ctx, duration = translate_expr ctx duration in
    let ctx, factor = translate_expr ctx factor in
    ctx, DateEncoding.mult_dur_int ctx duration factor
  | Div_dur_dur, [left; right] ->
    let ctx, left = translate_expr ctx left in
    let ctx, right = translate_expr ctx right in
    let valid, result = DateEncoding.div_dur_dur ctx left right in
    add_z3constraint valid ctx, result
  | Eq, [left; right] when has_duration_type left ->
    let ctx, left = translate_expr ctx left in
    let ctx, right = translate_expr ctx right in
    let valid, result = DateEncoding.duration_equality ctx left right in
    add_z3constraint valid ctx, result
  | ((Lt | Lte | Gt | Gte) as relation), [left; right]
    when has_duration_type left ->
    let ctx, left = translate_expr ctx left in
    let ctx, right = translate_expr ctx right in
    let comparison =
      match relation with
      | Lt -> Arithmetic.mk_lt ctx.ctx_z3
      | Lte -> Arithmetic.mk_le ctx.ctx_z3
      | Gt -> Arithmetic.mk_gt ctx.ctx_z3
      | Gte -> Arithmetic.mk_ge ctx.ctx_z3
      | _ -> assert false
    in
    let valid, result =
      DateEncoding.duration_comparison ctx comparison left right
    in
    add_z3constraint valid ctx, result
  | ToMoney_rat, [value] ->
    let ctx, value = translate_expr ctx value in
    let cents =
      Arithmetic.mk_mul ctx.ctx_z3
        [value; Arithmetic.Real.mk_numeral_i ctx.ctx_z3 100]
    in
    ctx, z3_round ctx cents
  | ToMoney_int, [value] ->
    let ctx, value = translate_expr ctx value in
    ctx,
    Arithmetic.mk_mul ctx.ctx_z3
      [value; Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 100]
  | ToInt_rat, [value] ->
    let ctx, value = translate_expr ctx value in
    let nonnegative =
      Arithmetic.mk_ge ctx.ctx_z3 value
        (Arithmetic.Real.mk_numeral_i ctx.ctx_z3 0)
    in
    let positive = Arithmetic.Real.mk_real2int ctx.ctx_z3 value in
    let negative =
      Arithmetic.mk_unary_minus ctx.ctx_z3
        (Arithmetic.Real.mk_real2int ctx.ctx_z3
           (Arithmetic.mk_unary_minus ctx.ctx_z3 value))
    in
    ctx, Boolean.mk_ite ctx.ctx_z3 nonnegative positive negative
  | Minus_dur, [duration] ->
    let ctx, duration = translate_expr ctx duration in
    ctx, DateEncoding.minus_dur ctx duration
  | Round_rat, [value] ->
    let ctx, value = translate_expr ctx value in
    ctx, Arithmetic.Integer.mk_int2real ctx.ctx_z3 (z3_round ctx value)
  | Round_mon, [value] ->
    let ctx, value = translate_expr ctx value in
    let units =
      Arithmetic.mk_mul ctx.ctx_z3
        [ z3_force_real ctx value;
          Arithmetic.Real.mk_numeral_nd ctx.ctx_z3 1 100 ]
    in
    ctx,
    Arithmetic.mk_mul ctx.ctx_z3
      [ z3_round ctx units;
        Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 100 ]
  | (Mult_mon_rat | Mult_mon_int), [money; factor] ->
    let ctx, money = translate_expr ctx money in
    let ctx, factor = translate_expr ctx factor in
    let product = Arithmetic.mk_mul ctx.ctx_z3 [money; factor] in
    ctx, z3_round ctx product
  | (Div_mon_rat | Div_mon_int), [money; divisor] ->
    let ctx, money = translate_expr ctx money in
    let ctx, divisor = translate_expr ctx divisor in
    let zero =
      match Sort.get_sort_kind (Expr.get_sort divisor) with
      | Z3enums.INT_SORT -> Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 0
      | _ -> Arithmetic.Real.mk_numeral_i ctx.ctx_z3 0
    in
    let ctx =
      add_z3constraint
        (Boolean.mk_not ctx.ctx_z3
           (Boolean.mk_eq ctx.ctx_z3 divisor zero))
        ctx
    in
    let quotient =
      Arithmetic.mk_div ctx.ctx_z3 (z3_force_real ctx money) divisor
    in
    ctx, z3_round ctx quotient
  (* Special case for GetYear comparisons *)
  (* FIXME: getYear is no longer an operator but an stdlib function*)
  (* | ( Lt_int_int, [(EAppOp { op = GetYear, _; args = [e1]; _ }, _); (ELit
     (LInt n), _)] ) -> let n = Runtime.integer_to_int n in let ctx, e1 =
     translate_expr ctx e1 in let e2 = Arithmetic.Integer.mk_numeral_i
     ctx.ctx_z3 (date_to_int (date_of_year n)) in (* e2 corresponds to the first
     day of the year n. GetYear e1 < e2 can thus be directly translated as < in
     the Z3 encoding using the number of days *) ctx, Arithmetic.mk_lt
     ctx.ctx_z3 e1 e2 | ( Lte_int_int, [(EAppOp { op = GetYear, _; args = [e1];
     _ }, _); (ELit (LInt n), _)] ) -> let ctx, e1 = translate_expr ctx e1 in
     let nb_days = if is_leap_year n then 365 else 364 in let n =
     Runtime.integer_to_int n in (* We want that the year corresponding to e1 is
     smaller or equal to n. We encode this as the day corresponding to e1 is
     smaller or equal than the last day of the year [n], which is Jan 1st + 365
     days if [n] is a leap year, Jan 1st + 364 else *) let e2 =
     Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 (date_to_int (date_of_year n) +
     nb_days) in ctx, Arithmetic.mk_le ctx.ctx_z3 e1 e2 | ( Gt_int_int, [(EAppOp
     { op = GetYear, _; args = [e1]; _ }, _); (ELit (LInt n), _)] ) -> let ctx,
     e1 = translate_expr ctx e1 in let nb_days = if is_leap_year n then 365 else
     364 in let n = Runtime.integer_to_int n in (* We want that the year
     corresponding to e1 is greater to n. We encode this as the day
     corresponding to e1 is greater than the last day of the year [n], which is
     Jan 1st + 365 days if [n] is a leap year, Jan 1st + 364 else *) let e2 =
     Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 (date_to_int (date_of_year n) +
     nb_days) in ctx, Arithmetic.mk_gt ctx.ctx_z3 e1 e2 | ( Gte_int_int,
     [(EAppOp { op = GetYear, _; args = [e1]; _ }, _); (ELit (LInt n), _)] ) ->
     let n = Runtime.integer_to_int n in let ctx, e1 = translate_expr ctx e1 in
     let e2 = Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 (date_to_int
     (date_of_year n)) in (* e2 corresponds to the first day of the year n.
     GetYear e1 >= e2 can thus be directly translated as >= in the Z3 encoding
     using the number of days *) ctx, Arithmetic.mk_ge ctx.ctx_z3 e1 e2 | Eq,
     [(EAppOp { op = GetYear, _; args = [e1]; _ }, _); (ELit (LInt n), _)] ->
     let n = Runtime.integer_to_int n in let ctx, e1 = translate_expr ctx e1 in
     let min_date = Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 (date_to_int
     (date_of_year n)) in let max_date = Arithmetic.Integer.mk_numeral_i
     ctx.ctx_z3 (date_to_int (date_of_year (n + 1))) in ( ctx, Boolean.mk_and
     ctx.ctx_z3 [ Arithmetic.mk_ge ctx.ctx_z3 e1 min_date; Arithmetic.mk_lt
     ctx.ctx_z3 e1 max_date; ] ) *)
  | And, _ -> app Boolean.mk_and
  | Or, _ -> app Boolean.mk_or
  | Xor, _ -> app2 Boolean.mk_xor
  | (Add_int_int | Add_rat_rat | Add_mon_mon), _ ->
    app Arithmetic.mk_add
  | ( (Sub_int_int | Sub_rat_rat | Sub_mon_mon),
      _ ) ->
    app Arithmetic.mk_sub
  | (Mult_int_int | Mult_rat_rat), _ ->
    app Arithmetic.mk_mul
  | (Div_int_int | Div_rat_rat | Div_mon_mon), [numerator; denominator] ->
    let ctx, numerator = translate_expr ctx numerator in
    let ctx, denominator = translate_expr ctx denominator in
    let denominator_zero =
      match Sort.get_sort_kind (Expr.get_sort denominator) with
      | Z3enums.INT_SORT -> Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 0
      | _ -> Arithmetic.Real.mk_numeral_i ctx.ctx_z3 0
    in
    let ctx =
      add_z3constraint
        (Boolean.mk_not ctx.ctx_z3
           (Boolean.mk_eq ctx.ctx_z3 denominator denominator_zero))
        ctx
    in
    let numerator =
      match op with
      | Div_int_int | Div_mon_mon -> z3_force_real ctx numerator
      | Div_rat_rat -> numerator
      | _ -> assert false
    in
    ctx, Arithmetic.mk_div ctx.ctx_z3 numerator denominator
  | Lt, _ -> app2 Arithmetic.mk_lt
  | Lte, _ -> app2 Arithmetic.mk_le
  | Gt, _ -> app2 Arithmetic.mk_gt
  | Gte, _ -> app2 Arithmetic.mk_ge
  | Eq, _ -> app2 Boolean.mk_eq
  | ConstructorCheck (enum, constructor), [value] ->
    let ctx, value = translate_expr ctx value in
    let recognizer =
      enum_z3_members ctx enum (Expr.get_sort value)
      |> List.find (fun (candidate, _, _, _) ->
           EnumConstructor.equal candidate constructor)
      |> fun (_, _, recognizer, _) -> recognizer
    in
    ctx, Expr.mk_app ctx.ctx_z3 recognizer [value]
  | ArrayAccess index, [array] ->
    let ctx, array = translate_expr ctx array in
    let _, elements = bounded_array_components ctx array in
    begin match List.nth_opt elements index with
    | Some element -> ctx, element
    | None -> failwith "[Z3 encoding] bounded-list access exceeds the bound"
    end
  | Map, _ ->
    failwith "[Z3 encoding] application of binary operator Map not supported"
  | Concat, _ ->
    failwith "[Z3 encoding] application of binary operator Concat not supported"
  | Filter, _ ->
    failwith "[Z3 encoding] application of binary operator Filter not supported"
  | Not, _ -> app1 Boolean.mk_not
  (* Omitting the log from the VC *)
  | Tag _, [e1] -> translate_expr ctx e1
  | Length, [e1] ->
    let ctx, array = translate_expr ctx e1 in
    let accessors = List.hd (Datatype.get_accessors (Expr.get_sort array)) in
    begin match accessors with
    | length :: _ ->
      ctx, (if encoded_list_bound ctx e1 array = 0 then
              Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 0
            else Expr.mk_app ctx.ctx_z3 length [array])
    | [] -> failwith "[Z3 encoding] malformed bounded-list datatype"
    end
  | ToRat_int, [e] ->
    let ctx, e = translate_expr ctx e in
    ctx, Arithmetic.Integer.mk_int2real ctx.ctx_z3 e
  | ToRat_mon, [e] ->
    let ctx, cents = translate_expr ctx e in
    let cents = Arithmetic.Integer.mk_int2real ctx.ctx_z3 cents in
    let hundred = Arithmetic.Real.mk_numeral_i ctx.ctx_z3 100 in
    ctx, Arithmetic.mk_div ctx.ctx_z3 cents hundred
  | _ -> ill_formed ()

and needs_value_summary expression =
  let rec atomic expression = match Mark.remove expression with
    | EVar _ | ELit _ | EExternal _ | EPos _ | EEmpty -> true
    | EStructAccess { e; _ } | ETupleAccess { e; _ }
    | EInj { e; _ } | EPureDefault e -> atomic e
    | EStruct { fields; _ } -> StructField.Map.for_all (fun _ -> atomic) fields
    | EArray values | ETuple values -> List.for_all atomic values
    | EAppOp { op = ((Map | Filter | Find | Fold | Reduce | Concat), _); _ } -> false
    | EAppOp { args; _ } -> List.for_all atomic args
    | _ -> false in
  not (atomic expression)

(** [translate_expr] translate the expression [vc] to its corresponding Z3
    expression **)
and translate_expr (ctx : context) (vc : typed expr) : context * Expr.expr =
  let previous = !(ctx.ctx_calendar_pending) in
  Fun.protect ~finally:(fun () -> ctx.ctx_calendar_pending := previous) (fun () ->
  let ctx, value = translate_expr_body ctx vc in
  let rec flush ctx = function
    | tail when tail == previous -> ctx
    | relation :: rest -> flush (add_z3constraint relation ctx) rest
    | [] -> failwith "calendar constraint accumulator lost its tail" in
  let ctx = flush ctx !(ctx.ctx_calendar_pending) in
  let id = Z3.AST.get_id (Expr.ast_of_expr value) in
  let bound = expression_list_bound ctx vc in
  let bound = match Hashtbl.find_opt ctx.ctx_z3bounds id with
    | Some former -> min former bound | None -> bound in
  Hashtbl.replace ctx.ctx_z3bounds id bound;
  ctx, value)

and translate_expr_body (ctx : context) (vc : typed expr) : context * Expr.expr =
  let translate_match_arm
      (head : Expr.expr)
      (ctx : context)
      (e : 'm expr * FuncDecl.func_decl list) : context * Expr.expr =
    let e, accessors = e in
    match Mark.remove e with
    | EAbs { binder; tys; _ } ->
      (* Create a fresh Catala variable to substitue and obtain the body *)
      let fresh_v = Var.make "arm!tmp" in
      let fresh_e = EVar fresh_v in

      (* Invariant: Catala enums always have exactly one argument *)
      let accessor = List.hd accessors in
      let proj = Expr.mk_app ctx.ctx_z3 accessor [head] in
      (* The fresh variable should be substituted by a projection into the enum
         in the body, we add this to the context *)
      let former_types = ctx.ctx_z3types in
      let ctx = bind_type_sort ctx (List.hd tys) (Expr.get_sort proj) in
      let ctx = add_z3matchsubst fresh_v proj ctx in

      let body = Bindlib.msubst binder [| fresh_e |] in
      let ctx, value = translate_expr ctx body in
      { ctx with ctx_z3types = former_types }, value
    (* Invariant: Catala match arms are always lambda*)
    | _ -> failwith "[Z3 encoding] : Arms branches inside VCs should be lambdas"
  in

  match Mark.remove vc with
  | EVar v -> (
    match Var.Map.find_opt v ctx.ctx_z3matchsubsts with
    | Some e ->
      (* A lambda or match binder already has its exact symbolic value. *)
      ctx, e
    | None -> begin
      match Var.Map.find_opt v ctx.ctx_z3valuecache with
      | Some (value, constraints) ->
        { ctx with
          ctx_z3constraints = constraints @ ctx.ctx_z3constraints },
        value
      | None -> begin match Var.Map.find_opt v ctx.ctx_z3definitions with
      | Some definition when ctx.ctx_lazy_relations && needs_value_summary definition
          && not (type_contains_function ctx (Shared_ast.Expr.ty definition)) ->
        let key = "definition:" ^ string_of_int (Bindlib.uid_of v) ^ ":"
          ^ symbolic_environment_key ctx definition in
        suspend_value ctx key definition
      | Some definition ->
        if Var.Set.mem v ctx.ctx_z3resolving then
          failwith
            ("[Z3 encoding] recursive value definition: " ^ unique_name v)
        else
          let former_resolving = ctx.ctx_z3resolving in
          let ctx =
            { ctx with
              ctx_z3resolving = Var.Set.add v ctx.ctx_z3resolving }
          in
          let previous_constraints = ctx.ctx_z3constraints in
          let ctx, value = translate_expr ctx definition in
          let rec new_constraints acc = function
            | constraints when constraints == previous_constraints ->
              List.rev acc
            | constraint_ :: rest ->
              new_constraints (constraint_ :: acc) rest
            | [] ->
              failwith
                "[Z3 encoding] definition constraint accumulator lost its tail"
          in
          let constraints = new_constraints [] ctx.ctx_z3constraints in
          let relation = Boolean.mk_and ctx.ctx_z3 constraints in
          let constraints = [relation] in
          { ctx with
            ctx_z3constraints = relation :: previous_constraints;
            ctx_z3resolving = former_resolving;
            ctx_z3valuecache =
              Var.Map.add v (value, constraints) ctx.ctx_z3valuecache },
          value
      | None when ctx.ctx_allow_fatal_dummy
                  && not (Var.Set.mem v ctx.ctx_z3freevars) ->
        failwith
          ("[Z3 encoding] unresolved non-input value: " ^ unique_name v)
      | None ->
      (* This is a genuine free variable: a verification variable in the
         generic backend, or the one BOBCat scope-input value. *)
      let (Typed { ty = t; _ }) = Mark.get vc in
      let name = unique_name v in
      let ctx = add_z3var name v t ctx in
      let ctx, ty = translate_typ ctx (Mark.remove t) in
      let z3_var = Expr.mk_const_s ctx.ctx_z3 name ty in
      ctx, z3_var
      end end)
  | EExternal _ -> failwith "[Z3 encoding] EExternal unsupported"
  | EStruct { fields; name } ->
    let ctx, z3_struct = find_or_create_struct ctx name in
    let constructor = List.hd (Datatype.get_constructors z3_struct) in
    let declared_fields =
      StructName.Map.find name ctx.ctx_decl.ctx_structs
      |> StructField.Map.bindings
    in
    let ctx, values =
      List.fold_left_map
        (fun ctx (field, _) ->
          translate_expr ctx (StructField.Map.find field fields))
        ctx declared_fields
    in
    ctx, Expr.mk_app ctx.ctx_z3 constructor values
  | EStructAccess { e; field; name } ->
    let next, demanded =
      if ctx.ctx_allow_fatal_dummy then resolve_value_head ctx vc else ctx, vc in
    if demanded != vc then translate_expr next demanded else
    let ctx, z3_struct = find_or_create_struct ctx name in
    (* This datatype should have only one constructor, corresponding to
       mk_struct. The accessors of this constructor correspond to the field
       accesses *)
    let accessors = List.hd (Datatype.get_accessors z3_struct) in
    let fields = StructName.Map.find name ctx.ctx_decl.ctx_structs in
    let idx_mappings = List.combine (StructField.Map.keys fields) accessors in
    let _, accessor =
      List.find (fun (field1, _) -> StructField.equal field field1) idx_mappings
    in
    let ctx, s = translate_expr ctx e in
    ctx, Expr.mk_app ctx.ctx_z3 accessor [s]
  | ETuple values ->
    let (Typed { ty; _ }) = Mark.get vc in
    let tys = match Mark.remove ty with TTuple tys -> tys | _ -> assert false in
    let ctx, sort = find_or_create_tuple ctx tys in
    let ctx, values = List.fold_left_map translate_expr ctx values in
    ctx, Expr.mk_app ctx.ctx_z3 (Tuple.get_mk_decl sort) values
  | ETupleAccess { e; index; size } ->
    let ctx, tuple = translate_expr ctx e in
    let accessors = Tuple.get_field_decls (Expr.get_sort tuple) in
    if List.length accessors <> size then
      failwith "[Z3 encoding] tuple access arity mismatch";
    let accessor = List.nth accessors index in
    ctx, Expr.mk_app ctx.ctx_z3 accessor [tuple]
  | EInj { e; cons; name } ->
    (* This node corresponds to creating a value for the enumeration [en], by
       calling the [idx]-th constructor of enum [en], with argument [e] *)
    let ctx, z3_arg = translate_expr ctx e in
    let (Typed { ty; _ }) = Mark.get vc in
    let ctx, z3_enum =
      match Mark.remove ty with
      | TOption payload_ty ->
        if EnumConstructor.equal cons ConstantNames.some_constr then
          find_or_create_option_sort ctx (Expr.get_sort z3_arg)
        else find_or_create_option ctx payload_ty
      | _ -> find_or_create_enum ctx name
    in
    let ctr =
      enum_z3_members ctx name z3_enum
      |> List.find (fun (cons1, _, _, _) -> EnumConstructor.equal cons cons1)
      |> fun (_, ctr, _, _) -> ctr
    in
    ctx, Expr.mk_app ctx.ctx_z3 ctr [z3_arg]
  | EMatch { e; cases; name = enum } ->
    let ctx, z3_arg = translate_expr ctx e in
    let (Typed { ty = subject_ty; _ }) = Mark.get e in
    let ctx, z3_enum =
      match Mark.remove subject_ty with
      | TOption _ -> ctx, Expr.get_sort z3_arg
      | _ -> find_or_create_enum ctx enum
    in
    let members = enum_z3_members ctx enum z3_enum in
    let ctx, z3_arms =
      List.fold_left_map
        (fun ctx (selected, arm) ->
          let previous = ctx.ctx_z3constraints in
          let ctx, value = translate_match_arm z3_arg ctx arm in
          guard_new_constraints ctx previous selected, value)
        ctx
        (EnumConstructor.Map.bindings cases
        |> List.map (fun (constructor, arm) ->
             let accessors =
               members
               |> List.find (fun (candidate, _, _, _) ->
                    EnumConstructor.equal candidate constructor)
               |> fun (_, _, _, accessors) -> accessors
             in
             let recognizer = members
               |> List.find (fun (candidate, _, _, _) -> EnumConstructor.equal candidate constructor)
               |> fun (_, _, recognizer, _) -> recognizer in
             Expr.mk_app ctx.ctx_z3 recognizer [z3_arg], (arm, accessors)))
    in
    let guarded_arms =
      List.map2
        (fun (constructor, _) arm ->
          let recognizer =
            members
            |> List.find (fun (candidate, _, _, _) ->
                 EnumConstructor.equal candidate constructor)
            |> fun (_, _, recognizer, _) -> recognizer
          in
          Expr.mk_app ctx.ctx_z3 recognizer [z3_arg], arm)
        (EnumConstructor.Map.bindings cases)
        z3_arms
    in
    (* A Catala match is exhaustive.  A nested ITE is equivalent to the old
       fresh-result-plus-one-implication-per-arm encoding, but it keeps large
       enum maps local and avoids flooding the persistent solver with thousands
       of auxiliary implications when the match appears in a bounded list. *)
    begin match List.rev guarded_arms with
    | [] -> failwith "[Z3 encoding] match without arms"
    | (_, fallback) :: remaining ->
      let result =
        List.fold_left
          (fun fallback (selected, arm) ->
            Boolean.mk_ite ctx.ctx_z3 selected arm fallback)
          fallback remaining
      in
      ctx, result
    end
  | EArray values ->
    let (Typed { ty; _ }) = Mark.get vc in
    let element_ty =
      match Mark.remove ty with
      | TArray element_ty -> element_ty
      | _ -> assert false
    in
    if List.length values > ctx.ctx_max_list_length then
      failwith "[Z3 encoding] literal list exceeds BOBCat's bound";
    let ctx, encoded = List.fold_left_map translate_expr ctx values in
    (* Generic library helpers retain a TVar on their literal-list node even
       after their arguments have been instantiated.  Prefer the actual value
       sort when the literal is nonempty so e.g. [x] inside polymorphic
       `contains` becomes a list of x's concrete sort rather than a list of an
       unrelated uninterpreted sort. *)
    let ctx, element_sort =
      match encoded with
      | value :: _ -> ctx, Expr.get_sort value
      | [] -> translate_typ ctx (Mark.remove element_ty)
    in
    let ctx, sort = find_or_create_array_sort ctx element_sort in
    let constructor = List.hd (Datatype.get_constructors sort) in
    let padding =
      List.init (ctx.ctx_max_list_length - List.length encoded) (fun _ ->
        canonical_padding ctx element_sort)
    in
    let length =
      Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 (List.length encoded)
    in
    ctx, Expr.mk_app ctx.ctx_z3 constructor (length :: encoded @ padding)
  | ELit l -> ctx, translate_lit ctx l
  | EAbs _ -> ctx, snd ctx.ctx_z3unit
  | EAppOp { op = (Map, _); args = [fn; list]; _ } ->
    let ctx, array = translate_expr ctx list in
    let length, elements =
      bounded_array_components ~limit:(encoded_list_bound ctx list array) ctx array
    in
    let ctx, mapped =
      translate_bounded_function ctx fn length elements false
    in
    let (Typed { ty; _ }) = Mark.get vc in
    let result_element_ty =
      match Mark.remove ty with TArray ty -> ty | _ -> assert false
    in
    let ctx, result_element_sort =
      match mapped with
      | value :: _ -> ctx, Expr.get_sort value
      | [] -> translate_typ ctx (Mark.remove result_element_ty)
    in
    let ctx, result_sort =
      find_or_create_array_sort ctx result_element_sort
    in
    let constructor = List.hd (Datatype.get_constructors result_sort) in
    let padding =
      List.init (ctx.ctx_max_list_length - List.length mapped) (fun _ ->
        canonical_padding ctx
          result_element_sort)
    in
    let result = Expr.mk_app ctx.ctx_z3 constructor (length :: mapped @ padding) in
    let bound = List.fold_left (fun bound element ->
      max bound (Option.value ~default:ctx.ctx_max_list_length (known_value_bound ctx element)))
      (encoded_list_bound ctx list array) mapped in
    Hashtbl.replace ctx.ctx_z3bounds (Z3.AST.get_id (Expr.ast_of_expr result)) bound;
    ctx, result
  | EAppOp { op = (Filter, _); args = [fn; list]; _ } ->
    let ctx, array = translate_expr ctx list in
    let length, elements =
      bounded_array_components ~limit:(encoded_list_bound ctx list array) ctx array
    in
    let ctx, predicates =
      translate_bounded_function ctx fn length elements false
    in
    let zero = Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 0 in
    let one = Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 1 in
    let prefixes_rev, count =
      List.fold_left
        (fun (prefixes, count) (index, predicate) ->
          let present =
            Arithmetic.mk_gt ctx.ctx_z3 length
              (Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 index)
          in
          let selected = Boolean.mk_and ctx.ctx_z3 [present; predicate] in
          ( (count, selected) :: prefixes,
            Arithmetic.mk_add ctx.ctx_z3
              [count; Boolean.mk_ite ctx.ctx_z3 selected one zero] ))
        ([], zero) (List.mapi (fun i p -> i, p) predicates)
    in
    let prefixes = List.rev prefixes_rev in
    let element_sort =
      match elements with
      | element :: _ -> Expr.get_sort element
      | [] ->
        let accessor = List.nth (List.hd (Datatype.get_accessors (Expr.get_sort array))) 1 in
        FuncDecl.get_range accessor
    in
    let packed =
      List.init ctx.ctx_max_list_length (fun output_index ->
        let fallback =
          canonical_padding ctx element_sort
        in
        List.fold_right2
          (fun element (prefix, selected) fallback ->
            let at_index =
              Boolean.mk_eq ctx.ctx_z3 prefix
                (Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 output_index)
            in
            Boolean.mk_ite ctx.ctx_z3
              (Boolean.mk_and ctx.ctx_z3 [selected; at_index])
              element fallback)
          elements prefixes fallback)
    in
    ctx,
    Expr.mk_app ctx.ctx_z3 (bounded_array_constructor array)
      (count :: packed)
  | EAppOp { op = (Find, _); args = [fn; list]; _ } ->
    let ctx, array = translate_expr ctx list in
    let length, elements =
      bounded_array_components ~limit:(encoded_list_bound ctx list array) ctx array
    in
    let ctx, predicates =
      translate_bounded_function ctx fn length elements true
    in
    let selected =
      List.map2
        (fun (index, predicate) element ->
          let present =
            Arithmetic.mk_gt ctx.ctx_z3 length
              (Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 index)
          in
          Boolean.mk_and ctx.ctx_z3 [present; predicate], element)
        (List.mapi (fun i p -> i, p) predicates) elements
    in
    let (Typed { ty; _ }) = Mark.get vc in
    let payload_ty =
      match Mark.remove ty with TOption ty -> ty | _ -> assert false
    in
    let payload_sort =
      match elements with
      | element :: _ -> Expr.get_sort element
      | [] -> snd (translate_typ ctx (Mark.remove payload_ty))
    in
    let ctx, option_sort = find_or_create_option_sort ctx payload_sort in
    let constructors = Datatype.get_constructors option_sort in
    begin match constructors with
    | absent :: present :: _ ->
      let fallback =
        canonical_padding ctx payload_sort
      in
      let value =
        List.fold_right
          (fun (condition, element) fallback ->
            Boolean.mk_ite ctx.ctx_z3 condition element fallback)
          selected fallback
      in
      let found =
        match selected with
        | [] -> Boolean.mk_false ctx.ctx_z3
        | _ -> Boolean.mk_or ctx.ctx_z3 (List.map fst selected)
      in
      ctx,
      Boolean.mk_ite ctx.ctx_z3 found
        (Expr.mk_app ctx.ctx_z3 present [value])
        (Expr.mk_app ctx.ctx_z3 absent [snd ctx.ctx_z3unit])
    | _ -> failwith "[Z3 encoding] malformed option datatype"
    end
  | EAppOp { op = (Reduce, _); args = [fn; list]; _ } ->
    let ctx, array = translate_expr ctx list in
    let length, elements =
      bounded_array_components ~limit:(encoded_list_bound ctx list array) ctx array
    in
    let (Typed { ty; _ }) = Mark.get vc in
    let payload_ty =
      match Mark.remove ty with TOption ty -> ty | _ -> assert false
    in
    let ctx, payload_sort =
      match elements with
      | element :: _ -> ctx, Expr.get_sort element
      | [] -> translate_typ ctx (Mark.remove payload_ty)
    in
    let ctx, option_sort = find_or_create_option_sort ctx payload_sort in
    begin match Datatype.get_constructors option_sort, elements with
    | absent :: present :: _, first :: rest ->
      let ctx, reduced =
        List.fold_left
          (fun (ctx, accumulator) (index, element) ->
            let previous = ctx.ctx_z3constraints in
            let ctx, next =
              translate_function_value ctx fn [accumulator; element]
            in
            let included =
              Arithmetic.mk_gt ctx.ctx_z3 length
                (Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 index)
            in
            let ctx = guard_new_constraints ctx previous included in
            ctx, Boolean.mk_ite ctx.ctx_z3 included next accumulator)
          (ctx, first)
          (List.mapi (fun index element -> index + 1, element) rest)
      in
      let nonempty =
        Arithmetic.mk_gt ctx.ctx_z3 length
          (Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 0)
      in
      ctx,
      Boolean.mk_ite ctx.ctx_z3 nonempty
        (Expr.mk_app ctx.ctx_z3 present [reduced])
        (Expr.mk_app ctx.ctx_z3 absent [snd ctx.ctx_z3unit])
    | absent :: _present :: _, [] ->
      ctx, Expr.mk_app ctx.ctx_z3 absent [snd ctx.ctx_z3unit]
    | _ -> failwith "[Z3 encoding] malformed option datatype"
    end
  | EAppOp { op = (Concat, _); args = [left; right]; _ } ->
    let ctx, left = translate_expr ctx left in
    let ctx, right = translate_expr ctx right in
    let left_length, left_elements = bounded_array_components ctx left in
    let right_length, right_elements = bounded_array_components ctx right in
    let length =
      Arithmetic.mk_add ctx.ctx_z3 [left_length; right_length]
    in
    let ctx =
      add_z3constraint
        (Arithmetic.mk_le ctx.ctx_z3 length
           (Arithmetic.Integer.mk_numeral_i ctx.ctx_z3
              ctx.ctx_max_list_length))
        ctx
    in
    let element_sort =
      match left_elements with
      | element :: _ -> Expr.get_sort element
      | [] -> failwith "[Z3 encoding] zero list bound has no element sort"
    in
    let elements =
      List.mapi
        (fun output_index left_element ->
          let fallback =
            canonical_padding ctx
              element_sort
          in
          let from_right =
            List.mapi
              (fun right_index right_element ->
                let index =
                  Arithmetic.mk_add ctx.ctx_z3
                    [ left_length;
                      Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 right_index ]
                in
                let selected =
                  Boolean.mk_and ctx.ctx_z3
                    [ Arithmetic.mk_gt ctx.ctx_z3 right_length
                        (Arithmetic.Integer.mk_numeral_i ctx.ctx_z3
                           right_index);
                      Boolean.mk_eq ctx.ctx_z3 index
                        (Arithmetic.Integer.mk_numeral_i ctx.ctx_z3
                           output_index) ]
                in
                selected, right_element)
              right_elements
            |> fun candidates ->
            List.fold_right
              (fun (selected, value) fallback ->
                Boolean.mk_ite ctx.ctx_z3 selected value fallback)
              candidates fallback
          in
          let from_left =
            Arithmetic.mk_gt ctx.ctx_z3 left_length
              (Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 output_index)
          in
          Boolean.mk_ite ctx.ctx_z3 from_left left_element from_right)
        left_elements
    in
    ctx,
    Expr.mk_app ctx.ctx_z3 (bounded_array_constructor left)
      (length :: elements)
  | EAppOp { op = (Fold, _); args = [fn; init; list]; _ } ->
    let ctx, accumulator = translate_expr ctx init in
    let ctx, array = translate_expr ctx list in
    let length, elements =
      bounded_array_components ~limit:(encoded_list_bound ctx list array) ctx array
    in
    List.fold_left
      (fun (ctx, accumulator) (index, element) ->
        let previous = ctx.ctx_z3constraints in
        let ctx, next =
          translate_function_value ctx fn [accumulator; element]
        in
        let present =
          Arithmetic.mk_gt ctx.ctx_z3 length
            (Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 index)
        in
        let ctx = guard_new_constraints ctx previous present in
        ctx, Boolean.mk_ite ctx.ctx_z3 present next accumulator)
      (ctx, accumulator) (List.mapi (fun i e -> i, e) elements)
  | EAppOp { op; args; _ } -> translate_op ctx op args
  | EApp { f = head; args; _ } ->
    let lexical_let = match Mark.remove head with EAbs _ -> true | _ -> false in
    let ctx, head = resolve_value_head ctx head in
    (
    match Mark.remove head with
    | EVar v ->
      begin match Var.Map.find_opt v ctx.ctx_z3definitions with
      | Some definition ->
        let rec resolve seen e =
          match Mark.remove e with
          | EVar v ->
            if Var.Set.mem v seen then e
            else
              begin match Var.Map.find_opt v ctx.ctx_z3definitions with
              | Some definition -> resolve (Var.Set.add v seen) definition
              | None -> e
              end
          | _ -> e
        in
        begin match Mark.remove (resolve (Var.Set.singleton v) definition) with
        | EAbs { binder; _ }
          when Bindlib.mbinder_arity binder = List.length args ->
          let vars, body = Bindlib.unmbind binder in
          let ctx, z3_args = List.fold_left_map translate_expr ctx args in
          let former_substs = ctx.ctx_z3matchsubsts in
          let former_definitions = ctx.ctx_z3definitions in
          let ctx =
            List.fold_left2
              (fun ctx var arg -> add_z3matchsubst var arg ctx)
              ctx (Array.to_list vars) z3_args
          in
          let ctx =
            List.fold_left2
              (fun ctx var arg ->
                { ctx with
                  ctx_z3definitions =
                    Var.Map.add var arg ctx.ctx_z3definitions })
              ctx (Array.to_list vars) args
          in
          let ctx, result = translate_expr ctx body in
          { ctx with
            ctx_z3matchsubsts = former_substs;
            ctx_z3definitions = former_definitions }, result
        | _ ->
          failwith
            "[Z3 encoding] a bound function did not resolve to a lambda"
        end
      | None ->
        if ctx.ctx_allow_fatal_dummy then
          failwith
            ("[Z3 encoding] unresolved internal function: " ^ unique_name v)
        else
          let (Typed { ty = f_ty; _ }) = Mark.get head in
          let ctx, fd = find_or_create_funcdecl ctx v f_ty in
          (* Fold_right preserves argument order. *)
          let ctx, z3_args =
            List.fold_right
              (fun arg (ctx, acc) ->
                let ctx, z3_arg = translate_expr ctx arg in
                ctx, z3_arg :: acc)
              args (ctx, [])
          in
          ctx, Expr.mk_app ctx.ctx_z3 fd z3_args
      end
    | EExternal { name } ->
      let runtime_module, function_name = external_runtime_name name in
      begin match runtime_module, function_name, args with
      | ( ("List_internal" | "List_en" | "List_fr"),
          ("sequence" | "séquence"), [start; stop] ) ->
        (* Scalar endpoints need an additional output-length bound. Retain SAT
           witnesses, but never certify input-bounded UNSAT using that bound. *)
        ctx.ctx_capacity_limited := true;
        let ctx, start = translate_expr ctx start in
        let ctx, stop = translate_expr ctx stop in
        let zero = Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 0 in
        let positive = Arithmetic.mk_gt ctx.ctx_z3 stop start in
        let difference = Arithmetic.mk_sub ctx.ctx_z3 [stop; start] in
        let length = Boolean.mk_ite ctx.ctx_z3 positive difference zero in
        let ctx =
          add_z3constraint
            (Arithmetic.mk_le ctx.ctx_z3 length
               (Arithmetic.Integer.mk_numeral_i ctx.ctx_z3
                  ctx.ctx_max_list_length))
            ctx
        in
        let (Typed { ty; _ }) = Mark.get vc in
        let element_ty =
          match Mark.remove ty with TArray ty -> ty | _ -> assert false
        in
        let ctx, sort = find_or_create_array ctx element_ty in
        let constructor = List.hd (Datatype.get_constructors sort) in
        let elements =
          List.init ctx.ctx_max_list_length (fun index ->
            Arithmetic.mk_add ctx.ctx_z3
              [start; Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 index])
        in
        ctx, Expr.mk_app ctx.ctx_z3 constructor (length :: elements)
      | ( ("List_internal" | "List_en" | "List_fr"),
          ("nth_element" | "nième_élément"), [list; index] ) ->
        let ctx, array = translate_expr ctx list in
        let ctx, index = translate_expr ctx index in
        let length, elements =
          bounded_array_components ~limit:(expression_list_bound ctx list)
            ctx array
        in
        let one = Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 1 in
        let valid =
          Boolean.mk_and ctx.ctx_z3
            [ Arithmetic.mk_ge ctx.ctx_z3 index one;
              Arithmetic.mk_le ctx.ctx_z3 index length ]
        in
        let (Typed { ty; _ }) = Mark.get vc in
        let payload_ty =
          match Mark.remove ty with TOption ty -> ty | _ -> assert false
        in
        let payload_sort =
          match elements with
          | element :: _ -> Expr.get_sort element
          | [] -> snd (translate_typ ctx (Mark.remove payload_ty))
        in
        let ctx, option_sort = find_or_create_option_sort ctx payload_sort in
        begin match Datatype.get_constructors option_sort with
        | absent :: present :: _ ->
          let fallback =
            canonical_padding ctx payload_sort
          in
          let selected =
            List.mapi
              (fun i element -> i + 1, element) elements
            |> fun candidates ->
            List.fold_right
              (fun (i, element) fallback ->
                Boolean.mk_ite ctx.ctx_z3
                  (Boolean.mk_eq ctx.ctx_z3 index
                     (Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 i))
                  element fallback)
              candidates fallback
          in
          ctx,
          Boolean.mk_ite ctx.ctx_z3 valid
            (Expr.mk_app ctx.ctx_z3 present [selected])
            (Expr.mk_app ctx.ctx_z3 absent [snd ctx.ctx_z3unit])
        | _ -> failwith "[Z3 encoding] malformed option datatype"
        end
      | ( ("Date_internal" | "Date_en" | "Date_fr"),
          ("of_ymd" | "of_year_month_day" | "depuis_année_mois_jour"),
          [_position; year; month; day] ) ->
        let rec constant_int expression =
          match Mark.remove expression with
          | ELit (LInt value) -> Some value
          | EVar var ->
            Option.bind
              (Var.Map.find_opt var ctx.ctx_z3definitions)
              constant_int
          | _ -> None
        in
        begin match constant_int year, constant_int month, constant_int day with
        | Some year, Some month, Some day ->
          let date =
            Runtime.date_of_numbers (Z.to_int year) (Z.to_int month)
              (Z.to_int day)
          in
          ctx, translate_lit ctx (LDate date)
        | _ ->
          let ctx, year = translate_expr ctx year in
          let ctx, month = translate_expr ctx month in
          let ctx, day = translate_expr ctx day in
          let ctx =
            add_z3constraint (DateEncoding.valid_ymd ctx year month day) ctx
          in
          ctx, DateEncoding.civil_to_date ctx year month day
        end
      | ( ("Date_en" | "Date_fr"),
          ("get_year" | "accès_année"), [date] ) ->
        let ctx, date = translate_expr ctx date in
        let year, _, _ = DateEncoding.date_to_civil ctx date in
        ctx, year
      | ( ("Date_en" | "Date_fr"),
          ("get_month" | "accès_mois"), [date] ) ->
        let ctx, date = translate_expr ctx date in
        let _, month, _ = DateEncoding.date_to_civil ctx date in
        ctx, month
      | ( ("Date_en" | "Date_fr"),
          ("get_day" | "accès_jour"), [date] ) ->
        let ctx, date = translate_expr ctx date in
        let _, _, day = DateEncoding.date_to_civil ctx date in
        ctx, day
      | ( ("Date_internal" | "Date_en" | "Date_fr"),
          ("to_ymd" | "to_year_month_day" | "vers_année_mois_jour"),
          [date] ) ->
        let ctx, date = translate_expr ctx date in
        let year, month, day = DateEncoding.date_to_civil ctx date in
        let (Typed { ty; _ }) = Mark.get vc in
        let tys = match Mark.remove ty with TTuple tys -> tys | _ -> assert false in
        let ctx, sort = find_or_create_tuple ctx tys in
        ctx,
        Expr.mk_app ctx.ctx_z3 (Tuple.get_mk_decl sort) [year; month; day]
      | ( ("Date_internal" | "Date_en" | "Date_fr"),
          ("last_day_of_month" | "dernier_jour_du_mois"), [date] ) ->
        let ctx, date = translate_expr ctx date in
        let year, month, _ = DateEncoding.date_to_civil ctx date in
        let day = DateEncoding.days_in_month ctx year month in
        ctx, DateEncoding.civil_to_date ctx year month day
      | ( ("Date_internal" | "Date_en" | "Date_fr"),
          ("add_rounded_down" | "add_round_down"
          | "ajout_arrondi_inférieur"), [date; duration] ) ->
        let ctx, date = translate_expr ctx date in
        let ctx, duration = translate_expr ctx duration in
        ctx, DateEncoding.add_dat_dur ctx Dates_calc.RoundDown date duration
      | ( ("Date_internal" | "Date_en" | "Date_fr"),
          ("add_rounded_up" | "add_round_up" | "ajout_arrondi_supérieur"),
          [date; duration] ) ->
        let ctx, date = translate_expr ctx date in
        let ctx, duration = translate_expr ctx duration in
        ctx, DateEncoding.add_dat_dur ctx Dates_calc.RoundUp date duration
      | ( ("Date_en" | "Date_fr"),
          ("sub_round_down" | "soustraction_arrondi_inférieur"),
          [date; duration] ) ->
        let ctx, date = translate_expr ctx date in
        let ctx, duration = translate_expr ctx duration in
        ctx,
        DateEncoding.add_dat_dur ctx Dates_calc.RoundDown date
          (DateEncoding.minus_dur ctx duration)
      | ( ("Date_en" | "Date_fr"),
          ("sub_round_up" | "soustraction_arrondi_supérieur"),
          [date; duration] ) ->
        let ctx, date = translate_expr ctx date in
        let ctx, duration = translate_expr ctx duration in
        ctx,
        DateEncoding.add_dat_dur ctx Dates_calc.RoundUp date
          (DateEncoding.minus_dur ctx duration)
      | _ ->
        failwith
          ("[Z3 encoding] unsupported external function " ^ runtime_module
           ^ "." ^ function_name)
      end
    | EAbs { binder; tys; _ } ->
      let (Typed { ty = result_ty; _ }) = Mark.get vc in
      if lexical_let || type_contains_function ctx result_ty
         || List.exists (fun arg -> let (Typed { ty; _ }) = Mark.get arg in
           type_contains_function ctx ty) args then begin
        let vars, body = Bindlib.unmbind binder in
        let former_definitions = ctx.ctx_z3definitions in
        let former_types = ctx.ctx_z3types in
        let ctx = List.fold_left2 (fun ctx ty arg ->
          let (Typed { ty = actual_ty; _ }) = Mark.get arg in
          let ctx, sort = translate_typ ctx (Mark.remove actual_ty) in
          bind_type_sort ctx ty sort) ctx tys args in
        let ctx = List.fold_left2 (fun ctx var arg ->
          { ctx with ctx_z3definitions = Var.Map.add var arg ctx.ctx_z3definitions })
          ctx (Array.to_list vars) args in
        let ctx, result = translate_expr ctx body in
        { ctx with ctx_z3types = former_types; ctx_z3definitions = former_definitions }, result
      end else begin
        let ctx, arguments = List.fold_left_map translate_expr ctx args in
        translate_function_value ctx head arguments
      end
    | _ when computed_context head ->
      translate_expr ctx (apply_computed head args (Shared_ast.Expr.ty vc))
    | _ ->
      let detail =
        match Mark.remove head with
        | EStructAccess { e = ((EVar var, _) as base); _ } ->
          if Var.Map.mem var ctx.ctx_z3definitions then
            let kind =
              match Mark.remove (snd (resolve_value_head ctx base)) with
              | EVar _ -> "variable" | EApp _ -> "application"
              | EStruct _ -> "struct" | EDefault _ -> "default"
              | EErrorOnEmpty _ -> "error-on-empty" | EIfThenElse _ -> "if"
              | EMatch _ -> "match" | EAbs _ -> "function"
              | EStructAccess _ -> "struct access" | EAppOp _ -> "operator"
              | EPureDefault _ -> "pure default" | EExternal _ -> "external"
              | EInj _ -> "injection" | _ -> "expression"
            in
            " (base definition resolves to " ^ kind ^ ")"
          else " (base variable has no symbolic definition)"
        | _ -> ""
      in
      Format.kasprintf failwith
        "[Z3 encoding] unsupported function head%s: %a" detail
        Shared_ast.Expr.format
        (Shared_ast.Expr.untype head |> Shared_ast.Expr.unbox))
  | EAssert _ when ctx.ctx_allow_fatal_dummy -> ctx, snd ctx.ctx_z3unit
  | EAssert e -> translate_expr ctx e
  | EFatalError _ when ctx.ctx_allow_fatal_dummy ->
    (* Guarded reachability separately asserts that the path leading to this
       leaf is impossible. A typed dummy lets surrounding matches/ITEs retain
       their ordinary value sort while that path condition is assembled. *)
    let (Typed { ty; _ }) = Mark.get vc in
    let ctx, sort = translate_typ ctx (Mark.remove ty) in
    ctx, Expr.mk_const_s ctx.ctx_z3 ("bobcat_fatal_" ^ string_of_int (Sort.get_id sort)) sort
  | EFatalError _ -> failwith "[Z3 encoding] EFatalError unsupported"
  | EDefault { excepts; just; cons } ->
    let (Typed { ty; _ }) = Mark.get vc in
    let inner_ty =
      match Mark.remove ty with
      | TDefault ty -> ty
      | _ -> failwith "[Z3 encoding] EDefault has a non-default type"
    in
    let ctx, z3_excepts = List.fold_left_map translate_expr ctx excepts in
    let ctx, z3_just = translate_expr ctx just in
    let ctx, z3_cons = translate_expr ctx cons in
    let ctx, (_, mk_default, _) = find_or_create_default ctx inner_ty in
    let app accessor default = Expr.mk_app ctx.ctx_z3 accessor [default] in
    let parts default =
      match List.hd (Datatype.get_accessors (Expr.get_sort default)) with
      | [defined; conflict; value] ->
        ( app defined default,
          app conflict default,
          app value default )
      | _ -> failwith "[Z3 encoding] malformed default datatype"
    in
    let ex_parts = List.map parts z3_excepts in
    let ex_defined = List.map (fun (defined, _, _) -> defined) ex_parts in
    let ex_conflict = List.map (fun (_, conflict, _) -> conflict) ex_parts in
    let two_defined =
      List.concat_map
        (fun (i, left) ->
          List.filter_map
            (fun (j, right) ->
              if i < j then
                Some (Boolean.mk_and ctx.ctx_z3 [left; right])
              else None)
            (List.mapi (fun j x -> j, x) ex_defined))
        (List.mapi (fun i x -> i, x) ex_defined)
    in
    let any xs =
      match xs with
      | [] -> Boolean.mk_false ctx.ctx_z3
      | _ -> Boolean.mk_or ctx.ctx_z3 xs
    in
    let any_defined = any ex_defined in
    let cons_defined, cons_conflict, cons_value = parts z3_cons in
    let no_exception = Boolean.mk_not ctx.ctx_z3 any_defined in
    let is_conflict = any (ex_conflict @ two_defined) in
    let is_conflict =
      Boolean.mk_or ctx.ctx_z3
        [ is_conflict;
          Boolean.mk_and ctx.ctx_z3 [no_exception; z3_just; cons_conflict] ]
    in
    let is_defined =
      Boolean.mk_or ctx.ctx_z3
        [ any_defined;
          Boolean.mk_and ctx.ctx_z3 [no_exception; z3_just; cons_defined] ]
    in
    let chosen =
      List.fold_right2
        (fun present (_, _, default_value) fallback ->
          Boolean.mk_ite ctx.ctx_z3 present default_value fallback)
        ex_defined ex_parts cons_value
    in
    ctx,
    Expr.mk_app ctx.ctx_z3 mk_default [is_defined; is_conflict; chosen]
  | EPureDefault inner ->
    let ctx, z3_inner = translate_expr ctx inner in
    let ctx, (_, mk_default, _) =
      find_or_create_default_sort ctx (Expr.get_sort z3_inner)
    in
    ctx,
    Expr.mk_app ctx.ctx_z3 mk_default
      [ Boolean.mk_true ctx.ctx_z3;
        Boolean.mk_false ctx.ctx_z3;
        z3_inner ]
  | EIfThenElse { cond = e_if; etrue = e_then; efalse = e_else } ->
    (* We rely on Z3's native encoding for ite to encode this node. There might
       be some interesting optimization in the future about when to split this
       node/bubble up the if_then_else, but this is left as future work *)
    let ctx, z3_if = translate_expr ctx e_if in
    let previous = ctx.ctx_z3constraints in
    let ctx, z3_then = translate_expr ctx e_then in
    let ctx = guard_new_constraints ctx previous z3_if in
    let previous = ctx.ctx_z3constraints in
    let ctx, z3_else = translate_expr ctx e_else in
    let ctx = guard_new_constraints ctx previous (Boolean.mk_not ctx.ctx_z3 z3_if) in
    ctx, Boolean.mk_ite ctx.ctx_z3 z3_if z3_then z3_else
  | EEmpty ->
    let (Typed { ty; _ }) = Mark.get vc in
    let inner_ty =
      match Mark.remove ty with
      | TDefault ty -> ty
      | _ -> failwith "[Z3 encoding] EEmpty has a non-default type"
    in
    let ctx, value_sort = translate_typ ctx (Mark.remove inner_ty) in
    let ctx, (sort, mk_default, _) = find_or_create_default ctx inner_ty in
    let dummy =
      Expr.mk_const_s ctx.ctx_z3
        ("bobcat_empty_value_" ^ string_of_int (Sort.get_id sort)) value_sort
    in
    ctx,
    Expr.mk_app ctx.ctx_z3 mk_default
      [ Boolean.mk_false ctx.ctx_z3;
        Boolean.mk_false ctx.ctx_z3;
        dummy ]
  | EErrorOnEmpty inner ->
    let ctx, z3_inner = translate_expr ctx inner in
    let accessors = List.hd (Datatype.get_accessors (Expr.get_sort z3_inner)) in
    let defined, conflict, value =
      match accessors with
      | [defined; conflict; value] -> defined, conflict, value
      | _ -> assert false
    in
    let is_defined = Expr.mk_app ctx.ctx_z3 defined [z3_inner] in
    let is_conflict = Expr.mk_app ctx.ctx_z3 conflict [z3_inner] in
    let valid =
      Boolean.mk_and ctx.ctx_z3
        [is_defined; Boolean.mk_not ctx.ctx_z3 is_conflict]
    in
    let ctx = add_z3constraint valid ctx in
    ctx, Expr.mk_app ctx.ctx_z3 value [z3_inner]
  | EPos _ -> ctx, snd ctx.ctx_z3unit
  | EBad -> failwith "[Z3 encoding] EBad unsupported"
  | _ -> .

and translate_bounded_function ctx fn length elements short_circuit =
  let searching = ref (Boolean.mk_true ctx.ctx_z3) in
  List.fold_left_map (fun ctx (index, element) ->
    let present = Arithmetic.mk_gt ctx.ctx_z3 length
        (Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 index) in
    let active = Boolean.mk_and ctx.ctx_z3 [present; !searching] in
    let previous = ctx.ctx_z3constraints in
    let ctx, value = translate_function_value ctx fn [element] in
    let ctx = guard_new_constraints ctx previous active in
    if short_circuit then searching := Boolean.mk_and ctx.ctx_z3
        [!searching; Boolean.mk_not ctx.ctx_z3 value];
    ctx, value) ctx (List.mapi (fun i e -> i, e) elements)

and translate_function_value ctx fn arguments =
  let rec resolve seen fn =
    match Mark.remove fn with
    | EVar var when not (Var.Set.mem var seen) ->
      begin match Var.Map.find_opt var ctx.ctx_z3definitions with
      | Some definition -> resolve (Var.Set.add var seen) definition
      | None -> fn
      end
    | _ -> fn
  in
  let fn = resolve Var.Set.empty fn in
  if ctx.ctx_lazy_relations then translate_abstract_call ctx fn arguments else
  let bounds = List.map (fun value ->
      Option.value ~default:ctx.ctx_max_list_length (known_value_bound ctx value)) arguments in
  (* Specialize the finite representation by argument shape, not argument
     value. All applications of this lexical function at those bounds share
     the same SMT definition. Catala functions are acyclic; Z3's definition API
     is used without introducing recursive source semantics or quantifiers. *)
  let key = string_of_int (expression_identity ctx fn) ^ ":"
    ^ symbolic_environment_key ctx fn ^ ":"
    ^ String.concat "," (List.map2 (fun arg bound ->
        string_of_int (Sort.get_id (Expr.get_sort arg)) ^ "/" ^ string_of_int bound)
        arguments bounds) in
  let instantiate ctx (value, validity, bound, formals) =
    let result = Expr.substitute value formals arguments in
    let validity = Expr.substitute validity formals arguments in
    Hashtbl.replace ctx.ctx_z3bounds (Z3.AST.get_id (Expr.ast_of_expr result)) bound;
    add_z3constraint validity ctx, result
  in
  match Hashtbl.find_opt ctx.ctx_summary_cache key with
  | Some summary -> instantiate ctx summary
  | None ->
    match Mark.remove fn with
    | EAbs { binder; tys; _ }
      when Bindlib.mbinder_arity binder = List.length arguments ->
      let vars, body = Bindlib.unmbind binder in
      let former_types = ctx.ctx_z3types in
      let ctx = List.fold_left2 (fun ctx ty arg ->
        bind_type_sort ctx ty (Expr.get_sort arg)) ctx tys arguments in
      let former_substs = ctx.ctx_z3matchsubsts in
      let former_values = ctx.ctx_z3valuecache in
      let ctx = { ctx with ctx_z3valuecache = Var.Map.empty } in
      let previous_constraints = ctx.ctx_z3constraints in
      let formals = List.map2 (fun argument bound ->
          let formal = Expr.mk_fresh_const ctx.ctx_z3 "formal_argument" (Expr.get_sort argument) in
          Hashtbl.replace ctx.ctx_z3bounds (Z3.AST.get_id (Expr.ast_of_expr formal)) bound;
          formal) arguments bounds in
      let ctx = List.fold_left2
          (fun ctx var argument -> add_z3matchsubst var argument ctx)
          ctx (Array.to_list vars) formals in
      let ctx, value = translate_expr ctx body in
      let rec delta = function
        | tail when tail == previous_constraints -> []
        | c :: rest -> c :: delta rest
        | [] -> failwith "summary constraint accumulator lost its tail" in
      let relation = Boolean.mk_and ctx.ctx_z3 (delta ctx.ctx_z3constraints) in
      (* A template is a quantifier-free DAG. Capture-avoiding substitution
         instantiates its formal arguments while Z3 hash-consing preserves
         shared subexpressions. No recursive-function theory is required. *)
      let bound = Option.value ~default:ctx.ctx_max_list_length (known_value_bound ctx value) in
      let summary = value, relation, bound, formals in
      Hashtbl.add ctx.ctx_summary_cache key summary;
      instantiate { ctx with ctx_z3types = former_types;
                             ctx_z3matchsubsts = former_substs;
                             ctx_z3valuecache = former_values;
                             ctx_z3constraints = previous_constraints } summary
    | _ -> failwith "[Z3 encoding] list operator expected a lambda"

and translate_abstract_call ctx fn arguments =
  let key = "call:" ^ string_of_int (expression_identity ctx fn) ^ ":"
    ^ symbolic_environment_key ctx fn ^ ":"
    ^ String.concat "," (List.map (fun arg ->
        string_of_int (Z3.AST.get_id (Expr.ast_of_expr arg))) arguments) in
  match Mark.remove fn with
  | EAbs { binder; tys; _ } when Bindlib.mbinder_arity binder = List.length arguments ->
    let vars, body = Bindlib.unmbind binder in
    let work = List.fold_left2 (fun ctx ty arg ->
      bind_type_sort ctx ty (Expr.get_sort arg)) ctx tys arguments in
    let work = List.fold_left2 (fun ctx var arg -> add_z3matchsubst var arg ctx)
      work (Array.to_list vars) arguments in
    let work, result = suspend_value work key body in
    { work with ctx_z3types = ctx.ctx_z3types;
                ctx_z3matchsubsts = ctx.ctx_z3matchsubsts }, result
  | _ -> failwith "[Z3 encoding] abstract call expected a lambda"

and suspend_value ctx key expression =
  match Hashtbl.find_opt ctx.ctx_abstract_calls key with
  | Some (result, valid) -> add_z3constraint valid ctx, result
  | None ->
    let ctx, sort = translate_typ ctx (Mark.remove (Shared_ast.Expr.ty expression)) in
    let result = Expr.mk_fresh_const ctx.ctx_z3 "abstract_result" sort in
    let valid = Expr.mk_fresh_const ctx.ctx_z3 "abstract_valid"
        (Boolean.mk_sort ctx.ctx_z3) in
    Hashtbl.add ctx.ctx_abstract_calls key (result, valid);
    Hashtbl.replace ctx.ctx_z3bounds (Z3.AST.get_id (Expr.ast_of_expr result))
      (expression_list_bound ctx expression);
    List.iter (fun e -> Hashtbl.replace ctx.ctx_abstract_symbols
      (Z3.AST.get_id (Expr.ast_of_expr e)) ()) [result; valid];
    Queue.add (valid, [result; valid], fun live ->
      let work = { live with
        ctx_z3definitions = ctx.ctx_z3definitions;
        ctx_z3types = ctx.ctx_z3types;
        ctx_z3matchsubsts = ctx.ctx_z3matchsubsts;
        ctx_z3valuecache = Var.Map.empty;
        ctx_z3resolving = Var.Set.empty;
        ctx_z3constraints = [] } in
      let work, exact = translate_expr work expression in
      let equations = [
        Boolean.mk_eq work.ctx_z3 valid
          (Boolean.mk_and work.ctx_z3 work.ctx_z3constraints);
        Boolean.mk_implies work.ctx_z3 valid
          (Boolean.mk_eq work.ctx_z3 result exact)] in
      { work with
        ctx_z3definitions = live.ctx_z3definitions;
        ctx_z3types = live.ctx_z3types;
        ctx_z3matchsubsts = live.ctx_z3matchsubsts;
        ctx_z3valuecache = live.ctx_z3valuecache;
        ctx_z3resolving = live.ctx_z3resolving;
        ctx_z3constraints = live.ctx_z3constraints }, equations)
      ctx.ctx_pending_relations;
    add_z3constraint valid ctx, result

(** [create_z3unit] creates a Z3 sort and expression corresponding to the unit
    type and value respectively. Concretely, we represent unit as a tuple with 0
    elements **)
let create_z3unit (ctx : Z3.context) : Z3.context * (Sort.sort * Expr.expr) =
  let unit_sort = Tuple.mk_sort ctx (Symbol.mk_string ctx "unit") [] [] in
  let mk_unit = Tuple.get_mk_decl unit_sort in
  let unit_val = Expr.mk_app ctx mk_unit [] in
  ctx, (unit_sort, unit_val)

let create_z3duration (ctx : Z3.context) : Sort.sort =
  let integer = Arithmetic.Integer.mk_sort ctx in
  Tuple.mk_sort ctx (Symbol.mk_string ctx "bobcat_duration")
    (List.map (Symbol.mk_string ctx) ["years"; "months"; "days"])
    [integer; integer; integer]

module Backend = struct
  type backend_context = context
  type vc_encoding = Z3.Expr.expr

  let print_encoding (vc : vc_encoding) : string = Expr.to_string vc

  type model = Z3.Model.model
  type solver_result = ProvenTrue | ProvenFalse of model option | Unknown

  let solve_vc_encoding (ctx : backend_context) (encoding : vc_encoding) :
      solver_result =
    let solver = Z3.Solver.mk_solver ctx.ctx_z3 None in
    (* We take the negation of the query to check for possible
       counterexamples *)
    let query = Boolean.mk_not ctx.ctx_z3 encoding in
    (* Add all the hypotheses stored in the context *)
    let query_and_hyps = query :: ctx.ctx_z3constraints in
    Z3.Solver.add solver query_and_hyps;
    match Z3.Solver.check solver [] with
    | UNSATISFIABLE -> ProvenTrue
    | SATISFIABLE -> ProvenFalse (Z3.Solver.get_model solver)
    | UNKNOWN -> Unknown

  let print_model (ctx : backend_context) (m : model) : string =
    print_model ctx m

  let is_model_empty (m : model) : bool = Z3.Model.get_decls m = []

  let translate_expr (ctx : backend_context) (e : typed expr) =
    translate_expr ctx e

  let encode_asserts (ctx : backend_context) (e : typed expr) =
    let ctx, vc = translate_expr ctx e in
    add_z3constraint vc ctx

  let init_backend () = Message.debug "Running Z3 version %s" Version.to_string

  let make_context (decl_ctx : decl_ctx) : backend_context =
    let cfg =
      (if Globals.disable_counterexamples () then [] else ["model", "true"])
      @ ["proof", "false"]
    in
    let z3_ctx = mk_context cfg in
    let z3_ctx, z3unit = create_z3unit z3_ctx in
    let z3duration = create_z3duration z3_ctx in
    {
      ctx_z3 = z3_ctx;
      ctx_decl = decl_ctx;
      ctx_function_types = function_type_closure decl_ctx;
      ctx_funcdecl = Var.Map.empty;
      ctx_z3vars = StringMap.empty;
      ctx_z3datatypes = EnumName.Map.empty;
      ctx_z3matchsubsts = Var.Map.empty;
      ctx_z3structs = StructName.Map.empty;
      ctx_z3types = [];
      ctx_head_values = Hashtbl.create 257;
      ctx_z3unit = z3unit;
      ctx_z3duration = z3duration;
      ctx_z3defaults = StringMap.empty;
      ctx_z3options = StringMap.empty;
      ctx_z3arrays = StringMap.empty;
      ctx_z3tuples = StringMap.empty;
      ctx_max_list_length = 5;
      ctx_symbolic_list_bound = 5;
      ctx_allow_fatal_dummy = false;
      ctx_z3definitions = Var.Map.empty;
      ctx_z3valuecache = Var.Map.empty;
      ctx_capacity_limited = ref false;
      ctx_z3bounds = Hashtbl.create 257;
      ctx_calendar_pending = ref [];
      ctx_environment_ids = Hashtbl.create 257;
      ctx_expression_ids = ExpressionIdentity.create 257;
      ctx_pending_relations = Queue.create ();
      ctx_abstract_symbols = Hashtbl.create 257;
      ctx_relation_graph = Hashtbl.create 257;
      ctx_abstract_calls = Hashtbl.create 257;
      ctx_lazy_relations = false;
      ctx_summary_cache = Hashtbl.create 257;
      ctx_z3resolving = Var.Set.empty;
      ctx_z3freevars = Var.Set.empty;
      ctx_z3constraints = [];
    }
end

module Io = Io.MakeBackendIO (Backend)

type direct_session = {
  mutable direct_ctx : context;
  direct_input_ty : typ;
  direct_input_expr : Expr.expr;
  direct_solver : Z3.Solver.solver;
  mutable direct_objectives : Expr.expr StringMap.t;
  mutable direct_last_model : Model.model option;
  mutable direct_query_roots : Expr.expr list;
  mutable direct_failure_roots : Expr.expr list;
  mutable direct_unknowns : string StringMap.t;
  direct_compiled_definition_guards : (string, Expr.expr * Expr.expr list ref) Hashtbl.t;
  mutable direct_failures : (Runtime.code_location * bool ref * (unit -> unit)) list;
  direct_asserted_constraints : (int * int, unit) Hashtbl.t;
  mutable direct_complete : bool;
  mutable direct_errors : string list;
  direct_deferred_definitions : (unit -> unit) Queue.t;
  mutable direct_on_objective : string -> unit;
  mutable direct_lazy_target : string option;
}

let rec bounded_value_constraints ctx max_list_length ty value =
  match Mark.remove ty with
  | TArray element_ty ->
    let accessors = List.hd (Datatype.get_accessors (Expr.get_sort value)) in
    let length, elements =
      match accessors with
      | accessor :: elements ->
        Expr.mk_app ctx.ctx_z3 accessor [value], elements
      | [] -> assert false
    in
    let length_constraints =
      [ Arithmetic.mk_ge ctx.ctx_z3 length
          (Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 0);
        Arithmetic.mk_le ctx.ctx_z3 length
          (Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 max_list_length) ]
    in
    let element_constraints =
      List.mapi
        (fun index accessor ->
          let element = Expr.mk_app ctx.ctx_z3 accessor [value] in
          let present =
            Arithmetic.mk_gt ctx.ctx_z3 length
              (Arithmetic.Integer.mk_numeral_i ctx.ctx_z3 index)
          in
          let padding =
            let sort = Expr.get_sort element in
            Expr.mk_const_s ctx.ctx_z3
              ("bobcat_padding_"
               ^ Digest.(to_hex (string (Sort.to_string sort))))
              sort
          in
          Boolean.mk_implies ctx.ctx_z3 (Boolean.mk_not ctx.ctx_z3 present)
            (Boolean.mk_eq ctx.ctx_z3 element padding)
          :: (if index >= max_list_length then [] else
              bounded_value_constraints ctx max_list_length element_ty element
              |> List.map (Boolean.mk_implies ctx.ctx_z3 present)))
        elements
      |> List.concat
    in
    length_constraints @ element_constraints
  | TStruct name ->
    let fields = StructName.Map.find name ctx.ctx_decl.ctx_structs in
    let sort = StructName.Map.find name ctx.ctx_z3structs in
    let accessors = List.hd (Datatype.get_accessors sort) in
    List.map2
      (fun (_, field_ty) accessor ->
        bounded_value_constraints ctx max_list_length field_ty
          (Expr.mk_app ctx.ctx_z3 accessor [value]))
      (StructField.Map.bindings fields) accessors
    |> List.concat
  | TOption payload_ty ->
    let sort = Expr.get_sort value in
    begin match Datatype.get_recognizers sort, Datatype.get_accessors sort with
    | _ :: present :: _, _ :: (payload :: _) :: _ ->
      bounded_value_constraints ctx max_list_length payload_ty
        (Expr.mk_app ctx.ctx_z3 payload [value])
      |> List.map (fun constraint_ ->
           Boolean.mk_implies ctx.ctx_z3
             (Expr.mk_app ctx.ctx_z3 present [value]) constraint_)
    | _ -> []
    end
  | TEnum name ->
    let sort = EnumName.Map.find name ctx.ctx_z3datatypes in
    let constructors = EnumConstructor.Map.bindings
        (EnumName.Map.find name ctx.ctx_decl.ctx_enums) in
    List.map2
      (fun (_, payload_ty) (recognizer, accessors) ->
        match accessors with
        | payload :: _ ->
          bounded_value_constraints ctx max_list_length payload_ty
            (Expr.mk_app ctx.ctx_z3 payload [value])
          |> List.map (fun constraint_ ->
               Boolean.mk_implies ctx.ctx_z3
                 (Expr.mk_app ctx.ctx_z3 recognizer [value]) constraint_)
        | [] -> [])
      constructors
      (List.combine (Datatype.get_recognizers sort)
         (Datatype.get_accessors sort))
    |> List.concat
  | TDefault payload_ty ->
    let _, payload_sort = translate_typ ctx (Mark.remove payload_ty) in
    let _, _, accessors =
      StringMap.find (Sort.to_string payload_sort) ctx.ctx_z3defaults
    in
    begin match accessors with
    | defined :: _conflict :: payload :: _ ->
      bounded_value_constraints ctx max_list_length payload_ty
        (Expr.mk_app ctx.ctx_z3 payload [value])
      |> List.map (fun constraint_ ->
           Boolean.mk_implies ctx.ctx_z3
             (Expr.mk_app ctx.ctx_z3 defined [value]) constraint_)
    | _ -> []
    end
  | TTuple tys ->
    List.map2
      (fun ty accessor ->
        bounded_value_constraints ctx max_list_length ty
          (Expr.mk_app ctx.ctx_z3 accessor [value]))
      tys (Tuple.get_field_decls (Expr.get_sort value))
    |> List.concat
  | TLit TDate ->
    (* Concrete JSON replay accepts proleptic-Gregorian years 0 through 9999.
       Keeping symbolic dates in the same domain prevents SAT models which the
       concrete decoder cannot represent. *)
    let lower =
      DateEncoding.civil_to_date ctx
        (DateEncoding.int ctx 0) (DateEncoding.int ctx 1)
        (DateEncoding.int ctx 1)
    in
    let upper =
      DateEncoding.civil_to_date ctx
        (DateEncoding.int ctx 9999) (DateEncoding.int ctx 12)
        (DateEncoding.int ctx 31)
    in
    [Arithmetic.mk_ge ctx.ctx_z3 value lower;
     Arithmetic.mk_le ctx.ctx_z3 value upper]
  | TLit _ | TAbstract _ | TArrow _ | TVar _ | TForAll _
  | TClosureEnv | TError -> []

let create_direct_session
    ~lazy_relations
    (decl_ctx : decl_ctx)
    ~(input_var : typed expr Var.t)
    ~(input_ty : typ)
    ~(max_list_length : int)
    ~(array_capacity : int)
    ~(solver_timeout_ms : int) : direct_session =
  let ctx = Backend.make_context decl_ctx in
  (* The datatype needs enough slots for constants written by the program,
     independently of the bound imposed on symbolic input lists. *)
  let ctx =
    { ctx with
      ctx_max_list_length = array_capacity;
      ctx_symbolic_list_bound = max_list_length;
      ctx_allow_fatal_dummy = true;
      ctx_lazy_relations = lazy_relations;
      ctx_z3freevars = Var.Set.singleton input_var }
  in
  let ctx, input_sort = translate_typ ctx (Mark.remove input_ty) in
  let input_expr = Expr.mk_const_s ctx.ctx_z3 (unique_name input_var) input_sort in
  let solver = Z3.Solver.mk_solver ctx.ctx_z3 None in
  let params = Z3.Params.mk_params ctx.ctx_z3 in
  Z3.Params.add_int params (Z3.Symbol.mk_string ctx.ctx_z3 "timeout")
    solver_timeout_ms;
  Z3.Solver.set_parameters solver params;
  Z3.Solver.add solver
    (bounded_value_constraints ctx max_list_length input_ty input_expr);
  { direct_ctx = ctx;
    direct_input_ty = input_ty;
    direct_input_expr = input_expr;
    direct_solver = solver;
    direct_objectives = StringMap.empty;
    direct_last_model = None;
    direct_query_roots = [];
    direct_failure_roots = [];
    direct_unknowns = StringMap.empty;
    direct_compiled_definition_guards = Hashtbl.create 257;
    direct_failures = [];
    direct_asserted_constraints = Hashtbl.create 257;
    direct_complete = true;
    direct_errors = [];
    direct_deferred_definitions = Queue.create ();
    direct_lazy_target = None;
    direct_on_objective = (fun _ -> ()) }

let mark_capacity_limited session = session.direct_ctx.ctx_capacity_limited := true

let abstract_dependencies ctx expression =
  let seen = Hashtbl.create 31 in
  let pending = Stack.create () in
  let result = ref [] in
  Stack.push expression pending;
  while not (Stack.is_empty pending) do
    let value = Stack.pop pending in
    let id = Z3.AST.get_id (Expr.ast_of_expr value) in
    if not (Hashtbl.mem seen id) then begin
      Hashtbl.add seen id ();
      if Hashtbl.mem ctx.ctx_abstract_symbols id then result := id :: !result
      else if Z3.AST.get_ast_kind (Expr.ast_of_expr value) = Z3enums.APP_AST then
        List.iter (fun arg -> Stack.push arg pending) (Expr.get_args value)
    end
  done;
  !result

let refine_semantics session =
  let ctx = session.direct_ctx in
  let relevant = Hashtbl.create 127 in
  let work = Queue.create () in
  List.iter (fun root -> List.iter (fun id -> Queue.add id work)
    (abstract_dependencies ctx root))
    (session.direct_query_roots @ session.direct_failure_roots);
  while not (Queue.is_empty work) do
    let id = Queue.take work in
    if not (Hashtbl.mem relevant id) then begin
      Hashtbl.add relevant id ();
      Option.iter (List.iter (List.iter (fun id -> Queue.add id work)))
        (Hashtbl.find_opt ctx.ctx_relation_graph id)
    end
  done;
  let pending = ctx.ctx_pending_relations in
  let learned = ref 0 in
  for _ = 1 to Queue.length pending do
    let valid, outputs, expand = Queue.take pending in
    let needed = List.exists (fun e -> Hashtbl.mem relevant
        (Z3.AST.get_id (Expr.ast_of_expr e))) outputs in
    let active = match session.direct_last_model with
      | None -> true
      | Some model -> Option.fold ~none:true ~some:Boolean.is_true
          (Model.eval model valid true) in
    if needed && active then begin
      let ctx, equations = expand session.direct_ctx in
      session.direct_ctx <- ctx;
      List.iter (fun equation ->
        let ids = abstract_dependencies ctx equation in
        List.iter (fun id ->
          let former = Option.value ~default:[] (Hashtbl.find_opt ctx.ctx_relation_graph id) in
          Hashtbl.replace ctx.ctx_relation_graph id (ids :: former)) ids) equations;
      Z3.Solver.add session.direct_solver equations;
      incr learned
    end else Queue.add (valid, outputs, expand) pending
  done;
  !learned

let set_solver_timeout session timeout_ms =
  let timeout_ms = max 1 timeout_ms in
  let params = Z3.Params.mk_params session.direct_ctx.ctx_z3 in
  Z3.Params.add_int params
    (Z3.Symbol.mk_string session.direct_ctx.ctx_z3 "timeout") timeout_ms;
  Z3.Solver.set_parameters session.direct_solver params

let typed_expr_pos (e : typed expr) =
  let (Typed { pos; _ }) = Mark.get e in
  pos

let register_reach session objective reach =
  let reach =
    match StringMap.find_opt objective session.direct_objectives with
    | None -> reach
    | Some former ->
      Boolean.mk_or session.direct_ctx.ctx_z3 [former; reach]
  in
  session.direct_objectives <-
    StringMap.add objective reach session.direct_objectives;
  session.direct_on_objective objective

let mark_unknown session objective reason =
  session.direct_complete <- false;
  session.direct_errors <- reason :: session.direct_errors;
  if not (StringMap.mem objective session.direct_objectives) then
    session.direct_unknowns <-
      StringMap.add objective reason session.direct_unknowns

let rec objectives_in_expr objective_of_tag (e : typed expr) =
  let here =
    match Mark.remove e with
    | EAppOp { op = Tag ((Branching _ | Exception _) as tag), _; _ } ->
      Option.to_list (objective_of_tag tag (typed_expr_pos e))
    | _ -> []
  in
  let children =
    match Mark.remove e with
    | EAbs { binder; _ } ->
      let _, body = Bindlib.unmbind binder in [body]
    | EApp { f; args; _ } -> f :: args
    | EAppOp { args; _ } | EArray args | ETuple args -> args
    | EIfThenElse { cond; etrue; efalse } -> [cond; etrue; efalse]
    | EStruct { fields; _ } -> StructField.Map.values fields
    | EStructAccess { e; _ } | ETupleAccess { e; _ } | EInj { e; _ }
    | EAssert e | EPureDefault e | EErrorOnEmpty e -> [e]
    | EMatch { e; cases; _ } -> e :: EnumConstructor.Map.values cases
    | EDefault { excepts; just; cons } -> excepts @ [just; cons]
    | EExternal _ | EVar _ | ELit _ | EEmpty | EPos _ | EFatalError _ | EBad ->
      []
    | _ -> []
  in
  here @ List.concat_map (objectives_in_expr objective_of_tag) children

let mark_expr_unknown session objective_of_tag e reason =
  session.direct_complete <- false;
  session.direct_errors <- reason :: session.direct_errors;
  objectives_in_expr objective_of_tag e
  |> List.iter (fun objective -> mark_unknown session objective reason)

let resolve_callable definitions (e : typed expr) =
  let rec resolve seen (e : typed expr) =
  match Mark.remove e with
  | EVar var ->
    if Var.Set.mem var seen then e
    else
      Option.fold ~none:e ~some:(resolve (Var.Set.add var seen))
        (Var.Map.find_opt var definitions)
  | EAppOp { op = (Tag _, _); args = [inner]; _ } ->
    resolve seen inner
  | EApp { f; args; _ } ->
    begin match Mark.remove (resolve seen f) with
    | EAbs { binder; _ }
      when Bindlib.mbinder_arity binder = List.length args ->
      Bindlib.msubst binder (Array.of_list (List.map Mark.remove args))
      |> resolve seen
    | _ -> e
    end
  | EStructAccess { e = base; field; name } ->
    let base = resolve seen base in
    begin match Mark.remove base with
    | EStruct { fields; _ } ->
      StructField.Map.find_opt field fields
      |> Option.fold ~none:e ~some:(resolve seen)
    | _ when computed_context base -> project_computed base field name (Shared_ast.Expr.ty e)
    | _ -> e
    end
  | _ -> e
  in
  resolve Var.Set.empty e

let resolve_callable_environment definitions expression =
  let environment = ref definitions in
  let rec resolve seen e = match Mark.remove e with
    | EVar var when not (Var.Set.mem var seen) ->
      Option.fold ~none:e ~some:(resolve (Var.Set.add var seen))
        (Var.Map.find_opt var !environment)
    | EAppOp { op = (Tag _, _); args = [inner]; _ } -> resolve seen inner
    | EApp { f; args; _ } ->
      begin match Mark.remove (resolve seen f) with
      | EAbs { binder; _ } when Bindlib.mbinder_arity binder = List.length args ->
        let vars, body = Bindlib.unmbind binder in
        environment := List.fold_left2 (fun env var arg -> Var.Map.add var arg env)
          !environment (Array.to_list vars) args;
        resolve seen body
      | _ -> e
      end
    | EStructAccess { e = base; field; name } ->
      let base = resolve seen base in
      begin match Mark.remove base with
      | EStruct { fields; _ } -> resolve seen (StructField.Map.find field fields)
      | _ when computed_context base -> project_computed base field name (Shared_ast.Expr.ty e)
      | _ -> e
      end
    | _ -> e in
  let result = resolve Var.Set.empty expression in
  !environment, result

let reachable_objectives ~objective_of_tag ~definitions body =
  let definitions =
    List.fold_left
      (fun env (var, definition) -> Var.Map.add var definition env)
      Var.Map.empty definitions
  in
  let expanded = ref Var.Set.empty in
  let called = ref Var.Set.empty in
  let objectives = Hashtbl.create 64 in
  let rec visit env (e : typed expr) =
    begin match Mark.remove e with
    | EAppOp { op = Tag ((Branching _ | Exception _) as tag), _; _ } ->
      Option.iter (fun objective -> Hashtbl.replace objectives objective ())
        (objective_of_tag tag (typed_expr_pos e))
    | _ -> ()
    end;
    match Mark.remove e with
    | EVar var ->
      begin match Var.Map.find_opt var env with
      | Some definition when not (Var.Set.mem var !expanded) ->
        expanded := Var.Set.add var !expanded;
        visit env definition
      | _ -> ()
      end
    | EApp { f; args; _ } ->
      List.iter (visit env) args;
      visit_call env f args
    | EAbs _ -> ()
    | EAppOp { op = ((Map | Filter | Find | Reduce), _);
               args = [fn; list]; _ } ->
      visit env list;
      visit_call env fn []
    | EAppOp { op = (Fold, _); args = [fn; init; list]; _ } ->
      visit env init;
      visit env list;
      visit_call env fn []
    | EAppOp { args; _ } | EArray args | ETuple args ->
      List.iter (visit env) args
    | EIfThenElse { cond; etrue; efalse } ->
      List.iter (visit env) [cond; etrue; efalse]
    | EStruct { fields; _ } -> StructField.Map.iter (fun _ -> visit env) fields
    | EStructAccess { e; _ } | ETupleAccess { e; _ } | EInj { e; _ }
    | EAssert e | EPureDefault e | EErrorOnEmpty e -> visit env e
    | EMatch { e; cases; _ } ->
      visit env e;
      EnumConstructor.Map.iter
        (fun _ arm ->
          (* Match outcomes are source branches in their own right.  Some
             simplification paths retain the arm position but do not retain a
             nested Tag node, so enumerate the arm identity explicitly. *)
          Option.iter
            (fun objective -> Hashtbl.replace objectives objective ())
            (objective_of_tag (Branching None) (typed_expr_pos arm));
          visit env arm)
        cases
    | EDefault { excepts; just; cons } ->
      List.iter (visit env) excepts;
      visit env just;
      visit env cons
    | EExternal _ | ELit _ | EEmpty | EPos _ | EFatalError _ | EBad -> ()
    | _ -> ()
  and visit_call env (fn : typed expr) args =
    match Mark.remove fn with
    | EVar var ->
      begin match Var.Map.find_opt var env with
      | Some definition when not (Var.Set.mem var !called) ->
        called := Var.Set.add var !called;
        visit_call env definition args
      | _ -> ()
      end
    | _ ->
      let resolved = resolve_callable env fn in
      begin match Mark.remove resolved with
      | EAbs { binder; _ } ->
        let vars, body = Bindlib.unmbind binder in
        let env =
          if Array.length vars = List.length args then
            List.fold_left2
              (fun env var arg -> Var.Map.add var arg env)
              env (Array.to_list vars) args
          else env
        in
        visit env body
      | _ -> visit env fn
      end
  in
  visit definitions body;
  Hashtbl.fold (fun objective () acc -> objective :: acc) objectives []
  |> List.sort String.compare

let guarded_constraint ctx guard constraint_ =
  Boolean.mk_implies ctx.ctx_z3 guard constraint_

let encode_under_guard session guard e =
  let previous_constraints = session.direct_ctx.ctx_z3constraints in
  let ctx, value = translate_expr session.direct_ctx e in
  session.direct_ctx <- ctx;
  (* [add_z3constraint] prepends to this persistent list, so the former list
     is a physical tail of the new one. Walking only that prefix avoids the
     quadratic [List.length] + copy that dominated large historical scopes. *)
  let rec add_new = function
    | constraints when constraints == previous_constraints -> ()
    | constraint_ :: rest ->
      let key = Z3.AST.get_id (Expr.ast_of_expr guard),
                Z3.AST.get_id (Expr.ast_of_expr constraint_) in
      if not (Hashtbl.mem session.direct_asserted_constraints key) then begin
        Hashtbl.add session.direct_asserted_constraints key ();
        Z3.Solver.add session.direct_solver
          [guarded_constraint ctx guard constraint_]
      end;
      add_new rest
    | [] ->
      failwith "[Z3 encoding] constraint accumulator lost its previous tail"
  in
  add_new ctx.ctx_z3constraints;
  value

(* Failure obligations retain their exact symbolic call environment. They are
   activated by a concrete runtime location, never inferred from input values. *)
let defer_failure session e action =
  let types = session.direct_ctx.ctx_z3types in
  let substs = session.direct_ctx.ctx_z3matchsubsts in
  let definitions = session.direct_ctx.ctx_z3definitions in
  let run () =
    let former_types = session.direct_ctx.ctx_z3types in
      let former_substs = session.direct_ctx.ctx_z3matchsubsts in
    let former_definitions = session.direct_ctx.ctx_z3definitions in
    session.direct_ctx <- { session.direct_ctx with
      ctx_z3types = types; ctx_z3matchsubsts = substs; ctx_z3definitions = definitions };
    Fun.protect ~finally:(fun () ->
      session.direct_ctx <- { session.direct_ctx with
        ctx_z3types = former_types;
            ctx_z3matchsubsts = former_substs; ctx_z3definitions = former_definitions }) action
  in
  session.direct_failures <-
    (Shared_ast.Expr.pos_to_runtime (typed_expr_pos e), ref false, run)
    :: session.direct_failures

let refine_failure session locations =
  let learned = ref 0 in
  List.iter (fun (location, active, run) ->
    if not !active && List.exists (fun (failed : Runtime.code_location) ->
      String.equal location.Runtime.filename failed.filename
      && location.start_line <= failed.end_line
      && failed.start_line <= location.end_line) locations then begin
      run (); active := true; incr learned
    end) session.direct_failures;
  !learned

let rec resolve_definition definitions (e : typed expr) =
  match Mark.remove e with
  | EVar var ->
    begin match Var.Map.find_opt var definitions with
    | Some definition -> resolve_definition definitions definition
    | None -> e
    end
  | _ -> e

let rec compile_reach_expr
    ~reach_cache ~should_visit session objective_of_tag definitions guard (e : typed expr) =
  let guard = Expr.simplify guard None in
  if Boolean.is_false guard || not (should_visit definitions e) then () else
  let ctx () = session.direct_ctx.ctx_z3 in
  let compile =
    compile_reach_expr ~reach_cache ~should_visit session objective_of_tag definitions
  in
  let suspend_reach key target guard run =
    let use (active, reach) =
      Z3.Solver.add session.direct_solver [Boolean.mk_implies (ctx ()) guard active];
      register_reach session target (Boolean.mk_and (ctx ()) [guard; reach]) in
    match Hashtbl.find_opt reach_cache key with
    | Some summary -> use summary
    | None ->
    let reach = Expr.mk_fresh_const (ctx ()) "abstract_reach" (Boolean.mk_sort (ctx ())) in
    let active = Expr.mk_fresh_const (ctx ()) "active_call" (Boolean.mk_sort (ctx ())) in
    Hashtbl.add reach_cache key (active, reach);
    use (active, reach);
    let captured = session.direct_ctx in
    Hashtbl.replace captured.ctx_abstract_symbols (Z3.AST.get_id (Expr.ast_of_expr reach)) ();
    Queue.add (Boolean.mk_and (ctx ()) [active; reach], [reach], fun live ->
      let saved_objectives = session.direct_objectives in
      let saved_target = session.direct_lazy_target in
      session.direct_lazy_target <- Some target;
      session.direct_objectives <- StringMap.empty;
      session.direct_ctx <- { live with
        ctx_z3definitions = captured.ctx_z3definitions;
        ctx_z3types = captured.ctx_z3types;
        ctx_z3matchsubsts = captured.ctx_z3matchsubsts;
        ctx_z3valuecache = captured.ctx_z3valuecache };
      Fun.protect ~finally:(fun () ->
        session.direct_lazy_target <- saved_target;
        session.direct_objectives <- saved_objectives)
        (fun () ->
          run active;
          while not (Queue.is_empty session.direct_deferred_definitions) do
            Queue.take session.direct_deferred_definitions ()
          done;
          let exact = Option.value ~default:(Boolean.mk_false (ctx ()))
            (StringMap.find_opt target session.direct_objectives) in
          let next = { session.direct_ctx with
            ctx_z3definitions = live.ctx_z3definitions;
            ctx_z3types = live.ctx_z3types;
            ctx_z3matchsubsts = live.ctx_z3matchsubsts;
            ctx_z3valuecache = live.ctx_z3valuecache } in
          next, [Boolean.mk_eq (ctx ()) reach exact]))
      captured.ctx_pending_relations
  in
  let share_call key guard run =
    match session.direct_lazy_target with
    | Some target -> suspend_reach key target guard run
    | None -> match Hashtbl.find_opt session.direct_compiled_definition_guards key with
    | Some (_, callers) -> callers := guard :: !callers
    | None ->
      let active = Boolean.mk_const_s (ctx ())
        ("active_definition_" ^ string_of_int
          (Hashtbl.length session.direct_compiled_definition_guards)) in
      Hashtbl.add session.direct_compiled_definition_guards key (active, ref [guard]);
      let captured_types = session.direct_ctx.ctx_z3types in
      let captured_substs = session.direct_ctx.ctx_z3matchsubsts in
      let captured_definitions = session.direct_ctx.ctx_z3definitions in
      Queue.add (fun () ->
        let former_types = session.direct_ctx.ctx_z3types in
      let former_substs = session.direct_ctx.ctx_z3matchsubsts in
        let former_definitions = session.direct_ctx.ctx_z3definitions in
        session.direct_ctx <- { session.direct_ctx with
          ctx_z3types = captured_types;
            ctx_z3matchsubsts = captured_substs;
          ctx_z3definitions = captured_definitions };
        Fun.protect ~finally:(fun () ->
          session.direct_ctx <- { session.direct_ctx with
            ctx_z3types = former_types;
            ctx_z3matchsubsts = former_substs;
            ctx_z3definitions = former_definitions })
          (fun () -> run active)) session.direct_deferred_definitions
  in
  let compile_function guard fn arguments =
    let former_definitions = session.direct_ctx.ctx_z3definitions in
    let next_ctx, fn = resolve_value_head
        { session.direct_ctx with ctx_z3definitions = definitions } fn in
    let definitions = next_ctx.ctx_z3definitions in
    session.direct_ctx <- next_ctx;
    match Mark.remove fn with
    | EAbs { binder; tys; _ }
      when Bindlib.mbinder_arity binder = List.length arguments ->
      let vars, body = Bindlib.unmbind binder in
      let former_types = session.direct_ctx.ctx_z3types in
      let former_substs = session.direct_ctx.ctx_z3matchsubsts in
      session.direct_ctx <- List.fold_left2 (fun ctx ty value ->
        bind_type_sort ctx ty (Expr.get_sort value)) session.direct_ctx tys arguments;
      session.direct_ctx <-
        List.fold_left2
          (fun ctx var argument -> add_z3matchsubst var argument ctx)
          session.direct_ctx (Array.to_list vars) arguments;
      compile_reach_expr ~reach_cache ~should_visit session objective_of_tag definitions guard body;
      session.direct_ctx <-
        { session.direct_ctx with ctx_z3definitions = former_definitions; ctx_z3types = former_types; ctx_z3matchsubsts = former_substs }
    | _ ->
      mark_expr_unknown session objective_of_tag fn
        "a bounded-list operator did not receive a lambda"
  in
  match Mark.remove e with
  | EAppOp
      { op = Tag ((Branching _ | Exception _) as tag), _;
        args = [inner]; _ } ->
    begin match objective_of_tag tag (typed_expr_pos e) with
    | None -> ()
    | Some objective ->
      begin match tag with
      | Branching _ -> register_reach session objective guard
      | Exception _ ->
        begin
          try
            let predicate = encode_under_guard session guard inner in
            register_reach session objective
              (Boolean.mk_and (ctx ()) [guard; predicate])
          with
          | Failure reason | Invalid_argument reason | Z3.Error reason ->
            mark_unknown session objective reason
        end
      | _ -> assert false
      end
    end;
    compile guard inner
  | EIfThenElse { cond; etrue; efalse } ->
    compile guard cond;
    if should_visit definitions etrue || should_visit definitions efalse then begin
      try
        let predicate = encode_under_guard session guard cond in
        let yes = Boolean.mk_and (ctx ()) [guard; predicate] in
        let no =
          Boolean.mk_and (ctx ()) [guard; Boolean.mk_not (ctx ()) predicate]
        in
        compile yes etrue;
        compile no efalse
      with
      | Failure reason | Invalid_argument reason | Z3.Error reason ->
        mark_expr_unknown session objective_of_tag etrue reason;
        mark_expr_unknown session objective_of_tag efalse reason
    end
  | EMatch { e = subject; cases; name = enum } ->
    compile guard subject;
    begin
      try
        let z3_subject = encode_under_guard session guard subject in
        let (Typed { ty = subject_ty; _ }) = Mark.get subject in
        let ctx', z3_enum =
          match Mark.remove subject_ty with
          | TOption _ -> session.direct_ctx, Expr.get_sort z3_subject
          | _ -> find_or_create_enum session.direct_ctx enum
        in
        session.direct_ctx <- ctx';
        let members = enum_z3_members session.direct_ctx enum z3_enum in
        EnumConstructor.Map.iter
          (fun constructor arm ->
            let former_types = session.direct_ctx.ctx_z3types in
      let former_substs = session.direct_ctx.ctx_z3matchsubsts in
            let _, _, recognizer, accessors =
              List.find
                (fun (candidate, _, _, _) ->
                  EnumConstructor.equal candidate constructor)
                members
            in
            match Mark.remove arm with
            | EAbs { binder; tys; _ } ->
              let vars, body = Bindlib.unmbind binder in
              let arm_guard =
                Boolean.mk_and (ctx ())
                  [ guard; Expr.mk_app (ctx ()) recognizer [z3_subject] ]
              in
              Option.iter
                (fun objective -> register_reach session objective arm_guard)
                (objective_of_tag (Branching None) (typed_expr_pos arm));
              let arm_ctx = session.direct_ctx in
              let arm_ctx =
                if Array.length vars = 1 then
                  add_z3matchsubst vars.(0)
                    (Expr.mk_app (ctx ()) (List.hd accessors) [z3_subject])
                    arm_ctx
                else arm_ctx
              in
              session.direct_ctx <- arm_ctx;
              compile arm_guard body;
              session.direct_ctx <-
                { session.direct_ctx with ctx_z3types = former_types; ctx_z3matchsubsts = former_substs }
            | _ -> mark_expr_unknown session objective_of_tag arm
                     "a DCalc match arm is not a lambda")
          cases
      with
      | Failure reason | Invalid_argument reason | Z3.Error reason ->
        EnumConstructor.Map.iter
          (fun _ arm ->
            Option.iter
              (fun objective -> mark_unknown session objective reason)
              (objective_of_tag (Branching None) (typed_expr_pos arm));
            mark_expr_unknown session objective_of_tag arm reason)
          cases
    end
  | EDefault { excepts; just; cons } ->
    List.iter (compile guard) excepts;
    begin
      try
        let encoded = List.map (encode_under_guard session guard) excepts in
        let defined_values =
          List.map
            (fun default ->
              match
                List.hd (Datatype.get_accessors (Expr.get_sort default))
              with
              | defined :: _ -> Expr.mk_app (ctx ()) defined [default]
              | _ -> assert false)
            encoded
        in
        let any_defined =
          match defined_values with
          | [] -> Boolean.mk_false (ctx ())
          | xs -> Boolean.mk_or (ctx ()) xs
        in
        let base_guard =
          Boolean.mk_and (ctx ())
            [guard; Boolean.mk_not (ctx ()) any_defined]
        in
        compile base_guard just;
        let z3_just = encode_under_guard session base_guard just in
        compile (Boolean.mk_and (ctx ()) [base_guard; z3_just]) cons
      with
      | Failure reason | Invalid_argument reason | Z3.Error reason ->
        mark_expr_unknown session objective_of_tag just reason;
        mark_expr_unknown session objective_of_tag cons reason
    end
  | EApp { f = (EAbs { binder; tys; _ }, _); args; _ } ->
    List.iter (compile guard) args;
    if Bindlib.mbinder_arity binder = List.length args then begin
      let vars, body = Bindlib.unmbind binder in
      let former_types = session.direct_ctx.ctx_z3types in
      let former_substs = session.direct_ctx.ctx_z3matchsubsts in
      let former_definitions = session.direct_ctx.ctx_z3definitions in
      let definitions = ref definitions in
      begin
        try
          Array.iteri
            (fun index var ->
              let arg = List.nth args index in
              definitions := Var.Map.add var arg !definitions;
              session.direct_ctx <-
                { session.direct_ctx with
                  ctx_z3definitions =
                    Var.Map.add var arg
                      session.direct_ctx.ctx_z3definitions };
              let (Typed { ty; _ }) = Mark.get arg in
              match Mark.remove ty with
              | TArrow _ ->
                ()
              | _ ->
                let value = encode_under_guard session guard arg in
                session.direct_ctx <- bind_type_sort session.direct_ctx (List.nth tys index) (Expr.get_sort value);
                session.direct_ctx <-
                  add_z3matchsubst var value session.direct_ctx)
            vars;
          compile_reach_expr ~reach_cache ~should_visit session objective_of_tag
            !definitions guard body
        with
        | Failure reason | Invalid_argument reason | Z3.Error reason ->
          mark_expr_unknown session objective_of_tag body reason
      end;
      session.direct_ctx <-
        { session.direct_ctx with
          ctx_z3types = former_types;
            ctx_z3matchsubsts = former_substs;
          ctx_z3definitions = former_definitions }
    end else
      mark_expr_unknown session objective_of_tag e
        "function arity mismatch during reachability compilation"
  | EApp { f; args; _ } ->
    compile guard f;
    let next_ctx, resolved = resolve_value_head
        { session.direct_ctx with ctx_z3definitions = definitions } f in
    let definitions = next_ctx.ctx_z3definitions in
    session.direct_ctx <- next_ctx;
    begin match Mark.remove resolved with
    | EAbs { binder; _ } ->
      List.iter (compile guard) args;
      let argument_key arg =
        let (Typed { ty; _ }) = Mark.get arg in
        if type_contains_function session.direct_ctx ty then
          "closure:" ^ string_of_int (expression_identity session.direct_ctx arg)
          ^ ":" ^ symbolic_environment_key session.direct_ctx arg
        else
          let value = encode_under_guard session guard arg in
          "value:" ^ string_of_int (Z3.AST.get_id (Expr.ast_of_expr value))
      in
      let key = "call:" ^ string_of_int (expression_identity session.direct_ctx resolved)
        ^ ":" ^ symbolic_environment_key session.direct_ctx resolved
        ^ ":" ^ String.concat ";" (List.map argument_key args) in
      share_call key guard (fun active ->
        compile_reach_expr ~reach_cache ~should_visit session objective_of_tag definitions active
          (EApp { f = resolved; args; tys = [] }, Mark.get e))
    | _ when computed_context resolved ->
      compile_reach_expr ~reach_cache ~should_visit session objective_of_tag definitions guard
        (apply_computed resolved args (Shared_ast.Expr.ty e))
    | _ ->
      compile guard resolved;
      List.iter (compile guard) args
    end
  | EAppOp { op = (((Map | Filter | Find) as operator), _); args = [fn; list]; _ } ->
    compile guard list;
    begin
      try
        let array = encode_under_guard session guard list in
        let length, elements =
          bounded_array_components
            ~limit:(encoded_list_bound session.direct_ctx list array)
            session.direct_ctx array
        in
        let searching = ref (Boolean.mk_true (ctx ())) in
        List.iteri
          (fun index element ->
            let present = Arithmetic.mk_gt (ctx ()) length
                (Arithmetic.Integer.mk_numeral_i (ctx ()) index) in
            let active = Boolean.mk_and (ctx ()) [guard; present; !searching] in
            compile_function active fn [element];
            if operator = Find then begin
              let previous = session.direct_ctx.ctx_z3constraints in
              let next_ctx, predicate = translate_function_value session.direct_ctx fn [element] in
              session.direct_ctx <- guard_new_constraints next_ctx previous active;
              searching := Boolean.mk_and (ctx ())
                [!searching; Boolean.mk_not (ctx ()) predicate]
            end)
          elements
      with
      | Failure reason | Invalid_argument reason | Z3.Error reason ->
      mark_expr_unknown session objective_of_tag fn reason
    end
  | EAppOp { op = (Reduce, _); args = [fn; list]; _ } ->
    compile guard list;
    begin
      try
        let array = encode_under_guard session guard list in
        let length, elements =
          bounded_array_components
            ~limit:(encoded_list_bound session.direct_ctx list array)
            session.direct_ctx array
        in
        begin match elements with
        | [] -> ()
        | first :: rest ->
          let accumulator = ref first in
          List.iteri
            (fun offset element ->
              let index = offset + 1 in
              let present =
                Arithmetic.mk_gt (ctx ()) length
                  (Arithmetic.Integer.mk_numeral_i (ctx ()) index)
              in
              let iteration_guard =
                Boolean.mk_and (ctx ()) [guard; present]
              in
              compile_function iteration_guard fn [!accumulator; element];
              let next_ctx, next =
                translate_function_value session.direct_ctx fn
                  [!accumulator; element]
              in
              session.direct_ctx <- next_ctx;
              accumulator :=
                Boolean.mk_ite (ctx ()) present next !accumulator)
            rest
        end
      with
      | Failure reason | Invalid_argument reason | Z3.Error reason ->
        mark_expr_unknown session objective_of_tag fn reason
    end
  | EAppOp { op = (Fold, _); args = [fn; init; list]; _ } ->
    compile guard init;
    compile guard list;
    begin
      try
        let accumulator = ref (encode_under_guard session guard init) in
        let array = encode_under_guard session guard list in
        let length, elements =
          bounded_array_components
            ~limit:(encoded_list_bound session.direct_ctx list array)
            session.direct_ctx array
        in
        List.iteri
          (fun index element ->
            let present =
              Arithmetic.mk_gt (ctx ()) length
                (Arithmetic.Integer.mk_numeral_i (ctx ()) index)
            in
            let iteration_guard = Boolean.mk_and (ctx ()) [guard; present] in
            compile_function iteration_guard fn [!accumulator; element];
            let next_ctx, next =
              translate_function_value session.direct_ctx fn
                [!accumulator; element]
            in
            session.direct_ctx <- next_ctx;
            accumulator := Boolean.mk_ite (ctx ()) present next !accumulator)
          elements
      with
      | Failure reason | Invalid_argument reason | Z3.Error reason ->
        mark_expr_unknown session objective_of_tag fn reason
    end
  | EAbs _ ->
    (* A lambda body is not executed merely because the closure is created.
       Applications above beta-reduce it; bounded higher-order list operators
       receive a dedicated unrolling translation separately. *)
    ()
  | EAppOp { args; _ } | EArray args | ETuple args ->
    List.iter (compile guard) args
  | EStruct { fields; _ } ->
    StructField.Map.iter (fun _ field -> compile guard field) fields
  | EAssert assertion ->
    (* Assertion predicates remain lazy, but their own source branches are
       ordinary coverage objectives and must retain executable instances. *)
    if reachable_objectives ~objective_of_tag
         ~definitions:(Var.Map.bindings definitions) assertion <> [] then
      compile guard assertion;
    defer_failure session e (fun () ->
      let predicate = encode_under_guard session guard assertion in
      let obligation = Boolean.mk_implies (ctx ()) guard predicate in
      session.direct_failure_roots <- obligation :: session.direct_failure_roots;
      Z3.Solver.add session.direct_solver [obligation])
  | EErrorOnEmpty inner ->
    compile guard inner;
    (* Normal execution requires a defined, nonconflicting default. Keep this
       obligation deferred, including when its value is outside the target's
       dependency slice. *)
    defer_failure session e (fun () ->
      let previous = session.direct_ctx.ctx_z3constraints in
      ignore (encode_under_guard session guard e);
      let rec retain = function
        | constraints when constraints == previous -> ()
        | constraint_ :: rest ->
          session.direct_failure_roots <-
            guarded_constraint session.direct_ctx guard constraint_
            :: session.direct_failure_roots;
          retain rest
        | [] -> failwith "[Z3 encoding] lost failure constraint tail"
      in
      retain session.direct_ctx.ctx_z3constraints)
  | EStructAccess { e; _ } | ETupleAccess { e; _ } | EInj { e; _ }
  | EPureDefault e -> compile guard e
  | EFatalError _ ->
    defer_failure session e (fun () ->
      let obligation = Boolean.mk_not (ctx ()) guard in
      session.direct_failure_roots <- obligation :: session.direct_failure_roots;
      Z3.Solver.add session.direct_solver [obligation])
  | EVar var ->
    begin match Var.Map.find_opt var definitions with
    | None -> ()
    | Some (EAbs _, _) -> ()
    | Some definition when session.direct_lazy_target <> None
        && not (needs_value_summary definition) -> compile guard definition
    | Some definition when session.direct_lazy_target <> None ->
      let key = "value:" ^ string_of_int (Bindlib.uid_of var) ^ ":"
        ^ symbolic_environment_key session.direct_ctx definition in
      suspend_reach key (Option.get session.direct_lazy_target) guard
        (fun guard -> compile guard definition)
    | Some definition ->
      let key = string_of_int (Bindlib.uid_of var) ^ ":"
        ^ symbolic_environment_key session.direct_ctx definition in
      begin match Hashtbl.find_opt session.direct_compiled_definition_guards key with
      | Some (_, callers) -> callers := guard :: !callers
      | None ->
        let active = Boolean.mk_const_s (ctx ())
          ("active_definition_" ^ string_of_int (Hashtbl.length session.direct_compiled_definition_guards)) in
        let callers = ref [guard] in
        Hashtbl.add session.direct_compiled_definition_guards key (active, callers);
        let captured_types = session.direct_ctx.ctx_z3types in
      let captured_substs = session.direct_ctx.ctx_z3matchsubsts in
        let captured_definitions = session.direct_ctx.ctx_z3definitions in
        Queue.add (fun () ->
          let former_types = session.direct_ctx.ctx_z3types in
      let former_substs = session.direct_ctx.ctx_z3matchsubsts in
          let former_definitions = session.direct_ctx.ctx_z3definitions in
          session.direct_ctx <- { session.direct_ctx with
            ctx_z3types = captured_types;
            ctx_z3matchsubsts = captured_substs;
            ctx_z3definitions = captured_definitions };
          compile active definition;
          session.direct_ctx <- { session.direct_ctx with
            ctx_z3types = former_types;
            ctx_z3matchsubsts = former_substs;
            ctx_z3definitions = former_definitions }) session.direct_deferred_definitions
      end
    end
  | EExternal _ | ELit _ | EEmpty | EPos _ | EBad ->
    ()
  | _ -> ()

let compile_reachability
    ?(on_objective = fun _ -> ())
    session ~objective_of_tag ~definitions body =
  let reach_cache = Hashtbl.create 257 in
  let entry = Boolean.mk_true session.direct_ctx.ctx_z3 in
  let definitions =
    List.fold_left
      (fun env (var, definition) -> Var.Map.add var definition env)
      Var.Map.empty definitions
  in
  session.direct_ctx <-
    { session.direct_ctx with ctx_z3definitions = definitions };
  session.direct_on_objective <- on_objective;
  Fun.protect
    ~finally:(fun () -> session.direct_on_objective <- (fun _ -> ()))
    (fun () ->
      compile_reach_expr ~reach_cache ~should_visit:(fun _ _ -> true) session objective_of_tag
        definitions entry body;
      (* Definition nodes are expanded breadth-first. Shallow objectives can
         therefore be solved and replayed before one deep historical/default
         chain monopolizes guarded formula construction. *)
      while not (Queue.is_empty session.direct_deferred_definitions) do
        Queue.take session.direct_deferred_definitions ()
      done;
      Hashtbl.iter (fun _ (active, callers) ->
        Z3.Solver.add session.direct_solver
          [Boolean.mk_eq session.direct_ctx.ctx_z3 active
             (Boolean.mk_or session.direct_ctx.ctx_z3 !callers)])
        session.direct_compiled_definition_guards)

let compile_objective
    ?(on_objective = fun _ -> ())
    ?(on_timing = fun _ _ -> ())
    ?(failure_locations = [])
    session ~objective_of_tag ~definitions objective body =
  let reach_cache = Hashtbl.create 257 in
  (* Re-slicing after a newly observed failure replaces the old abstraction.
     Keeping it as an OR alternative would let the solver bypass refinement. *)
  session.direct_objectives <- StringMap.remove objective session.direct_objectives;
  session.direct_lazy_target <- Some objective;
  let started = Sys.time () in
  let globals = List.fold_left (fun env (var, value) ->
    Var.Map.add var value env) Var.Map.empty definitions in
  let global_memo = Hashtbl.create 257 in
  let matches_failure e =
    let pos = Shared_ast.Expr.pos_to_runtime (typed_expr_pos e) in
    List.exists (fun (loc : Runtime.code_location) ->
      String.equal pos.filename loc.filename
      && pos.start_line <= loc.end_line && loc.start_line <= pos.end_line)
      failure_locations in
  (* A conservative effect census. All callers are retained, including callers
     through unknown higher-order parameters. No source-location ranking or
     candidate root selection is used: guards always start at the entry. *)
  let rec contains env seen e =
    let own = match Mark.remove e with
      | EAppOp { op = Tag ((Branching _ | Exception _) as tag), _; _ } ->
        Option.fold ~none:false ~some:(String.equal objective)
          (objective_of_tag tag (typed_expr_pos e))
      | EAssert _ | EErrorOnEmpty _ | EFatalError _ -> matches_failure e
      | _ -> false in
    own || match Mark.remove e with
    | EVar var ->
      if Var.Set.mem var seen then true else
      begin match Var.Map.find_opt var env with
      | None -> type_contains_function session.direct_ctx (Shared_ast.Expr.ty e)
      | Some definition ->
        let compute () = contains env (Var.Set.add var seen) definition in
        if Var.Map.mem var globals then
          let key = Bindlib.uid_of var in
          begin match Hashtbl.find_opt global_memo key with
          | Some answer -> answer
          | None -> let answer = compute () in
            Hashtbl.add global_memo key answer; answer
          end
        else compute ()
      end
    | EAbs { binder; _ } ->
      let _, body = Bindlib.unmbind binder in contains env seen body
    | EApp { f; args; _ } -> List.exists (contains env seen) (f :: args)
    | EMatch { e; cases; _ } ->
      contains env seen e || EnumConstructor.Map.exists (fun _ arm ->
        Option.fold ~none:false ~some:(String.equal objective)
          (objective_of_tag (Branching None) (typed_expr_pos arm))
        || contains env seen arm) cases
    | EAppOp { args; _ } | EArray args | ETuple args ->
      List.exists (contains env seen) args
    | EIfThenElse { cond; etrue; efalse } ->
      List.exists (contains env seen) [cond; etrue; efalse]
    | EStruct { fields; _ } ->
      StructField.Map.exists (fun _ e -> contains env seen e) fields
    | EStructAccess { e; _ } | ETupleAccess { e; _ } | EInj { e; _ }
    | EAssert e | EPureDefault e | EErrorOnEmpty e -> contains env seen e
    | EDefault { excepts; just; cons } ->
      List.exists (contains env seen) (just :: cons :: excepts)
    | _ -> false in
  let objective_of_tag tag pos =
    match objective_of_tag tag pos with
    | Some candidate when String.equal candidate objective -> Some candidate
    | _ -> None in
  let should_visit env e = contains env Var.Set.empty e in
  session.direct_ctx <- { session.direct_ctx with ctx_z3definitions = globals };
  on_timing "slice_selection" (Sys.time () -. started);
  let started = Sys.time () in
  session.direct_on_objective <- on_objective;
  Fun.protect ~finally:(fun () ->
    session.direct_on_objective <- (fun _ -> ());
    on_timing "slice_compilation" (Sys.time () -. started)) (fun () ->
    compile_reach_expr ~reach_cache ~should_visit session objective_of_tag globals
      (Boolean.mk_true session.direct_ctx.ctx_z3) body;
    while not (Queue.is_empty session.direct_deferred_definitions) do
      Queue.take session.direct_deferred_definitions ()
    done;
    Hashtbl.iter (fun _ (active, callers) ->
      Z3.Solver.add session.direct_solver
        [Boolean.mk_eq session.direct_ctx.ctx_z3 active
          (Boolean.mk_or session.direct_ctx.ctx_z3 !callers)])
      session.direct_compiled_definition_guards;
    let learned = refine_failure session failure_locations in
    if learned > 0 then Message.result "BOBCAT_REFINEMENT %s"
      (Yojson.Safe.to_string (`Assoc [
        "reason", `String "expanded failure dependency slice";
        "learned_obligations", `Int learned])))

let unknown_objectives session = StringMap.bindings session.direct_unknowns

let compiled_objectives session =
  StringMap.bindings session.direct_objectives |> List.map fst

type coverage_result =
  | Coverage_sat of Yojson.Safe.t * string list
  | Coverage_unsat
  | Coverage_unknown of string

let solve_uncovered
    (session : direct_session)
    ~(list_bound : int)
    (objectives : string list) : coverage_result =
  let ctx = session.direct_ctx in
  let selected =
    List.filter_map
      (fun objective ->
        Option.map (fun reach -> objective, reach)
          (StringMap.find_opt objective session.direct_objectives))
      objectives
  in
  session.direct_query_roots <- List.map snd selected;
  match selected with
  | [] -> Coverage_unsat
  | _ ->
    let decode model predicted_pool =
      session.direct_last_model <- Some model;
      let predicted =
        List.filter_map
          (fun (objective, reach) ->
            if Boolean.is_true (eval_model model reach) then Some objective
            else None)
          predicted_pool
      in
      Coverage_sat
        ( json_of_z3model_expr ctx model ~scope_input:true
            session.direct_input_ty session.direct_input_expr,
          predicted )
    in
    let hard_constraints =
      bounded_value_constraints session.direct_ctx list_bound
        session.direct_input_ty session.direct_input_expr
      @ [Boolean.mk_or ctx.ctx_z3 (List.map snd selected)]
    in
    Z3.Solver.push session.direct_solver;
    Z3.Solver.add session.direct_solver hard_constraints;
    let answer =
    match Z3.Solver.check session.direct_solver [] with
    | Z3.Solver.SATISFIABLE ->
      begin match Z3.Solver.get_model session.direct_solver with
      | Some model -> decode model selected
      | None -> Coverage_unknown "Z3 returned SAT without a model"
      end
    | Z3.Solver.UNSATISFIABLE -> Coverage_unsat
    | Z3.Solver.UNKNOWN ->
      Coverage_unknown (Z3.Solver.get_reason_unknown session.direct_solver)
    in
    Z3.Solver.pop session.direct_solver 1;
    answer

let encoding_complete session =
  session.direct_complete && not !(session.direct_ctx.ctx_capacity_limited)

let encoding_statistics session =
  `Assoc ["input_bound", `Int session.direct_ctx.ctx_symbolic_list_bound;
          "array_capacity", `Int session.direct_ctx.ctx_max_list_length;
          "pending_relations", `Int (Queue.length session.direct_ctx.ctx_pending_relations);
          "value_summaries", `Int (Var.Map.cardinal session.direct_ctx.ctx_z3valuecache);
          "call_summaries", `Int (Hashtbl.length session.direct_ctx.ctx_summary_cache);
          "reachability_summaries", `Int (Hashtbl.length session.direct_compiled_definition_guards);
          "deferred_failures", `Int (List.length session.direct_failures);
          "asserted_constraints", `Int (Hashtbl.length session.direct_asserted_constraints);
          "incomplete_reasons", `List (List.map (fun x -> `String x)
            (List.sort_uniq String.compare session.direct_errors));
          "complete", `Bool (encoding_complete session)]
