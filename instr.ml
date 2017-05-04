module Variable = struct
  type t = string
  let compare = String.compare
end

module Label = struct
  type t = string
  let compare = String.compare
end

module Address : sig
  type t = private int
  val compare : t -> t -> int
  val fresh : unit -> t
end = struct
  type t = int
  let compare (x : int) y = Pervasives.compare x y
  let counter = ref (-1)
  let fresh () = incr counter; !counter
end

type variable = Variable.t
type label = Label.t

module VarSet = Set.Make(Variable)

module Identifier = struct
  type t = string
  let compare = String.compare
end
type identifier = Identifier.t

module Pc = struct
  type t = int
  let compare (x : int) y = Pervasives.compare x y
end

type pc = Pc.t

type instructions = instruction array
and instruction =
  | Call of variable * expression * (expression list)
  | Return of expression
  | Declare of variable * (expression option)
  | Drop of variable
  | Assign of variable * expression
  | Array_assign of variable * expression * expression
  | Read of variable
  | Branch of expression * label * label
  | Label of label
  | Goto of label
  | Print of expression
  | Osr of expression * label * label * label * osr_def list
  | Comment of string
and osr_def =
  | Osr_move of variable * variable
  | Osr_materialize of variable * expression option
and expression =
  | Simple of simple_expression
  | Op of primop * simple_expression list
and simple_expression =
  | Constant of value
  | Var of variable
and value =
  | Nil
  | Bool of bool
  | Int of int
  | Fun_ref of string
  | Array of (value array) ref
and primop =
  | Eq
  | Neq
  | Plus
  | Array_alloc
  | Array_of_list
  | Array_index
  | Array_length

type scope_annotation =
  | ExactScope of VarSet.t
  | AtLeastScope of VarSet.t

type inferred_scope =
  | DeadScope
  | Scope of VarSet.t

type annotations = scope_annotation option array

type version = {
  label : label;
  instrs : instructions;
  annotations : annotations option;
}
type afunction = {
  name : identifier;
  formals : variable list;
  body : version list;
}
type program = {
  main : afunction;
  functions : afunction list;
}
type analysis_input = {
  formals : VarSet.t;
  instrs : instructions;
}

type heap_value =
  | Undefined
  | Value of value

type address = Address.t

let rec string_of_value : value -> string = function
  | Nil -> "nil"
  | Bool b -> string_of_bool b
  | Int n -> string_of_int n
  | Fun_ref f -> "'" ^ f
  | Array vs ->
    let ss = Array.to_list (Array.map string_of_value !vs) in
    "[" ^ String.concat "," ss ^ "]"

let value_of_string : string -> value = function
  | "nil" -> Nil
  | "true" -> Bool true
  | "false" -> Bool false
  (* Should we allow function literals as user input? *)
  | n ->
    try Int (int_of_string n) with _ ->
      Printf.kprintf invalid_arg "value_of_string %S" n
(* TODO add case for array *)

exception Unbound_label of label

let resolve (code : instructions) (label : string) =
  let rec loop i =
    if i >= Array.length code then raise (Unbound_label label)
    else if code.(i) = Label label then i
    else loop (i + 1)
  in loop 0

let simple_expr_vars = function
  | Var x -> VarSet.singleton x
  | Constant _ -> VarSet.empty

let expr_vars = function
  | Simple e -> simple_expr_vars e
  | Op (_op, xs) ->
    List.map simple_expr_vars xs
    |> List.fold_left VarSet.union VarSet.empty

let declared_vars = function
  | Call (x, _, _)
  | Declare (x, _) -> VarSet.singleton x
  | (Assign _
    | Array_assign _
    | Return _
    | Branch _
    | Label _
    | Goto _
    | Read _
    | Print _
    | Osr _
    | Drop _
    | Comment _) -> VarSet.empty

(* Which variables need to be in scope
 * Producer: declared_vars *)
let required_vars = function
  | Call (_x, f, es) ->
    let s = expr_vars f in
    let vs = List.map expr_vars es in
    List.fold_left VarSet.union s vs
  | Return e -> expr_vars e
  | Declare (_x, Some e) -> expr_vars e
  | Declare (_x, None) -> VarSet.empty
  | Drop x
  | Read x -> VarSet.singleton x
  | Assign (x, e) -> VarSet.union (VarSet.singleton x) (expr_vars e)
  | Array_assign (x, i, e) ->
    VarSet.singleton x
    |> VarSet.union (expr_vars i)
    |> VarSet.union (expr_vars e)
  | Branch (e, _l1, _l2) -> expr_vars e
  | Label _l | Goto _l -> VarSet.empty
  | Comment _ -> VarSet.empty
  | Print e -> expr_vars e
  | Osr (e, _, _, _, osr) ->
    let exps = List.map (function
        | Osr_move (_, x) -> Simple (Var x)
        | Osr_materialize (_, Some e) -> e
        | Osr_materialize (_, None) -> Simple (Constant Nil)) osr in
    let exps_vars = List.map expr_vars exps in
    List.fold_left VarSet.union (expr_vars e) exps_vars

let defined_vars = function
  | Call (x, _, _)
  | Declare (x, Some _)
  | Assign (x ,_)
  | Read x -> VarSet.singleton x
  | Drop _
  | Declare (_, None)
  | Return _
  | Branch _
  | Label _
  | Goto _
  | Comment _
  | Print _
  | Osr _
  | Array_assign _ (* The array has to be defined already. *)
    -> VarSet.empty

let dropped_vars = function
  | Drop x -> VarSet.singleton x
  | Return _
  | Call _
  | Declare _
  | Assign _
  | Array_assign _
  | Read _
  | Branch _
  | Label _
  | Goto _
  | Comment _
  | Print _
  | Osr _ -> VarSet.empty

(* Which variables need to be defined
 * Producer: defined_vars *)
let used_vars = function
  | Call (_x, f, es) ->
    let v = expr_vars f in
    let vs = List.map expr_vars es in
    List.fold_left VarSet.union v vs
  | Return e -> expr_vars e
  | Declare (_x, Some e) -> expr_vars e
  | Declare (_x, None) -> VarSet.empty
  (* the assignee is only required to be in scope, but not used! *)
  | Assign (_, e)
  | Branch (e, _, _)
  | Print e -> expr_vars e
  | Array_assign (x, i, e) ->
    VarSet.singleton x
    |> VarSet.union (expr_vars i)
    |> VarSet.union (expr_vars e)
  | Label _
  | Goto _
  | Comment _
  | Drop _
  | Read _ -> VarSet.empty
  | Osr (e, _, _, _, osr) ->
    let exps = List.map (function
        | Osr_move (_, x) -> Simple (Var x)
        | Osr_materialize (_, Some e) -> e
        | Osr_materialize (_, None) -> Simple (Constant Nil)) osr in
    let exps_vars = List.map expr_vars exps in
    List.fold_left VarSet.union (expr_vars e) exps_vars

exception FunctionDoesNotExist of identifier

let lookup_fun (prog : program) (f : identifier) : afunction =
  if f = "main" then prog.main else
  try List.find (fun {name} -> name = f) prog.functions with
  | Not_found -> raise (FunctionDoesNotExist f)

let get_version (func : afunction) (v : label) : version =
  List.find (fun {label} -> label = v) func.body

let active_version (func : afunction) : version =
  (List.hd func.body)

let replace_active_version (func : afunction) (repl : version) : afunction =
  { func with
    body = repl :: (List.tl func.body); }

module Value = struct
  let int n : value = Int n
  let bool b : value = Bool b
end

