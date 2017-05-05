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
type address = Address.t

type variable = Variable.t
type label = Label.t

module VarSet = Set.Make(Variable)

type variable_type = Mut_var | Const_var

type moded_var = variable_type * variable

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

type unique_pos = {func : label; version : label; label : label;}

type instructions = instruction array
and instruction =
  | Declare of variable * rhs
  | Assign of variable * rhs
  | Array_assign of variable * expression * expression
  | Return of expression
  | Drop of variable
  | Branch of expression * label * label
  | Label of label
  | Goto of label
  | Print of expression
  | Osr of {cond : expression list; target : unique_pos; map : osr_def list; }
and rhs =
  | Call of expression * argument list
  | Expr of expression
  | Read
and osr_def =
  | Osr_move of variable * variable
  | Osr_materialize of variable * expression
and argument = expression
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
  | Array_ref of address
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

type formal_parameter = variable

type version = {
  label : label;
  instrs : instructions;
  annotations : annotations option;
}
type afunction = {
  name : identifier;
  formals : formal_parameter list;
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
  | Array of value array
  | Deleted_h
type env_val

module Heap = Map.Make(Address)
type heap = heap_value Heap.t

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

let list_vars ls =
  let vs = List.map expr_vars ls in
  List.fold_left VarSet.union VarSet.empty vs

let declared_vars = function
  | Declare (x, _) -> VarSet.singleton x
  | (Assign _
    | Array_assign _
    | Drop _
    | Return _
    | Branch _
    | Label _
    | Goto _
    | Print _
    | Osr _) -> VarSet.empty

let rhs_vars = function
  | Call (e, es) ->
    let s = expr_vars e in
    let vs = List.map expr_vars es in
    List.fold_left VarSet.union s vs
  | Expr e ->
    expr_vars e
  | Read ->
    VarSet.empty

(* Which variables need to be in scope
 * Producer: declared_vars *)
let required_vars = function
  | Declare (x, rhs) ->
    rhs_vars rhs
  | Return e -> expr_vars e
  | Assign (x, rhs) ->
    VarSet.singleton x
    |> VarSet.union (rhs_vars rhs)
  | Array_assign (x, i, e) ->
    VarSet.singleton x
    |> VarSet.union (expr_vars i)
    |> VarSet.union (expr_vars e)
  | Drop x -> VarSet.singleton x
  | Branch (e, _l1, _l2) -> expr_vars e
  | Label _l | Goto _l -> VarSet.empty
  | Print e -> expr_vars e
  | Osr {cond; map} ->
    let exps = List.map (function
        | Osr_move (_, x) -> Simple (Var x)
        | Osr_materialize (_, e) -> e) map in
    VarSet.union (list_vars cond) (list_vars exps)

let assigned_vars = function
  | Declare (x, _)
  | Assign (x, _)
  | Array_assign (x, _, _) -> VarSet.singleton x
  | Return _
  | Drop _
  | Branch _
  | Label _
  | Goto _
  | Print _
  | Osr _ -> VarSet.empty

let dropped_vars = function[@warning "-4"]
  | Drop x -> VarSet.singleton x
  | _ -> VarSet.empty

(* Which variables are consumed *)
let used_vars = function
  | Declare(_, rhs)
  (* the assignee is only required to be in scope, but not used! *)
  | Assign(_, rhs) ->
    rhs_vars rhs
  | Return e -> expr_vars e
  | Branch (e, _, _)
  | Print e -> expr_vars e
  | Array_assign (x, i, e) ->
    VarSet.singleton x
    |> VarSet.union (expr_vars i)
    |> VarSet.union (expr_vars e)
  | Drop _
  | Label _
  | Goto _ -> VarSet.empty
  | Osr {cond; map} ->
    let exps = List.map (function
        | Osr_move (_, x) -> Simple (Var x)
        | Osr_materialize (_, e) -> e) map in
    VarSet.union (list_vars cond) (list_vars exps)

let changed_vars = function
  | Drop x
  | Declare (x, _)
  | Assign (x, _)
  | Array_assign (x, _, _) -> VarSet.singleton x
  | Return _
  | Branch _
  | Label _
  | Goto _
  | Print _
  | Osr _ -> VarSet.empty

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

let checkpoint_prefix = "checkpoint_"
let is_checkpoint_label l =
  let len = String.length checkpoint_prefix in
  String.length l > len && (String.sub l 0 11) = checkpoint_prefix
let checkpoint_label pc =
  checkpoint_prefix ^ (string_of_int pc)

let independent instr exp =
  VarSet.is_empty (VarSet.inter (changed_vars instr) (expr_vars exp))
