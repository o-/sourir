open Instr

module Env = Map.Make(Variable)

type binding =
  | Val of value
  | Deleted

type input = IO.input
type trace = value list
type environment = binding Env.t

type call_result =
  | Assign of variable
  | Declare of variable

type status = Running | Result of value
type position = identifier * label * pc
type continuation = call_result * environment * position

type configuration = {
  input : input;
  trace : trace;
  heap : heap;
  env : environment;
  program : program;
  pc : pc;
  cur_fun : identifier;
  cur_vers : label;
  instrs : instructions;
  status : status;
  deopt : string option;
  continuation : continuation list;
}

type type_tag = Nil | Bool | Int | Fun_ref | Array
let get_tag : value -> type_tag = function
  | Nil -> Nil
  | Bool _ -> Bool
  | Int _ -> Int
  | Fun_ref _ -> Fun_ref
  | Array_ref _ -> Array

exception Unbound_variable of variable
exception Undefined_variable of variable
exception Redeclared_variable of variable
exception Invalid_heap
exception Arity_error of primop
exception Invalid_update
exception Invalid_clear

type type_error = {
  expected : type_tag;
  received : type_tag;
}
exception Type_error of type_error
type product_type_error = {
  expected : type_tag * type_tag;
  received : type_tag * type_tag;
}
exception ProductType_error of product_type_error

let lookup (env : environment) (x : variable) : value =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Deleted -> raise (Unbound_variable x)
  | Val v -> v

let deref (heap : heap) (a : address) : value array =
  match Heap.find a heap with
  | exception Not_found -> assert(false)
  | Array arr -> arr
  | Deleted_h -> raise Invalid_heap

let drop (heap : heap) (env : environment) x : heap * environment =
  match[@warning "-4"] Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Deleted -> raise (Unbound_variable x)
  | Val (Array_ref a) -> (Heap.add a Deleted_h heap, Env.add x Deleted env)
  | Val _ -> (heap, Env.add x Deleted env)

let assign (env : environment) (x : variable) (v : value) : environment =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Deleted -> raise (Unbound_variable x)
  | Val _ -> Env.add x (Val v) env

let declare (env : environment) (x : variable) (v : value) =
  match Env.find x env with
  | exception Not_found -> Env.add x (Val v) env
  | Deleted -> raise (Redeclared_variable x)
  | Val _ -> raise (Redeclared_variable x)


let rec value_eq heap (v1 : value) (v2 : value) =
  match v1, v2 with
  | Nil, Nil -> true
  | Nil, _ | _, Nil -> false
  | Bool b1, Bool b2 -> b1 = b2
  | Bool _, _ | _, Bool _ -> false
  | Int n1, Int n2 -> n1 = n2
  | Int _, _ | _, Int _ -> false
  | Fun_ref f1, Fun_ref f2 -> f1 = f2
  | Fun_ref _, _ | _, Fun_ref _ -> false
  | Array_ref a1, Array_ref a2 ->
    let vs1, vs2 = deref heap a1, deref heap a2 in
    let forall2 p arr1 arr2 =
      Array.mapi (fun i v1 -> p v1 arr2.(i)) arr1
      |> Array.for_all (fun b -> b)
    in
    Array.length vs1 = Array.length vs2
    && forall2 (value_eq heap) vs1 vs2
  | Array_ref _, _ | _, Array_ref _ -> .
    (* The case above cannot happen (`.` means "unreachable case",
       this is called a refutation clause) because all constructors
       other than Array have been filtered before.  If you add a new
       constructor, this line may need to return "false" and you can
       add a refutation clause of the same shape for the new
       constructor. *)

let value_plus (v1 : value) (v2 : value) =
  match v1, v2 with
  | Int n1, Int n2 -> n1 + n2
  | (Int _ | Nil | Bool _ | Fun_ref _ | Array_ref _) as x1, x2 ->
      let expected = (Int, Int) in
      let received = get_tag x1, get_tag x2 in
      raise (ProductType_error { expected; received })

let value_neq heap (v1 : value) (v2 : value) =
  not (value_eq heap v1 v2)

let eval_simple prog heap env = function
  | Var x -> lookup env x
  | Constant c -> c

let get_int (v : value) =
  match v with
  | Int i -> i
  | (Nil | Bool _ | Fun_ref _ | Array_ref _) as other ->
     let expected, received = Int, get_tag other in
     raise (Type_error { expected; received })

let get_bool (v : value) =
  match v with
  | Bool b -> b
  | (Nil | Int _ | Fun_ref _ | Array_ref _) as other ->
     let expected, received = Bool, get_tag other in
     raise (Type_error { expected; received })

let get_fun (v : value) =
  match v with
  | Fun_ref f -> f
  | (Nil | Int _ | Bool _ | Array_ref _) as other ->
     let expected, received = Fun_ref, get_tag other in
     raise (Type_error { expected; received })

let get_array heap (v : value) =
  match v with
  | Array_ref a -> deref heap a
  | (Nil | Int _ | Bool _ | Fun_ref _) as other ->
     let expected, received = Array, get_tag other in
     raise (Type_error { expected; received })

let rec eval prog heap env : expression -> heap * value = function
  | Simple e -> heap, eval_simple prog heap env e
  | Op (op, es) ->
    begin match op, List.map (eval_simple prog heap env) es with
    | Eq, [v1; v2] -> heap, Bool (value_eq heap v1 v2)
    | Neq, [v1; v2] -> heap, Bool (value_neq heap v1 v2)
    | Plus, [v1; v2] -> heap, Int (value_plus v1 v2)
    | (Eq | Neq | Plus), _vs -> raise (Arity_error op)
    | Array_alloc, [size] ->
      let size = get_int size in
      let arr = Instr.Array (Array.make size (Nil : value)) in
      let a = Address.fresh () in
      Heap.add a arr heap, Array_ref a
    | Array_of_list, vs ->
      let arr = Instr.Array (Array.of_list vs) in
      let a = Address.fresh () in
      Heap.add a arr heap, Array_ref a
    | Array_index, [array; index] ->
      let array, index = get_array heap array, get_int index in
      heap, array.(index)
    | Array_length, [array] ->
      let array = get_array heap array in
      heap, Int (Array.length array)
    | ((Array_alloc | Array_index | Array_length), _) -> raise (Arity_error op)
    end

exception InvalidArgument
exception InvalidNumArgs

let reduce conf =
  let eval conf e = eval conf.program conf.heap conf.env e in
  let resolve instrs label = Instr.resolve instrs label in
  let pc' = conf.pc + 1 in
  assert (conf.status = Running);

  let instruction =
    let default_exit = (Simple (Constant (Int 0))) in
    if conf.pc < Array.length conf.instrs
    then conf.instrs.(conf.pc)
    else if conf.continuation = []
    then Return default_exit
    else assert (false)
  in

  let build_call_frame heap formals actuals =
    let eval_arg (env, heap) (formal, actual) =
      let heap, value = eval conf actual in
      (Env.add formal (Val value) env, heap)
    in
    let args = List.combine formals actuals in
    List.fold_left eval_arg (Env.empty, heap) args
  in

  let build_osr_frame osr_def old_env old_heap =
    let add (env, heap) = function
      | Osr_materialize (x, e) ->
        let heap, v = eval conf e in
        (Env.add x (Val v) env, heap)
      | Osr_move (x, x') ->
        begin match Env.find x' old_env with
        | exception Not_found -> raise (Unbound_variable x')
        | v -> (Env.add x' v env, heap)
        end
    in
    List.fold_left add (Env.empty, old_heap) osr_def
  in

  let apply_call f args =
    let heap, f = eval conf f in
    let func = lookup_fun conf.program (get_fun f) in
    if List.length func.formals <> List.length args then raise InvalidNumArgs;
    let version = Instr.active_version func in
    let call_env, heap = build_call_frame heap func.formals args in
    let cont_pos = (conf.cur_fun, conf.cur_vers, pc') in
    (call_env, heap, func, version, cont_pos)
  in

  match instruction with
  | Assign (x, rhs) ->
    begin match rhs with
      | Call (f, args) ->
        let call_env, heap, func, version, cont_pos = apply_call f args in
        { conf with
          env = call_env;
          instrs = version.instrs;
          pc = 0;
          cur_fun = func.name;
          cur_vers = version.label;
          continuation = (Assign x, conf.env, cont_pos) :: conf.continuation
        }
      | Expr e ->
        let heap, v = eval conf e in
        let env = assign conf.env x v in
        { conf with env; heap; pc = pc'}
      | Read ->
        let (IO.Next (v, input)) = conf.input () in
        let env = assign conf.env x v in
        { conf with env; input; pc = pc' }
      end
  | Declare (x, rhs) ->
    begin match rhs with
      | Call (f, args) ->
        let call_env, heap, func, version, cont_pos = apply_call f args in
        { conf with
          env = call_env;
          instrs = version.instrs;
          pc = 0;
          cur_fun = func.name;
          cur_vers = version.label;
          continuation = (Declare x, conf.env, cont_pos) :: conf.continuation
        }
      | Expr e ->
        let heap, v = eval conf e in
        let env = declare conf.env x v in
        { conf with env; heap; pc = pc'}
      | Read ->
        let (IO.Next (v, input)) = conf.input () in
        let env = declare conf.env x v in
        { conf with env; input; pc = pc' }
      end
  | Return e ->
     let heap, res = eval conf e in
     begin match conf.continuation with
     | [] ->
       { conf with
         status = Result res }
     | (res_acc, env, (f, v, pc)) :: cont ->
       let env =
         match res_acc with
         | Assign x -> assign env x res
         | Declare x -> declare env x res
       in
       let func = Instr.lookup_fun conf.program f in
       let version = Instr.get_version func v in
       { conf with
         env; heap;
         cur_fun = func.name;
         cur_vers = version.label;
         instrs = version.instrs;
         pc = pc';
         continuation = cont; }
     end
  | Drop x ->
    let heap, env = drop conf.heap conf.env x in
    { conf with
      heap; env;
      pc = pc';
    }
  | Array_assign (x, i, e) ->
    let heap, vi = eval conf i in
    let heap, ve = eval conf e in
    let arr = lookup conf.env x in
    let vs = get_array conf.heap arr in
    vs.(get_int vi) <- ve;
    { conf with
      heap;
      pc = pc';
    }
  | Branch (e, l1, l2) ->
     let heap, b = eval conf e in
     let b = get_bool b in
     { conf with heap; pc = resolve conf.instrs (if b then l1 else l2) }
  | Label _ -> { conf with pc = pc' }
  | Goto label -> { conf with pc = resolve conf.instrs label }
  | Print e ->
    let heap, v = eval conf e in
    { conf with
      trace = v :: conf.trace;
      heap;
      pc = pc';
    }
  | Osr {cond; target={func;version; label}; map} ->
    let heap, triggered = List.fold_left (fun (heap, t) cond ->
        let heap, b = eval conf cond in
        (heap, t || get_bool b)) (conf.heap, false) cond in
    if not triggered then
      { conf with
        heap;
        pc = pc';
      }
    else begin
      let osr_env, heap' = build_osr_frame map conf.env heap in
      let func = Instr.lookup_fun conf.program func in
      let version = Instr.get_version func version in
      let instrs = version.instrs in
      { conf with
        pc = resolve instrs label;
        env = osr_env;
        heap = heap';
        instrs = instrs;
        cur_fun = func.name;
        cur_vers = version.label;
        deopt = Some label;
      }
    end

let start program input pc : configuration = {
  input;
  trace = [];
  heap = Heap.empty;
  env = Env.empty;
  status = Running;
  deopt = None;
  program = program;
  cur_fun = "main";
  cur_vers = (Instr.active_version program.main).label;
  instrs = (Instr.active_version program.main).instrs;
  pc = pc;
  continuation = []
}

let stop conf =
  match conf.status with
  | Running -> false
  | Result _ -> true

let rec reduce_bounded (conf, n) =
  if n = 0 then conf
  else let conf = reduce conf in
    reduce_bounded (conf, n - 1)

let run_bounded input (prog, n) =
  let conf = start prog input 0 in
    reduce_bounded (conf, n)

let rec reduce_forever conf =
  if stop conf then conf
  else reduce_forever (reduce conf)

let run_forever input (program : program) =
  reduce_forever (start program input 0)

let read_trace conf = List.rev conf.trace

let rec reduce_interactive conf =
  if stop conf then conf
  else begin
    let conf = reduce conf in
    begin match conf.trace with
      | [] -> ()
      | vs -> print_endline (String.concat " " (List.map IO.string_of_value vs))
    end;
    reduce_interactive { conf with trace = [] }
  end

let run_interactive input program =
  reduce_interactive (start program input 0)
