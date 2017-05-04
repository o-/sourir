open Instr

module Env = Map.Make(Variable)

type binding =
  | Val of value
  | Undef
  | Dropped

type input = IO.input
type trace = value list
type environment = binding Env.t

type status = Running | Result of value
type position = identifier * label * pc
type continuation = variable * environment * position

type configuration = {
  input : input;
  trace : trace;
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
  | Array _ -> Array

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

let drop env x =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Dropped -> raise (Unbound_variable x)
  | Val _ | Undef -> Env.add x Dropped env

let declare env x =
  match Env.find x env with
  | exception Not_found -> Env.add x Undef env
  | Val _ | Undef | Dropped -> raise (Redeclared_variable x)

let assign env x v =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Dropped -> raise (Unbound_variable x)
  | Undef | Val _ -> Env.add x (Val v) env

let lookup env x =
  match Env.find x env with
  | exception Not_found -> raise (Unbound_variable x)
  | Dropped -> raise (Unbound_variable x)
  | Undef -> raise (Undefined_variable x)
  | Val v -> v

let rec value_eq (v1 : value) (v2 : value) =
  match v1, v2 with
  | Nil, Nil -> true
  | Nil, _ | _, Nil -> false
  | Bool b1, Bool b2 -> b1 = b2
  | Bool _, _ | _, Bool _ -> false
  | Int n1, Int n2 -> n1 = n2
  | Int _, _ | _, Int _ -> false
  | Fun_ref f1, Fun_ref f2 -> f1 = f2
  | Fun_ref _, _ | _, Fun_ref _ -> false
  | Array vs1, Array vs2 ->
    let forall2 p arr1 arr2 =
      Array.mapi (fun i v1 -> p v1 arr2.(i)) arr1
      |> Array.for_all (fun b -> b)
    in
    Array.length !vs1 = Array.length !vs2
    && forall2 value_eq !vs1 !vs2
  | Array _, _ | _, Array _ -> .
    (* The case above cannot happen (`.` means "unreachable case",
       this is called a refutation clause) because all constructors
       other than Array have been filtered before.  If you add a new
       constructor, this line may need to return "false" and you can
       add a refutation clause of the same shape for the new
       constructor. *)

let value_plus (v1 : value) (v2 : value) =
  match v1, v2 with
  | Int n1, Int n2 -> n1 + n2
  | (Int _ | Nil | Bool _ | Fun_ref _ | Array _) as x1, x2 ->
      let expected = (Int, Int) in
      let received = get_tag x1, get_tag x2 in
      raise (ProductType_error { expected; received })

let value_neq (v1 : value) (v2 : value) =
  not (value_eq v1 v2)

let eval_simple prog env = function
  | Var x -> lookup env x
  | Constant c -> c

let get_int (v : value) =
  match v with
  | Int i -> i
  | (Nil | Bool _ | Fun_ref _ | Array _) as other ->
     let expected, received = Int, get_tag other in
     raise (Type_error { expected; received })

let get_bool (v : value) =
  match v with
  | Bool b -> b
  | (Nil | Int _ | Fun_ref _ | Array _) as other ->
     let expected, received = Bool, get_tag other in
     raise (Type_error { expected; received })

let get_fun (v : value) =
  match v with
  | Fun_ref f -> f
  | (Nil | Int _ | Bool _ | Array _) as other ->
     let expected, received = Fun_ref, get_tag other in
     raise (Type_error { expected; received })

let get_array (v : value) =
  match v with
  | Array vs -> vs
  | (Nil | Int _ | Bool _ | Fun_ref _) as other ->
     let expected, received = Array, get_tag other in
     raise (Type_error { expected; received })

let rec eval prog env = function
  | Simple e -> eval_simple prog env e
  | Op (op, es) ->
    begin match op, List.map (eval_simple prog env) es with
    | Eq, [v1; v2] -> Bool (value_eq v1 v2)
    | Neq, [v1; v2] -> Bool (value_neq v1 v2)
    | Plus, [v1; v2] -> Int (value_plus v1 v2)
    | (Eq | Neq | Plus), _vs -> raise (Arity_error op)
    | Array_alloc, [size] ->
      let size = get_int size in
      Array (ref (Array.make size (Nil : value)))
    | Array_of_list, vs -> Array (ref (Array.of_list vs))
    | Array_index, [array; index] ->
      let array, index = get_array array, get_int index in
      (!array).(index)
    | Array_length, [array] ->
      let array = get_array array in
      Int (Array.length !array)
    | ((Array_alloc | Array_index | Array_length), _) -> raise (Arity_error op)
    end

exception InvalidArgument
exception InvalidNumArgs

let reduce conf =
  let eval conf e = eval conf.program conf.env e in
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

  let build_call_frame formals actuals =
    let eval_arg env (formal, actual) =
        let value = eval conf actual in
        Env.add formal (Val value) env
    in
    let args = List.combine formals actuals in
    List.fold_left eval_arg Env.empty args
  in

  let build_osr_frame osr_def old_env =
    let add env = function
      | Osr_move (x, y) ->
        assign (declare env x) x (lookup old_env y)
      | Osr_materialize (x, Some e) ->
        assign (declare env x) x (eval conf e)
      | Osr_materialize (x, None) ->
        declare env x
    in
    List.fold_left add Env.empty osr_def
  in

  match instruction with
  | Call (x, f, args) ->
    let f = eval conf f in
    let func = lookup_fun conf.program (get_fun f) in
    if List.length func.formals <> List.length args then raise InvalidNumArgs;
    let version = Instr.active_version func in
    let call_env = build_call_frame func.formals args in
    let cont_pos = (conf.cur_fun, conf.cur_vers, pc') in
    { conf with
      env = call_env;
      instrs = version.instrs;
      pc = 0;
      cur_fun = func.name;
      cur_vers = version.label;
      continuation = (x, conf.env, cont_pos) :: conf.continuation
    }
  | Return e ->
     let res = eval conf e in
     begin match conf.continuation with
     | [] ->
       { conf with
         status = Result res }
     | (x, env, (f, v, pc)) :: cont ->
       let env = Env.add x (Val res) env in
       let func = Instr.lookup_fun conf.program f in
       let version = Instr.get_version func v in
       { conf with
         env = env;
         cur_fun = func.name;
         cur_vers = version.label;
         instrs = version.instrs;
         pc = pc;
         continuation = cont; }
     end
  | Comment _ -> { conf with
                   pc = pc' }
  | Drop x ->
     { conf with
       env = drop conf.env x;
       pc = pc';
     }
  | Declare (x, Some e) ->
     let v = eval conf e in
     { conf with
       env = assign (declare conf.env x) x v;
       pc = pc';
     }
  | Declare (x, None) ->
     { conf with
       env = declare conf.env x;
       pc = pc';
     }
  | Assign (x, e) ->
     let v = eval conf e in
     { conf with
       env = assign conf.env x v;
       pc = pc';
     }
  | Array_assign (x, i, e) ->
    let vi = eval conf i in
    let ve = eval conf e in
    let arr = lookup conf.env x in
    let vs = get_array arr in
    (!vs).(get_int vi) <- ve;
    { conf with
      pc = pc';
    }
  | Branch (e, l1, l2) ->
     let b = get_bool (eval conf e) in
     { conf with pc = resolve conf.instrs (if b then l1 else l2) }
  | Label _ -> { conf with pc = pc' }
  | Goto label -> { conf with pc = resolve conf.instrs label }
  | Read x ->
    let (IO.Next (v, input')) = conf.input () in
    { conf with
      env = assign conf.env x v;
      input = input';
      pc = pc';
    }
  | Print e ->
     let v = eval conf e in
     { conf with
       trace = v :: conf.trace;
       pc = pc';
     }
  | Osr (e, f, v, l, osr_def) ->
     let b = get_bool (eval conf e) in
     if not b then
       { conf with
         pc = pc';
       }
     else begin
       let osr_env = build_osr_frame osr_def conf.env in
       let osr_func = Instr.lookup_fun conf.program f in
       let osr_version = Instr.get_version osr_func v in
       let osr_instrs = osr_version.instrs in
       { conf with
         pc = resolve osr_instrs l;
         env = osr_env;
         instrs = osr_instrs;
         cur_fun = osr_func.name;
         cur_vers = osr_version.label;
         deopt = Some l;
       }
     end

let start program input pc : configuration = {
  input;
  trace = [];
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
      | vs -> print_endline (String.concat " " (List.map Instr.string_of_value vs))
    end;
    reduce_interactive { conf with trace = [] }
  end

let run_interactive input program =
  reduce_interactive (start program input 0)
