open Instr

(* These are exceptions at the scope of the program *)
exception MissingMain
exception InvalidMain
exception DuplicateFunctionDeclaration of identifier
exception DuplicateVersion of identifier * label
exception EmptyFunction of identifier
exception DuplicateParameter of identifier * variable

(* The following are exceptions at the scope of a particular
 * function body. To indicate the position where they occur
 * they will be wrapped in a ErrorAt exception. *)
exception ErrorAt of identifier * label * exn

exception FunctionDoesNotExist of identifier
exception VersionDoesNotExist of identifier * label
exception InvalidNumArgs of pc
exception InvalidArgument of pc * argument
exception MissingReturn

module IdentifierSet = Set.Make(Identifier)

let well_formed prog =
  (* Check if main exists and expects no arguments *)
  let check_main main =
    if main.name <> "main" then raise MissingMain;
    if main.formals <> [] then raise InvalidMain;
  in
  check_main prog.main;

  let lookup_version func label =
    try List.find (fun {label=l} -> label = l) func.body with
    | Not_found -> raise (VersionDoesNotExist (func.name, label))
  in
  let lookup_fun name =
    if name = "main" then prog.main else
    try List.find (fun {name = l} -> name = l) prog.functions with
    | Not_found -> raise (FunctionDoesNotExist name)
  in

  let functions = prog.main :: prog.functions in

  (* Formals args shall not contain duplicate variables *)
  let check_formals name formals =
    let check seen var =
      if VarSet.mem var seen
      then raise (DuplicateParameter (name, var))
      else VarSet.add var seen
    in ignore (List.fold_left check VarSet.empty formals)
  in

  let check_version func (version:version) =
    let instrs = version.instrs in

    if func.name <> "main" then
      begin if Array.length instrs = 0 then raise MissingReturn;
      begin match[@warning "-4"] instrs.((Array.length instrs) - 1) with
      | Return _ | Goto _ | Branch _ -> ()
      | _ -> raise MissingReturn end
    end;

    let check_signature pc (func:afunction) args =
      if (List.length args <> List.length func.formals)
      then raise (InvalidNumArgs pc)
    in

    let check_fun_ref instr =
      let rec check_value = function
        | Nil | Bool _ | Int _ -> ()
        | Fun_ref x -> ignore (lookup_fun x)
        | Array_ref _ -> ()
      in
      let check_simple_expr = function
        | Var _ -> ()
        | Constant v -> check_value v
      in
      let check_expr = function
        | Simple e -> check_simple_expr e
        | Op (_op, xs) ->
          List.iter check_simple_expr xs in
      let check_rhs = function
        | Call (e, es) ->
          check_expr e;
          List.iter check_expr es
        | Expr e ->
          check_expr e
        | Read -> () in
      let check_osr = function
        | Osr_materialize (_, e) -> check_expr e
        | Osr_move _ -> () in
      match instr with
      | Declare (_x, rhs) ->
        check_rhs rhs
      | Assign (_x, rhs) ->
        check_rhs rhs
      | Array_assign (_, i, e) ->
        check_expr i;
        check_expr e;
      | Branch (e, _, _)
      | Print e
      | Return e ->
        check_expr e
      | Drop _
      | Label _ | Goto _ -> ()
      | Osr {cond; map} ->
        List.iter check_expr cond;
        List.iter check_osr map
    in

    (* Check correctness of calls and osrs *)
    let check_instr pc instr =
      match[@warning "-4"] instr with
      | Assign (x, Call(f, exs))
      | Declare (x, Call(f, exs)) ->
        (* if it's a static call check that the function exists and if the
         * actual arguments are compatible with the formals *)
        begin match[@warning "-4"] f with
        | (Simple (Constant (Fun_ref f))) ->
          let func' = lookup_fun f in
          check_signature pc func' exs
        | _ -> ()
        end;
        check_fun_ref instr
      | Osr {target = {func; version; label}} ->
        (* check if the function exists and if the actual arguments
         * are compatible with the formals *)
        let func = lookup_fun func in
        let vers = lookup_version func version in
        let _ = Instr.resolve vers.instrs label in
        check_fun_ref instr
      | _ -> check_fun_ref instr
    in
    Array.iteri check_instr instrs
  in

  let check_function func =
    if func.body = [] then raise (EmptyFunction func.name);
    check_formals func.name func.formals;
    let check seen {label} =
      if VarSet.mem label seen
      then raise (DuplicateVersion (func.name, label))
      else VarSet.add label seen
    in ignore (List.fold_left check VarSet.empty func.body);
    List.iter (fun version ->
        try check_version func version with
        | e -> raise (ErrorAt (func.name, version.label, e))
      ) func.body
  in

  List.iter (fun func ->
      let all = List.filter (fun {name} -> name=func.name) functions in
      if List.length all > 1 then raise (DuplicateFunctionDeclaration func.name);
      check_function func;) functions;
  ()


