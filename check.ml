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
exception InvalidArgument of pc * expression
exception MissingReturn


module IdentifierSet = Set.Make(Identifier)

let well_formed prog =
  (* Check if main exists and expects no arguments *)
  let check_main main =
    if main.name <> "main" then raise MissingMain;
    if [] <> main.formals then raise InvalidMain;
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
        | Array vs -> Array.iter check_value !vs
      in
      let check_simple_expr = function
        | Var _ -> ()
        | Constant v -> check_value v
      in
      let check_expr = function
        | Simple e -> check_simple_expr e
        | Op (_op, xs) ->
          List.iter check_simple_expr xs in
      let check_osr = function
        | Osr_move _ -> ()
        | Osr_materialize (_, Some e) -> check_expr e
        | Osr_materialize (_, None) -> () in
      match instr with
      | Call (_x, f, es) ->
        (check_expr f;
         List.iter check_expr es)
      | Declare (_, Some e)
      | Assign (_, e)
      | Branch (e, _, _)
      | Print e
      | Return e ->
        check_expr e
      | Declare (_, None)
      | Read _
      | Drop _
      | Label _ | Goto _ | Comment _ -> ()
      | Osr (e, _, _, _, osr) ->
        check_expr e;
        List.iter check_osr osr
      | Array_assign (_, i, e) ->
        check_expr i;
        check_expr e;
    in

    (* Check correctness of calls and osrs *)
    let check_instr pc instr =
      match[@warning "-4"] instr with
      | Call (x, f, exs) ->
        (* if it's a static call check that the function exists and if the
         * actual arguments are compatible with the formals *)
        begin match[@warning "-4"] f with
        | (Simple (Constant (Fun_ref f))) ->
          let func' = lookup_fun f in
          check_signature pc func' exs
        | _ -> ()
        end;
        check_fun_ref instr
      | Osr (e, f, v, l, osr) ->
        (* function and version mentioned in the osr need to exist *)
        let func = lookup_fun f in
        let vers = lookup_version func v in
        let _ = Instr.resolve vers.instrs l in
        check_fun_ref instr
      | _ -> check_fun_ref instr
    in
    Array.iteri check_instr instrs
  in

  let check_function func =
    if func.body = [] then raise (EmptyFunction func.name);

    let check seen var =
      if VarSet.mem var seen
      then raise (DuplicateParameter (func.name, var))
      else VarSet.add var seen
    in ignore (List.fold_left check VarSet.empty func.formals);

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


