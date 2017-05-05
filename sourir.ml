open Instr

let quiet = ref false
let opts = ref []
let path = ref ""

let () =
  let cmd_args = [
    ("--quiet", Arg.Set quiet, "quiet");
    ("--opt", Arg.String (fun s -> opts := String.split_on_char ',' s), "Enable optimizations");
  ] in
  Arg.parse cmd_args (fun s ->
      if !path <> "" then raise (Arg.Bad ("Invalid argument "^s));
      path := s) "options";

  if !path = "" then (
    Printf.eprintf
      "You should provide a Sourir file to parse as command-line argument.\n\
       Example: %s examples/sum.sou\n%!"
      Sys.executable_name;
    exit 1);

  let program =
    try Parse.program_of_file !path
    with Parse.Error error ->
      Parse.report_error error;
      exit 2
  in

  opts := if !opts = ["all"] then Transform.all_opts else !opts;

  begin try Scope.check_program program with
  | Scope.ScopeExceptionAt (f, v, e) ->
    begin
      Printf.eprintf "Error in function %s version %s " f v;
      begin match e with
      | Scope.UndeclaredVariable (xs, pc) ->
        let l = pc+1 in
        begin match VarSet.elements xs with
          | [x] -> Printf.eprintf
                     "line %d: Variable %s is not declared.\n%!"
                     l x
          | xs -> Printf.eprintf
                    "line %d: Variables {%s} are not declared.\n%!"
                    l (String.concat ", " xs)
        end;
      | Scope.ExtraneousVariable (xs, pc) ->
        let l = pc+1 in
        let func = lookup_fun program f in
        let version = get_version func v in
        let annot = match version.annotations with | Some a -> a | None -> assert(false) in
        let annot_vars = match annot.(pc) with
          | None | Some (AtLeastScope _) ->
            (* we know from the exception-raising code that this cannot happen *)
            assert (false)
          | Some (ExactScope vars) ->
            VarSet.elements vars |>
            String.concat ", " |> Printf.sprintf " {%s}" in
        begin match VarSet.elements xs with
          | [x] -> Printf.eprintf
                     "line %d: Variable %s is present in scope but missing \
                     from the scope annotation%s.\n%!"
                     l x annot_vars
          | xs -> Printf.eprintf
                    "line %d: Variables {%s} are present in scope \
                     but missing from the scope annotation%s.\n%!"
                    l (String.concat ", " xs) annot_vars
        end;
      | Scope.DuplicateVariable (xs, pc) ->
        let l = pc+1 in
        begin match VarSet.elements xs with
          | [x] -> Printf.eprintf
                     "line %d: Variable %s is declared more than once.\n%!"
                     l x
          | xs -> Printf.eprintf
                    "line %d: Variables {%s} are declared more than once.\n%!"
                    l (String.concat ", " xs)
        end;
      | Scope.IncompatibleScope (scope1, scope2, pc) ->
        let func = lookup_fun program f in
        let version = get_version func v in
        let instrs = version.instrs in
        Disasm.pretty_print_version stderr (v, instrs);
        Scope.explain_incompatible_scope stderr scope1 scope2 pc;
        flush stderr;
      | _ -> assert(false)
      end;
      exit 1
    end
  end;

  begin try Check.well_formed program with
  | Check.MissingMain ->
    Printf.eprintf "Program is missing an explicit or implicit main function\n";
    exit 1
  | Check.InvalidMain ->
    Printf.eprintf "Main function cannot have arguments\n";
    exit 1
  | Check.DuplicateFunctionDeclaration f ->
    Printf.eprintf "Duplicate function declaration %s\n" f;
    exit 1
  | Check.DuplicateVersion (f, v) ->
    Printf.eprintf "Version %s in function %s is defined twice\n" v f;
    exit 1
  | Check.EmptyFunction f ->
    Printf.eprintf "Function %s has no body\n" f;
    exit 1
  | Check.DuplicateParameter (f, x) ->
    Printf.eprintf "Function %s : parameter %s is given twice\n" f x;
    exit 1
  | Check.ErrorAt (f, v, e) ->
    Printf.eprintf "Error in function %s version %s: " f v;
    begin match[@warning "-4"] e with
    | Check.MissingReturn ->
      Printf.eprintf "missing return statement\n";
    | Check.FunctionDoesNotExist f' ->
      Printf.eprintf "called function %s does not exist\n" f';
    | Check.VersionDoesNotExist (f', v') ->
      Printf.eprintf "osr target %s %s does not exist\n" f' v';
    | Check.InvalidNumArgs pc ->
      Printf.eprintf "at line %d: invalid number of arguments\n" (pc+1);
    | Check.InvalidArgument (pc, expression) ->
      Printf.eprintf "at line %d: invalid argument\n" (pc+1);
    | _ -> assert(false)
    end;
    exit 1
  end;

  let program = try Transform.(try_opt (optimize !opts) program) with
    | Transform.UnknownOptimization opt ->
      Printf.eprintf "Unknown optimization %s.\nValid optimizers are %s\n"
        opt (String.concat ", " Transform.all_opts);
      exit 1
  in

  if not !quiet then begin
    Printf.printf "After optimizations\n";
    Disasm.disassemble_o stdout program
  end;

  Scope.check_program program;

  let conf = Eval.run_interactive IO.stdin_input program in
  let open Eval in
  match conf.status with
  | Running -> assert(false)
  | Result (Int n) ->
    exit n
  | Result (Bool b) ->
    exit (if b then 1 else 0)
  | Result (Fun_ref _ | Array_ref _ | Nil) ->
    exit 0

