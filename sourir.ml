open Instr

let () =
  match Sys.argv.(-1 + Array.length Sys.argv) with
  | exception _ ->
    Printf.eprintf
      "You should provide a Sourir file to parse as command-line argument.\n\
       Example: %s examples/sum.sou\n%!"
      Sys.executable_name;
    exit 1
  | path ->
    let program : program =
      try Parse.parse_file path
      with Parse.Error error ->
        Parse.report_error error;
        exit 2
    in
    begin match Scope.infer program with
      | exception Scope.UndeclaredVariable (pc, xs) ->
        let line = pc+1 in
        begin match VarSet.elements xs with
          | [x] -> Printf.eprintf "Error: %s:%d Variable %s is not declared.\n%!" path line x
          | xs -> Printf.eprintf "Error: %s:%d Variables {%s} are not declared.\n%!"
                    path line (String.concat ", " xs)
        end;
        exit 1
      | exception Scope.UninitializedVariable (pc, xs) ->
        let line = pc+1 in
        begin match VarSet.elements xs with
          | [x] -> Printf.eprintf "Error: %s:%d Variable %s might be uninitialized.\n%!" path line x
          | xs -> Printf.eprintf "Error: %s:%d Variables {%s} might be uninitialized.\n%!"
                    path line (String.concat ", " xs)
        end;
        exit 1
      | exception Scope.DuplicateVariable (pc, xs) ->
        let line = pc+1 in
        begin match VarSet.elements xs with
          | [x] -> Printf.eprintf "Error: %s:%d Variable %s is declared more than once.\n%!" path line x
          | xs -> Printf.eprintf "Error: %s:%d Variables {%s} are declared more than once.\n%!"
                    path line (String.concat ", " xs)
        end;
        exit 1
      | scopes ->
        let program = if Array.exists (fun arg -> arg = "--prune") Sys.argv
          then
            let opt = Transform.branch_prune program in
            let () = Printf.printf "\nAfter branch pruning:\n%s\n" (Disasm.disassemble opt) in
            opt
          else program
        in
        let program = if Array.exists (fun arg -> arg = "--cm") Sys.argv
          then
            let opt = Codemotion.apply program in
            let () = Printf.printf "\nAfter program motion:\n%s\n" (Disasm.disassemble opt) in
            opt
          else program
        in
        Scope.check_whole_program program;
        ignore (Eval.run_interactive IO.stdin_input program.instructions)
    end
