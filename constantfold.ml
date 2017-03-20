open Instr

let const_prop instrs =
  let rec find_candidate pc =
    if pc = Array.length instrs then None else
    match instrs.(pc) with
    | Decl_const (x, Simple(Lit(n))) -> Some (pc, x, Simple(Lit(n)))
    | _ -> find_candidate (pc+1)
  in

  let convert x n instr =
    let replace e = Replace.var_in_exp x n e in
    match instr with
    | Decl_const (y, e) ->
      assert (x <> y);
      Decl_const (y, replace e)
    | Decl_mut (y, Some e) ->
      assert (x <> y);
      Decl_mut (y, Some (replace e))
    | Assign (y, e) ->
      assert (x <> y);
      Assign (y, replace e)
    | Branch (e, l1, l2) -> Branch (replace e, l1, l2)
    | Print e -> Print (replace e)
    | Osr (exp, l1, l2, env) ->
      let env' = List.map (fun osr_def ->
          match osr_def with
          | OsrConst (y, e) -> OsrConst (y, replace e)
          | _ -> osr_def) env
      in
      Osr (replace exp, l1, l2, env')
    | Drop y
    | Decl_mut (y, None)
    | Clear y
    | Read y ->
      assert (x <> y);
      instr
    | Label _ | Goto _ | Stop | Comment _ -> instr
    in
  find_candidate 0
