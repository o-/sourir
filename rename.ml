open Instr

(* TODO unify those 3 functions *)
let fresh_var instrs var =
  let cand i = var ^ "_" ^ (string_of_int i) in
  let is_fresh cand_var instr =
    let existing = ModedVarSet.untyped (declared_vars instr) in
    not (VarSet.mem cand_var existing) in
  let rec find i =
    let cand_var = cand i in
    if Array.for_all (is_fresh cand_var) instrs then cand_var else find (i+1) in
  find 1

let fresh_label instrs label =
  let cand i = label ^ "_" ^ (string_of_int i) in
  let is_fresh cand_lab instr = match[@warning "-4"] instr with
    | Label l -> l <> cand_lab
    | _ -> true in
  let rec find i =
    let cand_lab = cand i in
    if Array.for_all (is_fresh cand_lab) instrs
    then cand_lab else find (i+1) in
  find 1

let fresh_version_label (func : afunction) label =
  let cand i = label ^ "_" ^ (string_of_int i) in
  let existing = List.map (fun {label} -> label) func.body in
  let rec find i =
    let cand_lab = cand i in
    if not (List.mem cand_lab existing)
    then cand_lab else find (i+1) in
  find 1

let in_simple_expression old_name new_name (exp:simple_expression) : simple_expression =
  match exp with
  | Constant _ -> exp
  | Var x -> if x = old_name then Var new_name else exp

let in_expression old_name new_name exp : expression =
  let in_simple_expression = in_simple_expression old_name new_name in
  match exp with
  | Simple se -> Simple (in_simple_expression se)
  | Op (op, exps) ->
    Op (op, List.map in_simple_expression exps)

let in_arg old_name new_name exp : argument =
  let in_expression = in_expression old_name new_name in
  match exp with
  | Arg_by_val e -> Arg_by_val (in_expression e)
  | Arg_by_ref x -> if x = old_name then Arg_by_ref new_name else Arg_by_ref x

let in_osr old_name new_name osr : osr_def =
  let in_expression = in_expression old_name new_name in
  match osr with
  | Osr_const (x, exp) -> Osr_const (x, in_expression exp)
  | Osr_mut (x, y) -> if y = old_name then Osr_mut (x, new_name) else osr
  | Osr_mut_undef _ -> osr

let uses_in_instruction old_name new_name instr : instruction =
  let in_expression = in_expression old_name new_name in
  let in_arg = in_arg old_name new_name in
  let in_osr = in_osr old_name new_name in
  match instr with
  | Call (x, f, exs) ->
    assert(x != old_name);   (* -> invalid scope *)
    Call (x, in_expression f, List.map in_arg exs)
  | Stop e ->
    Stop (in_expression e)
  | Return e ->
    Return (in_expression e)
  | Decl_const (x, exp) ->
    assert(x != old_name);   (* -> invalid scope *)
    Decl_const (x, in_expression exp)
  | Decl_mut (x, Some exp) ->
    assert (x != old_name);
    Decl_mut (x, Some (in_expression exp))
  | Assign (x, exp) ->
    Assign (x, in_expression exp)
  | Drop x ->
    if x = old_name then Drop new_name else instr
  | Clear x ->
    if x = old_name then Clear new_name else instr
  | Print exp ->
    Print (in_expression exp)
  | Branch (exp, l1, l2) ->
    Branch (in_expression exp, l1, l2)
  | Osr {cond; target; map} ->
    Osr {cond = in_expression cond; target; map = List.map in_osr map}
  | Decl_mut (x, None)
  | Read x ->
    assert (x != old_name);
    instr

  | Label _ | Goto _ | Comment _ ->
    assert (VarSet.is_empty (used_vars instr));
    instr

let freshen_assign (instrs : instruction_stream) (def : pc) =
  let uses = Analysis.PcSet.elements (Analysis.used instrs def) in
  let instr = instrs.(def) in
  match[@warning "-4"] instr with
  | Assign (x, exp) ->
    let fresh = fresh_var instrs x in
    instrs.(def) <- Decl_mut (fresh, Some exp);
    List.iter (fun pc ->
      instrs.(pc) <- uses_in_instruction x fresh instrs.(pc)) uses
  | _ ->
    assert(false)
