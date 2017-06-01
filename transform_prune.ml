open Instr
open Types
open Transform_utils

let insert_branch_pruning_assumption (func : afunction) : version option =
  let version = Instr.active_version func in
  let instrs = version.instrs in
  (* Finds the first branch instruction in the stream *)
  let rec find_branch pc =
    if pc = Array.length instrs then None else
    match[@warning "-4"] instrs.(pc) with
    | Branch (exp, l1, l2) -> Some (pc, exp)
    | _ -> find_branch (pc+1)
  in
  match find_branch 0 with
  | None -> None
  | Some (pc, branch_cond) ->
    Transform_assumption.insert_assumption func branch_cond pc

let branch_prune : transform_instructions = fun input ->
  let assumptions = Analysis.valid_assumptions input in
  let transform pc =
    match[@warning "-4"] input.instrs.(pc) with
    | Branch (e, l1, l2) ->
      if Analysis.ExpressionSet.mem e (assumptions pc)
      then Replace [Goto l2]
      else Unchanged
    | _ -> Unchanged
  in
  match change_instrs transform input with
  | None -> None
  | Some instrs -> Transform_utils.normalize_graph {input with instrs}
