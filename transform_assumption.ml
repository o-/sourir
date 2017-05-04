open Instr
open Transform_utils

let result_version (func : afunction) (label : label) (instrs : instructions) : version =
  { label = Edit.fresh_version_label func label;
    instrs;
    annotations = None }

let insert_branch_pruning_assumption (func : afunction) : version option =
  let version = Instr.active_version func in
  let instrs = version.instrs in
  let inp = Analysis.as_analysis_input func version in
  let scope = Scope.infer inp in
  let live = Analysis.live inp in
  let transform pc =
    match scope.(pc) with
    | DeadScope -> assert(false)
    | Scope scope ->
      begin match[@warning "-4"] instrs.(pc) with
      | Branch (exp, l1, l2) ->
        let osr = List.map (fun x ->
            if List.mem x (live pc) then
              Osr_move (x,  x)
            else
              Osr_materialize (x, None))
            (VarSet.elements scope)
        in
        Insert [Osr (exp, func.name, version.label, l1, osr); Goto l2]
      | _ -> Unchanged
      end
  in
  match change_instrs transform inp with
  | None -> None
  | Some instrs -> Some (result_version func version.label instrs)
