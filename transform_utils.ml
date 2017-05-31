open Instr
open Types

type instruction_change =
  | Remove of int
  | Insert of instruction list
  | InsertAfter of instruction list
  | Replace of instruction list
  | Unchanged

let change_instrs (transform : pc -> instruction_change) ({formals; instrs} : analysis_input) =
  let rec acc_instr pc acc changed =
    if pc = Array.length instrs then
      if changed then Some (Array.of_list (List.rev acc)) else None
    else
      match transform pc with
      | Remove n ->
        acc_instr (pc+n) acc true
      | Replace is ->
        acc_instr (pc+1) (List.rev_append is acc) true
      | Insert is ->
        assert(match[@warning "-4"] instrs.(pc) with | Label _ -> false | _ -> true);
        acc_instr (pc+1) (instrs.(pc) :: List.rev_append is acc) true
      | InsertAfter is ->
        acc_instr (pc+1) (List.rev_append is (instrs.(pc) :: acc)) true
      | Unchanged ->
        acc_instr (pc+1) (instrs.(pc)::acc) changed
  in
  acc_instr 0 [] false


(* Splits all edges that have multi-predecessors branching *)
let normalize_graph instrs =
  let rec normalize instrs preds pc =
    let is_branch pred_pc = match[@warning "-4"] instrs.(pred_pc) with
    | Branch _ -> true
    | _ -> false in
    if pc = Array.length instrs then instrs
    else match[@warning "-4"] instrs.(pc) with
      | Label l ->
          let branches = List.filter (fun p ->
            is_branch p) preds.(pc) in
          if List.length branches < 2 then normalize instrs preds (pc+1)
          else begin
            let branch_pc = List.hd branches in
            let fixed, _ = Edit.split_edge instrs preds branch_pc l pc in
            normalize fixed (Analysis.predecessors fixed) 0
          end
      | _ -> normalize instrs preds (pc+1)
  in
  normalize instrs (Analysis.predecessors instrs) 0

(* This util can fix the scope after inserting a fresh variable in the graph.
 * As an additional sideeffect it will make every drop explicit. *)
let fix_scope : transform_instructions = fun {formals; instrs} ->
  let instrs = normalize_graph instrs in
  let merge pc cur incom =
    let res = VarSet.inter cur incom in
    if VarSet.equal res cur then None else Some res
  in
  let update pc cur =
    let instr = instrs.(pc) in
    let added = Instr.declared_vars instr in
    let updated = VarSet.union cur added in
    let dropped = Instr.dropped_vars instr in
    VarSet.diff updated dropped
  in
  let initial_state = formals in
  let scope = Analysis.forward_analysis initial_state instrs merge update in
  let succs = Analysis.successors instrs in
  let transform pc =
    let succs = succs.(pc) in
    assert(List.length succs <= 2);
    let my_scope = scope pc in
    let succ_scopes = List.map (fun pc -> scope pc) succs in
    let min_scope = List.fold_left VarSet.union VarSet.empty succ_scopes in
    (* Because of split edge all the succs should agree on one scope *)
    assert (succs = [] || VarSet.equal (List.hd succ_scopes) min_scope);

    let to_drop = VarSet.diff my_scope min_scope in
    let to_drop = VarSet.diff to_drop (dropped_vars instrs.(pc)) in
    let to_drop_instrs = List.map (fun var -> Drop var) (VarSet.elements to_drop) in

    match[@warning "-4"] instrs.(pc) with
    | Stop _
    | Goto _
    | Branch _
    | Return _ ->
        (* Don't insert drops after the last instruction *)
      Insert to_drop_instrs
    | _ ->
      InsertAfter to_drop_instrs
  in
  change_instrs transform {formals;instrs}
