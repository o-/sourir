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
        acc_instr (pc+1) (instrs.(pc) :: List.rev_append is acc) true
      | InsertAfter is ->
        acc_instr (pc+1) (List.rev_append is (instrs.(pc) :: acc)) true
      | Unchanged ->
        acc_instr (pc+1) (instrs.(pc)::acc) changed
  in
  acc_instr 0 [] false

(* Splits all edges that have multi-predecessors branching.
 * After this step a branch is guaranteed to be the sole predecessor of its target labels.
 * Only gotos are allowed to merge control flow.
 * Can't rely on cfg for this pass since it has to be applicable to a broken graph.
 *)
let normalize_graph inp =
  let normalize1 instrs pc =
    let has_fallthrough label pc =
      assert (instrs.(pc) = Label label);
      match instrs.(pc-1) with
      | Decl_var _ | Decl_array _
      | Assign _ | Array_assign _
      | Drop _ | Read _ | Call _ | Label _
      | Comment _ | Osr _ | Print _ | Assert _ -> true
      | Stop _ | Return _ | Goto _ | Branch _ -> false
    in
    match[@warning "-4"] instrs.(pc) with
    | Label l ->
        if has_fallthrough l pc
        then Insert [ Goto l ]
        else Unchanged
    | _ -> Unchanged
  in

  let normalize2 instrs pc =
    let incomming label =
      let rec incomming pc =
        if pc = Array.length instrs then [] else
        match[@warning "-4"] instrs.(pc) with
        | Branch (_, l1, l2) when l1 = label || l2 = label ->
            pc :: incomming (pc+1)
        | Goto l when l = label ->
            pc :: incomming (pc+1)
        | Goto l ->
            incomming (pc+1)
        | _->
            incomming (pc+1)
      in
      incomming 0
    in
    let fresh_label label tag = (Edit.fresh_label instrs label) ^ "_" ^ tag in
    match[@warning "-4"] instrs.(pc) with
    | Branch (e, l1, l2) ->
        let i1, i2 = incomming l1, incomming l2 in
        begin match i1, i2 with
        | _, [] -> assert(false)
        | [], _ -> assert(false)
        | [pc1], [pc2] ->
            assert(pc1 = pc && pc2 = pc);
            Unchanged
        | [pc1], _ ->
            assert(pc1 = pc);
            let l2' = fresh_label l2 (string_of_int pc) in
            Replace [ Branch (e, l1, l2'); Label l2'; Goto l2 ]
        | _, [pc2] ->
            assert(pc2 = pc);
            let l1' = fresh_label l1 (string_of_int pc) in
            Replace [ Branch (e, l1', l2); Label l1'; Goto l1 ]
        | _, _ ->
            (* It might be that l1 = l2. To avoid creating a duplicated label we tag with l/r *)
            let l1' = fresh_label l1 ((string_of_int pc) ^ "l") in
            let l2' = fresh_label l2 ((string_of_int pc) ^ "r") in
            Replace [ Branch (e, l1', l2'); Label l1'; Goto l1; Label l2'; Goto l2 ]
        end
    | _ -> Unchanged
  in

  match change_instrs (normalize1 inp.instrs) inp with
  | None -> change_instrs (normalize2 inp.instrs) inp
  | Some instrs ->
      match change_instrs (normalize2 instrs) {inp with instrs} with
      | Some instrs -> Some instrs
      | None -> Some instrs
