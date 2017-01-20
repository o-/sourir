open Instr

let remove_empty_jmp prog =
  let pred = Analysis.predecessors prog in
  let succ = Analysis.successors prog in
  let rec remove_empty_jmp pc =
    let pc' = pc + 1 in
    if pc' = Array.length prog then [prog.(pc)] else
      match[@warning "-4"] (prog.(pc), prog.(pc')) with
      | EndOpt, _ -> Array.to_list (Array.sub prog pc ((Array.length prog) - pc))
      | (Goto l1, Label l2) when l1 = l2 && List.length pred.(pc') = 1 ->
          remove_empty_jmp (pc+2)
      | (Label _, _) when pred.(pc) = [pc-1] && succ (pc-1) = [pc] ->
          (* A label is unused if the previous instruction is the only predecessor
           * unless the previous instruction jumps to it. The later can happen
           * if its a goto (then we already remove it -- see above) or if its a branch (which
           * is excluded by the second tests "succ (pc-1) = [pc]")
           * TODO: we should implement some generic api for instructions like, "Instr.is_jmp" *)
          remove_empty_jmp pc'
      | (_, _) ->
          prog.(pc) :: remove_empty_jmp pc'
  in
  remove_empty_jmp 0

let remove_dead_code prog entry =
  let dead_code =
    let merge _ _ = None in
    let update _ _ = () in
    Analysis.symmetric_forward_analysis_from entry () prog merge update
  in
  let rec remove_dead_code pc =
    let pc' = pc+1 in
    if pc = Array.length prog then []
    else
      match[@warning "-4"] dead_code.(pc), prog.(pc) with
      | _, EndOpt -> Array.to_list (Array.sub prog pc ((Array.length prog) - pc))
      (* Comments are considered live, if the next instruction is live.
       * This prevents removing comments above jump labels *)
      | None, Comment c ->
          if pc' = Array.length prog then [] else
            begin match dead_code.(pc') with
            | None -> remove_dead_code pc'
            | Some _ -> Comment c :: remove_dead_code pc'
            end
      | None, _ -> remove_dead_code pc'
      | Some _, _ -> prog.(pc) :: remove_dead_code pc'
  in
  remove_dead_code 0

module LabelSet = Set.Make(String)

let collect_labels prog =
  let rec labels pc =
    if pc = Array.length prog then LabelSet.empty else
      let pc' = pc + 1 in
      match[@warning "-4"] prog.(pc) with
      | Label l -> LabelSet.union (LabelSet.singleton l) (labels pc')
      | _ -> labels pc' in
  labels 0

let next_fresh_label used hint =
  let is_fresh l = match LabelSet.find l used with
    | exception Not_found -> true
    | x -> false
  in
  if is_fresh hint then hint else
    let l i = hint ^ "." ^ (string_of_int i) in
    let rec next_fresh i =
      let cur = l i in
      if is_fresh cur then cur else next_fresh (i+1) in
    next_fresh 0

module LabelMap = Map.Make(String)

(* Takes a list of globally occurring labels and a program
 * returns a copy of the program with all labels fresh and
 * an updated list of all occurring labels *)
let copy_fresh global_labels prog =
  let prog_labels = collect_labels prog in
  let rec freshened_labels labels todo =
    match todo with
    | [] -> LabelMap.empty
    | l :: tl ->
      let l_fresh = next_fresh_label labels l in
      let labels_used = LabelSet.add l_fresh labels in
      let mapping = freshened_labels labels_used tl in
      LabelMap.add l l_fresh mapping
  in
  let all_labels = LabelSet.union global_labels prog_labels in
  let prog_labels_map = freshened_labels all_labels (LabelSet.elements prog_labels) in
  let map l = LabelMap.find l prog_labels_map in
  let rec copy pc =
    if pc = Array.length prog then [] else
      let pc' = pc + 1 in
      match prog.(pc) with
      | Label l -> Label (map l) :: copy pc'
      | Goto l -> Goto (map l) :: copy pc'
      | Branch (exp, l1, l2) -> Branch (exp, map l1, map l2) :: copy pc'
      | Invalidate (exp, l, sc) -> Invalidate (exp, map l, sc) :: copy pc'
      | (Decl_const _ | Decl_mut _ | Assign _
        | Read _ | Print _ | EndOpt | Stop | Comment _) as i -> i :: copy pc'
  in
  let new_labels = LabelSet.map map prog_labels in
  let new_all_labels = LabelSet.union all_labels new_labels in
  (new_all_labels, Array.of_list (copy 0))

let lift_declarations (code : instruction_stream) (insert : pc) to_lift : instruction_stream =
  let open Instr in
  let cfg = Cfg.of_program code in
  let doms_at = Cfg.dominators (code, cfg) in
  let bb_insert = Cfg.bb_at cfg insert in
  let defs = List.map (fun v -> Decl_mut (v, None)) (VarSet.elements to_lift) in
  let rec lift pos =
    let len = Array.length code in
    if pos = len then []
    else if code.(pos) = EndOpt then Array.to_list (Array.sub code pos (len-pos))
    else
      let instr = code.(pos) in
      begin
        if pos = insert then defs else []
      end @
      let declared = declared_vars instr in
      if TypedVarSet.is_empty declared then instr :: lift (pos+1)
      else
        let declared_mut = TypedVarSet.muts declared in
        if VarSet.is_empty (VarSet.inter declared_mut to_lift) then instr :: lift (pos+1)
        else
          let open Cfg in
          let bb = bb_at cfg pos in
          let doms = doms_at.(bb.id) in
          let below_scope = BasicBlockSet.exists (fun bb -> bb.id = bb_insert.id) doms in
          if below_scope || (bb.id == bb_insert.id && insert <= pos) then
            begin match[@warning "-4"] instr with
              | Decl_mut (x, None) -> lift (pos+1)
              | Decl_mut (x, Some exp) -> Assign (x, exp) :: lift (pos+1)
              | _ -> instr :: lift (pos+1)
            end
          else
            instr :: lift (pos+1)
  in
  Array.of_list (lift 0)

let lift_all (code : instruction_stream) : instruction_stream =
  let rec collect_decls pc =
    let len = Array.length code in
    if pc = len then [] else
      match[@warning "-4"] code.(pc) with
      | Decl_mut (x, _) -> x :: collect_decls (pc+1)
      | EndOpt -> []
      | _ -> collect_decls (pc+1)
  in
  let all_decls = VarSet.of_list (collect_decls 0) in
  lift_declarations code 0 all_decls
