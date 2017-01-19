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
    if pos = Array.length code then []
    else
      begin
        if pos = insert then defs else []
      end @
      let instr = code.(pos) in
      let declared = declared_vars instr in
      if TypedVarSet.is_empty declared then instr :: lift (pos+1)
      else
        let declared_mut = TypedVarSet.muts declared in
        if VarSet.is_empty (VarSet.inter declared_mut to_lift) then instr :: lift (pos+1)
        else
          let open Cfg in
          let bb = bb_at cfg pos in
          let doms = doms_at.(bb.id) in
          match BasicBlockSet.find bb_insert doms with
          | exception Not_found -> instr :: lift (pos+1)
          | _ ->
            begin match[@warning "-4"] instr with
              | Decl_mut (x, None) -> lift (pos+1)
              | Decl_mut (x, Some exp) -> Assign (x, exp) :: lift (pos+1)
              | _ -> instr :: lift (pos+1)
            end
  in
  Array.of_list (lift 0)

let branch_prune (prog : program) : program =
  let scope = Scope.infer prog in
  let code = prog.instructions in
  let live_at = Analysis.live code in
  let rec branch_prune pc used_labels pruned landing_pads =
    if pc = Array.length code then (pruned, landing_pads) else
    let pc' = pc + 1 in
    match scope.(pc) with
    | Dead -> branch_prune pc' used_labels (code.(pc) :: pruned) landing_pads
    | Scope scope ->
      begin match[@warning "-4"] code.(pc) with
      | Branch (exp, l1, l2) ->
        (* 1. Copy the program with fresh labels for the landing pad *)
        let used_labels, landing_pad = copy_fresh used_labels code in
        let entry = resolve code l2 in
        let deopt_label_entry = next_fresh_label used_labels ("deopt_entry_" ^ l2) in
        let deopt_label_cont = next_fresh_label used_labels ("deopt_cont_" ^ l2) in
        let used_labels = LabelSet.add deopt_label_entry (LabelSet.add deopt_label_cont used_labels) in
        (* 2. Create the actual landing pad *)
        let landing_pad = Array.concat [
          (* deoptimization entry label *)
          [| Comment ("Landing pad for " ^ deopt_label_entry);
             Label deopt_label_entry |];
          (* continuation *)
          [| Goto deopt_label_cont |];
          (* program before entry point *)
          Array.sub landing_pad 0 entry;
          (* deoptimization continuation label *)
          [| Label deopt_label_cont |];
          (* rest of the program *)
          Array.sub landing_pad entry ((Array.length landing_pad) - entry);
          (* explicit stop since we might fall through the next landing pad otherwise *)
          [| Stop |]
        ] in
        (* 3. Trim the landing pad to contain only the continuation
         *    part reachable from the entry label *)
        let cont' = Array.of_list (
            remove_dead_code landing_pad (resolve landing_pad deopt_label_entry)) in
        (* 4. Fix the frame: Since the dead mutable variables might be written to
         *    in the continuation we need to lift their declaration to the beginning
         *    of the landing pad *)
        let live = live_at entry in
        let muts_in_scope = TypedVarSet.muts scope in
        let dead = Instr.VarSet.diff muts_in_scope (Instr.VarSet.of_list live) in
        let cont = lift_declarations cont' 2 dead in
        (* 5. Replace the branch instruction by an invalidate *)
        let pruned = Invalidate (exp, deopt_label_entry, {captured = live; out = live}) :: pruned in
        let pruned = Goto l1 :: pruned in
        let landing_pads = cont :: landing_pads in
        branch_prune pc' used_labels pruned landing_pads
      | i -> branch_prune pc' used_labels (i :: pruned) landing_pads
      end
  in
  let rev_pruned, landing_pads = branch_prune 0 LabelSet.empty [] [] in
  (* In case the program does not end in a stop this is needed to not fall
   * through into the landing pads *)
  let rev_pruned = Stop :: rev_pruned in
  let pruned = Array.of_list (List.rev rev_pruned) in
  let cleaned = Array.of_list (remove_dead_code pruned 0) in
  let final = Array.of_list (remove_empty_jmp cleaned) in
  Scope.no_annotations (Array.concat (final :: [| EndOpt |] :: List.rev landing_pads))
