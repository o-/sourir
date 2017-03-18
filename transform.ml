open Instr

let remove_empty_jmp (instrs : segment) : segment =
  let pred = Analysis.predecessors instrs in
  let succ = Analysis.successors instrs in
  let rec remove_empty_jmp pc acc : segment =
    let pc' = pc + 1 in
    if pc' = Array.length instrs then
      Array.of_list (List.rev (instrs.(pc) :: acc))
    else
      match[@warning "-4"] instrs.(pc), instrs.(pc') with
      | Goto l1, Label l2 when l1 = l2 && List.length pred.(pc') = 1 ->
        remove_empty_jmp (pc+2) acc
      | Label _, _ when pred.(pc) = [pc-1] && succ.(pc-1) = [pc] ->
          (* A label is unused if the previous instruction is the only predecessor
           * unless the previous instruction jumps to it. The later can happen
           * if its a goto (then we already remove it -- see above) or if its a branch (which
           * is excluded by the second tests "succ (pc-1) = [pc]")
           * TODO: we should implement some generic api for instructions like, "Instr.is_jmp" *)
        remove_empty_jmp pc' acc
      | i, _ ->
        remove_empty_jmp pc' (i::acc)
  in
  remove_empty_jmp 0 []

let remove_unreachable_code (instrs : segment) : segment =
  let unreachable =
    let merge _ _ _ = None in
    let update _ _ = () in
    Analysis.forward_analysis () instrs merge update
  in
  let rec remove_unreachable pc acc : segment =
    let pc' = pc+1 in
    if pc = Array.length instrs then
      Array.of_list (List.rev acc)
    else
      let i = instrs.(pc) in
      match unreachable pc with
      | exception Analysis.UnreachableCode _ ->
        remove_unreachable pc' acc
      | () ->
        remove_unreachable pc' (i::acc)
  in
  remove_unreachable 0 []

let branch_prune (prog : program) : program =
  let main = List.assoc "main" prog in
  let rest = List.remove_assoc "main" prog in
  let deopt_label = "main_" ^ string_of_int (List.length prog) in
  let scope = Scope.infer main in
  let live = Analysis.live main in
  let rec branch_prune pc acc =
    if pc = Array.length main then
      Array.of_list (List.rev acc)
    else
      match scope.(pc) with
      | Scope.Dead -> assert(false)
      | Scope.Scope scope ->
        let pc' = pc + 1 in
        begin match[@warning "-4"] main.(pc) with
        | Branch (exp, l1, l2) ->
          let osr = List.map (function
              | (Const_var, x) ->
                OsrConst (x, (Simple (Var x)))
              | (Mut_var, x) ->
                if List.exists (fun x' -> x = x') (live pc) then
                  OsrMut (x, x)
                else
                  OsrMutUndef x)
              (ModedVarSet.elements scope)
          in
          branch_prune pc'
            (Goto l2 :: Osr (exp, deopt_label, l1, osr) :: acc)
        | i ->
          branch_prune pc' (i::acc)
        end
  in
  let final = branch_prune 0 [] in
  let cleanup = remove_empty_jmp (remove_unreachable_code final) in
  ("main", cleanup) :: (deopt_label, main) :: rest

let optimized_branch_prune prog =
  let main = List.assoc "main" prog in
  let rest = List.remove_assoc "main" prog in

  (* Before starting to modify the program we add a label to every
   * instruction to be able to find deopt points across optimizations.
   * Also we add a comment as the first instruction because our later
   * algorithm assumes that the entry point does not have a predecessor
   * (eg. which would not work for: "loop: goto loop") *)
  let main = Array.concat ([| Comment "__Entry" |] ::
      List.mapi (fun pc instr ->
        [| Label ("__pc_" ^ string_of_int pc); instr |])
        (Array.to_list main)) in

  let rec find_curr_pc_label instrs pc =
    match[@warning "-4"] instrs.(pc) with
    | Label l when String.length l > 5 && String.sub l 0 5 = "__pc_" -> l
    | _ -> find_curr_pc_label instrs (pc-1)
  in

  let resolve_main = Instr.resolve main in
  let scope_main = Scope.infer main in
  let live_main = Analysis.live main in

  (* Prune one Branch (e, l1, l2) at branch_pc.
   * Guard_pc is a list of necessary guards. Note: guard_pcs can contain
   * a pc which is equal to the branch_pc! *)
  let prune_the_branch instrs branch_pc e l1 l2 guard_pcs deopt_version : instruction_stream =
    let open Analysis in
    let rec prune_the_branch pc acc =
      if pc = Array.length instrs then
        Array.of_list (List.rev acc)
      else
        (* Determine what to do at this pc *)
        let remove_branch = pc = branch_pc in
        let insert_osr = PcSet.mem pc guard_pcs in
        let replace_branch_with_osr = insert_osr && remove_branch in

        if remove_branch then
          prune_the_branch (pc+1) (Goto l2 :: acc)
        else if not insert_osr then
          prune_the_branch (pc+1) (instrs.(pc) :: acc)
        else begin
          (* Create the guard *)
          let deopt_label = if replace_branch_with_osr then l1 else find_curr_pc_label instrs pc in
          let deopt_pc = resolve_main deopt_label in
          let osr_capture = match scope_main.(deopt_pc) with
            | Scope.Dead -> []
            | Scope.Scope scope ->
              List.map (function
                | (Const_var, x) ->
                  OsrConst (x, (Simple (Var x)))
                | (Mut_var, x) ->
                  if List.mem x (live_main deopt_pc) ||
                     (* live is after the instruction but we need before *)
                     VarSet.mem x (used_vars main.(deopt_pc))
                  then OsrMut (x, x)
                  else OsrMutUndef x)
                (ModedVarSet.elements scope)
          in
          let osr_instr = Osr (e, deopt_version, deopt_label, osr_capture) in

          if replace_branch_with_osr then
            prune_the_branch (pc+1) (Goto l2 :: osr_instr :: acc)
          else begin
            assert (insert_osr);
            match[@warning "-4"] instrs.(pc) with
            | Label l ->
              prune_the_branch (pc+1) (osr_instr :: Label l :: acc)
            | _ ->
              prune_the_branch (pc+1) (instrs.(pc) :: osr_instr :: acc)
          end
        end
    in

    prune_the_branch 0 []
  in

  let rec find_branch instrs pc =
    if pc = Array.length instrs then None else
    match[@warning "-4"] instrs.(pc) with
    | Branch (e, l1, l2) ->
      Some (pc, e, l1, l2)
    | _ -> find_branch instrs (pc+1)
  in

  let find_optimal_guards_pos instrs pc used_vars =
    let open Analysis in
    let preds = Analysis.predecessors instrs in

    (* Push the guard up in the cfg. As long as the guarded expression stays
     * unchanged we can proceed. If we have multiple predecessors we push to
     * all of them. (In unstructured cfgs we might push the guard to a branch
     * which would not have to deopt).
     * We push breadth first. If we end up in a position where all
     * predecessors have been visited before we can drop this osr. The reason
     * is that if we established the condition to be stable across a region
     * spanning over all predecessors it must be the case that we also pushed
     * the guard to some dominating positions. The only case where this can go
     * wrong is if we are in a region without a dominator (ie. a loop without
     * entry) but that is wrong code in the first place.
     * This algo might might produce more guards than necessary. But we
     * speculate it pays off since it can move loop invariant guards out of
     * loops. *)
    let rec find_optimal_guards_pos seen acc =
      let can_move pc =
        let affected = VarSet.inter (changed_vars instrs.(pc)) used_vars in
        VarSet.is_empty affected in
      let new_acc = PcSet.fold (fun pc set ->
          let preds = PcSet.of_list preds.(pc) in
          let new_preds = PcSet.diff preds seen in
          let no_move = not (PcSet.for_all can_move new_preds) in
          let seen pc = PcSet.mem pc seen in
          let all_seen = PcSet.for_all seen preds in
          if all_seen then set
          else if no_move || PcSet.is_empty new_preds then PcSet.add pc set
          else PcSet.union set new_preds
        ) acc PcSet.empty
      in
      if PcSet.equal new_acc acc then acc
      else find_optimal_guards_pos (PcSet.union seen acc) new_acc
    in
    find_optimal_guards_pos PcSet.empty (PcSet.singleton pc)
  in

  let deopt_version = "main_" ^ string_of_int (List.length prog) in
  let rec prune_all_branches instrs =
    match find_branch instrs 0 with
    | None -> instrs
    | Some (pc, e, l1, l2) ->
      let used_vars = used_vars instrs.(pc) in
      let guards = find_optimal_guards_pos instrs pc used_vars in
      let opt_instrs = prune_the_branch instrs pc e l1 l2 guards deopt_version in
      let opt_instrs = remove_unreachable_code opt_instrs in
      prune_all_branches opt_instrs
  in

  let pruned = remove_empty_jmp (prune_all_branches main) in
  (* remove entry comment *)
  let pruned = Array.sub pruned 1 ((Array.length pruned)-1) in
  ("main", pruned) :: (deopt_version, main) :: rest


let move instrs from_pc to_pc =
  let (dir, to_pc) = if from_pc > to_pc then (-1, to_pc) else (1, to_pc-1) in
  let from = instrs.(from_pc) in
  let rec move pc =
    if pc != to_pc then begin
      instrs.(pc) <- instrs.(pc+dir);
      move (pc+dir)
    end
  in
  move from_pc;
  instrs.(to_pc) <- from

(* Hoisting assignments "x <- exp" as far up the callgraph as possible.
 *
 * Since we are not in SSA moving assignments is only possible (without further
 * analysis) if the assignments dominates all its uses. Otherwise we might
 * accidentally capture uses on some traces.
 *
 * The condition for a move to be valid is that the move target dominates the
 * move origin (ie. we are moving upwards) and is dominated by all reaching
 * defs (ie. we are not moving above our dependencies).
 *
 * We only look at our own use-def chain. Thus the transformation renames the
 * variable to avoid overriding unrelated uses of the same name.
 *)
let hoist_assignment prog =
  let main = List.assoc "main" prog in
  let rest = List.remove_assoc "main" prog in
  let reaching = Analysis.reaching main in
  let uses = Analysis.used main in
  let dominates = Analysis.dominates main in
  let dominates_all_uses pc =
    Analysis.PcSet.for_all (fun use -> dominates pc use) (uses pc) in
  let rec find_possible_move pc =
    if pc = Array.length main then None
    else
      let pc' = pc + 1 in
      match[@warning "-4"] main.(pc) with
      | Assign (x, exp) ->
        if not (dominates_all_uses pc) then find_possible_move pc'
        else
          let reaching_defs = reaching pc in
          let valid_move candidate =
            let dominate_me = Analysis.PcSet.for_all (fun pc -> dominates pc candidate) in
            dominates candidate pc && dominate_me reaching_defs in

          begin match Analysis.find_first main valid_move with
          | exception Not_found -> find_possible_move pc'
          | pc' -> Some (pc, pc')
          end

      (* TODO: others? *)
      | i -> find_possible_move pc'
  in

  match find_possible_move 0 with
  | None -> prog
  | Some (from_pc, to_pc) ->
    let copy = Array.copy main in
    Rename.freshen_assign copy from_pc;
    move copy from_pc to_pc;
    ("main", copy) :: rest

let remove_unused_vars instrs =
  let open Analysis in
  let required = Analysis.required instrs in
  let used = Analysis.used instrs in
  let rec result (pc : pc) =
    if pc = Array.length instrs then []
    else let pc', i = pc+1, instrs.(pc) in
      match[@warning "-4"] i with
      | Decl_mut (x, _)
      | Decl_const (x, _) when PcSet.is_empty (required pc) -> result pc'
      | Assign _ when PcSet.is_empty (used pc) -> result pc'
      | i -> i :: result pc'
  in
  Array.of_list (result 0)

let remove_drops instrs =
  Array.of_list (
    List.filter (fun x -> match[@warning "-4"] x with
        | Drop _ -> false | _ -> true)
      (Array.to_list instrs))

let minimize_lifetimes prog =
  let main = List.assoc "main" prog in
  let rest = List.remove_assoc "main" prog in
  let main = remove_unused_vars main in
  let main = remove_drops main in
  let predecessors = Analysis.predecessors main in
  let required = Analysis.required_vars main in
  let required = Analysis.saturate required main in
  let required_before pc =
    (* It might seem like we need to take the union over all predecessors. But
     * since required_merged_vars_at extends lifetimes to mergepoints this is
     * equivalent to just look at the first predecessor *)
    match predecessors.(pc) with | [] -> VarSet.empty | p :: _ -> required p
  in
  let rec result (pc : pc) =
    if pc = Array.length main then [] else
      let required = required pc in
      let required_before = required_before pc in
      let to_drop = VarSet.diff required_before required in
      let drops = List.map (fun x -> Drop x) (VarSet.elements to_drop) in
      drops @ main.(pc) :: result (pc+1)
  in
  let dropped = Array.of_list (result 0) in
  ("main", dropped) :: rest
