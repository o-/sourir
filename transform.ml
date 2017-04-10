open Instr

let remove_empty_jmp (instrs : instruction_stream) : instruction_stream =
  let pred = Analysis.predecessors instrs in
  let succ = Analysis.successors instrs in
  let rec remove_empty_jmp pc acc =
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

let remove_unreachable_code (instrs : instruction_stream) : instruction_stream =
  let unreachable =
    let merge _ _ _ = None in
    let update _ _ = () in
    Analysis.forward_analysis () instrs merge update
  in
  let rec remove_unreachable pc acc =
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

let branch_prune (func : afunction) : afunction =
  let version = Instr.active_version func in
  let instrs = version.instrs in
  let scope = Scope.infer func version in
  let live = Analysis.live instrs in
  let rec branch_prune pc acc =
    if pc = Array.length instrs then
      Array.of_list (List.rev acc)
    else
      match scope.(pc) with
      | DeadScope -> assert(false)
      | Scope scope ->
        let pc' = pc + 1 in
        begin match[@warning "-4"] instrs.(pc) with
        | Branch (exp, l1, l2) ->
          let osr = List.map (function
              | (Const_var, x) ->
                Osr_const (x, (Simple (Var x)))
              | (Mut_var, x) ->
                if List.mem x (live pc) then
                  Osr_mut (x, x)
                else
                  Osr_mut_undef x)
              (ModedVarSet.elements scope)
          in
          branch_prune pc'
            (Goto l2 :: Osr {cond=exp; target={func=func.name; version=version.label; label=l1}; map=osr} :: acc)
        | i ->
          branch_prune pc' (i::acc)
        end
  in
  let final = branch_prune 0 [] in
  let cleanup = {
    label = Rename.fresh_version_label func version.label;
    instrs = remove_empty_jmp (remove_unreachable_code final);
    annotations = None } in
  { func with
    body = cleanup :: func.body }


let remove_fallthroughs_to_label instrs =
  let rec loop pc acc =
    if pc = Array.length instrs then acc
    else match[@warning "-4"] instrs.(pc-1), instrs.(pc) with
    | Goto _, Label _
    | Branch _, Label _ ->
      loop (pc+1) acc
    | _, Label l ->
      let edit = (pc, 0, [| Goto l |]) in
      loop (pc+1) (edit :: acc)
    | _, _ ->
      loop (pc+1) acc
  in
  let edits = loop 1 [] in
  fst (Edit.subst_many instrs edits)


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
let hoist_assignment (func : afunction) : afunction =
  let version = Instr.active_version func in
  let instrs = version.instrs in
  let reaching = Analysis.reaching instrs in
  let uses = Analysis.used instrs in
  let dominates = Analysis.dominates instrs in
  let dominates_all_uses pc =
    Analysis.PcSet.for_all (fun use -> dominates pc use) (uses pc) in
  let rec find_possible_move pc =
    if pc = Array.length instrs then None
    else
      let pc' = pc + 1 in
      match[@warning "-4"] instrs.(pc) with
      | Assign (x, exp) ->
        if not (dominates_all_uses pc) then find_possible_move pc'
        else
          let reaching_defs = reaching pc in
          let valid_move candidate =
            let dominate_me = Analysis.PcSet.for_all (fun pc -> dominates pc candidate) in
            dominates candidate pc && dominate_me reaching_defs in

          begin match Analysis.find_first instrs valid_move with
          | exception Not_found -> find_possible_move pc'
          | pc' -> Some (pc, pc')
          end

      (* TODO: others? *)
      | i -> find_possible_move pc'
  in

  match find_possible_move 0 with
  | None -> func
  | Some (from_pc, to_pc) ->
    let copy = Array.copy instrs in
    Rename.freshen_assign copy from_pc;
    Edit.move copy from_pc to_pc;
    let res = {
      label = version.label;
      instrs = copy;
      annotations = None } in
    Instr.replace_active_version func res

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

let minimize_lifetimes (func : afunction) : afunction =
  let version = Instr.active_version func in
  let instrs = remove_unused_vars version.instrs in
  let instrs = remove_drops instrs in
  let predecessors = Analysis.predecessors instrs in
  let required = Analysis.required_vars instrs in
  let required = Analysis.saturate required instrs in
  let required_before pc =
    (* It might seem like we need to take the union over all predecessors. But
     * since required_merged_vars_at extends lifetimes to mergepoints this is
     * equivalent to just look at the first predecessor *)
    match predecessors.(pc) with | [] -> VarSet.empty | p :: _ -> required p
  in
  let rec result (pc : pc) =
    if pc = Array.length instrs then [] else
      let required = required pc in
      let required_before = required_before pc in
      let to_drop = VarSet.diff required_before required in
      let drops = List.map (fun x -> Drop x) (VarSet.elements to_drop) in
      drops @ instrs.(pc) :: result (pc+1)
  in
  let dropped = Array.of_list (result 0) in
  let res = {
    label = version.label;
    instrs = dropped;
    annotations = None; } in
  Instr.replace_active_version func res
