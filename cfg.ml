
type basic_block = {
  id : int;                        (* dominators have smaller id *)
  entry : Instr.pc;                (* first instruction *)
  exit : Instr.pc;                 (* last instruction *)
  prepend : Instr.pc;              (* insert at this pc to prepend (ie. after the label) *)
  append : Instr.pc;               (* insert at this pc to append (ie. before the jump *)
  mutable succ : basic_block list  (* successors *) }

module BasicBlock = struct
  type t = basic_block
  let compare a b = Pervasives.compare a.id b.id
end

type cfg = basic_block array

let bb_at cfg pc =
  let rec bb_at id =
    if id = Array.length cfg then raise (Analysis.DeadCode pc)
    else
      let node = cfg.(id) in
      if node.entry <= pc && node.exit >= pc then node
      else bb_at (id+1) in
  bb_at 0

let of_program (code : Instr.instruction_stream) : cfg =
  let rec next_exit pc =
    let open Instr in
    if Array.length code = pc then (pc-1, pc-1)
    else
      match[@warning "-4"] code.(pc) with
      | Goto _ | Branch _ | Stop | Invalidate _ -> (pc, pc)
      (* Fall through to another label exits the basic block *)
      | Label _ -> (pc-1, pc)
      | _ -> next_exit (pc+1)
  in
  let rec find_nodes work id acc : basic_block list =
    match work with
    | [] -> acc
    | pc :: rest ->
        let seen acc pc = List.exists (fun n -> n.entry = pc) acc in
        if seen acc pc then find_nodes rest id acc
        else
          (* first bb might start without label *)
          let prepend =
            match[@warning "-4"] code.(pc) with
            | Instr.Label _ -> (pc+1)
            | _ -> pc
          in
          let exit, append = next_exit prepend in
          let node = {id = id; entry = pc; exit = exit;
                      prepend = prepend; append = append; succ = []} in
          let acc = node :: acc in
          let succ = Analysis.successors code exit in
          let succ = List.filter (fun pc -> not (seen acc pc)) succ in
          (* explore cfg depth first to ensure topological order of id *)
          find_nodes (succ @ rest) (id+1) acc
  in
  let entries = find_nodes [0] 0 [] in
  let cfg = Array.of_list (List.rev entries) in
  (* TODO: maybe assign the successors in the above loop
   * but its kinda hard with the order constraints *)
  let update_succ node =
    let succ_instr = Analysis.successors code node.exit in
    let succ = List.map (fun pc -> bb_at cfg pc) succ_instr in
    node.succ <- succ;
  in
  Array.iter update_succ cfg;
  cfg

module BasicBlockSet = Set.Make(BasicBlock)

let cfg_dataflow_analysis (init_state : 'a)
                          (cfg : cfg)
                          (merge : 'a -> 'a -> 'a option)
                          (update : basic_block -> 'a -> 'a)
                          : 'a array =
  let program_state = Array.make (Array.length cfg) None in
  let rec work = function
    | [] -> ()
    | (in_state, bb) :: rest ->
        let merged =
          match program_state.(bb.id) with
          | None -> Some in_state
          | Some cur_state -> merge cur_state in_state
        in begin match merged with
        | None -> work rest
        | Some merged ->
          program_state.(bb.id) <- Some merged;
          let updated = update bb merged in
          let new_work = List.map (fun bb -> (updated, bb)) bb.succ in
          work (new_work @ rest)
        end
  in
  work [(init_state, cfg.(0))];
  Array.map (fun state ->
    match state with
    | None -> assert(false)
    | Some x -> x) program_state

let dominators (program, cfg) =
  let merge cur_dom in_dom =
    let merged = BasicBlockSet.inter cur_dom in_dom in
    if BasicBlockSet.equal cur_dom merged then None else Some merged
  in
  let update node dom = BasicBlockSet.add node dom in
  cfg_dataflow_analysis BasicBlockSet.empty cfg merge update

let common_dominator (program, cfg, doms) pcs =
  let nodes = List.map (bb_at cfg) pcs in
  let doms = List.map (fun n -> BasicBlockSet.add n doms.(n.id)) nodes in
  let common = List.fold_left BasicBlockSet.inter (List.hd doms) (List.tl doms) in
  assert (not (BasicBlockSet.is_empty common));
  BasicBlockSet.max_elt common

let dominates_all_uses (program, cfg, doms, used) pc =
  let uses = used pc in
  if Analysis.InstrSet.is_empty uses then true
  else
    let bb_at pc = bb_at cfg pc in
    let bb_def = bb_at pc in
    let uses = Analysis.InstrSet.elements uses in
    let doms_uses = List.map (fun pc ->
        let bb = bb_at pc in
        (pc, bb_at pc, doms.(bb.id))) uses in
    List.for_all (fun (use, bb, doms) ->
        (* in the same basic block -> fine if def is before use
         * (eg. linear loop body with both def and use) *)
        ((bb_def.id = bb.id && use > pc) ||
         (BasicBlockSet.exists (fun bb ->
              bb_def.id = bb.id) doms))) doms_uses
