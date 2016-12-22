open Instr

let successors program pc =
  let pc' = pc + 1 in
  let next = if pc' = Array.length program then [] else [pc'] in
  let resolve = Instr.resolve program in
  match program.(pc) with
  | Decl_const _
  | Decl_mut _
  | Assign _
  | Label _
  | Comment _
  | Read _
  | Print _ -> next
  | Goto l -> [resolve l]
  | Invalidate (_, l, _) -> next @ [resolve l]
  | Branch (_e, l1, l2) -> [resolve l1; resolve l2]
  | Stop -> []

let predecessors program =
  let preds = Array.map (fun _ -> []) program in
  let mark_successor pc pc' =
    preds.(pc') <- pc :: preds.(pc') in
  for pc = 0 to Array.length program - 1 do
    List.iter (mark_successor pc) (successors program pc)
  done;
  preds

let dataflow_analysis (next : pc -> pc list)
                      (init_state : ('a * pc) list)
                      (program : program)
                      (merge : 'a -> 'a -> 'a option)
                      (update : pc -> 'a -> 'a)
                      : 'a option array =
  let program_state = Array.map (fun _ -> ref None) program in
  let rec work = function
    | [] -> ()
    | (in_state, pc) :: rest ->
        let cell = program_state.(pc) in
        let merged =
          match !cell with
          | None -> Some in_state
          | Some cur_state -> merge cur_state in_state
        in begin match merged with
        | None -> work rest
        | Some merged ->
            cell := Some merged;
            let updated = update pc merged in
            let cont = next pc in
            let new_work = List.map (fun pc -> (updated, pc)) cont in
            work (new_work @ rest)
        end
  in
  work init_state;
  Array.map (!) program_state

let exits program =
  let rec exits pc : Pc.t list =
    if Array.length program = pc then []
    else
      let is_exit = successors program pc = [] in
      if is_exit then pc :: exits (pc + 1) else exits (pc + 1)
  in
  exits 0

let forward_analysis_from init_pos init_state program =
  let successors pc = successors program pc in
  dataflow_analysis successors [(init_state, init_pos)] program

let forward_analysis init_state program =
  forward_analysis_from 0 init_state program

let backwards_analysis init_state program =
  let exits = exits program in
  let init_state = List.map (fun pc -> (init_state, pc)) exits in
  let preds = predecessors program in
  let predecessors pc = preds.(pc) in
  dataflow_analysis predecessors init_state program



(* Use - Def style analysis *)

(* a set of instructions *)
module InstrSet = Set.Make(Pc)

(* [Analysis result] Map: variable -> pc set
 *
 * Is used to represent the eg. the set of instructions
 * defining a certain variable *)
module VariableMap = struct
  include Map.Make(Variable)

  (* merge is defined as the union of their equally named sets *)
  let merge =
    let merge_one _ a b : InstrSet.t option =
      match a, b with
      | None, None -> None
      | Some a, None -> Some a
      | None, Some b -> Some b
      | Some a, Some b -> Some (InstrSet.union a b) in
    merge merge_one

  let equal =
    let is_equal a b = InstrSet.equal a b in
    equal is_equal

  let at var this =
    match find var this with
    | v -> v
    | exception Not_found -> InstrSet.empty
end

exception DeadCode of pc

(* returns a 'pc -> pc set' computing reaching definitions *)
let reaching prog : pc -> InstrSet.t =
  let merge cur_defs in_defs =
    let merged = VariableMap.merge cur_defs in_defs in
    if VariableMap.equal cur_defs merged then None else Some merged
  in
  let update pc defs =
    let instr = prog.(pc) in
    (* add or override defined vars in one go*)
    let kill = defined_vars instr in
    let loc = InstrSet.singleton pc in
    let replace acc var = VariableMap.add var loc acc in
    List.fold_left replace defs kill
  in
  let res = forward_analysis VariableMap.empty prog merge update in
  fun pc ->
    let instr = prog.(pc) in
    match res.(pc) with
    | None -> raise (DeadCode pc)
    | Some res ->
        let used = consumed_vars instr in
        let definitions_of var = VariableMap.find var res in
        let all_definitions = List.map definitions_of used in
        List.fold_left InstrSet.union InstrSet.empty all_definitions


let liveness_analysis prog =
  let merge cur_uses in_uses =
    let merged = VariableMap.merge cur_uses in_uses in
    if VariableMap.equal cur_uses merged then None else Some merged
  in
  let update pc uses =
    let instr = prog.(pc) in
    (* First remove defined vars *)
    let kill = defined_vars instr in
    let remove acc var = VariableMap.remove var acc in
    let uses = List.fold_left remove uses kill in
    (* Then add used vars *)
    let used = consumed_vars instr in
    let loc = InstrSet.singleton pc in
    let merge acc var =
      (* TODO: creates a new singleton map and merges it with existing uses
       * this seems inefficient, but I dont see a better way. *)
      let insert = VariableMap.add var loc VariableMap.empty in
      VariableMap.merge insert acc
    in
    List.fold_left merge uses used
  in
  backwards_analysis VariableMap.empty prog merge update


(* returns a 'pc -> variable set' computing live vars at a certain pc *)
let live prog : pc -> variable list =
  let res = liveness_analysis prog in
  fun pc ->
    match res.(pc) with
    | None -> raise (DeadCode pc)
    | Some res ->
      let collect_key (key, value) = key in
      let live_vars = List.map collect_key (VariableMap.bindings res) in
      live_vars

(* returns a 'pc -> pc set' computing uses of a definition *)
let used prog : pc -> InstrSet.t =
  let res = liveness_analysis prog in
  fun pc ->
    let instr = prog.(pc) in
    match res.(pc) with
    | None -> raise (DeadCode pc)
    | Some res ->
        let defined = defined_vars instr in
        let uses_of var = VariableMap.at var res in
        let all_uses = List.map uses_of defined in
        List.fold_left InstrSet.union InstrSet.empty all_uses


type cfg_node = { id : int; entry : pc; exit : pc}
module CfgNode = struct
  type t = cfg_node
  let compare a b = Pervasives.compare a.entry b.entry
end
module Cfg = struct
  type t = cfg_node array

  let node_at cfg pc =
    let rec node_at id =
      assert (id < Array.length cfg);
      let node = cfg.(id) in
      if node.entry <= pc && node.exit >= pc then node
      else node_at (id+1) in
    node_at 0

  let of_program program =
    let rec next_exit pc =
      if Array.length program = pc then (pc-1)
      else
        match program.(pc) with
        | Goto _ | Branch _ | Stop -> pc
        (* Fall through to another label exits the basic block *)
        | Label _ -> (pc-1)
        | _ -> next_exit (pc+1)
    in
    let rec find_nodes work id acc : cfg_node list =
      match work with
      | [] -> acc
      | pc :: rest ->
          (* first bb starts without label *)
          let exit = if pc = 0 then next_exit 0 else next_exit (pc+1) in
          let node = {id = id; entry = pc; exit = exit} in
          let acc = node :: acc in
          let not_done pc = not (List.exists (fun n -> n.entry = pc) acc) in
          let succ = successors program node.exit in
          let succ = List.filter not_done succ in
          (* explore cfg depth first to ensure topological order of id *)
          find_nodes (succ @ rest) (id+1) acc
    in
    let entries = find_nodes [0] 0 [] in
    Array.of_list (List.rev entries)

  let successors program cfg node =
    let cont_pc = successors program node.exit in
    let node_at = node_at cfg in
    List.map node_at cont_pc
end
module CfgNodeSet = Set.Make(CfgNode)

let cfg_dataflow_analysis (next : cfg_node -> cfg_node list)
                          (init_state : 'a)
                          (cfg : Cfg.t)
                          (merge : 'a -> 'a -> 'a option)
                          (update : cfg_node -> 'a -> 'a)
                          : 'a array =
  let program_state = Array.map (fun _ -> ref None) cfg in
  let rec work = function
    | [] -> ()
    | (in_state, cfg_node) :: rest ->
        let cell = program_state.(cfg_node.id) in
        let merged =
          match !cell with
          | None -> Some in_state
          | Some cur_state -> merge cur_state in_state
        in begin match merged with
        | None -> work rest
        | Some merged ->
            cell := Some merged;
            let updated = update cfg_node merged in
            let cont = next cfg_node in
            let new_work = List.map (fun pc -> (updated, pc)) cont in
            work (new_work @ rest)
        end
  in
  work [(init_state, cfg.(0))];
  Array.map (fun cell ->
    match !cell with
    | None -> assert(false)
    | Some x -> x) program_state


let dominators (program, cfg) =
  let merge cur_dom in_dom =
    let merged = CfgNodeSet.inter cur_dom in_dom in
    if CfgNodeSet.equal cur_dom merged then None else Some merged
  in
  let update node dom = CfgNodeSet.add node dom in
  let successors = Cfg.successors program cfg in
  cfg_dataflow_analysis successors CfgNodeSet.empty cfg merge update

let least_common_dominator (program, cfg) pc1 pc2 =
  let doms = dominators (program, cfg) in
  let node1 = Cfg.node_at cfg pc1 in
  let node2 = Cfg.node_at cfg pc2 in
  let dom1 = doms.(node1.id) in
  let dom2 = doms.(node2.id) in
  let common = CfgNodeSet.inter dom1 dom2 in
  CfgNodeSet.max_elt common

let dominates_all_uses (program, cfg, doms, used) pc =
  let uses = InstrSet.elements (used pc) in
  let node_id_at pc = (Cfg.node_at cfg pc).id in
  let node = node_id_at pc in
  let dom = doms.(node) in
  let least = CfgNodeSet.max_elt dom in
  let uses_doms = List.map (fun pc -> doms.(node_id_at pc)) uses in
  let common = List.fold_left CfgNodeSet.inter dom uses_doms in
  let uses_least = CfgNodeSet.max_elt common in
  least.id = uses_least.id

let least_reaching (program, cfg, doms, reaching) pc =
  let defs = InstrSet.elements (reaching pc) in
  let node_id_at pc = (Cfg.node_at cfg pc).id in
  let defs_doms = List.map (fun pc -> doms.(node_id_at pc)) defs in
  let common = List.fold_left CfgNodeSet.inter CfgNodeSet.empty defs_doms in
  CfgNodeSet.max_elt common

let can_move (program, cfg, doms, reaching, used) pc =
  let dominates_uses = dominates_all_uses (program, cfg, doms, used) pc in
  if not dominates_uses then None
  else
    let node = Cfg.node_at cfg pc in
    let least_reaching = least_reaching (program, cfg, doms, reaching) pc in
    if least_reaching.id >= node.id then None
    else Some least_reaching

