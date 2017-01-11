open Instr
open Analysis

type cfg_node = { id : int; entry : pc; exit : pc; succ : int list }
module CfgNode = struct
  type t = cfg_node
  let compare a b = Pervasives.compare a.id b.id
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
        match[@warning "-4"] program.(pc) with
        | Goto _ | Branch _ | Stop -> pc
        (* Fall through to another label exits the basic block *)
        | Label _ -> (pc-1)
        | _ -> next_exit (pc+1)
    in
    let rec find_nodes work id acc : cfg_node list =
      match work with
      | [] -> acc
      | pc :: rest ->
          let seen acc pc = List.exists (fun n -> n.entry = pc) acc in
          if seen acc pc then find_nodes rest id acc
          else
            (* first bb starts without label *)
            let exit = if pc = 0 then next_exit 0 else next_exit (pc+1) in
            let node = {id = id; entry = pc; exit = exit; succ = []} in
            let acc = node :: acc in
            let succ = successors program exit in
            let succ = List.filter (fun pc -> not (seen acc pc)) succ in
            (* explore cfg depth first to ensure topological order of id *)
            find_nodes (succ @ rest) (id+1) acc
    in
    let entries = find_nodes [0] 0 [] in
    let prov_cfg = Array.of_list entries in
    (* TODO: maybe assign the successors in the above loop
     * but its kinda hard with the order constraints *)
    let rec find_succ nodes =
      match nodes with
      | [] -> []
      | node :: rest ->
          let succ = successors program node.exit in
          let ids = List.map (fun pc -> (node_at prov_cfg pc).id) succ in
          let node = {id = node.id; entry = node.entry; exit = node.exit; succ = ids} in
          node :: find_succ rest
    in
    let entries = find_succ entries in
    Array.of_list (List.rev entries)

  let successors cfg node =
    List.map (fun i -> cfg.(i)) node.succ
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
  let successors = Cfg.successors cfg in
  cfg_dataflow_analysis successors CfgNodeSet.empty cfg merge update

let common_dominator (program, cfg, doms) pcs =
  let nodes = List.map (Cfg.node_at cfg) pcs in
  let doms = List.map (fun n -> CfgNodeSet.add n doms.(n.id)) nodes in
  let common = List.fold_left CfgNodeSet.inter (List.hd doms) (List.tl doms) in
  assert (not (CfgNodeSet.is_empty common));
  CfgNodeSet.max_elt common

