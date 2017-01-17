let dominates_all_uses (program, cfg, doms, used) pc =
  let open Cfg in
  let uses = used pc in
  if Analysis.InstrSet.is_empty uses then true
  else
    let sentinel = {id = -1; entry = -1; exit = -1; prepend = -1; append = -1; succ = [cfg.(0)]} in
    let bb_at pc = bb_at cfg pc in
    let bb_def = bb_at pc in
    let doms_def = doms.(bb_def.id) in
    let dom_def = if BasicBlockSet.is_empty doms_def then sentinel
          else BasicBlockSet.max_elt doms_def in
    let uses = Analysis.InstrSet.elements uses in
    let bb_uses = List.map (fun pc -> bb_at pc) uses in
    let doms_uses = List.map (fun bb -> doms.(bb.id)) bb_uses in
    let dom_uses = List.map (fun doms ->
        if BasicBlockSet.is_empty doms then sentinel
            else BasicBlockSet.max_elt doms) doms_uses in
    List.for_all2 (fun use dom ->
        dom_def.id < dom.id ||
        (* common dominator and in the same basic block -> fine if def is before use
         * (eg. linear loop body with both def and use) *)
        (dom_def.id = dom.id && bb_def.id = (bb_at use).id &&
           use > pc)) uses dom_uses

let can_move_analysis (program, scope, cfg, doms, reaching, used) pc
  : Cfg.basic_block option =
  let defs = Instr.defined_vars program.(pc) in
  (* 1. Condition: I have a dominator *)
  let open Cfg in
  let bb = bb_at cfg pc in
  let my_doms = doms.(bb.id) in
  if BasicBlockSet.is_empty my_doms then None
  else
    (* 2. Condition: I dominates all uses *)
    if not (dominates_all_uses (program, cfg, doms, used) pc) then None
    else
      (* 3. Condition: All reaching definitions dominate me *)
      let reaching_def = Analysis.InstrSet.elements (reaching pc) in
      let reaching = List.map (fun pc -> bb_at cfg pc) reaching_def in
      let dominates_me other =
        match BasicBlockSet.find other my_doms with
        | exception Not_found -> false
        | _ -> true
      in
      let reaching_dominates_me = List.map dominates_me reaching in
      if not (List.fold_left (&&) true reaching_dominates_me) then None
      else
        (* 4. Condition: Do not move above reaching definitions *)
        let max_reaching =
          if reaching = [] then -1 else (BasicBlockSet.max_elt (BasicBlockSet.of_list reaching)).id in
        let move_candidates = BasicBlockSet.filter (fun bb ->
            bb.id >= max_reaching) my_doms in
        (* 5. Condition: Do not move out of scope *)
        let open Instr in
        let candidates_in_scope = BasicBlockSet.filter (fun bb ->
            match[@warning "-4"] scope.(bb.append) with
            | Scope scope when not (VarSet.is_empty (VarSet.inter defs scope)) -> true
            | _ -> false) move_candidates in
        (* Done *)
        if BasicBlockSet.is_empty candidates_in_scope then None
        else Some (BasicBlockSet.min_elt candidates_in_scope)

let can_move prog =
  let scope = Scope.infer (Scope.no_annotations prog) in
  let cfg = Cfg.of_program prog in
  let doms = Cfg.dominators (prog, cfg) in
  let reaching = Analysis.reaching prog in
  let used = Analysis.used prog in
  can_move_analysis (prog, scope, cfg, doms, reaching, used)

let rec apply (prog : Instr.program) : Instr.program =
  let apply_step (prog : Instr.program) =
    let scope = Scope.infer (Scope.no_annotations prog) in
    let cfg = Cfg.of_program prog in
    let doms = Cfg.dominators (prog, cfg) in
    let reaching = Analysis.reaching prog in
    let used = Analysis.used prog in
    let can_move = can_move_analysis (prog, scope, cfg, doms, reaching, used) in

    let rec get_move_candidate pc =
      if pc = Array.length prog then None
      else match can_move pc with
        | None -> get_move_candidate (pc + 1)
        | Some bb -> Some (pc, bb)
    in

    match get_move_candidate 0 with
    | None -> None
    | Some (pc, bb) ->
      let open Cfg in
      Some (Array.concat [
        Array.sub prog 0 (bb.append);
        [| prog.(pc) |];
        Array.sub prog (bb.append) (pc-bb.append);
        Array.sub prog (pc+1) ((Array.length prog)-(pc+1))
      ])
  in

  match apply_step prog with
  | None -> prog
  | Some prog -> apply prog
