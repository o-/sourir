open Instr

let dominates_all_uses (program, cfg, doms, used) pc =
  let open Cfg in
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

let fresh_variable program =
  let rec collect_vars pc =
    if pc = Array.length program then TypedVarSet.empty
    else
      let vars = Instr.defined_vars program.(pc) in
      TypedVarSet.union vars (collect_vars (pc+1))
  in
  let used = TypedVarSet.untyped (collect_vars 0) in
  fun var ->
    let rec find_next i =
      let new_var = var ^ "." ^ (string_of_int i) in
      match VarSet.find new_var used with
      | exception Not_found -> new_var
      | _ -> find_next (i+1)
    in
    find_next 0

let can_move_analysis (program, scope, cfg, doms, reaching, used) pc
  : Cfg.basic_block option =
  (* 1. Condition: I have a dominator *)
  let open Cfg in
  match bb_at cfg pc with
  | exception Analysis.DeadCode _ -> None
  | bb ->
    let instr = program.(pc) in
    match instr with
    | Branch _ | Label _ | Goto _ | Read _ | Print _ | Invalidate _
    | Stop | Comment _ | EndOpt | Decl_mut _ -> None
    | Decl_const _ | Assign _ ->
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
            let needed_vars = TypedVarSet.diff (defined_vars instr) (declared_vars instr) in
            let candidates_in_scope = if TypedVarSet.is_empty needed_vars then move_candidates
              else BasicBlockSet.filter (fun bb ->
                  match[@warning "-4"] scope.(bb.append) with
                  | Scope scope when TypedVarSet.equal needed_vars
                                       (TypedVarSet.inter needed_vars scope) -> true
                  | _ -> false) move_candidates
            in
            (* Done *)
            if BasicBlockSet.is_empty candidates_in_scope then None
            else Some (BasicBlockSet.min_elt candidates_in_scope)

let can_move (prog : instruction_stream) : pc -> Cfg.basic_block option =
  let scope = Scope.infer (Scope.no_annotations prog) in
  let cfg = Cfg.of_program prog in
  let doms = Cfg.dominators (prog, cfg) in
  let reaching = Analysis.reaching prog in
  let used = Analysis.used prog in
  can_move_analysis (prog, scope, cfg, doms, reaching, used)

let replace_used_var instr old_var new_var =
  let replace_var_simple_exp exp old_var new_var =
    match exp with
    | Var v when v = old_var -> Var new_var
    | Var _
    | Lit _ -> exp
  in
  let replace_var_exp exp old_var new_var =
    match exp with
    | Simple e -> Simple (replace_var_simple_exp e old_var new_var)
    | Op (Plus, [a; b]) ->
      Op (Plus, [replace_var_simple_exp a old_var new_var;
                 replace_var_simple_exp b old_var new_var])
    | Op (Neq, [a; b]) ->
      Op (Neq, [replace_var_simple_exp a old_var new_var;
                replace_var_simple_exp b old_var new_var])
    | Op (Eq, [a; b]) ->
      Op (Eq, [replace_var_simple_exp a old_var new_var;
               replace_var_simple_exp b old_var new_var])
    | Op ((Plus | Neq | Eq), _) -> assert false
  in
  match instr with
  | Decl_const (x, e) -> Decl_const (x, replace_var_exp e old_var new_var)
  | Decl_mut (x, Some e) -> Decl_mut (x, Some (replace_var_exp e old_var new_var))
  | Branch (e, l1, l2) -> Branch (replace_var_exp e old_var new_var, l1, l2)
  | Read x when x = old_var -> Read new_var
  | Print e -> Print (replace_var_exp e old_var new_var)
  | Invalidate (e, l, xs) ->
    Invalidate (replace_var_exp e old_var new_var, l,
                { captured = List.map (fun v -> if v = old_var then new_var else v) xs.captured;
                  out = xs.out })
  | Assign (x, e) -> Assign (x, replace_var_exp e old_var new_var)
  | Decl_mut _
  | Label _
  | Goto _
  | Read _
  | Comment _
  | EndOpt
  | Stop -> instr

let apply (code : instruction_stream) : instruction_stream =
  let code = Transform.lift_all code in

  let rec do_apply (code : instruction_stream) : instruction_stream =
    let apply_step (code : instruction_stream) : instruction_stream option =
      let scope = Scope.infer (Scope.no_annotations code) in
      let cfg = Cfg.of_program code in
      let doms = Cfg.dominators (code, cfg) in
      let reaching = Analysis.reaching code in
      let used = Analysis.used code in
      let can_move = can_move_analysis (code, scope, cfg, doms, reaching, used) in

      let rec get_move_candidate pc =
        if pc = Array.length code then None
        else if code.(pc) = EndOpt then None
        else match can_move pc with
          | None -> get_move_candidate (pc + 1)
          | Some bb -> Some (pc, bb)
      in

      let apply_move code used to_insert old_var new_var remove insert =
        Analysis.InstrSet.iter (fun pc ->
            code.(pc) <- replace_used_var code.(pc) old_var new_var
          ) used;
        let len = Array.length code in
        if remove < insert then
          Array.concat [
            Array.sub code 0 remove;
            Array.sub code (remove+1) (insert-remove-1);
            [| to_insert |];
            Array.sub code insert (len-insert)
          ]
        else
          Array.concat [
            Array.sub code 0 insert;
            [| to_insert |];
            Array.sub code insert (remove-insert);
            Array.sub code (remove+1) (len-remove-1)
          ]
      in

      match get_move_candidate 0 with
      | None -> None
      | Some (pc, bb) ->
        let open Cfg in
        let used = used pc in
        let fresh_var = fresh_variable code in
        let res =
          match[@warning "-4"] code.(pc) with
          | Decl_const (x, e) ->
            let new_var = fresh_var x in
            apply_move
              code
              used
              (Decl_const (new_var, e))
              x
              new_var
              pc
              bb.append
          | Assign (x, e) ->
            let new_var = fresh_var x in
            apply_move
              code
              used
              (Decl_mut (new_var, Some e))
              x
              new_var
              pc
              bb.append
          | _ -> assert false
        in
        Some res
    in

    match apply_step code with
    | None -> code
    | Some code -> do_apply code
  in
  do_apply code
