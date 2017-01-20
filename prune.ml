open Instr
open Transform

let branch_false (code : instruction_stream) : instruction_stream =
  let scope = Scope.infer (Scope.no_annotations code) in
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
  Array.concat (final :: [| EndOpt |] :: List.rev landing_pads)
