open Instr

(*
(*
 * Constant propagation. Takes a program `prog` and returns an updated stream.
 *
 * Finds all constant declarations of the form:
 *     const x = l
 * where `l` is a literal.
 *
 * Then, whenever `x` is used in an expression (while x is still in scope), it
 * is replaced by the literal `l`. Afterwards, the variable `x` is no longer
 * used, and the declaration can be removed by running `minimize_lifetimes`.
 *)
let const_prop ({formals; instrs} : analysis_input) : instructions option =
  (* Finds the declarations that can be used for constant propagation.
     Returns a list of (pc, x, l) where `const x = l` is defined at pc `pc`. *)
  let rec find_candidates instrs pc acc =
    if pc = Array.length instrs then acc
    else match[@warning "-4"] instrs.(pc) with
    | Decl_const (x, Simple(Constant(l))) ->
        find_candidates instrs (pc+1) ((pc, x, l) :: acc)
    | _ -> find_candidates instrs (pc+1) acc
  in

  (* Replaces the variable `x` with literal `l` in instruction `instr`. *)
  let convert x l instr =
    let replace = Edit.replace_var_in_exp x l in
    let replace_arg = Edit.replace_var_in_arg x l in
    match instr with
    | Call (y, f, es) ->
      assert (x <> y);
      Call (y, replace f, List.map replace_arg es)
    | Stop e ->
      Stop (replace e)
    | Return e ->
      Return (replace e)
    | Decl_const (y, e) ->
      assert (x <> y);
      Decl_const (y, replace e)
    | Decl_mut (y, Some e) ->
      assert (x <> y);
      Decl_mut (y, Some (replace e))
    | Assign (y, e) ->
      assert (x <> y);
      Assign (y, replace e)
    | Array_assign (y, i, e) ->
      assert (x <> y);
      Array_assign (y, replace i, replace e)
    | Branch (e, l1, l2) -> Branch (replace e, l1, l2)
    | Print e -> Print (replace e)
    | Osr (exp, tf, tv, tl, env) ->
      (* Replace all expressions in the osr environment. *)
      let env' = List.map (fun osr_def ->
        match osr_def with
        | Osr_const (y, e) -> Osr_const (y, replace e)
        | Osr_mut (y, e) -> Osr_mut (y, replace e)
        | Osr_mut_ref (y, z) -> if x=z then Osr_mut (y, Simple l) else osr_def
        | Osr_mut_undef y -> Osr_mut_undef y) env
      in
      Osr (replace exp, tf, tv, tl, env')
    | Drop y
    | Decl_mut (y, None)
    | Clear y
    | Read y ->
      assert (x <> y);
      instr
    | Label _ | Goto _ | Comment _ -> instr in

  (* Finds the target pcs to perform constant propagation. *)
  let rec find_targets instrs x worklist acc =
    let open Analysis in
    match worklist with
    | [] -> acc
    | pc :: rest ->
      begin match[@warning "-4"] instrs.(pc) with
      | Drop y when x = y ->
        (* `x` is now out of scope, but continue searching the `rest` of the
           worklist. *)
        find_targets instrs x rest acc
      | instr ->
        if PcSet.mem pc acc then
          (* Already seen this pc, but continue searching the `rest` of the
             worklist. *)
          find_targets instrs x rest acc
        else
          (* Add the current `pc` to the accumulator and update the worklist
             with our successors. *)
          let succs = successors_at instrs pc in
          find_targets instrs x (succs @ rest) (PcSet.add pc acc)
      end
  in

  (* Perform constant propagation. *)
  let work instrs =
    let open Analysis in
    (* Find all constant propagation candidates. *)
    let candidates = find_candidates instrs 0 [] in
    if candidates = [] then None else
    (* Perform all propagations for a single candidate. *)
    let propagate instrs (pc, x, l) =
      let succs = successors_at instrs pc in
      let targets = find_targets instrs x succs PcSet.empty in
      let instrs = Array.copy instrs in
      let convert_at pc = instrs.(pc) <- convert x (Constant(l)) instrs.(pc) in
      PcSet.iter convert_at targets;
      instrs
    in
    Some (List.fold_left propagate instrs candidates)
  in

  work instrs

open Transform_utils

let make_constant (({formals; instrs} as inp) : analysis_input) : instructions option =
  let required = Analysis.required inp in
  let constant var pc =
    match[@warning "-4"] instrs.(pc) with
    | Assign (x, _) when x = var -> false
    | Drop x when x = var -> false
    | Clear x when x = var -> false
    | Read x when x = var -> false
    | Call (_, _, exp) ->
      let is_passed_by_val = function
        | Arg_by_ref x when x = var -> false
        | _ -> true in
      List.for_all is_passed_by_val exp
    | _ -> true
  in

  let changes = Array.map (fun _ -> Unchanged) instrs in
  let rec apply pc =
    if Array.length instrs = pc then () else
    match[@warning "-4"] instrs.(pc) with
    | Decl_mut (var, Some exp) ->
      let required = required pc in
      if Analysis.PcSet.for_all (constant var) required
      then begin
        let fixup pc =
          let fixup_instr pc = function[@warning "-4"]
            | Osr (e, f, v, l, osr) ->
              let fixup_def = function[@warning "-4"]
                | Osr_mut_ref (x, y) when var = y -> Osr_mut (x, Simple (Var var))
                | d -> d in
              changes.(pc) <- Replace (Osr (e, f, v, l, List.map fixup_def osr))
            | _ -> () in
          match[@warning "-4"] changes.(pc) with
          | Unchanged -> fixup_instr pc instrs.(pc)
          | Replace i -> fixup_instr pc i
          | _ -> assert(false)
        in
        (* all uses keep this variable constant:
         * 1. Change the declaration to const
         * 2. Fixup osr uses: We need to materialize the heap value on osr-out *)
        changes.(pc) <- Replace (Decl_const (var, exp));
        Analysis.PcSet.iter fixup required;
      end;
      apply (pc+1)
    | _ ->
      apply (pc+1)
  in
  let () = apply 0 in
  change_instrs (fun pc -> changes.(pc)) inp
   *)
