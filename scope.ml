open Instr

(* TODO:
    - keep track of const/mut status
*)

exception UndeclaredVariable of pc * VarSet.t
exception UninitializedVariable of pc * VarSet.t
exception DuplicateVariable of pc * VarSet.t

type scope_info = { declared : VarSet.t; defined : VarSet.t }
module ScopeInfo = struct
  type t = scope_info
  let inter a b = {declared = VarSet.inter a.declared b.declared;
                   defined = VarSet.inter a.defined b.defined}
  let union a b = {declared = VarSet.union a.declared b.declared;
                   defined = VarSet.union a.defined b.defined}
  let equal a b = VarSet.equal a.declared b.declared &&
                  VarSet.equal a.defined b.defined
end

let no_annotations (code : instruction_stream) : program  =
  { instructions = code; annotations = Array.map (fun _ -> None) code }

(* Internally we keep track of the declared and defined variables.
 * The output scopes and the annotations contain only the declarations. But
 * internally infer asserts that undefined variables are never used and
 * declarations do not shadow a previous one
 *)
let generic_infer update (code : program) : inferred_scope array =
  let instructions = code.instructions in
  let annotations = code.annotations in
  let open Analysis in
  let merge cur incom =
    let merged = ScopeInfo.inter cur incom in
    if ScopeInfo.equal cur merged then None else Some merged in
  let update pc incomming =
    (* Verify new declarations do not shadow existing ones *)
    let instr = instructions.(pc) in
    let created = { declared = Instr.declared_vars instr;
                    defined = Instr.defined_vars instr } in
    let shadowed = VarSet.inter incomming.declared created.declared in
    if not (VarSet.is_empty shadowed) then raise (DuplicateVariable (pc, shadowed))
    else
      (* Remove incomming variables which are excluded by the annotations
       * (The actual checking of scope annotations happens later) *)
      let annot = annotations.(pc) in
      let incomming' =
      { incomming with
        declared = begin match annot with
          | None | Some (At_least _) -> incomming.declared
          | Some (Exact constraints) ->
             VarSet.inter incomming.declared constraints
        end
      } in
      update instructions pc incomming' created
  in
  let initial_state = [({declared = VarSet.empty; defined = VarSet.empty}, 0)] in
  let res = Analysis.dataflow_analysis initial_state instructions merge update in
  let finish pc res =
    let annotation = annotations.(pc) in
    let instr = instructions.(pc) in
    match res with
    | None -> Dead
    | Some res ->
      let must_have_declared vars =
        if not (VarSet.subset vars res.declared)
        then raise (UndeclaredVariable (pc, (VarSet.diff vars res.declared))) in
      must_have_declared (Instr.required_vars instr);
      begin match annotation with
        | None -> ()
        | Some (At_least xs | Exact xs) -> must_have_declared xs;
      end;
      let must_have_defined vars =
        if not (VarSet.subset vars res.defined)
        then raise (UninitializedVariable (pc, (VarSet.diff vars res.defined))) in
      must_have_defined (Instr.used_vars instr);
      Scope res.declared
  in
  Array.mapi finish res

let infer (code : program) : inferred_scope array =
  let update code pc incomming created =
    let updated = ScopeInfo.union incomming created in
    let succ = Analysis.successors code pc in
    List.map (fun pc -> (updated, pc)) succ
  in
  generic_infer update code

(* Only if we have the whole program we can follow invalidate labels *)
let check_whole_program (code : program) =
  let update code pc incomming created =
    let updated = ScopeInfo.union incomming created in
    let instr = code.(pc) in
    match[@warning "-4"] instr with
    | Invalidate (_exp, br, scope) ->
      (* The Invalidate instruction continues in a new context,
       * only explicitly captured variables are preserved. *)
      let scope = VarSet.of_list scope in
      let pc_next, pc_deopt = pc+1, resolve code br in
      let deopt_frame = {
        declared = VarSet.inter updated.declared scope;
        defined = VarSet.inter updated.defined scope } in
      [(updated, pc_next); (deopt_frame, pc_deopt)]
    | _ ->
      let succ = Analysis.successors code pc in
      List.map (fun pc -> (updated, pc)) succ
  in
  ignore (generic_infer update code)


