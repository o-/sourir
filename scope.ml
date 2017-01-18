open Instr

(* TODO:
    - keep track of const/mut status
*)

exception UndeclaredVariable of pc * VarSet.t
exception UninitializedVariable of pc * VarSet.t
exception DuplicateVariable of pc * VarSet.t

type scope_info = { declared : TypedVarSet.t; defined : TypedVarSet.t; osr : VarSet.t }

module ScopeInfo = struct
  type t = scope_info
  let inter a b = {declared = TypedVarSet.inter a.declared b.declared;
                   defined = TypedVarSet.inter a.defined b.defined;
                   osr = VarSet.inter a.osr b.osr}
  let union a b = {declared = TypedVarSet.union a.declared b.declared;
                   defined = TypedVarSet.union a.defined b.defined;
                   osr = VarSet.union a.osr b.osr}
  let equal a b = TypedVarSet.equal a.declared b.declared &&
                  TypedVarSet.equal a.defined b.defined &&
                  VarSet.equal a.osr b.osr
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
    let instr = instructions.(pc) in
    let created = { declared = Instr.declared_vars instr;
                    defined = Instr.defined_vars instr;
                    osr = VarSet.empty } in
    (* Verify new declarations do not shadow existing ones.
     * Note: Only invalidate is allowed to create conflicting declarations *)
    let shadowed = TypedVarSet.inter incomming.declared created.declared in
    let real_shadowed = TypedVarSet.diff_untyped shadowed incomming.osr in
    if not (TypedVarSet.is_empty real_shadowed)
    then raise (DuplicateVariable (pc, TypedVarSet.untyped shadowed))
    else
      (* Remove incomming variables which are excluded by the annotations
       * (The actual checking of scope annotations happens later) *)
      let annot = annotations.(pc) in
      let incomming' =
      { incomming with
        declared = begin match annot with
          | None | Some (At_least _) -> incomming.declared
          | Some (Exact constraints) ->
             TypedVarSet.inter_untyped incomming.declared constraints
        end
      } in
      update instructions pc incomming' created
  in
  let initial_state = [({declared = TypedVarSet.empty; defined = TypedVarSet.empty; osr = VarSet.empty}, 0)] in
  let res = Analysis.dataflow_analysis initial_state instructions merge update in
  let finish pc res =
    let annotation = annotations.(pc) in
    let instr = instructions.(pc) in
    match res with
    | None -> Dead
    | Some res ->
      let must_have_declared vars =
        let declared = TypedVarSet.untyped res.declared in
        if not (VarSet.subset vars declared)
        then raise (UndeclaredVariable (pc, (VarSet.diff vars declared))) in
      must_have_declared (Instr.required_vars instr);
      begin match annotation with
        | None -> ()
        | Some (At_least xs | Exact xs) -> must_have_declared xs;
      end;
      let must_have_defined vars =
        let defined = TypedVarSet.untyped res.defined in
        if not (VarSet.subset vars defined)
        then raise (UninitializedVariable (pc, (VarSet.diff vars defined))) in
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
        declared = TypedVarSet.inter_untyped updated.declared scope;
        defined = TypedVarSet.inter_untyped updated.defined scope;
        osr = scope } in
      [(updated, pc_next); (deopt_frame, pc_deopt)]
    | _ ->
      let succ = Analysis.successors code pc in
      List.map (fun pc -> (updated, pc)) succ
  in
  ignore (generic_infer update code)


