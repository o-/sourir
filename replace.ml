open Instr

let var_in_simple_exp var exp (in_exp:simple_expression) : simple_expression =
  match in_exp with
  | Lit _ -> in_exp
  | Var x -> if x = var then exp else in_exp

let var_in_exp var exp in_exp : expression =
  let in_simple_expression = var_in_simple_exp var exp in
  match in_exp with
  | Simple se -> Simple (in_simple_expression se)
  | Op (op, exps) ->
    Op (op, List.map in_simple_expression exps)
