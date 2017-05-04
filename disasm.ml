open Instr

let no_line_number buf pc = ()
let line_number buf pc = Printf.bprintf buf "% 6d |" pc

let pr = Printf.bprintf

let disassemble_instrs buf ?(format_pc = no_line_number) (prog : instructions) =
  let dump_instr buf pc instr =
    let rec dump_comma_separated how buf what =
      match what with
      | [] -> ()
      | [e] -> how buf e
      | e::t -> pr buf "%a, %a" how e (dump_comma_separated how) t
    in
    let simple buf = function
      | Var v             -> pr buf "%s" v
      | Constant c        -> pr buf "%s" (string_of_value c)
    in
    let dump_expr buf exp =
      match exp with
      | Simple e          -> simple buf e
      | Op (Plus, [a; b]) -> pr buf "(%a + %a)" simple a simple b
      | Op (Neq,  [a; b]) -> pr buf "(%a != %a)" simple a simple b
      | Op (Eq,   [a; b]) -> pr buf "(%a == %a)" simple a simple b
      | Op ((Plus | Neq | Eq), _)         -> assert(false)
      | Op (Array_alloc, [size]) -> pr buf "array(%a)" simple size
      | Op (Array_of_list, li) -> pr buf "[%a]" (dump_comma_separated simple) li
      | Op (Array_index, [array; index]) -> pr buf "%a[%a]" simple array simple index
      | Op (Array_length, [array]) -> pr buf "length(%a)" simple array
      | Op ((Array_alloc | Array_index | Array_length), _) -> assert(false)
    in
    format_pc buf pc;
    begin match instr with
    | Call (var, f, args)               ->
      pr buf " call %s = "var;
      dump_expr buf f;
      pr buf " (%a)" (dump_comma_separated dump_expr) args;
    | Return exp                      -> pr buf " return %a" dump_expr exp
    | Declare (var, Some exp)         -> pr buf " var %s = %a" var dump_expr exp
    | Declare (var, None)             -> pr buf " var %s" var
    | Assign (var, exp)               -> pr buf " %s <- %a" var dump_expr exp
    | Array_assign (var, index, exp)  -> pr buf " %s[%a] <- %a" var dump_expr index dump_expr exp
    | Branch (exp, l1, l2)            -> pr buf " branch %a %s %s" dump_expr exp l1 l2
    | Label label                     -> pr buf "%s:" label
    | Goto label                      -> pr buf " goto %s" label
    | Print exp                       -> pr buf " print %a" dump_expr exp
    | Read var                        -> pr buf " read %s" var
    | Drop var                        -> pr buf " drop %s" var
    | Osr (exp, f, v, l, vars)        ->
      let dump_var buf = function
        | Osr_move (x, y)     -> pr buf "%s = &%s" x y
        | Osr_materialize (x, Some e)     -> pr buf "%s = %a" x dump_expr e
        | Osr_materialize (x, None)       -> pr buf "%s" x
      in
      pr buf " osr %a %s %s %s [%a]"
        dump_expr exp
        f v l
        (dump_comma_separated dump_var) vars
    | Comment str                     -> pr buf " #%s" str
    end;
    pr buf "\n"
  in
  Array.iteri (dump_instr buf) prog

let disassemble buf (prog : Instr.program) =
  (* TODO: disassemble annotations *)
  List.iter (fun {name; formals; body} ->
      let print_formal buf = pr buf "%s" in
      let print_formals buf = List.iter (print_formal buf) formals in
      Printf.bprintf buf "function %s (%t)\n" name print_formals;
      List.iter (fun version ->
          pr buf "version %s\n" version.label;
          disassemble_instrs buf version.instrs) body
    ) (prog.main :: prog.functions)

let disassemble_s (prog : Instr.program) =
  let b = Buffer.create 1024 in
  disassemble b prog;
  Buffer.to_bytes b

let disassemble_o outchan (prog : Instr.program) =
  let b = Buffer.create 1024 in
  disassemble b prog;
  Buffer.output_buffer outchan b

let disassemble_instrs_s (prog : instructions) =
  let b = Buffer.create 1024 in
  disassemble_instrs b prog;
  Buffer.to_bytes b

let pretty_print_version outchan (name, version) =
  let b = Buffer.create 1024 in
  Printf.bprintf b "version %s\n" name;
  disassemble_instrs b ~format_pc:line_number version;
  Buffer.output_buffer outchan b

let pretty_print outchan prog =
  List.iter (pretty_print_version outchan) prog
