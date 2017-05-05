%token NIL
%token<bool> BOOL
%token<int> INT
%token<string> IDENTIFIER
%token AMPERSAND SINGLE_QUOTE
%token DOUBLE_EQUAL NOT_EQUAL PLUS /* MINUS TIMES LT LTE GT GTE */
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token COLON EQUAL LEFTARROW TRIPLE_DOT COMMA
%token VAR BRANCH GOTO PRINT OSR DROP RETURN CALL VERSION FUNCTION
%token ARRAY LENGTH READ
%token<string> COMMENT
%token NEWLINE
%token EOF

%start<Instr.program> program
%start<Instr.value> value

%{ open Instr

let scope_annotation (mode, xs) =
  let xs = Instr.VarSet.of_list xs in
  match mode with
  | `Exact -> Instr.ExactScope xs
  | `At_least -> Instr.AtLeastScope xs
%}


%%

program: optional_newlines prog=program_code EOF { prog }

program_code:
| l1=instruction_line prog=list(instruction_line) fs=list(afunction)
  {
    let annotations, instructions = List.split prog in
    let a1, i1 = l1 in
    { main = {
          name = "main";
          formals = [];
          body = [{
              label = "anon";
              instrs = Array.of_list (i1::instructions);
              annotations = Some (Array.of_list (a1::annotations));}] };
      functions = fs;
    }
  }
| f1=afunction fs=list(afunction)
  {
    let fs = f1 :: fs in
    let main = (try List.find (fun {name = n} -> n = "main") fs with
        | Not_found -> {
            (* This is a bit dodgy, but will be caught and reported by the checker later *)
            name = "invalid"; formals = []; body = [];
          }
      ) in
    let rest = List.filter (fun {name = n} -> n <> "main") fs in
    { main = main;
      functions = rest; }
  }

afunction:
| FUNCTION name=variable LPAREN formals=separated_list(COMMA, variable) RPAREN NEWLINE optional_newlines prog=list(instruction_line)
  {
    let annotations, instructions = List.split prog in
    { name = name;
      formals = formals;
      body = [{
          label = "anon";
          instrs = Array.of_list instructions;
          annotations = Some (Array.of_list annotations)}]; }
  }
| FUNCTION name=variable LPAREN formals=separated_list(COMMA, variable) RPAREN NEWLINE optional_newlines v1=version vs=list(version)
  {
    let vs = v1 :: vs in
    { name = name;
      formals = formals;
      body = vs; }
  }

version:
| VERSION label=variable NEWLINE optional_newlines prog=list(instruction_line)
  {
    let annotations, instructions = List.split prog in
    { label = label;
      instrs = Array.of_list instructions;
      annotations = Some (Array.of_list annotations); }
  }

instruction_line:
| comments a=scope_annotation i=instruction NEWLINE optional_newlines { (a, i) }

scope_annotation:
| { None }
| annot=delimited(LBRACE, scope, RBRACE) optional_newlines { Some (scope_annotation annot) }

optional_newlines: list(NEWLINE) { () }
comments: list(COMMENT) { () }

scope:
| x=variable COMMA sc=scope { let (mode, xs) = sc in (mode, x::xs) }
| x=variable { (`Exact, [x]) }
| { (`Exact, []) }
| TRIPLE_DOT { (`At_least, []) }

osr_def:
| VAR x=variable EQUAL AMPERSAND y=variable
    { Osr_move (x, y) }
| VAR x=variable EQUAL e=expression
    { Osr_materialize (x, e) }

instruction:
| RETURN e=expression
  { Return e }
| VAR x=variable EQUAL e=expression
  { Declare (x, Expr e) }
| VAR x=variable EQUAL READ
  { Declare (x, Read) }
| VAR x=variable EQUAL f=expression LPAREN args=separated_list(COMMA, expression) RPAREN
  { Declare (x, Call (f, args)) }
| x=variable EQUAL e=expression
  { Assign (x, Expr e) }
| x=variable EQUAL READ
  { Assign (x, Read) }
| x=variable EQUAL f=expression LPAREN args=separated_list(COMMA, expression) RPAREN
  { Assign (x, Call (f, args)) }
| x=variable LBRACKET i=expression RBRACKET LEFTARROW e=expression
  { Array_assign (x, i, e) }
| BRANCH e=expression l1=label l2=label
  { Branch (e, l1, l2) }
| l=label COLON
  { Label l }
| GOTO l=label
  { Goto l }
| DROP x=variable
  { Drop x }
| PRINT e=expression
  { Print e }
| OSR LBRACKET cs=separated_list(COMMA, expression) RBRACKET LPAREN f=label COMMA v=label COMMA l=label RPAREN LBRACKET xs=separated_list(COMMA, osr_def) RBRACKET
  { Osr {cond=cs; target= {func=f; version=v; label=l}; map=xs} }

simple_expression:
  | v=lit { Constant v }
  | x=variable { Var x }

expression:
  | e = simple_expression { Simple e }
  | LPAREN e1=simple_expression op=infixop e2=simple_expression RPAREN
    { Op (op, [e1;e2]) }
  | ARRAY LPAREN size=simple_expression RPAREN
    { Op (Array_alloc, [size]) }
  | LBRACKET xs=separated_list(COMMA, simple_expression) RBRACKET
    { Op (Array_of_list, xs) }
  | x=variable LBRACKET index=simple_expression RBRACKET
    { Op (Array_index, [Var x; index]) }
  | LENGTH LPAREN x=simple_expression RPAREN
    { Op (Array_length, [x]) }

label: id=IDENTIFIER { (id : Label.t) }
variable: id=IDENTIFIER { (id : Variable.t) }

infixop:
  | DOUBLE_EQUAL { Eq }
  | NOT_EQUAL { Neq }
  | PLUS { Plus }
  (* | MINUS { Sub } *)
  (* | TIMES { Mult } *)
  (* | LT { Lt } *)
  (* | LTE { Lte } *)
  (* | GT { Gt } *)
  (* | GTE { Gte } *)

lit:
  | NIL { (Nil : value) }
  | SINGLE_QUOTE f=variable { (Fun_ref f : value) }
  | b=BOOL { (Bool b : value) }
  | n=INT { (Int n : value) }

value:
  | lit { $1 }
  | LBRACKET vs=separated_list(COMMA, value) RBRACKET
    { (Array_ref (Address.fresh ())) (* TODO *) }
