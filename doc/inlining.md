## Warmup

As a simple warmup example lets consider inlining a function without osrs.
Using some fresh variables for all variables of the function we simulate a letrec
block to evaluate the body inside.

```
function main()
  var x = 1
  call y = 'foo(x)
  print y

function foo(var x)
  return x
```

The call to foo is constant and we can inline.

```
function main()
  var x = 1

  #inline prologue: create fresh names
  var x_1 = x
  # inline body
  var res = x_1
  goto inline_epilogue:
  # epilogue
  inline_epiloque:
  drop x_1
  var y = res
  drop res

  print y
```

## Static calls

As a sidenote: If the call is not constant yet we could optimistically make it constant with the following transformation:

```
function main()
  var x = 1
  var call = someExpression
  call y = call(x)
  print y
```

to:

```
function main()
  var x = 1
  var call = someExpression
  osr [call != 'foo] ...
  call y = 'foo(x)
  print y
```

## With osr

Having the osr in the outer function poses no additional difficulties. Now lets assume the inlinee has assumptions.
As an example:

```
function main()
  version base
    var x = 1
    call y = 'foo(x)
    print y

function foo(var z)
  version opt
    cp1:
    osr [z != 1] (foo, base, cp1) [var z = 1]
    return 1

  version base
    cp1:
    return z
```

When we inline the optimized version of foo the osr is no longer correct because it replaces the current execution environment. We need to make sure
that the deoptimized inlined function returns to the correct place -- which is after the inlined body. To acchieve this we extend osr to take an additional
continuation. The idea is that this version of osr leaves the current frame untouched and instead creates a fresh one. As an additional complication
we also need to drop the variables of the inlinee from the current frame.

```
function main()
  version base
    1   var x = 1
    2
    3   #inline prologue: create fresh names
    4   var z_1 = x
    5   # inline body
    6   osr [z_1 != 1] (foo, base, cp1) [var z = 1] @ (main, base, inline_end, y) [drop z_1]
    7   var res = 1
    8   goto inline_epilogue:
    9   # epilogue
    10  inline_epilogue:
    11  drop z_1
    12  var y = res
    13  drop res
    14  inline_end:
    15
    16  print y

function foo(var z)
  version opt
    1   cp1:
    2   osr [z != 1] (foo, base, cp1) [var z = 1]
    3   return 1

  version base
    1   cp1:
    2   return z
```

Remember the following defs from the semantic:

    C ::= (a, E, I, l)                 continuation:  result accumulator, environment, instructions, label
    M ::= (P, C*) : (I, T, H, E, l)    machine state: program, continuations : instructions, trace, heap, environment, pc

in the above example the continuation `(y, E \ {z_1}, main::base, inline_end)` is pushed on the continuation stack.


Therefore, before the osr our machine state is:

    (P, ())                                 :  (main::base, T, H, {x=1, z_1=1}, 6)

After osr it is

    (P, (y, {x=1}, main::base, inline_end)) :  (foo::base, T, H, {z=1},         1)

After the function foo returns it is:

    (P, ())                                 :  (main::base, T, H, {x=1, y=1},   14)
