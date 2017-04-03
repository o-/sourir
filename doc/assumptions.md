# Inserting Assumptions

## Language

The following assumes a slightly changed language: no functions, no mut cells.
The osr map is kept separate in explicit checkpoint instructions. The osr
always jumps one version down (from right to left) and to the last checkpoint.

    P  ::= Iₒ, O*                   - program
    Iₒ ::= i*                       - base version instructions
    O  ::= o*                       - version with assumptions
    Δ  ::= (x ↤ e)*                 - osr map
    o  ::=
      | i                           - normal instruction
      | checkpoint l Δ              - checkpoint
      | osr e                       - guard

## Definitions

We refer to the edges of a control flow graph of a program `I` as `⇢`

    i ⇢ i' ⇔ i' ∈ succ(I, i)

Note `⇢` is a preorder. From `i < i'` it follows that `i` dominates `i'`.

S denotes the scope

    S(I, l) = { x | x in scope in I at label l }

An expression `e` is valid at `l` in `I` iff all its variables are in scope.
If no ambiguities arise we leave out `l` and `I`

    e-valid (at l in I) iff x ∈ e ⇒ x ∈ S(I, l)

A correct speculatively optimized program is supposed to be equivalent to
the base version

    (Iₒ, O*) ✓     iff     Iₒ ≈ (Iₒ, O*)

The introspection program ↺ is a special program which at every checkpoint label
prints the content of the current environment and stops.

A correct optimization ↜ of a version with assumptions preserves equivalence
up to the osr boundary.

    (↺, O) ≈ (↺, O')
    ----------------
    O ↜ O'

To add an assumption we insert an osr guard directly after a checkpoint, ie.

    c = checkpoint l Δ
    O = o₁* ; c ; o₂*
    ------------------------------------------
    assume (e, l, O)  =  o₁* ; c ; osr !e ; o₂*

## Inserting assumptions

First we want to be able to add an assumption to a not yet speculatively
optimized program. Initially we add all possible checkpoints (they can
be trimmed later).

    I   = i*
    I' := (label lᵢ ; i)*
    O  := (checkpoint lᵢ Δᵢ ; i)*
    lᵢ  - fresh
    Δᵢ := { x ↤ x | ∀ x ∈ S(I', lᵢ) }
    --------------------------------   (init)
    (I', O) ✓

We can insert assumptions at every checkpoint

    (..., O) ✓
    l - checkpoint in O
    e - valid
    O' := assume (e, l, O)
    ----------------------   (asm)
    (..., O, O') ✓

We can perform optimizations on the program with assumptions without consulting
the base version:

    (..., O) ✓
    O ↜ O'
    -----------   (opt)
    (..., O') ✓

Finally we can compress intermediate versions

    (..., O, O') ✓
    O'' := O'[checkpoint l Δ' / checkpoint l (Δ' ° Δ)
              ∀   l - checkpoints in O'
              and Δ - osr map of checkpoint l in O]
    -------------------------------------------------   (comb)
    (..., O'') ✓

And remove unused checkpoints

    (..., O) ✓
    l,l' - checkpoints in O
    l' < l
    ∀ i : l' ⇢* i ⇢* l
      i - pure
    O' := [checkpoint l Δ / ⊥]
    --------------------------
    (..., O') ✓

### Proofs

*asm*

There exists a (trivial) bisimulation between `P` and `P'`.

* at position `l' ≠ l` the states remain in sync since `I₁(l') = I₂(l')`.
* at position `l' = l` the osr instruction is a noop
  since `S(I₁, l) = S(I₂, l)` and δ is the identity function.

TODO: other proofs

### Example

     I                              I'

      1  const x = read              1  const x = read
      2  y = x                       2  checkpoint 2 (x ↤ x)
                                        osr !(x=0)
                                        y = x
      3  branch (x=0) 4 5            3  branch (x=0) 4 5
      4  print y                     4  print y
      5  stop                        5  stop


# Non-Reordering Transformations

## Branch pruning

Assume true:

    I ∋ g = (osr !e)
    I ∋ b = (branch e' l₁, l₂)
    !e ⇒ e'
    g < b
    ∀ i : g ⇢* i ⇢* b
      i does not change vars in e
    ------------------------------
    I ≈ I[b/goto l₁]

Assume false:

    I ∋ g = osr !e
    I ∋ b = branch e' l₁, l₂
    e ⇒ !e'
    g < b
    ∀ i : g ⇢* i ⇢* b
      i does not change vars in e
    ------------------------------
    I ≈ I[b/goto l₂]

## Constant Propagation

    I ∋ a = (x = v)
    I ∋ u
    a < u
    u' := u[x/v]
    ∀ i : a ⇢* i ⇢* u
      I[i] does not change x
    -------------------------
    I ≈ I[u/u']

## Composition

Non-reordering transformations compose with speculate iff the refinements they
define are composed with all Δ's.

Proof: TODO show it is equivalent to (opt)

### Example

The following is an example for the chain of optimizations
`speculate; branch prune; const prop; speculate; branch prune`

(unused checkpoints are not shown)

Input program

    1  y = 1
    2  x = read
    3  checkpoint 3 (x ↤ x, y ↤ y)
       branch (x=0) 4 5
    4  y = 2
    5  checkpoint 5 (x ↤ x, y ↤ y)
       branch (y=x) 6 7
    6  print y
    7  stop

Speculate `x != 0` at 3 (copies the program so we can jump back)

    1  y = 1
    2  x = read
    3  checkpoint 3 (x ↤ x, y ↤ y)
       osr (x=0)
       branch (x=0) 4 5
    4  y = 2
    5  checkpoint 5 (x ↤ x, y ↤ y)
       branch (y=x) 6 7
    6  print y
    7  stop

Prune branch at 3

    1  y = 1
    2  x = read
    3  checkpoint 3 (x ↤ x, y ↤ y)
       osr (x=0)
       goto 5
    4  y = 2
    5  checkpoint 5 (x ↤ x, y ↤ y)
       branch (y=x) 6 7
    6  print y
    7  stop

Now `y` became constant, lets propagate it. Note how Δ is refined at line 3 and 5

    1  y = 1
    2  x = read
    3  checkpoint 3 (x ↤ x, y ↤ 1)
       osr (x=0)
       goto 5
    4  y = 2
    5  checkpoint 5 (x ↤ x, y ↤ 1)
       branch (1=x) 6 7
    6  print 1
    7  stop

Speculate `x != 1` at 5

    1  y = 1
    2  x = read
    3  checkpoint 3 (x ↤ x, y ↤ 1)
       osr (x=0)
       goto 5
    4  y = 2
    5  checkpoint 5 (x ↤ x, y ↤ 1)
       osr (x=1)
       branch (1=x) 6 7
    6  print 1
    7  stop

Prune branch at 5

    1  y = 1
    2  x = read
    3  checkpoint 3 (x ↤ x, y ↤ 1)
       osr (x=0)
       goto 5
    4  y = 2
    5  checkpoint 5 (x ↤ x, y ↤ 1)
       osr (x=1)
       goto 7
    6  print 1
    7  stop

Eliminate dead code

    2  x = read
    3  checkpoint 3 (x ↤ x, y ↤ 1)
       osr (x=0)
    5  checkpoint 5 (x ↤ x, y ↤ 1)
       osr (x=1)
    7  stop

Eliminate unused checkpoint and combine osr

    2  x = read
    3  checkpoint 3 (x ↤ x, y ↤ 1)
       osr (x=0) || (x=1)
    7  stop
