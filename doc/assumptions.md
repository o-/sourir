# Inserting Assumptions

The following assumes a subset of the language: no functions, no mut cells, two
segments per program, the first segment is the currently active, osr always goes
from segment 1 to segment 2, there is one instruction and at most one osr per
label and the osr occurs before the other instruction.

    P ::= (I, I)            - program
    I ::= (l ↦ g; i)*       - guarded instruction
    g ::= ⊥ | osr e l' Δ    - guard

We use the following two operators to access guards and instructions under the
same label:

    I{l} = g
    I[l] = i

## Definitions

S denotes the scope

    S(I, l) = { x | x in scope in I at label l }

An expression `e` is valid at `l` in `I` iff all its variables are in scope.
If no ambiguities arise we leave out `l` and `I`

    e-valid (at l in I) iff x ∈ e ⇒ x ∈ S(I, l)

We say `P := (I₂, I₁)` is a valid speculatively optimized program iff
`(I₂, I₁)` is equivalent to `I₁` and all checkpoints are valid.

    (I₂, I₁) ≈ I₁
    ∀ l-checkpoint ∈ dom I₂
      (I₂, I₁) : l ↦ I₂{l} ✓
    ------------------------ (✓)
    (I₂, I₁) ✓

A checkpoint is a label `l` with non-empty guard `I{l} ≠ ⊥`.

Checkpoints are valid if Δ is consistent with some bisimulation `(I₂, I₁) ≈ I₁`

    ∃ bisimulation relation for (I₂, I₁) ≈ I₁  st.
      ∀ (P, I₂, T, H, E, l) ~ (P, I₁, T', H', E', l')
        ⇒ E' = ΔE
    --------------------------------------------------- (g✓)
    (I₂, I₁) : l ↦ osr (e l' Δ) ✓

Checkpoints can be initialized with `osr ⊥ l {x = x | ∀ x ∈ S(I, l)}`. Those are
called *initial checkpoints*.

Finally, let `speculate` be the mechanism to add an assumption `e` at `l`

    speculate (e, l, I) =
      let osr (e', l', Δ) = I{l}
      I{l ↦ osr (!e || e', l', Δ)}

## Inserting assumptions

First we want to be able to add an assumption to a not yet optimized program.

*Lemma 1*

    I - with only initial checkpoints
    e - valid
    l - initial checkpoint
    I' := speculate (e, l, I₁)
    ---------------------------------
    (I', I) ✓

We want to add further assumptions to an already optimized program.

*Thm 1*

    (I₂, I₁) ✓
    e - valid
    l - checkpoint
    I' := speculate (e, l, I₁)
    --------------------------
    (I', I₁) ✓

Note that the input to *Thm 1* is any valid optimized program -- not just
programs produced by itself.

From *L1* and *T1* it follows that an arbitrary chain of assumption insertion
is valid if every insertion point is a checkpoint.

*Corollary 1*

    I
    l₁, l₂, ..., lₙ - initial checkpoints in I
    e₁, e₂, ..., eₙ - valid assumptions at corresponding l
    ------------------------------------------------------
    I ≈ (... ° speculate e₂ l₂ ° speculate e₁ l₁) I

### Proofs

*Lemma 1*

There exists a (trivial) bisimulation between `P` and `P'`.

* at position `l' ≠ l` the states remain in sync since `I₁(l') = I₂(l')`.
* at position `l' = l` the osr instruction is a noop
  since `S(I₁, l) = S(I₂, l)` and Δ is the identity function.

TODO: Proof for *Thm 1*

### Example

     I₁                             I₂

      1:                             1:
          const x = read                 const x = read
      2:  osr (⊥, I₁, 2, [x = x])    2:  osr (!(x=0), I₁, 2, [x = x])
          y = x                          y = x
      3:                             3:
          branch (x=0) 4 5               branch (x=0) 4 5
      4:                             4:
          print y                        print y
      5:                             5:
          stop                           stop


# Non-Reordering Transformations

## Definitions

We refer to the edges of a control flow graph of a program `I` as `↦`

    l ⇢ l' ⇔ l' ∈ succ(I, l)

Note `⇢` is a preorder. From `l > l'` it follows that `l` dominates `l'`.

## Branch pruning

Assume true:

    !e ⇒ e'
    l' ↦ osr !e
    l  ↦ branch e' l₁, l₂
    l' > l
    ∀ l⁺ : l' ⇢* l⁺ ⇢* l
      I[l⁺] does not change vars in e
    ---------------------------------
    I ≈ I[l ↦ goto l₁]

Assume false:

    e ⇒ !e'
    l' ↦ osr e
    l  ↦ branch e' l₁, l₂
    l' > l
    ∀ l⁺ : l' ⇢* l⁺ ⇢* l
      I[l⁺] does not change vars in e
    ---------------------------------
    I ≈ I[l ↦ goto l₂]

## Constant Propagation

    l' ↦ x = v
    l  ↦ i
    l' > l
    ∀ l⁺ : l' ⇢* l⁺ ⇢* l
      I[l⁺] does not change x
    -------------------------
    I ≈ I[l][x/v]

## Composition

Non-reordering transformations compose with speculate iff the refinements they
define are composed with all Δ's.

Proof: TODO

### Example

The following is an example for the chain of optimizations
`speculate; branch prune; const prop; speculate; branch prune`

Input program

    1:
        y = 1
    2:
        x = read
    3:  osr ⊥ 3 [x=x, y=y]
        branch (x=0) 4 5
    4:
        y = 2
    5:
        branch (y=x) 6 7
    6:
        print y
    7:
        stop

Speculate `x != 0` at 3

    1:
        y = 1
    2:
        x = read
    3:  osr (x=0) 3 [x=x, y=y]
        branch (x=0) 4 5
    4:
        y = 2
    5:
        branch (y=x) 6 7
    6:
        print y
    7:
        stop

Prune branch at 3

    1:
        y = 1
    2:
        x = read
    3:  osr (x=0) 3 [x=x, y=y]
        goto 5
    4:
        y = 2
    5:
        branch (y=x) 6 7
    6:
        print y
    7:
        stop

Now `y` became constant, lets propagete it. Note how Δ is refined at line 3

    1:
        y = 1
    2:
        x = read
    3:  osr (x=0) 3 [x=x, y=1]
        goto 5
    4:
        y = 2
    5:
        branch (1=x) 6 7
    6:
        print 1
    7:
        stop

Speculate `x != 1` at 3

    1:
        y = 1
    2:
        x = read
    3:  osr (x=0) || (x=1) 3 [x=x, y=1]
        goto 5
    4:
        y = 2
    5:
        branch (1=x) 6 7
    6:
        print 1
    7:
        stop

Prune branch at 5

    1:
        y = 1
    2:
        x = read
    3:  osr (x=0) || (x=1) 3 [x=x, y=1]
        goto 5
    4:
        y = 2
    5:
        goto 7
    6:
        print 1
    7:
        stop

Eliminate dead code

    2:
        x = read
    3:  osr (x=0) || (x=1) 3 [x=x, y=1]
        nop
    7:
        stop
