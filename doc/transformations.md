# Inserting Assumptions

This assumes the subset without functions and ref cells, two segments per program,
and only one osr allowed right after a label.

    P ::= <I₁, (⊥|I₂)>         - Program: tuple with one or two lists of labeled instructions
    I ::= (l ↦ <⊥|osr, i>)*    - Instructions: labels pointing to potentially guarded instruction

    S(I, l) = { x | x in scope in I at label l }

Execution of P starts at I₂ if I₂ not ⊥ else I₁

## Base case

given

    P  = <I₁, ⊥>           - program with one version
    I₁ = (l ↦ <⊥, i>)*    - list of unguarded instructions

let A-assumption `e` at `l`

    A(e,l) = osr(!e, I₁, l, { x = x | ∀ x ∈ S(I₁,l) })

*Thm*

    ∀ e,l  where x∈e ⇒ x∈S(M, l)

      let insert(I, e, l) =
        when <⊥, i> = I(l)
          I[l ↦ <A(e,l), i>

      P
      ≈
      P' := <I₁, insert(I₁, e, l)>

### Example

     I₁                             I₂

      1:                             1:
          const x = read                 const x = read
      2:                             2:  osr (!(x=0), I₁, 2, [x = x])
          y = x                          y = x
      3:                             3:
          branch (x=0) 4 5               branch (x=0) 4 5
      4:                             4:
          print y                        print y
      5:                             5:
          stop                           stop

### Proof

The states of `P` and `P'` are in a bisimulation relation.

* Trivially for all labels `l' ≠ l` since `I₂(l') = I₁(l')`.
* For `l' = l` the osr instruction is a noop since `S(I₂,l) = S(I₁,l)` and
  the osr-env is the identity function.

## Inductive case

given

    P = <I₁, I₂>               - program with optimized version
    I₁ = (l ↦ <⊥, i>)*         - unoptimized version
    I₂ = (l ↦ <(⊥|osr), i>)*   - optimized version

let A-assumption `e` at `l`

    A(e,l) = osr(!e, I₁, l, { x = x | ∀ x ∈ S(I₁,l) })

*Thm*

    ∀ e,l
      where x∈e ⇒ x∈S(M, l)
      and <I₁, ⊥> ≈ <I₁, I₂>

      and ∀l' : I₁(l') ~ I₂(l')
      TODO: What is the weakest condition here???
            maybe ∀l' :
                I₂(l') = <osr, i>
              ⇒ I₁(l') ~ I₂(l')


      let insert(I, e, l) =
        when <⊥, i> = I(l)
          I[l ↦ <A(e,l), i>
        when <A(e', l), i> = I(l)
          I[l ↦ <A(e && e',l), i>

      P
      ≈
      P' := <I₁, insert(I₂, e, l)>
