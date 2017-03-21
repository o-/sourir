# Inserting Quasi Invariants

given

    P = active ↦ M       - Program with one segment
    M = (l ↦ (i))*       - Segment with labels pointing to singleton list

    S(M, l) = { x | x in scope in segment M at label l }

let Q-quasi invariant `e` at `l`

    Q(e, v, l) = osr !e v l { x = x | ∀ x ∈ S(M, l) }

*Thm*

    ∀ e,l  where x∈e ⇒ x∈S(M, l)

      P
      ≈
      P' = (active ↦ M[l ↦ (Q(e, old, l), M(l)], old ↦ M)

## Example

    old:                           active:

      1:                             1:
          read x                         read x
      2:                             2:  osr !(x=0) old 2 [x = x]
          y = x                          y = x
      3:                             3:
          branch (x=0) 4 5               branch (x=0) 4 5
      4:                             4:
          print y                        print y
      5:                             5:
          stop                           stop

## Proof

The states of `P` and `P'` are in a bisimulation relation.

* Trivially for all versions `v`, `v'` and label `l' <> l` since `P(v,l') = P(v',l)`.
* For `l' = l` the osr instruction is a noop since `S(v,l) = S(v',l)` and
  the osr-env is the identity function.

TODO:

* How to compose (ie. Introduce the next Q)
