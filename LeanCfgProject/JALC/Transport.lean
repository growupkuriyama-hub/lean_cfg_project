import Mathlib

namespace LeanCfgProject
namespace JALC

universe u v

/-
Transport invariants for the JALC paper.

This file checks the orientation-sensitive part of the two-sided typed
refinement:

  A_p^{m,n} -> B_q^{m,r*n} C_r^{m*q,n}

The development works over an arbitrary monoid.  No commutativity assumption
is used.  Thus the left/right order of the transported frames is genuinely
checked by Lean.
-/


/-- A word observer into a monoid.

We use `List Sigma` as words.  The observer is required to preserve the empty
word and concatenation.
-/
structure WordObserver (Sigma : Type u) (M : Type v) [Monoid M] where
  h : List Sigma → M
  h_nil : h [] = 1
  h_append : ∀ u v : List Sigma, h (u ++ v) = h u * h v


/-- A typed derivation tree with a yield annotation.

`TypedDeriv Obs p w` means that the typed derivation has yield annotation `p`
and produces the word `w`.
-/
inductive TypedDeriv {Sigma : Type u} {M : Type v} [Monoid M]
    (Obs : WordObserver Sigma M) : M → List Sigma → Prop
  | leaf (a : Sigma) :
      TypedDeriv Obs (Obs.h [a]) [a]
  | node {p q r : M} {u v : List Sigma}
      (hp : q * r = p)
      (left : TypedDeriv Obs q u)
      (right : TypedDeriv Obs r v) :
      TypedDeriv Obs p (u ++ v)


/-- Yield-type invariant for typed derivations.

This is the Lean counterpart of the yield-type invariant used in the paper.
-/
theorem TypedDeriv.yield_type_invariant
    {Sigma : Type u} {M : Type v} [Monoid M]
    {Obs : WordObserver Sigma M}
    {p : M} {w : List Sigma}
    (d : TypedDeriv Obs p w) :
    Obs.h w = p := by
  induction d with
  | leaf a =>
      rfl
  | node hp left right ihLeft ihRight =>
      rw [Obs.h_append, ihLeft, ihRight, hp]


/-- A one-hole typed context derivation.

`TypedCtx Obs p m n u v` means that a hole with yield annotation `p`
is reached with inherited left frame `m`, inherited right frame `n`, and
actual surrounding terminal words `u` and `v`.

The constructors encode the two-sided frame-transport equation:
the left child has frame `(m, r * n)`, while the right child has frame
`(m * q, n)`.
-/
inductive TypedCtx {Sigma : Type u} {M : Type v} [Monoid M]
    (Obs : WordObserver Sigma M) :
    M → M → M → List Sigma → List Sigma → Prop
  | start (p : M) :
      TypedCtx Obs p 1 1 [] []
  | toLeft {p m n q r : M} {u v z : List Sigma}
      (hp : q * r = p)
      (hz : Obs.h z = r)
      (parent : TypedCtx Obs p m n u v) :
      TypedCtx Obs q m (r * n) u (z ++ v)
  | toRight {p m n q r : M} {u v y : List Sigma}
      (hp : q * r = p)
      (hy : Obs.h y = q)
      (parent : TypedCtx Obs p m n u v) :
      TypedCtx Obs r (m * q) n (u ++ y) v


/-- Context-type invariant for two-sided frame transport.

The proof uses only associativity and multiplication order in an arbitrary
monoid.  In particular, it does not assume commutativity.
-/
theorem TypedCtx.context_type_invariant
    {Sigma : Type u} {M : Type v} [Monoid M]
    {Obs : WordObserver Sigma M}
    {p m n : M} {u v : List Sigma}
    (d : TypedCtx Obs p m n u v) :
    Obs.h u = m ∧ Obs.h v = n := by
  induction d with
  | start p =>
      exact ⟨Obs.h_nil, Obs.h_nil⟩
  | toLeft hp hz parent ih =>
      refine ⟨ih.1, ?_⟩
      rw [Obs.h_append, hz, ih.2]
  | toRight hp hy parent ih =>
      refine ⟨?_, ih.2⟩
      rw [Obs.h_append, ih.1, hy]

end JALC
end LeanCfgProject
