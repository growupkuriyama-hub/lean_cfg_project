import LeanCfgProject.JALC.StateSemantics

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject.JALC

open TwoSidedTypedCFG

universe u v

def TwoSidedResidual
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (alpha beta : Q) : Set Q :=
  { gamma | alpha * gamma * beta ∈ S }

def CommonContexts
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (U : Set Q) : Set (Q × Q) :=
  { ab | ∀ gamma : Q, gamma ∈ U → ab.1 * gamma * ab.2 ∈ S }

def ElementsOfContexts
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (K : Set (Q × Q)) : Set Q :=
  { gamma | ∀ ab : Q × Q, ab ∈ K → ab.1 * gamma * ab.2 ∈ S }

def ConceptClosure
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (U : Set Q) : Set Q :=
  ElementsOfContexts S (CommonContexts S U)

theorem residual_galois_connection
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (U : Set Q)
    (K : Set (Q × Q)) :
    K ⊆ CommonContexts S U ↔ U ⊆ ElementsOfContexts S K := by
  constructor
  · intro hK gamma hgamma ab hab
    exact hK hab gamma hgamma
  · intro hU ab hab gamma hgamma
    exact hU hgamma ab hab

theorem subset_conceptClosure
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (U : Set Q) :
    U ⊆ ConceptClosure S U := by
  intro gamma hgamma ab hab
  exact hab gamma hgamma

theorem state_semantics_subset_residual
    {Sigma : Type u} {Q : Type v} [Monoid Q]
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (L Y : Set (Word Sigma))
    (ell r : Word Sigma)
    (hctx : ∀ w : Word Sigma, w ∈ Y → ell ++ w ++ r ∈ L) :
    ImageOfLanguage q Y ⊆
      TwoSidedResidual (ImageOfLanguage q L) (q ell) (q r) := by
  intro gamma hgamma
  rcases hgamma with ⟨w, hwY, hgamma_eq⟩
  refine ⟨ell ++ w ++ r, hctx w hwY, ?_⟩
  rw [hgamma_eq]
  rw [← q_mul ell w]
  rw [← q_mul (ell ++ w) r]

end LeanCfgProject.JALC