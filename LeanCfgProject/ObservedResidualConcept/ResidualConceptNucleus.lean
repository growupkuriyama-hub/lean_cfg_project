import LeanCfgProject.ObservedResidualConcept.ResidualConcept
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u

/-
ResidualConceptNucleus.lean

Planned theorem item 1:
  the residual concept closure is multiplicative/nuclear:
    cl_S(A) · cl_S(B) ⊆ cl_S(A · B).

This file is intentionally not a release/summary/package/certificate module.
It proves new mathematical content from the existing definitions in
ResidualConcept.lean:
  SetMul, CommonContexts, ElementsOfContexts, ConceptClosure,
  ConceptProduct, IsConceptExtent, subset_conceptClosure,
  conceptClosure_mono, conceptClosure_idempotent.
-/

theorem conceptClosure_setMul_subset
    {Q : Type u} [Semigroup Q]
    (S : Set Q) (A B : Set Q) :
    SetMul (ConceptClosure S A) (ConceptClosure S B)
      ⊆
    ConceptClosure S (SetMul A B) := by
  intro z hz
  rcases hz with ⟨x, hx, y, hy, hz_eq⟩
  rw [hz_eq]
  intro ab hab
  -- It remains to show that the arbitrary frame `ab` accepting `A · B`
  -- also accepts `x * y`.
  -- First, use `x ∈ cl(A)` to prove that every `b ∈ B` is accepted
  -- by the transported frame `(ab.1 * x, ab.2)`.
  have hctxB : (ab.1 * x, ab.2) ∈ CommonContexts S B := by
    intro b hb
    -- For this fixed `b`, the frame `(ab.1, b * ab.2)` accepts all of `A`.
    have hctxA : (ab.1, b * ab.2) ∈ CommonContexts S A := by
      intro a ha
      have hAB : ab.1 * (a * b) * ab.2 ∈ S := by
        exact hab (a * b) ⟨a, ha, b, hb, rfl⟩
      simpa [mul_assoc] using hAB
    have hx_accepts : ab.1 * x * (b * ab.2) ∈ S := by
      exact hx (ab.1, b * ab.2) hctxA
    simpa [mul_assoc] using hx_accepts
  -- Now use `y ∈ cl(B)` with the transported frame.
  have hy_accepts : (ab.1 * x) * y * ab.2 ∈ S := by
    exact hy (ab.1 * x, ab.2) hctxB
  simpa [mul_assoc] using hy_accepts

theorem setMul_subset_closure_setMul_closure
    {Q : Type u} [Mul Q]
    (S : Set Q) (A B : Set Q) :
    SetMul A B
      ⊆
    SetMul (ConceptClosure S A) (ConceptClosure S B) := by
  intro z hz
  rcases hz with ⟨a, ha, b, hb, hz_eq⟩
  exact ⟨a, subset_conceptClosure S A ha,
    b, subset_conceptClosure S B hb, hz_eq⟩

theorem conceptProduct_closure_closure_eq
    {Q : Type u} [Semigroup Q]
    (S : Set Q) (A B : Set Q) :
    ConceptProduct S (ConceptClosure S A) (ConceptClosure S B)
      =
    ConceptProduct S A B := by
  unfold ConceptProduct
  apply Set.Subset.antisymm
  · have hmono :
        ConceptClosure S
          (SetMul (ConceptClosure S A) (ConceptClosure S B))
          ⊆
        ConceptClosure S (ConceptClosure S (SetMul A B)) :=
      conceptClosure_mono S (conceptClosure_setMul_subset S A B)
    rw [conceptClosure_idempotent S (SetMul A B)] at hmono
    exact hmono
  · exact conceptClosure_mono S
      (setMul_subset_closure_setMul_closure S A B)

theorem setMul_singleton_one_left_subset
    {Q : Type u} [Monoid Q]
    (A : Set Q) :
    SetMul ({1} : Set Q) A ⊆ A := by
  intro z hz
  rcases hz with ⟨a, ha, b, hb, hz_eq⟩
  have ha_one : a = 1 := by
    simpa using ha
  rw [hz_eq, ha_one]
  simpa using hb

theorem setMul_singleton_one_right_subset
    {Q : Type u} [Monoid Q]
    (A : Set Q) :
    SetMul A ({1} : Set Q) ⊆ A := by
  intro z hz
  rcases hz with ⟨a, ha, b, hb, hz_eq⟩
  have hb_one : b = 1 := by
    simpa using hb
  rw [hz_eq, hb_one]
  simpa using ha

theorem subset_setMul_singleton_one_left
    {Q : Type u} [Monoid Q]
    (A : Set Q) :
    A ⊆ SetMul ({1} : Set Q) A := by
  intro a ha
  exact ⟨1, by simp, a, ha, by simp⟩

theorem subset_setMul_singleton_one_right
    {Q : Type u} [Monoid Q]
    (A : Set Q) :
    A ⊆ SetMul A ({1} : Set Q) := by
  intro a ha
  exact ⟨a, ha, 1, by simp, by simp⟩

theorem conceptProduct_one_left_of_isConceptExtent
    {Q : Type u} [Monoid Q]
    (S : Set Q) (U : Set Q)
    (hU : IsConceptExtent S U) :
    ConceptProduct S ({1} : Set Q) U = U := by
  unfold ConceptProduct
  unfold IsConceptExtent at hU
  apply Set.Subset.antisymm
  · have hmono :
        ConceptClosure S (SetMul ({1} : Set Q) U)
          ⊆
        ConceptClosure S U :=
      conceptClosure_mono S (setMul_singleton_one_left_subset U)
    rw [hU] at hmono
    exact hmono
  · intro x hx
    exact subset_conceptClosure S (SetMul ({1} : Set Q) U)
      (subset_setMul_singleton_one_left U hx)

theorem conceptProduct_one_right_of_isConceptExtent
    {Q : Type u} [Monoid Q]
    (S : Set Q) (U : Set Q)
    (hU : IsConceptExtent S U) :
    ConceptProduct S U ({1} : Set Q) = U := by
  unfold ConceptProduct
  unfold IsConceptExtent at hU
  apply Set.Subset.antisymm
  · have hmono :
        ConceptClosure S (SetMul U ({1} : Set Q))
          ⊆
        ConceptClosure S U :=
      conceptClosure_mono S (setMul_singleton_one_right_subset U)
    rw [hU] at hmono
    exact hmono
  · intro x hx
    exact subset_conceptClosure S (SetMul U ({1} : Set Q))
      (subset_setMul_singleton_one_right U hx)

theorem conceptProduct_unital_on_concept_extents
    {Q : Type u} [Monoid Q]
    (S : Set Q) (U : Set Q)
    (hU : IsConceptExtent S U) :
    ConceptProduct S ({1} : Set Q) U = U
      ∧
    ConceptProduct S U ({1} : Set Q) = U := by
  exact ⟨conceptProduct_one_left_of_isConceptExtent S U hU,
    conceptProduct_one_right_of_isConceptExtent S U hU⟩

end LeanCfgProject
