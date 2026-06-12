import LeanCfgProject.ObservedSyntacticResidualCorollaries

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
FiniteObservedFrameBasis.lean

Finite observed frame-basis layer.

For finite Q, the two-sided frame space Q x Q is finite. Thus every closed
extent is represented by a finite intersection of frame residuals.
-/

variable {Q : Type u} [Mul Q]

/--
Every concept closure is represented as an intersection of frame residuals over
its common-context set.
-/
theorem conceptClosure_has_common_frame_basis
    (S U : Set Q) :
    ∃ K : Set (Q × Q),
      ConceptClosure S U = ResidualIntersection S K := by
  exact ⟨CommonContexts S U,
    conceptClosure_as_common_residual_intersection S U⟩

/--
For finite Q, every concept closure has a finite observed frame basis.
-/
theorem conceptClosure_has_finite_frame_basis
    [Fintype Q] (S U : Set Q) :
    ∃ K : Set (Q × Q),
      K.Finite ∧ ConceptClosure S U = ResidualIntersection S K := by
  refine ⟨CommonContexts S U, ?_, ?_⟩
  · exact Set.toFinite _
  · exact conceptClosure_as_common_residual_intersection S U

/--
Every closed concept extent has a finite residual-intersection presentation
when Q is finite.
-/
theorem closedConcept_has_finite_frame_basis
    [Fintype Q] (S U : Set Q)
    (hclosed : ConceptClosure S U = U) :
    ∃ K : Set (Q × Q),
      K.Finite ∧ U = ResidualIntersection S K := by
  obtain ⟨K, hKfin, hK⟩ :=
    conceptClosure_has_finite_frame_basis (Q := Q) S U
  exact ⟨K, hKfin, hclosed ▸ hK⟩

/--
Finite observed frame-basis summary.
-/
theorem finiteObservedFrameBasis_summary
    [Fintype Q] (S U : Set Q) :
    (∃ K : Set (Q × Q),
      K.Finite ∧ ConceptClosure S U = ResidualIntersection S K)
    ∧
    (ConceptClosure S U = U →
      ∃ K : Set (Q × Q),
        K.Finite ∧ U = ResidualIntersection S K) := by
  constructor
  · exact conceptClosure_has_finite_frame_basis (Q := Q) S U
  · intro hclosed
    exact closedConcept_has_finite_frame_basis (Q := Q) S U hclosed

end LeanCfgProject
