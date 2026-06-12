import LeanCfgProject.ObservedResidualConcept.FaithfulRepresentativeCorollaries
import LeanCfgProject.ObservedResidualConcept.FiniteObservedFrameBasis
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
FiniteObservedBasisCorollaries.lean

Finite-basis corollaries for the observed concept object.
-/

variable {Q : Type u} [Mul Q]

theorem finite_observed_basis_for_frame_residual
    [Fintype Q] (S : Set Q) (a b : Q) :
    ∃ K : Set (Q × Q),
      K.Finite ∧
      FrameResidual S a b = ResidualIntersection S K := by
  have hclosed :
      ConceptClosure S (FrameResidual S a b) = FrameResidual S a b := by
    exact canonical_frameResidual_closed (Q := Q) S a b
  exact closedConcept_has_finite_frame_basis
    (Q := Q) S (FrameResidual S a b) hclosed

theorem finite_observed_basis_for_canonical_frame
    [Fintype Q] (S : Set Q) (a b : Q) :
    ∃ K : Set (Q × Q),
      K.Finite ∧
      CanonicalFrame S a b = ResidualIntersection S K := by
  simpa [CanonicalFrame, FrameResidual] using
    finite_observed_basis_for_frame_residual (Q := Q) S a b

theorem finite_observed_basis_summary_v2
    [Fintype Q] (S : Set Q) :
    ∀ a b : Q,
      ∃ K : Set (Q × Q),
        K.Finite ∧
        FrameResidual S a b = ResidualIntersection S K := by
  intro a b
  exact finite_observed_basis_for_frame_residual (Q := Q) S a b

end LeanCfgProject
