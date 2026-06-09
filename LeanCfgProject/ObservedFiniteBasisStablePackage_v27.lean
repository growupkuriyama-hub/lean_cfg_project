import LeanCfgProject.FiniteObservedFrameBasis
import LeanCfgProject.ObservedFrameStructure

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
ObservedFiniteBasisStablePackage_v27.lean

Stable finite-basis corollaries for frame residuals.  This file avoids the
harder point-concept basis statements and records the residual/frame part that
is already supported by the CI #166 observed-learning core.
-/

variable {Q : Type u} [Mul Q]

theorem finite_basis_for_frameResidual_stable
    [Fintype Q] (S : Set Q) (a b : Q) :
    ∃ K : Set (Q × Q),
      K.Finite ∧
      FrameResidual S a b = ResidualIntersection S K := by
  have hclosed :
      ConceptClosure S (FrameResidual S a b) = FrameResidual S a b := by
    exact canonical_frameResidual_closed (Q := Q) S a b
  exact closedConcept_has_finite_frame_basis
    (Q := Q) S (FrameResidual S a b) hclosed

theorem finite_basis_for_all_frameResiduals_stable
    [Fintype Q] (S : Set Q) :
    ∀ a b : Q,
      ∃ K : Set (Q × Q),
        K.Finite ∧
        FrameResidual S a b = ResidualIntersection S K := by
  intro a b
  exact finite_basis_for_frameResidual_stable (Q := Q) S a b

theorem finite_basis_for_canonical_residual_map_stable
    [Fintype Q] (S : Set Q) :
    ∀ a b : Q,
      ∃ K : Set (Q × Q),
        K.Finite ∧
        (canonicalObservedFrameStructure (Q := Q) S).residual a b =
          ResidualIntersection S K := by
  intro a b
  simpa [canonicalObservedFrameStructure, FrameResidual] using
    finite_basis_for_frameResidual_stable (Q := Q) S a b

theorem finite_basis_stable_under_membership_equality
    [Fintype Q] {S T : Set Q}
    (h : ∀ x : Q, x ∈ S ↔ x ∈ T) :
    (∀ a b : Q,
      ∃ K : Set (Q × Q),
        K.Finite ∧
        FrameResidual S a b = ResidualIntersection S K)
    ∧
    canonicalObservedFrameStructure (Q := Q) S =
      canonicalObservedFrameStructure (Q := Q) T := by
  constructor
  · exact finite_basis_for_all_frameResiduals_stable (Q := Q) S
  · exact observedFrameStructure_identified_from_membership (Q := Q) h

end LeanCfgProject
