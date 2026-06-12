import LeanCfgProject.ObservedResidualConcept.ICSubmissionSummary_v11
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace LeanCfgProject

universe u

/-
FiniteBasisReleaseRegression_v27_2.lean

Regression target for the finite residual-basis release layer after
Lean CI #180 / commit c6c1705.
-/

variable {Q : Type u} [Mul Q]

theorem finiteBasisRegression_all_frame_residuals
    [Fintype Q] (S : Set Q) :
    ∀ a b : Q,
      ∃ K : Set (Q × Q),
        K.Finite ∧
        FrameResidual S a b = ResidualIntersection S K := by
  exact finiteBasis_release_all_frame_residuals (Q := Q) S

theorem finiteBasisRegression_canonical_residual_map
    [Fintype Q] (S : Set Q) :
    ∀ a b : Q,
      ∃ K : Set (Q × Q),
        K.Finite ∧
        (canonicalObservedFrameStructure (Q := Q) S).residual a b =
          ResidualIntersection S K := by
  exact finiteBasis_release_canonical_residual_map (Q := Q) S

theorem finiteBasisRegression_transport
    [Fintype Q] {S T : Set Q}
    (h : ObservedMembershipEquivalent (Q := Q) S T) :
    (∀ a b : Q,
      ∃ K : Set (Q × Q),
        K.Finite ∧
        FrameResidual S a b = ResidualIntersection S K)
    ↔
    (∀ a b : Q,
      ∃ K : Set (Q × Q),
        K.Finite ∧
        FrameResidual T a b = ResidualIntersection T K) := by
  exact finiteBasis_release_transport (Q := Q) h

theorem finiteBasisReleaseRegression_v27_2_summary :
    True := by
  trivial

end LeanCfgProject
