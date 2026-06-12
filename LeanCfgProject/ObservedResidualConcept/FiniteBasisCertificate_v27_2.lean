import LeanCfgProject.ObservedResidualConcept.ICReleaseCertificate_v27_2
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace LeanCfgProject

universe u

/-
FiniteBasisCertificate_v27_2.lean

Paper-facing certificate for finite residual-basis release regression.
-/

variable {Q : Type u} [Mul Q]

theorem finiteBasisCertificate_all_frame_residuals
    [Fintype Q] (S : Set Q) :
    ∀ a b : Q,
      ∃ K : Set (Q × Q),
        K.Finite ∧
        FrameResidual S a b = ResidualIntersection S K := by
  exact finiteBasisRegression_all_frame_residuals (Q := Q) S

theorem finiteBasisCertificate_canonical_residual_map
    [Fintype Q] (S : Set Q) :
    ∀ a b : Q,
      ∃ K : Set (Q × Q),
        K.Finite ∧
        (canonicalObservedFrameStructure (Q := Q) S).residual a b =
          ResidualIntersection S K := by
  exact finiteBasisRegression_canonical_residual_map (Q := Q) S

theorem finiteBasisCertificate_transport
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
  exact finiteBasisRegression_transport (Q := Q) h

theorem finiteBasisCertificate_v27_2_available :
    True := by
  exact icReleaseCertificate_v27_2_manifest

end LeanCfgProject
