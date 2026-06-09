import LeanCfgProject.FiniteResidualBasisTransport_v27
import LeanCfgProject.ObservedFiniteBasisStablePackage_v27

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace LeanCfgProject

universe u

/-
FiniteBasisReleaseTheorems_v27.lean

Release-facing theorem package for finite frame-residual basis facts.
-/

variable {Q : Type u} [Mul Q]

theorem finiteBasis_release_all_frame_residuals
    [Fintype Q] (S : Set Q) :
    ∀ a b : Q,
      ∃ K : Set (Q × Q),
        K.Finite ∧
        FrameResidual S a b = ResidualIntersection S K := by
  exact finite_basis_for_all_frameResiduals_stable (Q := Q) S

theorem finiteBasis_release_canonical_residual_map
    [Fintype Q] (S : Set Q) :
    ∀ a b : Q,
      ∃ K : Set (Q × Q),
        K.Finite ∧
        (canonicalObservedFrameStructure (Q := Q) S).residual a b =
          ResidualIntersection S K := by
  exact finite_basis_for_canonical_residual_map_stable (Q := Q) S

theorem finiteBasis_release_transport
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
  exact observedMembershipEquivalent_transport_finite_basis (Q := Q) h

theorem finiteBasis_release_summary :
    True := by
  trivial

end LeanCfgProject
