import LeanCfgProject.ObservedFiniteBasisStablePackage_v27
import LeanCfgProject.ObservedMembershipEquivalence_v27

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
FiniteResidualBasisTransport_v27.lean

Transport of finite residual-basis presentations along observed membership
equivalence.
-/

variable {Q : Type u} [Mul Q]

theorem observedMembershipEquivalent_transport_finite_basis
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
  have hST : S = T := (observedMembershipEquivalent_iff_eq (Q := Q)).1 h
  subst T
  exact Iff.rfl

theorem observedMembershipEquivalent_finite_basis_package
    [Fintype Q] {S T : Set Q}
    (h : ObservedMembershipEquivalent (Q := Q) S T) :
    (∀ a b : Q,
      ∃ K : Set (Q × Q),
        K.Finite ∧
        FrameResidual S a b = ResidualIntersection S K)
    ∧
    canonicalObservedFrameStructure (Q := Q) S =
      canonicalObservedFrameStructure (Q := Q) T := by
  exact finite_basis_stable_under_membership_equality (Q := Q) h

theorem finite_basis_for_transport_target
    [Fintype Q] {S T : Set Q}
    (h : ObservedMembershipEquivalent (Q := Q) S T) :
    ∀ a b : Q,
      ∃ K : Set (Q × Q),
        K.Finite ∧
        FrameResidual T a b = ResidualIntersection T K := by
  have hpack := observedMembershipEquivalent_finite_basis_package
    (Q := Q) h
  have hST : S = T := (observedMembershipEquivalent_iff_eq (Q := Q)).1 h
  subst T
  exact hpack.1

end LeanCfgProject
