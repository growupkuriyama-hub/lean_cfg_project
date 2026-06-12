import LeanCfgProject.FiniteObservedConceptIdentification

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u v

/-
ObservedLearningCorollaries.lean

Additional corollaries from the v26.4 observed-learning layer.
-/

variable {Q : Type u} [Mul Q]

theorem identified_frameResidual_from_membership
    {S T : Set Q}
    (h : ∀ x : Q, x ∈ S ↔ x ∈ T) :
    ∀ a b : Q, FrameResidual S a b = FrameResidual T a b := by
  have hST : S = T := finiteSet_eq_of_same_membership h
  exact reconstructed_subset_reconstructs_frameResidual (Q := Q) hST

theorem identified_singleBlock_from_membership
    {S T : Set Q}
    (h : ∀ x : Q, x ∈ S ↔ x ∈ T) :
    ∀ a b : Q, SingleObservedBlock S a b ↔ SingleObservedBlock T a b := by
  have hST : S = T := finiteSet_eq_of_same_membership h
  exact reconstructed_subset_reconstructs_singleBlock (Q := Q) hST

theorem identified_finite_frame_basis_from_membership
    [Fintype Q] {S T : Set Q}
    (h : ∀ x : Q, x ∈ S ↔ x ∈ T) (U : Set Q) :
    (∃ K : Set (Q × Q),
      K.Finite ∧ ConceptClosure S U = ResidualIntersection S K)
    ∧
    canonicalObservedFrameStructure (Q := Q) S =
      canonicalObservedFrameStructure (Q := Q) T := by
  have hST : S = T := finiteSet_eq_of_same_membership h
  constructor
  · exact conceptClosure_has_finite_frame_basis (Q := Q) S U
  · subst T
    rfl

theorem faithful_representatives_identify_frameResidual
    {W : Type v} {L : Set W} {q : W → Q} {S T : Set Q}
    (R : FaithfulRepresentatives W Q L q S)
    (hT : ∀ s : Q, R.rep s ∈ L ↔ s ∈ T) :
    ∀ a b : Q, FrameResidual S a b = FrameResidual T a b := by
  have hST : S = T :=
    observedSubset_eq_of_same_representative_answers R hT
  exact reconstructed_subset_reconstructs_frameResidual (Q := Q) hST

end LeanCfgProject
