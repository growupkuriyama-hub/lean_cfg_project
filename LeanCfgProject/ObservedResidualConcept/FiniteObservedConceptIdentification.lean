import LeanCfgProject.ObservedLearningExamples

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u v

/-
FiniteObservedConceptIdentification.lean

Top-level identification wrapper for the observed-learning layer.

The target is the observed frame-concept data determined by S, not the original
language itself.
-/

variable {Q : Type u} [Mul Q]

/--
Same membership answers for S and T identify the canonical observed frame
structure.
-/
theorem observedFrameStructure_identified_from_membership
    {S T : Set Q}
    (h : ∀ x : Q, x ∈ S ↔ x ∈ T) :
    canonicalObservedFrameStructure (Q := Q) S =
      canonicalObservedFrameStructure (Q := Q) T := by
  have hST : S = T := finiteSet_eq_of_same_membership h
  subst T
  rfl

/--
Faithful representatives identify the observed frame structure determined by S.
-/
theorem observedFrameStructure_identified_from_faithful_representatives
    {W : Type v}
    {L : Set W} {q : W → Q} {S T : Set Q}
    (R : FaithfulRepresentatives W Q L q S)
    (hT : ∀ s : Q, R.rep s ∈ L ↔ s ∈ T) :
    canonicalObservedFrameStructure (Q := Q) S =
      canonicalObservedFrameStructure (Q := Q) T := by
  have hST : S = T :=
    observedSubset_eq_of_same_representative_answers R hT
  subst T
  rfl

/--
For finite Q, identification of S also gives finite-frame-basis descriptions of
all concept closures in the identified object.
-/
theorem finiteObservedConceptIdentification_summary
    [Fintype Q] {S T : Set Q}
    (h : ∀ x : Q, x ∈ S ↔ x ∈ T) (U : Set Q) :
    canonicalObservedFrameStructure (Q := Q) S =
      canonicalObservedFrameStructure (Q := Q) T
    ∧
    (∃ K : Set (Q × Q),
      K.Finite ∧ ConceptClosure S U = ResidualIntersection S K) := by
  have hST : S = T := finiteSet_eq_of_same_membership h
  exact reconstructed_finite_observed_learning_package
    (Q := Q) hST U

end LeanCfgProject
