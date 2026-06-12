import LeanCfgProject.ObservedLearningCorollaries
import LeanCfgProject.UniversalFrameModelCore

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
ObservedLearningConstructibilitySummary.lean

Summary target connecting the canonical point-frame representation layer with
the observed-learning identification layer.
-/

variable {Q : Type u} [Mul Q]

theorem observedLearningConstructibility_from_membership
    {S T : Set Q}
    (h : ∀ x : Q, x ∈ S ↔ x ∈ T) :
    canonicalObservedFrameStructure (Q := Q) S =
      canonicalObservedFrameStructure (Q := Q) T
    ∧
    (∀ a b : Q, FrameResidual S a b = FrameResidual T a b)
    ∧
    (∀ a b : Q, SingleObservedBlock S a b ↔ SingleObservedBlock T a b) := by
  constructor
  · exact observedFrameStructure_identified_from_membership (Q := Q) h
  constructor
  · exact identified_frameResidual_from_membership (Q := Q) h
  · exact identified_singleBlock_from_membership (Q := Q) h

theorem observedLearningConstructibility_summary
    (S : Set Q) :
    (∀ gamma a b : Q,
      CanonicalPoint S gamma ⊆
          (canonicalObservedFrameStructure (Q := Q) S).residual a b
        ↔ a * gamma * b ∈ S)
    ∧
    (∀ x y : Q,
      CanonicalPoint S x = CanonicalPoint S y
        ↔ (canonicalObservedFrameStructure (Q := Q) S).rel x y) := by
  exact universalFrameModelCore_summary (Q := Q) S

end LeanCfgProject
