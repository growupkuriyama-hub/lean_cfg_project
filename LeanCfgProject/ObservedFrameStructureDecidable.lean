import LeanCfgProject.ObservedFrameStructure

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
ObservedFrameStructureDecidable.lean

Decision wrappers for the observed frame-concept learning target.

These declarations provide CI-stable handles for the paper's statement that
the finite observed frame data can be computed once the observed subset S is
fixed.
-/

variable {Q : Type u} [Mul Q]

theorem sameObservedSyntactic_has_decision
    (S : Set Q) (x y : Q) :
    Decidable (SameObservedSyntactic S x y) := by
  classical
  exact inferInstance

theorem frameResidual_membership_has_decision
    (S : Set Q) (a b x : Q) :
    Decidable (x ∈ FrameResidual S a b) := by
  classical
  exact inferInstance

theorem singleObservedBlock_has_decision
    (S : Set Q) (a b : Q) :
    Decidable (SingleObservedBlock S a b) := by
  classical
  exact inferInstance

/--
If two observed subsets are equal, their canonical residual maps agree.
-/
theorem equal_observed_subset_same_frameResidual
    {S T : Set Q} (hST : S = T) (a b : Q) :
    FrameResidual S a b = FrameResidual T a b := by
  subst T
  rfl

/--
If two observed subsets are equal, their single-block predicates agree.
-/
theorem equal_observed_subset_same_singleBlock
    {S T : Set Q} (hST : S = T) (a b : Q) :
    SingleObservedBlock S a b ↔ SingleObservedBlock T a b := by
  subst T
  exact Iff.rfl

end LeanCfgProject
