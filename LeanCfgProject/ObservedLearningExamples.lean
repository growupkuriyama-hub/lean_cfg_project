import LeanCfgProject.FaithfulRepresentatives
import LeanCfgProject.FiniteObservedFrameBasis

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
ObservedLearningExamples.lean

Small abstract transfer lemmas for the observed-learning layer. Concrete
monoids can instantiate these declarations in later files.
-/

variable {Q : Type u} [Mul Q]

/--
If the observed subset has been reconstructed, the frame residual map is
reconstructed as well.
-/
theorem reconstructed_subset_reconstructs_frameResidual
    {S T : Set Q}
    (hST : S = T) :
    ∀ a b : Q, FrameResidual S a b = FrameResidual T a b := by
  intro a b
  exact equal_observed_subset_same_frameResidual (Q := Q) hST a b

/--
If the observed subset has been reconstructed, the single-block tests are
reconstructed as well.
-/
theorem reconstructed_subset_reconstructs_singleBlock
    {S T : Set Q}
    (hST : S = T) :
    ∀ a b : Q, SingleObservedBlock S a b ↔ SingleObservedBlock T a b := by
  intro a b
  exact equal_observed_subset_same_singleBlock (Q := Q) hST a b

/--
Reconstruction of the observed subset transfers to reconstruction of the
canonical frame-concept structure.
-/
theorem reconstructed_subset_reconstructs_observedFrameStructure
    {S T : Set Q}
    (hST : S = T) :
    canonicalObservedFrameStructure (Q := Q) S =
      canonicalObservedFrameStructure (Q := Q) T := by
  subst T
  rfl

/--
Finite observed frame-basis reconstruction package.
-/
theorem reconstructed_finite_observed_learning_package
    [Fintype Q] {S T : Set Q}
    (hST : S = T) (U : Set Q) :
    canonicalObservedFrameStructure (Q := Q) S =
      canonicalObservedFrameStructure (Q := Q) T
    ∧
    (∃ K : Set (Q × Q),
      K.Finite ∧ ConceptClosure S U = ResidualIntersection S K) := by
  constructor
  · exact reconstructed_subset_reconstructs_observedFrameStructure (Q := Q) hST
  · exact conceptClosure_has_finite_frame_basis (Q := Q) S U

end LeanCfgProject
