import LeanCfgProject.CanonicalFrameModelCorollaries
import LeanCfgProject.ObservedLearningQueryModel

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
ObservedSubsetStability.lean

Stability of the canonical observed structures under equality of observed
subsets.
-/

variable {Q : Type u} [Mul Q]

theorem same_observed_subset_same_sameObservedSyntactic
    {S T : Set Q} (hST : S = T) (x y : Q) :
    SameObservedSyntactic S x y ↔ SameObservedSyntactic T x y := by
  subst T
  exact Iff.rfl

theorem same_observed_subset_same_canonicalPoint
    {S T : Set Q} (hST : S = T) (gamma : Q) :
    CanonicalPoint S gamma = CanonicalPoint T gamma := by
  subst T
  rfl

theorem same_observed_subset_same_canonicalFrame
    {S T : Set Q} (hST : S = T) (a b : Q) :
    CanonicalFrame S a b = CanonicalFrame T a b := by
  subst T
  rfl

theorem same_observed_subset_same_canonicalFrameModelCore
    {S T : Set Q} (hST : S = T) :
    canonicalFrameModelCore Q S = canonicalFrameModelCore Q T := by
  subst T
  rfl

theorem transcript_identifies_sameObservedSyntactic
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T) (x y : Q) :
    SameObservedSyntactic S x y ↔ SameObservedSyntactic T x y := by
  have hST : S = T := transcript_identifies_observed_subset (Q := Q) Tr
  exact same_observed_subset_same_sameObservedSyntactic (Q := Q) hST x y

theorem transcript_identifies_canonicalPoint
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T) (gamma : Q) :
    CanonicalPoint S gamma = CanonicalPoint T gamma := by
  have hST : S = T := transcript_identifies_observed_subset (Q := Q) Tr
  exact same_observed_subset_same_canonicalPoint (Q := Q) hST gamma

theorem transcript_identifies_canonicalFrame
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T) (a b : Q) :
    CanonicalFrame S a b = CanonicalFrame T a b := by
  have hST : S = T := transcript_identifies_observed_subset (Q := Q) Tr
  exact same_observed_subset_same_canonicalFrame (Q := Q) hST a b

theorem transcript_identifies_canonicalFrameModelCore
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T) :
    canonicalFrameModelCore Q S = canonicalFrameModelCore Q T := by
  have hST : S = T := transcript_identifies_observed_subset (Q := Q) Tr
  exact same_observed_subset_same_canonicalFrameModelCore (Q := Q) hST

end LeanCfgProject
