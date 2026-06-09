import LeanCfgProject.ObservedLearningQueryModel

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u v

/-
FaithfulRepresentativeCorollaries.lean

More paper-facing consequences of faithful representatives for observed
learning.
-/

variable {Q : Type u} [Mul Q]

theorem faithful_representatives_identify_observed_subset
    {W : Type v} {L : Set W} {q : W → Q} {S T : Set Q}
    (R : FaithfulRepresentatives W Q L q S)
    (hT : ∀ s : Q, R.rep s ∈ L ↔ s ∈ T) :
    S = T := by
  exact observedSubset_eq_of_same_representative_answers R hT

theorem faithful_representatives_identify_frame_structure
    {W : Type v} {L : Set W} {q : W → Q} {S T : Set Q}
    (R : FaithfulRepresentatives W Q L q S)
    (hT : ∀ s : Q, R.rep s ∈ L ↔ s ∈ T) :
    canonicalObservedFrameStructure (Q := Q) S =
      canonicalObservedFrameStructure (Q := Q) T := by
  exact observedFrameStructure_identified_from_faithful_representatives
    (Q := Q) R hT

theorem faithful_representatives_give_transcript
    {W : Type v} {L : Set W} {q : W → Q} {S T : Set Q}
    (R : FaithfulRepresentatives W Q L q S)
    (hT : ∀ s : Q, R.rep s ∈ L ↔ s ∈ T) :
    ObservedMembershipTranscript (Q := Q) S T := by
  refine ⟨?_⟩
  intro s
  exact (R.rep_membership s).symm.trans (hT s)

theorem faithful_representatives_constructibility_package
    {W : Type v} {L : Set W} {q : W → Q} {S T : Set Q}
    (R : FaithfulRepresentatives W Q L q S)
    (hT : ∀ s : Q, R.rep s ∈ L ↔ s ∈ T) :
    canonicalObservedFrameStructure (Q := Q) S =
      canonicalObservedFrameStructure (Q := Q) T
    ∧
    (∀ a b : Q, FrameResidual S a b = FrameResidual T a b)
    ∧
    (∀ a b : Q, SingleObservedBlock S a b ↔ SingleObservedBlock T a b) := by
  have Tr : ObservedMembershipTranscript (Q := Q) S T :=
    faithful_representatives_give_transcript (Q := Q) R hT
  exact transcript_constructibility_package (Q := Q) Tr

end LeanCfgProject
