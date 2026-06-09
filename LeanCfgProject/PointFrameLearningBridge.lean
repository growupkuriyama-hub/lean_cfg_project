import LeanCfgProject.ObservedSubsetStability
import LeanCfgProject.FaithfulRepresentativeCorollaries

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u v

/-
PointFrameLearningBridge.lean

Bridge between finite observed-learning transcripts and the canonical
point-frame layer.
-/

variable {Q : Type u} [Mul Q]

theorem transcript_identifies_point_frame_incidence
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T)
    (gamma a b : Q) :
    (CanonicalPoint S gamma ⊆ CanonicalFrame S a b)
      ↔
    (CanonicalPoint T gamma ⊆ CanonicalFrame T a b) := by
  have hp := transcript_identifies_canonicalPoint (Q := Q) Tr gamma
  have hf := transcript_identifies_canonicalFrame (Q := Q) Tr a b
  constructor
  · intro h
    rw [← hp, ← hf]
    exact h
  · intro h
    rw [hp, hf]
    exact h

theorem transcript_identifies_point_collapse
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T)
    (x y : Q) :
    (CanonicalPoint S x = CanonicalPoint S y)
      ↔
    (CanonicalPoint T x = CanonicalPoint T y) := by
  constructor
  · intro h
    rw [← transcript_identifies_canonicalPoint (Q := Q) Tr x]
    rw [← transcript_identifies_canonicalPoint (Q := Q) Tr y]
    exact h
  · intro h
    rw [transcript_identifies_canonicalPoint (Q := Q) Tr x]
    rw [transcript_identifies_canonicalPoint (Q := Q) Tr y]
    exact h

theorem faithful_representatives_identify_point_frame_incidence
    {W : Type v} {L : Set W} {q : W → Q} {S T : Set Q}
    (R : FaithfulRepresentatives W Q L q S)
    (hT : ∀ s : Q, R.rep s ∈ L ↔ s ∈ T)
    (gamma a b : Q) :
    (CanonicalPoint S gamma ⊆ CanonicalFrame S a b)
      ↔
    (CanonicalPoint T gamma ⊆ CanonicalFrame T a b) := by
  have Tr : ObservedMembershipTranscript (Q := Q) S T :=
    faithful_representatives_give_transcript (Q := Q) R hT
  exact transcript_identifies_point_frame_incidence (Q := Q) Tr gamma a b

theorem faithful_representatives_identify_point_collapse
    {W : Type v} {L : Set W} {q : W → Q} {S T : Set Q}
    (R : FaithfulRepresentatives W Q L q S)
    (hT : ∀ s : Q, R.rep s ∈ L ↔ s ∈ T)
    (x y : Q) :
    (CanonicalPoint S x = CanonicalPoint S y)
      ↔
    (CanonicalPoint T x = CanonicalPoint T y) := by
  have Tr : ObservedMembershipTranscript (Q := Q) S T :=
    faithful_representatives_give_transcript (Q := Q) R hT
  exact transcript_identifies_point_collapse (Q := Q) Tr x y

end LeanCfgProject
