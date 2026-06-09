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

theorem transcript_identifies_point_frame_incidence_observed_structure
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T)
    (gamma a b : Q) :
    (CanonicalPoint S gamma ⊆
        (canonicalObservedFrameStructure (Q := Q) S).residual a b)
      ↔
    (CanonicalPoint T gamma ⊆
        (canonicalObservedFrameStructure (Q := Q) T).residual a b) := by
  have hp := transcript_identifies_canonicalPoint (Q := Q) Tr gamma
  have hr := transcript_identifies_observed_structure_residual
    (Q := Q) Tr a b
  constructor
  · intro h
    rw [← hp, ← hr]
    exact h
  · intro h
    rw [hp, hr]
    exact h

theorem transcript_identifies_point_collapse
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T)
    (x y : Q) :
    (CanonicalPoint S x = CanonicalPoint S y)
      ↔
    (CanonicalPoint T x = CanonicalPoint T y) := by
  have hx := transcript_identifies_canonicalPoint (Q := Q) Tr x
  have hy := transcript_identifies_canonicalPoint (Q := Q) Tr y
  constructor
  · intro h
    rw [← hx, ← hy]
    exact h
  · intro h
    rw [hx, hy]
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
