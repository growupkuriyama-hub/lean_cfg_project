import LeanCfgProject.ObservedResidualConcept.PointFrameLearningBridge
import LeanCfgProject.ObservedResidualConcept.ObservedSubsetTransportPackage_v27
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u v

/-
PointFrameTransportSummary_v27.lean

Summary lemmas showing that finite observed-learning transcripts transport the
canonical point-frame incidence and point-collapse data.
-/

variable {Q : Type u} [Mul Q]

theorem transcript_point_frame_transport_summary
    {S T : Set Q}
    (Tr : ObservedMembershipTranscript (Q := Q) S T) :
    (∀ gamma a b : Q,
      (CanonicalPoint S gamma ⊆ CanonicalFrame S a b)
        ↔
      (CanonicalPoint T gamma ⊆ CanonicalFrame T a b))
    ∧
    (∀ gamma a b : Q,
      (CanonicalPoint S gamma ⊆
          (canonicalObservedFrameStructure (Q := Q) S).residual a b)
        ↔
      (CanonicalPoint T gamma ⊆
          (canonicalObservedFrameStructure (Q := Q) T).residual a b))
    ∧
    (∀ x y : Q,
      (CanonicalPoint S x = CanonicalPoint S y)
        ↔
      (CanonicalPoint T x = CanonicalPoint T y)) := by
  constructor
  · intro gamma a b
    exact transcript_identifies_point_frame_incidence (Q := Q) Tr gamma a b
  constructor
  · intro gamma a b
    exact transcript_identifies_point_frame_incidence_observed_structure
      (Q := Q) Tr gamma a b
  · intro x y
    exact transcript_identifies_point_collapse (Q := Q) Tr x y

theorem faithful_representatives_point_frame_transport_summary
    {W : Type v} {L : Set W} {q : W → Q} {S T : Set Q}
    (R : FaithfulRepresentatives W Q L q S)
    (hT : ∀ s : Q, R.rep s ∈ L ↔ s ∈ T) :
    (∀ gamma a b : Q,
      (CanonicalPoint S gamma ⊆ CanonicalFrame S a b)
        ↔
      (CanonicalPoint T gamma ⊆ CanonicalFrame T a b))
    ∧
    (∀ x y : Q,
      (CanonicalPoint S x = CanonicalPoint S y)
        ↔
      (CanonicalPoint T x = CanonicalPoint T y)) := by
  constructor
  · intro gamma a b
    exact faithful_representatives_identify_point_frame_incidence
      (Q := Q) R hT gamma a b
  · intro x y
    exact faithful_representatives_identify_point_collapse
      (Q := Q) R hT x y

end LeanCfgProject
