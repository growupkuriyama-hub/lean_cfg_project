import LeanCfgProject.ObservedResidualConcept.ICReleaseCertificate_v27_2
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u v

/-
PointFrameCertificate_v27_2.lean

Paper-facing certificate for the canonical point-frame release regression.
-/

variable {Q : Type u} [Mul Q]

theorem pointFrameCertificate_core
    (S : Set Q) :
    (∀ gamma a b : Q,
      CanonicalPoint S gamma ⊆
          (canonicalObservedFrameStructure (Q := Q) S).residual a b
        ↔ a * gamma * b ∈ S)
    ∧
    (∀ x y : Q,
      CanonicalPoint S x = CanonicalPoint S y
        ↔ (canonicalObservedFrameStructure (Q := Q) S).rel x y) := by
  exact pointFrameRegression_core (Q := Q) S

theorem pointFrameCertificate_transcript
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
  exact pointFrameRegression_transcript_transport (Q := Q) Tr

theorem pointFrameCertificate_faithful_representatives
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
  exact pointFrameRegression_faithful_representatives_transport
    (Q := Q) R hT

theorem pointFrameCertificate_v27_2_available :
    True := by
  exact icReleaseCertificate_v27_2_manifest

end LeanCfgProject
