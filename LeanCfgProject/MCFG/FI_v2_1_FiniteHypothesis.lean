import LeanCfgProject.MCFG.FI_v2_1_FiniteSupport

/-!
# FI v2.1 Lean experiment: finite learner hypotheses

This file is the twelfth formalization layer for the FI v2.1 MCFG paper.

The previous finite-support layer packages the finite data enumerated from a
sample: supported tuples, supported contexts, and listed unit edges.  This file
turns that finite support into a lightweight learner-hypothesis object.

The object formalized here is still not the full canonical MCFG hypothesis of
the paper.  It is the part of the hypothesis that has already been justified by
the previous layers:

* a fixed fan-out bound and observation map;
* a finite support extracted from a sample;
* a proof that every listed unit edge is sample-safe;
* the induced unit closure and transported-context approximation;
* soundness and exactness statements for a target language under the fixed
  substitutability promise and a distribution-completeness certificate.

This layer is useful as a stable interface between the finite enumeration side
of the learner and the distribution-level reconstruction certificate.
-/

namespace FIv21

universe u v

section FiniteHypotheses

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]

/-- A finite learner hypothesis supported by a finite sample.

It bundles a finite support together with the fixed observation interface and a
certificate that each listed unit edge passes the sample-safe merge test. -/
structure FiniteLearnerHypothesis (α : Type u) (M : Type v) [Monoid M] where
  f : Nat
  obs : α → M
  support : FiniteLearnerSupport α
  safeEdges : FiniteLearnerSupport.ListedUnitEdgesAreSafe support obs f

namespace FiniteLearnerHypothesis

/-- The positive sample underlying a finite learner hypothesis. -/
def sampleSet (H : FiniteLearnerHypothesis α M) : Finset (Word α) :=
  H.support.sample

/-- The unit-closure relation induced by the finite learner hypothesis. -/
def UnitReach (H : FiniteLearnerHypothesis α M) {d : Nat}
    (x y : Tuple α d) : Prop :=
  LearnerUnitReach (sampleSet H) H.obs H.f x y

/-- The transported-context approximation induced by the finite learner
hypothesis. -/
def ApproxDistribution (H : FiniteLearnerHypothesis α M) {d : Nat}
    (x : Tuple α d) : Set (NamedSentenceContext α d) :=
  LearnerApproxDistribution (sampleSet H) H.obs H.f x

/-- Context licensing induced by the finite learner hypothesis. -/
def LicensedContext (H : FiniteLearnerHypothesis α M) {d : Nat}
    (x : Tuple α d) (c : NamedSentenceContext α d) : Prop :=
  LearnerLicensedContext (sampleSet H) H.obs H.f x c

/-- Forget the finite support and keep only the unit-hypothesis skeleton. -/
def toUnitHypothesis (H : FiniteLearnerHypothesis α M) :
    LearnerUnitHypothesis α M :=
  { f := H.f, obs := H.obs, sample := sampleSet H }

/-- The unit reachability relation agrees with the one in the older lightweight
unit-hypothesis skeleton. -/
theorem unitReach_eq_toUnitHypothesisReach
    (H : FiniteLearnerHypothesis α M) {d : Nat} (x y : Tuple α d) :
    H.UnitReach x y ↔ (H.toUnitHypothesis).Reach x y := by
  rfl

/-- A listed unit edge gives one-step reachability in the finite hypothesis. -/
theorem listedEdge_reach
    (H : FiniteLearnerHypothesis α M)
    {d : Nat} {x y : Tuple α d}
    (hxy : H.support.SupportsUnitEdge x y) :
    H.UnitReach x y := by
  exact FiniteLearnerSupport.listedUnitEdge_reach
    (S := H.support) (obs := H.obs) (f := H.f) H.safeEdges hxy

/-- A listed unit edge is sound for every positive fixed-substitutable target. -/
theorem listedEdge_sound_for_language
    (H : FiniteLearnerHypothesis α M)
    {L : Set (Word α)}
    (hK : PositiveForLanguage (sampleSet H) L)
    (hL : FixedNamedTupleSubstitutable H.f H.obs L)
    {d : Nat} {x y : Tuple α d}
    (hxy : H.support.SupportsUnitEdge x y) :
    NamedDistribution L x = NamedDistribution L y := by
  exact FiniteLearnerSupport.listedUnitEdge_sound_for_language
    (S := H.support) (obs := H.obs) (f := H.f)
    (L := L) hK hL H.safeEdges hxy

/-- Soundness of arbitrary unit reachability in the finite hypothesis. -/
theorem unitReach_sound_for_language
    (H : FiniteLearnerHypothesis α M)
    {L : Set (Word α)}
    (hK : PositiveForLanguage (sampleSet H) L)
    (hL : FixedNamedTupleSubstitutable H.f H.obs L)
    {d : Nat} {x y : Tuple α d}
    (hxy : H.UnitReach x y) :
    NamedDistribution L x = NamedDistribution L y := by
  exact LearnerUnitReach.sound_for_language hK hL hxy

/-- A sample context transported along a listed edge is sound in the target
language. -/
theorem sampleContext_transport_sound_for_listedEdge
    (H : FiniteLearnerHypothesis α M)
    {L : Set (Word α)}
    (hK : PositiveForLanguage (sampleSet H) L)
    (hL : FixedNamedTupleSubstitutable H.f H.obs L)
    {d : Nat} {x y : Tuple α d}
    (hxy : H.support.SupportsUnitEdge x y)
    {c : NamedSentenceContext α d}
    (hc : c ∈ SampleNamedDistribution (sampleSet H) x) :
    c ∈ NamedDistribution L y := by
  exact FiniteLearnerSupport.sample_context_transport_sound_for_listed_edge
    (S := H.support) (obs := H.obs) (f := H.f)
    (L := L) hK hL H.safeEdges hxy hc

/-- The finite hypothesis's approximate distribution is always sound for a
positive fixed-substitutable target. -/
theorem approxDistribution_sound_for_language
    (H : FiniteLearnerHypothesis α M)
    {L : Set (Word α)}
    (hK : PositiveForLanguage (sampleSet H) L)
    (hL : FixedNamedTupleSubstitutable H.f H.obs L)
    {d : Nat} (x : Tuple α d) :
    H.ApproxDistribution x ⊆ NamedDistribution L x := by
  intro c hc
  exact learnerApproxDistribution_sound_for_language
    (K := sampleSet H) (obs := H.obs) (f := H.f)
    (L := L) hK hL x hc

/-- A finite hypothesis is complete for a target when every true target context
is licensed by the hypothesis's transported-context approximation. -/
def CompleteForLanguage
    (H : FiniteLearnerHypothesis α M) (L : Set (Word α)) : Prop :=
  DistributionComplete (sampleSet H) H.obs H.f L

/-- If the finite hypothesis is complete for the target, then its approximate
distribution is exactly the target distribution. -/
theorem approxDistribution_exact_of_complete
    (H : FiniteLearnerHypothesis α M)
    {L : Set (Word α)}
    (hK : PositiveForLanguage (sampleSet H) L)
    (hL : FixedNamedTupleSubstitutable H.f H.obs L)
    (hcomplete : H.CompleteForLanguage L)
    {d : Nat} (x : Tuple α d) :
    H.ApproxDistribution x = NamedDistribution L x := by
  exact learnerApproxDistribution_exact_of_complete
    (K := sampleSet H) (obs := H.obs) (f := H.f)
    (L := L) hK hL hcomplete x

/-- A bundled exactness certificate for a finite learner hypothesis and target
language. -/
structure ExactForLanguage
    (H : FiniteLearnerHypothesis α M) (L : Set (Word α)) : Prop where
  positive : PositiveForLanguage (sampleSet H) L
  substitutable : FixedNamedTupleSubstitutable H.f H.obs L
  complete : H.CompleteForLanguage L

namespace ExactForLanguage

/-- Exactness certificate as a reconstruction certificate in the previous
semantic interface. -/
def toDistributionCertificate
    {H : FiniteLearnerHypothesis α M} {L : Set (Word α)}
    (C : ExactForLanguage H L) :
    DistributionReconstructionCertificate (sampleSet H) H.obs H.f L :=
  { positive := C.positive
    substitutable := C.substitutable
    complete := C.complete }

/-- Exact equality of the finite hypothesis approximation and the target
distribution. -/
theorem approxDistribution_exact
    {H : FiniteLearnerHypothesis α M} {L : Set (Word α)}
    (C : ExactForLanguage H L)
    {d : Nat} (x : Tuple α d) :
    H.ApproxDistribution x = NamedDistribution L x := by
  exact H.approxDistribution_exact_of_complete
    C.positive C.substitutable C.complete x

/-- Membership form of exactness. -/
theorem licensed_iff_target_context
    {H : FiniteLearnerHypothesis α M} {L : Set (Word α)}
    (C : ExactForLanguage H L)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d) :
    c ∈ H.ApproxDistribution x ↔ c ∈ NamedDistribution L x := by
  rw [approxDistribution_exact C x]

end ExactForLanguage

end FiniteLearnerHypothesis

end FiniteHypotheses

end FIv21
