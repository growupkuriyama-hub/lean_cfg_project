import LeanCfgProject.MCFG.FI_v2_1_LearnerDistribution

/-!
# FI v2.1 Lean experiment: reconstruction certificates

This file is the eighth formalization layer for the FI v2.1 MCFG paper.

The previous layer introduced the learner's approximate distribution: contexts
observed in a finite sample may be transported along the learner's sample-safe
unit closure.  It also proved soundness of that approximation with respect to a
target language satisfying the fixed-`h` tuple-substitutability promise.

This file packages the next proof-theoretic interface used in the paper's
exact-reconstruction theorem.  Instead of constructing the full learner grammar,
we isolate a *certificate* saying that the finite sample is rich enough for the
transported sample contexts to cover all true target contexts.  Under such a
certificate, the learner approximation is exactly the target distribution.

The main point is deliberately modest but useful for the paper:

* positivity + fixed-`h` substitutability give soundness;
* distribution completeness gives completeness;
* a characteristic distribution sample is a finite sufficient set that forces
  exactness for all larger positive samples.

Later files can connect this distribution-level certificate to the actual MCFG
rule reconstruction and to the presentation-relative characteristic sample.
-/

namespace FIv21

universe u v

section BasicRelations

variable {α : Type u}
variable [DecidableEq α]

/-- Finite-sample extension, written without relying on coercion-heavy notation.
`SampleExtends S K` means that the current sample `K` contains the proposed
finite characteristic sample `S`. -/
def SampleExtends (S K : Finset (Word α)) : Prop :=
  ∀ w : Word α, w ∈ S → w ∈ K

/-- Extension is reflexive. -/
theorem SampleExtends.refl (K : Finset (Word α)) : SampleExtends K K := by
  intro w hw
  exact hw

/-- Extension is transitive. -/
theorem SampleExtends.trans
    {S K K' : Finset (Word α)}
    (hSK : SampleExtends S K) (hKK' : SampleExtends K K') :
    SampleExtends S K' := by
  intro w hw
  exact hKK' w (hSK w hw)

/-- Positivity is monotone downward along finite-sample extension.  If the
larger sample is positive for the target, then every contained finite sample is
positive as well. -/
theorem positiveForLanguage_of_extends
    {S K : Finset (Word α)} {L : Set (Word α)}
    (hSK : SampleExtends S K)
    (hK : PositiveForLanguage K L) :
    PositiveForLanguage S L := by
  intro w hw
  exact hK w (hSK w hw)

end BasicRelations

section Certificates

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]

/-- The distribution-level exactness property of the learner approximation for a
fixed finite sample and target language. -/
def LearnerDistributionExact
    (K : Finset (Word α)) (obs : α → M) (f : Nat)
    (L : Set (Word α)) : Prop :=
  ∀ {d : Nat} (x : Tuple α d),
    LearnerApproxDistribution K obs f x = NamedDistribution L x

/-- A reconstruction certificate for the distribution component of the canonical
learner.

This record is intentionally semantic.  In the paper, the presentation-relative
characteristic sample is constructed so that these fields hold.  The Lean layer
keeps the certificate abstract and proves the consequences once it is available. -/
structure DistributionReconstructionCertificate
    (K : Finset (Word α)) (obs : α → M) (f : Nat)
    (L : Set (Word α)) where
  positive : PositiveForLanguage K L
  substitutable : FixedNamedTupleSubstitutable f obs L
  complete : DistributionComplete K obs f L

namespace DistributionReconstructionCertificate

/-- A reconstruction certificate gives exact equality between the learner's
transported sample-context distribution and the target distribution. -/
theorem exact_distribution
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (C : DistributionReconstructionCertificate K obs f L)
    {d : Nat} (x : Tuple α d) :
    LearnerApproxDistribution K obs f x = NamedDistribution L x := by
  exact learnerApproxDistribution_exact_of_complete
    C.positive C.substitutable C.complete x

/-- Membership form of `exact_distribution`. -/
theorem licensed_iff_target_context
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (C : DistributionReconstructionCertificate K obs f L)
    {d : Nat} (x : Tuple α d)
    (c : NamedSentenceContext α d) :
    c ∈ LearnerApproxDistribution K obs f x ↔
      c ∈ NamedDistribution L x := by
  rw [exact_distribution C x]

/-- Soundness direction extracted from a certificate. -/
theorem licensed_context_sound
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (C : DistributionReconstructionCertificate K obs f L)
    {d : Nat} {x : Tuple α d} {c : NamedSentenceContext α d}
    (hc : c ∈ LearnerApproxDistribution K obs f x) :
    c ∈ NamedDistribution L x := by
  exact (licensed_iff_target_context C x c).1 hc

/-- Completeness direction extracted from a certificate. -/
theorem target_context_licensed
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (C : DistributionReconstructionCertificate K obs f L)
    {d : Nat} {x : Tuple α d} {c : NamedSentenceContext α d}
    (hc : c ∈ NamedDistribution L x) :
    c ∈ LearnerApproxDistribution K obs f x := by
  exact (licensed_iff_target_context C x c).2 hc

/-- A certificate states exactly `LearnerDistributionExact`. -/
theorem distribution_exact
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (C : DistributionReconstructionCertificate K obs f L) :
    LearnerDistributionExact K obs f L := by
  intro d x
  exact exact_distribution C x

end DistributionReconstructionCertificate

/-- Distribution completeness, written in pointwise witness form.

This expands the subset condition in `DistributionComplete`: every true target
context for a tuple is licensed by the finite sample after unit transport. -/
def TargetContextsLicensed
    (K : Finset (Word α)) (obs : α → M) (f : Nat)
    (L : Set (Word α)) : Prop :=
  ∀ {d : Nat} (x : Tuple α d) {c : NamedSentenceContext α d},
    c ∈ NamedDistribution L x → LearnerLicensedContext K obs f x c

/-- The witness form is definitionally equivalent to distribution completeness,
up to unfolding the learner approximate distribution. -/
theorem distributionComplete_iff_targetContextsLicensed
    (K : Finset (Word α)) (obs : α → M) (f : Nat)
    (L : Set (Word α)) :
    DistributionComplete K obs f L ↔
      TargetContextsLicensed K obs f L := by
  constructor
  · intro hcomplete d x c hc
    exact hcomplete x hc
  · intro hwitness d x c hc
    exact hwitness x hc

/-- A more explicit witness form: every true context is a sample-observed
context for some tuple that reaches the target tuple by unit closure. -/
def TargetContextsTransportWitnessed
    (K : Finset (Word α)) (obs : α → M) (f : Nat)
    (L : Set (Word α)) : Prop :=
  ∀ {d : Nat} (x : Tuple α d) {c : NamedSentenceContext α d},
    c ∈ NamedDistribution L x →
      ∃ y : Tuple α d,
        LearnerUnitReach K obs f y x ∧ c ∈ SampleNamedDistribution K y

/-- The explicit transport-witness form is equivalent to target-context
licensing, because `LearnerLicensedContext` is exactly the corresponding
existential. -/
theorem targetContextsLicensed_iff_transportWitnessed
    (K : Finset (Word α)) (obs : α → M) (f : Nat)
    (L : Set (Word α)) :
    TargetContextsLicensed K obs f L ↔
      TargetContextsTransportWitnessed K obs f L := by
  constructor
  · intro h d x c hc
    exact h x hc
  · intro h d x c hc
    exact h x hc

/-- Combined equivalence between distribution completeness and the explicit
transport-witness view. -/
theorem distributionComplete_iff_transportWitnessed
    (K : Finset (Word α)) (obs : α → M) (f : Nat)
    (L : Set (Word α)) :
    DistributionComplete K obs f L ↔
      TargetContextsTransportWitnessed K obs f L := by
  exact (distributionComplete_iff_targetContextsLicensed K obs f L).trans
    (targetContextsLicensed_iff_transportWitnessed K obs f L)

end Certificates

section CharacteristicDistributionSamples

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]

/-- A finite characteristic sample for the distribution component of the
learner.

This is the distribution-level analogue of the paper's characteristic sample:
once a text prefix contains `S` and remains positive for the target language,
the learner's transported-context approximation is complete.  Soundness still
comes from positivity and fixed-`h` substitutability. -/
def DistributionCharacteristicSample
    (S : Finset (Word α)) (obs : α → M) (f : Nat)
    (L : Set (Word α)) : Prop :=
  PositiveForLanguage S L ∧
  ∀ K : Finset (Word α),
    SampleExtends S K →
    PositiveForLanguage K L →
    DistributionComplete K obs f L

namespace DistributionCharacteristicSample

/-- A distribution characteristic sample yields a reconstruction certificate for
any larger positive sample, assuming the target satisfies fixed-`h`
substitutability. -/
def certificate
    {S K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hS : DistributionCharacteristicSample S obs f L)
    (hsub : FixedNamedTupleSubstitutable f obs L)
    (hSK : SampleExtends S K)
    (hK : PositiveForLanguage K L) :
    DistributionReconstructionCertificate K obs f L where
  positive := hK
  substitutable := hsub
  complete := hS.2 K hSK hK

/-- Stabilization theorem for the distribution component: after the current
positive sample contains the characteristic sample, the learner's approximate
distribution is exactly the target distribution for every tuple. -/
theorem exact_after_extending
    {S K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hS : DistributionCharacteristicSample S obs f L)
    (hsub : FixedNamedTupleSubstitutable f obs L)
    (hSK : SampleExtends S K)
    (hK : PositiveForLanguage K L) :
    LearnerDistributionExact K obs f L := by
  intro d x
  exact DistributionReconstructionCertificate.exact_distribution
    (certificate hS hsub hSK hK) x

/-- Pointwise membership version of `exact_after_extending`. -/
theorem licensed_iff_target_after_extending
    {S K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hS : DistributionCharacteristicSample S obs f L)
    (hsub : FixedNamedTupleSubstitutable f obs L)
    (hSK : SampleExtends S K)
    (hK : PositiveForLanguage K L)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d) :
    c ∈ LearnerApproxDistribution K obs f x ↔
      c ∈ NamedDistribution L x := by
  have hexact : LearnerApproxDistribution K obs f x = NamedDistribution L x :=
    exact_after_extending hS hsub hSK hK x
  rw [hexact]

/-- The characteristic sample itself is positive for the target. -/
theorem positive
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hS : DistributionCharacteristicSample S obs f L) :
    PositiveForLanguage S L :=
  hS.1

/-- Applying the characteristic property to `K = S`. -/
theorem complete_self
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hS : DistributionCharacteristicSample S obs f L) :
    DistributionComplete S obs f L := by
  exact hS.2 S (SampleExtends.refl S) hS.1

end DistributionCharacteristicSample

end CharacteristicDistributionSamples

section GrammarTargetCertificates

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]
variable {N : Type v}

/-- Distribution-level exactness specialized to a grammar target. -/
def LearnerDistributionExactForGrammar
    (K : Finset (Word α)) (obs : α → M) (f : Nat)
    (G : WorkingMCFG N α) : Prop :=
  LearnerDistributionExact K obs f G.StringLanguage

/-- A positive grammar sample plus a distribution characteristic sample gives
exact learner distributions for the grammar target. -/
theorem exact_for_grammar_after_characteristic_sample
    {S K : Finset (Word α)} {obs : α → M} {f : Nat}
    (G : WorkingMCFG N α)
    (hS : DistributionCharacteristicSample S obs f G.StringLanguage)
    (hsub : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSK : SampleExtends S K)
    (hK : PositiveSample G K) :
    LearnerDistributionExactForGrammar K obs f G := by
  exact DistributionCharacteristicSample.exact_after_extending
    hS hsub hSK (positiveForLanguage_of_positiveSample G K hK)

end GrammarTargetCertificates

end FIv21
