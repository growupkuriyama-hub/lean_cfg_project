import LeanCfgProject.MCFG.FI_v2_1_ReconstructionCertificate

/-!
# FI v2.1 Lean experiment: Gold-style stabilization

This file is the ninth formalization layer for the FI v2.1 MCFG paper.

The previous layer packaged a distribution-level reconstruction certificate:
if a finite positive sample is rich enough, then the learner's transported
named-context distribution agrees exactly with the target distribution.

This file adds the standard Gold-style limiting-learning wrapper around that
certificate.  The point is deliberately modest and close to the paper's
learning-theoretic argument:

* a text for a target language is an infinite enumeration of positive examples;
* every finite characteristic sample eventually appears in any text;
* after that stage, every prefix sample is positive and contains the
  characteristic sample;
* hence the learner's distribution-level hypothesis is exact at every later
  stage.

This file still does not construct the presentation-relative characteristic
sample from an MCFG presentation.  It proves the general finite-telltale to
identification-in-the-limit implication for the distribution component already
formalized in the previous files.
-/

namespace FIv21

universe u v w

section Texts

variable {α : Type u}
variable [DecidableEq α]

/-- A positive-data text is represented as a stream of words. -/
abbrev Text (α : Type u) := Nat → Word α

/-- A text for `L` enumerates only words of `L` and eventually enumerates every
word of `L`. -/
def TextFor (t : Text α) (L : Set (Word α)) : Prop :=
  (∀ n : Nat, t n ∈ L) ∧
  (∀ w : Word α, w ∈ L → ∃ n : Nat, t n = w)

/-- The finite sample seen in the first `n` positions of a text.  We use
`Finset.range n`, so positions are `0, ..., n-1`. -/
def PrefixSample (t : Text α) (n : Nat) : Finset (Word α) :=
  (Finset.range n).image t

/-- Every prefix sample of a text for `L` is positive for `L`. -/
theorem prefixSample_positive
    {t : Text α} {L : Set (Word α)}
    (ht : TextFor t L) (n : Nat) :
    PositiveForLanguage (PrefixSample t n) L := by
  intro w hw
  unfold PrefixSample at hw
  rcases Finset.mem_image.mp hw with ⟨i, _hi, htw⟩
  rw [← htw]
  exact ht.1 i

/-- Prefix samples are monotone with respect to the prefix length. -/
theorem prefixSample_extends_mono
    {t : Text α} {m n : Nat}
    (hmn : m ≤ n) :
    SampleExtends (PrefixSample t m) (PrefixSample t n) := by
  intro w hw
  unfold PrefixSample at hw ⊢
  rcases Finset.mem_image.mp hw with ⟨i, hi, htw⟩
  apply Finset.mem_image.mpr
  refine ⟨i, ?_, htw⟩
  exact Finset.mem_range.mpr
    (Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) hmn)

/-- A finite positive sample eventually appears in every text for the target.

This is the standard finite-telltale lemma behind Gold-style identification:
for each word in the finite set, choose a stage where it appears, then take the
maximum of those finitely many stages.  The proof is by induction on the finite
sample, avoiding any noncomputable maximum construction. -/
theorem text_eventually_contains_finite_sample
    {t : Text α} {L : Set (Word α)}
    (ht : TextFor t L) :
    ∀ S : Finset (Word α),
      PositiveForLanguage S L →
      ∃ N : Nat,
        ∀ n : Nat, N ≤ n → SampleExtends S (PrefixSample t n) := by
  intro S
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro _hS
      refine ⟨0, ?_⟩
      intro n _hn w hw
      simpa using hw
  | insert a S ha ih =>
      intro hS
      have haL : a ∈ L := hS a (Finset.mem_insert_self a S)
      rcases ht.2 a haL with ⟨ia, hia⟩
      have hSpos : PositiveForLanguage S L := by
        intro w hw
        exact hS w (Finset.mem_insert_of_mem hw)
      rcases ih hSpos with ⟨N, hN⟩
      refine ⟨Nat.max (ia + 1) N, ?_⟩
      intro n hn w hw
      have hw' := Finset.mem_insert.mp hw
      rcases hw' with hwa | hwS
      · rw [hwa]
        unfold PrefixSample
        apply Finset.mem_image.mpr
        refine ⟨ia, ?_, hia⟩
        exact Finset.mem_range.mpr
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self ia)
            (le_trans (Nat.le_max_left (ia + 1) N) hn))
      · exact hN n (le_trans (Nat.le_max_right (ia + 1) N) hn) w hwS

end Texts

section DistributionIdentification

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]

/-- Distribution-level identification in the limit for a single target language.

After some finite stage, every later prefix sample gives exact transported
named-context distributions for all tuples. -/
def DistributionIdentifiesInLimit
    (obs : α → M) (f : Nat) (L : Set (Word α)) : Prop :=
  ∀ t : Text α,
    TextFor t L →
      ∃ N : Nat,
        ∀ n : Nat, N ≤ n → LearnerDistributionExact (PrefixSample t n) obs f L

/-- A distribution characteristic sample implies identification in the limit for
that target, provided the target satisfies the fixed-`h` substitutability
promise. -/
theorem distributionCharacteristicSample_identifiesInLimit
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hS : DistributionCharacteristicSample S obs f L)
    (hsub : FixedNamedTupleSubstitutable f obs L) :
    DistributionIdentifiesInLimit obs f L := by
  intro t ht
  rcases text_eventually_contains_finite_sample ht S hS.1 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact DistributionCharacteristicSample.exact_after_extending
    hS hsub (hN n hn) (prefixSample_positive ht n)

/-- Pointwise context-membership form of limiting identification. -/
theorem eventually_licensed_iff_target_context
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hS : DistributionCharacteristicSample S obs f L)
    (hsub : FixedNamedTupleSubstitutable f obs L)
    {t : Text α} (ht : TextFor t L) :
    ∃ N : Nat,
      ∀ n : Nat, N ≤ n →
        ∀ {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d),
          c ∈ LearnerApproxDistribution (PrefixSample t n) obs f x ↔
            c ∈ NamedDistribution L x := by
  rcases text_eventually_contains_finite_sample ht S hS.1 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn d x c
  exact DistributionCharacteristicSample.licensed_iff_target_after_extending
    hS hsub (hN n hn) (prefixSample_positive ht n) x c

end DistributionIdentification

section GrammarIdentification

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]
variable {N : Type w}

/-- A text for a grammar target. -/
def TextForGrammar (t : Text α) (G : WorkingMCFG N α) : Prop :=
  TextFor t G.StringLanguage

/-- Distribution-level identification in the limit for a grammar target. -/
def DistributionIdentifiesInLimitForGrammar
    (obs : α → M) (f : Nat) (G : WorkingMCFG N α) : Prop :=
  DistributionIdentifiesInLimit obs f G.StringLanguage

/-- Grammar-target version of the Gold-style stabilization theorem. -/
theorem distributionCharacteristicSample_identifiesGrammarInLimit
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    (G : WorkingMCFG N α)
    (hS : DistributionCharacteristicSample S obs f G.StringLanguage)
    (hsub : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    DistributionIdentifiesInLimitForGrammar obs f G := by
  exact distributionCharacteristicSample_identifiesInLimit hS hsub

/-- Pointwise grammar-target version: after some stage in any text for `G`, the
learner's transported contexts agree with the true grammar target contexts. -/
theorem eventually_licensed_iff_grammar_context
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    (G : WorkingMCFG N α)
    (hS : DistributionCharacteristicSample S obs f G.StringLanguage)
    (hsub : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {t : Text α} (ht : TextForGrammar t G) :
    ∃ N0 : Nat,
      ∀ n : Nat, N0 ≤ n →
        ∀ {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d),
          c ∈ LearnerApproxDistribution (PrefixSample t n) obs f x ↔
            c ∈ NamedDistribution G.StringLanguage x := by
  exact eventually_licensed_iff_target_context hS hsub ht

end GrammarIdentification

end FIv21
