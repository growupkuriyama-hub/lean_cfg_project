import LeanCfgProject.MCFG.FI_v2_1_FiniteHypothesis

/-!
# FI v2.1 Lean experiment: finite-hypothesis Gold wrapper

This file is the thirteenth formalization layer for the FI v2.1 MCFG paper.

The previous layer packaged a finite learner hypothesis: a finite support,
listed safe unit edges, the induced unit closure, and the transported-context
approximation.  This file connects that finite-hypothesis interface to the
Gold-style stabilization layer.

The result is still deliberately abstract.  We do not yet construct the full
canonical learner from a sample.  Instead, we assume a sample-indexed finite
hypothesis learner and a finite characteristic-sample certificate saying that,
once a positive prefix sample contains the characteristic sample, the finite
hypothesis returned for that prefix is exact for the target language.

Under that assumption, the usual finite-telltale argument gives eventual
stabilization of the finite hypothesis's transported-context approximation on
every text for the target.
-/

namespace FIv21

universe u v w

section FiniteHypothesisGold

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]

/-- A sample-driven finite-hypothesis learner.

At this level, the learner is simply a function from finite positive samples to
finite learner hypotheses.  The construction of this function from the actual
canonical MCFG rule enumeration is left to later layers. -/
abbrev FiniteHypothesisLearner (α : Type u) (M : Type v) [Monoid M] :=
  Finset (Word α) → FiniteLearnerHypothesis α M

/-- A finite hypothesis learner identifies a target in the limit at the
transported-context distribution level if, on every text for the target, all
sufficiently late prefix hypotheses have exactly the target named-context
distributions. -/
def FiniteHypothesisIdentifiesInLimit
    (A : FiniteHypothesisLearner α M) (L : Set (Word α)) : Prop :=
  ∀ t : Text α,
    TextFor t L →
      ∃ N : Nat,
        ∀ n : Nat, N ≤ n →
          ∀ {d : Nat} (x : Tuple α d),
            (A (PrefixSample t n)).ApproxDistribution x = NamedDistribution L x

/-- Membership form of finite-hypothesis identification in the limit. -/
def FiniteHypothesisEventuallyCorrectContexts
    (A : FiniteHypothesisLearner α M) (L : Set (Word α)) : Prop :=
  ∀ t : Text α,
    TextFor t L →
      ∃ N : Nat,
        ∀ n : Nat, N ≤ n →
          ∀ {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d),
            c ∈ (A (PrefixSample t n)).ApproxDistribution x ↔
              c ∈ NamedDistribution L x

/-- A characteristic-sample certificate for a sample-driven finite-hypothesis
learner.

The field `exact_after_extending` is the finite-hypothesis analogue of the
paper's characteristic-sample property: every positive sample extending the
characteristic sample yields an exact finite hypothesis for the target. -/
structure FiniteHypothesisCharacteristicSample
    (A : FiniteHypothesisLearner α M) (L : Set (Word α)) where
  sample : Finset (Word α)
  positive : PositiveForLanguage sample L
  exact_after_extending :
    ∀ K : Finset (Word α),
      SampleExtends sample K →
      PositiveForLanguage K L →
        FiniteLearnerHypothesis.ExactForLanguage (A K) L

namespace FiniteHypothesisCharacteristicSample

/-- A finite-hypothesis characteristic sample gives Gold-style limiting
identification of the finite-hypothesis approximations. -/
theorem identifiesInLimit
    {A : FiniteHypothesisLearner α M} {L : Set (Word α)}
    (C : FiniteHypothesisCharacteristicSample A L) :
    FiniteHypothesisIdentifiesInLimit A L := by
  intro t ht
  rcases text_eventually_contains_finite_sample ht C.sample C.positive with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn d x
  exact FiniteLearnerHypothesis.ExactForLanguage.approxDistribution_exact
    (C.exact_after_extending
      (PrefixSample t n) (hN n hn) (prefixSample_positive ht n)) x

/-- Pointwise context-membership form of `identifiesInLimit`. -/
theorem eventuallyCorrectContexts
    {A : FiniteHypothesisLearner α M} {L : Set (Word α)}
    (C : FiniteHypothesisCharacteristicSample A L) :
    FiniteHypothesisEventuallyCorrectContexts A L := by
  intro t ht
  rcases text_eventually_contains_finite_sample ht C.sample C.positive with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn d x c
  exact FiniteLearnerHypothesis.ExactForLanguage.licensed_iff_target_context
    (C.exact_after_extending
      (PrefixSample t n) (hN n hn) (prefixSample_positive ht n)) x c

/-- The distribution-level statement implies the pointwise membership statement.
This is a small convenience lemma for later interfaces. -/
theorem eventuallyCorrectContexts_of_identifiesInLimit
    {A : FiniteHypothesisLearner α M} {L : Set (Word α)}
    (hA : FiniteHypothesisIdentifiesInLimit A L) :
    FiniteHypothesisEventuallyCorrectContexts A L := by
  intro t ht
  rcases hA t ht with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn d x c
  rw [hN n hn x]

end FiniteHypothesisCharacteristicSample

end FiniteHypothesisGold

section FiniteHypothesisClasses

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]

/-- A language class has finite-hypothesis telltales for a sample-driven finite
hypothesis learner if every target in the class has a finite characteristic
sample for that learner. -/
def FiniteHypothesisTelltaleClass
    (C : LanguageClass α) (A : FiniteHypothesisLearner α M) : Prop :=
  ∀ L : Set (Word α), L ∈ C →
    ∃ S : FiniteHypothesisCharacteristicSample A L, True

/-- A sample-driven finite-hypothesis learner identifies every language in a
class at the transported-context distribution level. -/
def FiniteHypothesisIdentifiesLanguageClass
    (C : LanguageClass α) (A : FiniteHypothesisLearner α M) : Prop :=
  ∀ L : Set (Word α), L ∈ C → FiniteHypothesisIdentifiesInLimit A L

/-- Class-level finite-telltale theorem for finite hypotheses. -/
theorem FiniteHypothesisTelltaleClass.identifies
    {C : LanguageClass α} {A : FiniteHypothesisLearner α M}
    (hC : FiniteHypothesisTelltaleClass C A) :
    FiniteHypothesisIdentifiesLanguageClass C A := by
  intro L hL
  rcases hC L hL with ⟨S, _htriv⟩
  exact S.identifiesInLimit

/-- Pointwise class-level form. -/
theorem FiniteHypothesisTelltaleClass.eventuallyCorrectContexts
    {C : LanguageClass α} {A : FiniteHypothesisLearner α M}
    (hC : FiniteHypothesisTelltaleClass C A)
    {L : Set (Word α)} (hL : L ∈ C) :
    FiniteHypothesisEventuallyCorrectContexts A L := by
  rcases hC L hL with ⟨S, _htriv⟩
  exact S.eventuallyCorrectContexts

end FiniteHypothesisClasses

section GrammarFiniteHypothesisGold

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]
variable {N : Type w}

/-- A finite-hypothesis learner identifies a grammar target in the limit when it
identifies the grammar's string language. -/
def FiniteHypothesisIdentifiesGrammarInLimit
    (A : FiniteHypothesisLearner α M) (G : WorkingMCFG N α) : Prop :=
  FiniteHypothesisIdentifiesInLimit A G.StringLanguage

/-- Grammar-target finite-hypothesis characteristic sample. -/
abbrev GrammarFiniteHypothesisCharacteristicSample
    (A : FiniteHypothesisLearner α M) (G : WorkingMCFG N α) :=
  FiniteHypothesisCharacteristicSample A G.StringLanguage

/-- Grammar-target Gold wrapper. -/
theorem GrammarFiniteHypothesisCharacteristicSample.identifiesInLimit
    {A : FiniteHypothesisLearner α M} {G : WorkingMCFG N α}
    (C : GrammarFiniteHypothesisCharacteristicSample A G) :
    FiniteHypothesisIdentifiesGrammarInLimit A G := by
  exact FiniteHypothesisCharacteristicSample.identifiesInLimit C

/-- Grammar-target pointwise context form. -/
theorem GrammarFiniteHypothesisCharacteristicSample.eventuallyCorrectContexts
    {A : FiniteHypothesisLearner α M} {G : WorkingMCFG N α}
    (C : GrammarFiniteHypothesisCharacteristicSample A G) :
    FiniteHypothesisEventuallyCorrectContexts A G.StringLanguage := by
  exact FiniteHypothesisCharacteristicSample.eventuallyCorrectContexts C

/-- Grammar-class finite-hypothesis telltales. -/
def GrammarFiniteHypothesisTelltaleClass
    (C : GrammarClass N α) (A : FiniteHypothesisLearner α M) : Prop :=
  ∀ G : WorkingMCFG N α, G ∈ C →
    ∃ S : GrammarFiniteHypothesisCharacteristicSample A G, True

/-- Grammar-class finite-hypothesis identification. -/
def FiniteHypothesisIdentifiesGrammarClass
    (C : GrammarClass N α) (A : FiniteHypothesisLearner α M) : Prop :=
  ∀ G : WorkingMCFG N α, G ∈ C → FiniteHypothesisIdentifiesGrammarInLimit A G

/-- Grammar-class finite-telltale theorem for finite hypotheses. -/
theorem GrammarFiniteHypothesisTelltaleClass.identifies
    {C : GrammarClass N α} {A : FiniteHypothesisLearner α M}
    (hC : GrammarFiniteHypothesisTelltaleClass C A) :
    FiniteHypothesisIdentifiesGrammarClass C A := by
  intro G hG
  rcases hC G hG with ⟨S, _htriv⟩
  exact GrammarFiniteHypothesisCharacteristicSample.identifiesInLimit S

end GrammarFiniteHypothesisGold

end FIv21
