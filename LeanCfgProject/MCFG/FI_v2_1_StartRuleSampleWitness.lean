import LeanCfgProject.MCFG.FI_v2_1_SampleWordConsistencyGold

/-!
# FI v2.1 Lean experiment: start-rule sample witnesses

This forty-first layer refines the sample-word consistency skeleton on the
*target grammar* side.  The previous files recorded that every externally
sampled word belongs to the target string language.  Here we unpack that
membership into an explicit start-symbol derivation witness.

This is still not a learner-grammar consistency theorem: it does not claim that
the extracted learner grammar generates every sampled word.  It records the
presentation-relative target witness that a later canonical learner
construction must mirror.
-/

namespace FIv21

universe u v w

section StartRuleSampleWitness

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Target-side start-derivation witnesses for every sampled word. -/
structure SampleStartDerivationWitnesses
    (G : WorkingMCFG N α) (K : Finset (Word α)) : Prop where
  start_derives :
    ∀ w : Word α, w ∈ K →
      ∃ h : 1 = G.arity G.start,
        DerivesTuple G G.start (castTuple h (singletonTuple w))

namespace SampleStartDerivationWitnesses

/-- Build start witnesses from grammar-target sample-word consistency. -/
def ofSampleWordStartConsistency
    {G : WorkingMCFG N α} {K : Finset (Word α)}
    (C : SampleWordStartConsistency G K) :
    SampleStartDerivationWitnesses G K :=
  { start_derives := by
      intro w hw
      exact SampleWordStartConsistency.sample_word_start_derives C w hw }

/-- Build start witnesses directly from positivity for the target grammar. -/
def ofPositiveSample
    {G : WorkingMCFG N α} {K : Finset (Word α)}
    (hK : PositiveSample G K) :
    SampleStartDerivationWitnesses G K :=
  ofSampleWordStartConsistency
    (SampleWordStartConsistency.ofPositiveSample hK)

/-- Forget start witnesses back to positivity for the grammar target. -/
theorem positiveSample
    {G : WorkingMCFG N α} {K : Finset (Word α)}
    (C : SampleStartDerivationWitnesses G K) :
    PositiveSample G K := by
  intro w hw
  rcases C.start_derives w hw with ⟨h, hd⟩
  exact mem_StringLanguage_of_start_derives G w h hd

/-- Pointwise membership in the generated string language. -/
theorem sample_word_in_stringLanguage
    {G : WorkingMCFG N α} {K : Finset (Word α)}
    (C : SampleStartDerivationWitnesses G K)
    (w : Word α) (hw : w ∈ K) :
    w ∈ G.StringLanguage := by
  exact C.positiveSample w hw

end SampleStartDerivationWitnesses

/-- Start-derivation witnesses attached to concrete extracted sample data. -/
structure ConcreteExtractedSampleStartWitnessForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) : Prop where
  witnesses : SampleStartDerivationWitnesses G K

namespace ConcreteExtractedSampleStartWitnessForGrammar

/-- Construct target start witnesses from the earlier grammar-target word
consistency package. -/
def ofWordConsistency
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleWordConsistencyForGrammar E) :
    ConcreteExtractedSampleStartWitnessForGrammar E :=
  { witnesses :=
      SampleStartDerivationWitnesses.ofSampleWordStartConsistency C.words }

/-- Construct target start witnesses from the exact/context/word package. -/
def ofExactContextWord
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactContextWordForGrammar E) :
    ConcreteExtractedSampleStartWitnessForGrammar E :=
  { witnesses :=
      { start_derives := by
          intro w hw
          exact ConcreteExtractedSampleExactContextWordForGrammar.sample_word_start_derives
            C w hw } }

/-- Pointwise start-symbol derivation witness for an externally sampled word. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleStartWitnessForGrammar E)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact C.witnesses.start_derives w hw

/-- Forget start witnesses back to positivity for the grammar target. -/
theorem positiveSample
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleStartWitnessForGrammar E) :
    PositiveSample G K := by
  exact SampleStartDerivationWitnesses.positiveSample C.witnesses

/-- Pointwise membership of a sampled word in the target string language. -/
theorem sample_word_in_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleStartWitnessForGrammar E)
    (w : Word α) (hw : w ∈ K) :
    w ∈ G.StringLanguage := by
  exact SampleStartDerivationWitnesses.sample_word_in_stringLanguage C.witnesses w hw

end ConcreteExtractedSampleStartWitnessForGrammar

end StartRuleSampleWitness

end FIv21
