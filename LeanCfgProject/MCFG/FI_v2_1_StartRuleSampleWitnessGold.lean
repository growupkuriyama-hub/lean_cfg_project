import LeanCfgProject.MCFG.FI_v2_1_StartRuleSampleWitnessExact

/-!
# FI v2.1 Lean experiment: Gold wrapper with start witnesses

This forty-third layer adds a grammar-target characteristic-sample wrapper in
which all post-threshold concrete extractions are exact and also carry explicit
start-symbol derivation witnesses for the sampled words.

The limiting identification theorem is inherited from the previous
word-consistent Gold wrapper; the new value is that the target-side start
witness obligation is now part of the same certificate interface.
-/

namespace FIv21

universe u v w

section StartRuleSampleWitnessGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Grammar-target characteristic sample with post-threshold exact extraction
and explicit start witnesses for every sampled word. -/
structure GrammarConcreteStartWitnessCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : ConcreteExtractedSampleLearner G obs) where
  base : GrammarConcreteWordConsistentCharacteristicSample A
  exact_context_word_start_after_extending :
    ∀ K : Finset (Word α),
      SampleExtends base.sample K →
      PositiveForLanguage K G.StringLanguage →
        ConcreteExtractedSampleExactContextWordStartForGrammar (A K)

namespace GrammarConcreteStartWitnessCharacteristicSample

/-- Promote the previous word-consistent characteristic-sample certificate to
the start-witness version.  The start witnesses are obtained by unpacking
membership in the target grammar's string language. -/
def ofGrammarConcreteWordConsistentCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteWordConsistentCharacteristicSample A) :
    GrammarConcreteStartWitnessCharacteristicSample A :=
  { base := C
    exact_context_word_start_after_extending := by
      intro K hExt hPos
      exact ConcreteExtractedSampleExactContextWordStartForGrammar.ofExactContextWord
        (C.exact_context_word_after_extending K hExt hPos) }

/-- Forget back to the previous word-consistent characteristic-sample wrapper. -/
def toGrammarConcreteWordConsistentCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteStartWitnessCharacteristicSample A) :
    GrammarConcreteWordConsistentCharacteristicSample A :=
  C.base

/-- Post-threshold exact/context/word/start extraction. -/
theorem exact_context_word_start_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteStartWitnessCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    ConcreteExtractedSampleExactContextWordStartForGrammar (A K) := by
  exact C.exact_context_word_start_after_extending K hExt hPos

/-- Post-threshold start-symbol derivation witness for an externally sampled
word. -/
theorem sample_word_start_derives_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteStartWitnessCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact (C.exact_context_word_start_after K hExt hPos).sample_word_start_derives w hw

/-- Limiting identification follows by forgetting the start-witness field. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteStartWitnessCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact GrammarConcreteWordConsistentCharacteristicSample.identifiesInLimit C.base

/-- Pointwise limiting context correctness also follows by forgetting the
start-witness field. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteStartWitnessCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact GrammarConcreteWordConsistentCharacteristicSample.eventuallyCorrectContexts C.base

end GrammarConcreteStartWitnessCharacteristicSample

end StartRuleSampleWitnessGold

end FIv21
