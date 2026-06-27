import LeanCfgProject.MCFG.FI_v2_1_LearnerWordSemanticsExact

/-!
# FI v2.1 Lean experiment: Gold wrapper with packaged learner word semantics

This forty-ninth layer packages learner-side word semantics across all finite
samples and connects it to the existing Gold wrapper with learner-side
word-consistency.

The result is still distribution-level identification, not a full
machine-checked canonical learner grammar theorem.  The new contribution is an
interface saying that a future canonical learner grammar may provide a concrete
sample-indexed word semantics, and once this semantics explains all sampled
words, the existing exactness and Gold arguments can use it uniformly.
-/

namespace FIv21

universe u v w

section LearnerWordSemanticsGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Grammar-target characteristic sample with packaged learner-side word
semantics.  The semantics certificate supplies the learner-side word language
for each finite sample and proves sample-word consistency for that language. -/
structure GrammarConcreteLearnerWordSemanticsCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : ConcreteExtractedSampleLearner G obs) where
  startWitness : GrammarConcreteStartWitnessCharacteristicSample A
  semantics : ConcreteExtractedSampleLearnerWordSemanticsCertificate A

namespace GrammarConcreteLearnerWordSemanticsCharacteristicSample

/-- Forget packaged semantics to the previous bare-semantics Gold wrapper. -/
def toGrammarConcreteLearnerWordCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteLearnerWordSemanticsCharacteristicSample A) :
    GrammarConcreteLearnerWordCharacteristicSample
      A C.semantics.toBareSemantics :=
  { startWitness := C.startWitness
    learner_word_after_extending := by
      intro K _hExt _hPos
      exact C.semantics.sample_consistent K }

/-- Post-threshold exact/context/word/start plus packaged learner-side word
semantics. -/
def exact_with_word_semantics_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteLearnerWordSemanticsCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    ConcreteExtractedSampleExactWithWordSemanticsForGrammar (A K) :=
  { exact_start := C.startWitness.exact_context_word_start_after K hExt hPos
    semantics := C.semantics.at K }

/-- Post-threshold learner-side generation of a sampled word by the packaged
semantics at sample `K`. -/
theorem sample_word_generated_by_learner_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteLearnerWordSemanticsCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    w ∈ C.semantics.wordLanguage K := by
  exact (C.exact_with_word_semantics_after K hExt hPos).sample_word_generated_by_learner w hw

/-- Post-threshold target-side start-symbol derivation witness for a sampled
word. -/
theorem sample_word_start_derives_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteLearnerWordSemanticsCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact C.startWitness.sample_word_start_derives_after K hExt hPos w hw

/-- Post-threshold exact equality of extracted and target named-context
distributions. -/
theorem approxDistribution_exact_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteLearnerWordSemanticsCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    {d : Nat} (x : Tuple α d) :
    (A K).ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact (C.exact_with_word_semantics_after K hExt hPos).approxDistribution_exact x

/-- Limiting distributional identification follows by forgetting the packaged
semantics to the earlier bare-semantics wrapper. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteLearnerWordSemanticsCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact GrammarConcreteLearnerWordCharacteristicSample.identifiesInLimit
    C.toGrammarConcreteLearnerWordCharacteristicSample

/-- Pointwise limiting context correctness follows by the same forgetful map. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : ConcreteExtractedSampleLearner G obs}
    (C : GrammarConcreteLearnerWordSemanticsCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact GrammarConcreteLearnerWordCharacteristicSample.eventuallyCorrectContexts
    C.toGrammarConcreteLearnerWordCharacteristicSample

end GrammarConcreteLearnerWordSemanticsCharacteristicSample

end LearnerWordSemanticsGold

end FIv21
