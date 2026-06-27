import LeanCfgProject.MCFG.FI_v2_1_CanonicalLearnerGrammarExact

/-!
# FI v2.1 Lean experiment: Gold wrapper for canonical learner grammar packages

This fifty-second layer packages a sample-indexed canonical learner grammar
interface and connects it to the previously checked Gold wrapper with packaged
learner-side word semantics.

The file still deliberately avoids constructing concrete rule lists by
`List.bind`.  Its role is to identify the exact API that the future canonical
learner grammar construction must instantiate in order to inherit the existing
Gold-style distributional identification theorem.
-/

namespace FIv21

universe u v w

section CanonicalLearnerGrammarGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A sample-indexed canonical learner grammar package. -/
abbrev CanonicalLearnerGrammarLearner
    (G : WorkingMCFG N α) (obs : α → M) :=
  (K : Finset (Word α)) → CanonicalLearnerGrammarPackage G obs K

namespace CanonicalLearnerGrammarLearner

/-- Forget a canonical learner package to the concrete extracted-sample learner
already used by the previous Gold wrappers. -/
def toConcreteExtractedSampleLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerGrammarLearner G obs) :
    ConcreteExtractedSampleLearner G obs :=
  fun K => (A K).data

/-- Forget a canonical learner package to the finite-hypothesis learner. -/
def toFiniteHypothesisLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerGrammarLearner G obs) :
    FiniteHypothesisLearner α M :=
  A.toConcreteExtractedSampleLearner.toFiniteHypothesisLearner

/-- The sample-indexed learner-side word semantics carried by a canonical
learner package. -/
def wordSemantics
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerGrammarLearner G obs) :
    ConcreteExtractedSampleLearnerWordSemantics A.toConcreteExtractedSampleLearner :=
  fun K => (A K).wordLanguage

/-- The packaged sample-indexed word-semantics certificate carried by a
canonical learner package. -/
def wordSemanticsCertificate
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerGrammarLearner G obs) :
    ConcreteExtractedSampleLearnerWordSemanticsCertificate
      A.toConcreteExtractedSampleLearner :=
  { wordLanguage := A.wordSemantics
    sample_consistent := by
      intro K
      exact (A K).learner_word_consistent }

/-- Pointwise learner-side generation of a sampled word. -/
theorem sample_word_generated
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerGrammarLearner G obs)
    (K : Finset (Word α))
    (w : Word α) (hw : w ∈ K) :
    w ∈ A.wordSemantics K := by
  exact (A K).sample_word_generated w hw

/-- The finite hypothesis associated with sample `K` uses exactly `K`. -/
theorem finiteHypothesis_sampleSet
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerGrammarLearner G obs)
    (K : Finset (Word α)) :
    (A.toFiniteHypothesisLearner K).sampleSet = K := by
  exact (A K).finiteHypothesis_sampleSet

end CanonicalLearnerGrammarLearner

/-- Characteristic-sample certificate for a sample-indexed canonical learner
grammar package.

The only target-specific obligation retained here is the already-checked start
witness characteristic-sample certificate for the underlying concrete extracted
data.  The learner-side word semantics is supplied automatically by the package
itself. -/
structure CanonicalLearnerGrammarCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (A : CanonicalLearnerGrammarLearner G obs) where
  startWitness :
    GrammarConcreteStartWitnessCharacteristicSample
      A.toConcreteExtractedSampleLearner

namespace CanonicalLearnerGrammarCharacteristicSample

/-- Forget a canonical learner characteristic-sample certificate to the previous
packaged-word-semantics Gold wrapper. -/
def toGrammarConcreteLearnerWordSemanticsCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalLearnerGrammarCharacteristicSample A) :
    GrammarConcreteLearnerWordSemanticsCharacteristicSample
      A.toConcreteExtractedSampleLearner :=
  { startWitness := C.startWitness
    semantics := A.wordSemanticsCertificate }

/-- Post-threshold exact/context/word/start plus canonical learner word
semantics. -/
def exact_with_word_semantics_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalLearnerGrammarCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage) :
    ConcreteExtractedSampleExactWithWordSemanticsForGrammar (A K).data :=
  C.toGrammarConcreteLearnerWordSemanticsCharacteristicSample
    |>.exact_with_word_semantics_after K hExt hPos

/-- Post-threshold exact distribution equality. -/
theorem approxDistribution_exact_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalLearnerGrammarCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    {d : Nat} (x : Tuple α d) :
    (A K).ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact (C.exact_with_word_semantics_after K hExt hPos).approxDistribution_exact x

/-- Post-threshold target-side start-symbol derivation witness for a sampled
word. -/
theorem sample_word_start_derives_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalLearnerGrammarCharacteristicSample A)
    (K : Finset (Word α))
    (hExt : SampleExtends C.startWitness.base.sample K)
    (hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact (C.exact_with_word_semantics_after K hExt hPos).sample_word_start_derives w hw

/-- Post-threshold learner-side generation of a sampled word by the canonical
package semantics. -/
theorem sample_word_generated_by_learner_after
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalLearnerGrammarCharacteristicSample A)
    (K : Finset (Word α))
    (_hExt : SampleExtends C.startWitness.base.sample K)
    (_hPos : PositiveForLanguage K G.StringLanguage)
    (w : Word α) (hw : w ∈ K) :
    w ∈ (A K).wordLanguage := by
  exact (A K).sample_word_generated w hw

/-- Limiting distributional identification inherited from the packaged
semantics Gold wrapper. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalLearnerGrammarCharacteristicSample A) :
    FiniteHypothesisIdentifiesGrammarInLimit A.toFiniteHypothesisLearner G := by
  exact GrammarConcreteLearnerWordSemanticsCharacteristicSample.identifiesInLimit
    C.toGrammarConcreteLearnerWordSemanticsCharacteristicSample

/-- Pointwise limiting context correctness inherited from the packaged
semantics Gold wrapper. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    {A : CanonicalLearnerGrammarLearner G obs}
    (C : CanonicalLearnerGrammarCharacteristicSample A) :
    FiniteHypothesisEventuallyCorrectContexts
      A.toFiniteHypothesisLearner G.StringLanguage := by
  exact GrammarConcreteLearnerWordSemanticsCharacteristicSample.eventuallyCorrectContexts
    C.toGrammarConcreteLearnerWordSemanticsCharacteristicSample

end CanonicalLearnerGrammarCharacteristicSample

end CanonicalLearnerGrammarGold

end FIv21
