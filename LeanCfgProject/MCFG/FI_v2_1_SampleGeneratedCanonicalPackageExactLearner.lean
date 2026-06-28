import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedCanonicalPackageExact

/-!
# FI v2.1 Lean experiment: learner view for exact sample-generated packages

This layer packages the exact sample-generated canonical-package construction as
a learner-like map from finite samples to exact canonical packages.
-/

namespace FIv21

universe u v w

section SampleGeneratedCanonicalPackageExactLearner

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Learner-like map assigning to each finite sample an exact sample-generated
canonical package. -/
structure SampleGeneratedCanonicalPackageExactLearner
    (G : WorkingMCFG N α) (obs : α → M) where
  exactPackage :
    (K : Finset (Word α)) → SampleGeneratedCanonicalPackageExact G obs K

namespace SampleGeneratedCanonicalPackageExactLearner

/-- Underlying semantics bridge at sample `K`. -/
def bridge
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedCanonicalPackageExactLearner G obs)
    (K : Finset (Word α)) :
    SampleGeneratedPackageSemanticsBridge G obs K :=
  (L.exactPackage K).bridge

/-- Generated consistency package at sample `K`. -/
def package
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedCanonicalPackageExactLearner G obs)
    (K : Finset (Word α)) :
    SampleGeneratedConsistencyPackage G obs K :=
  (L.exactPackage K).package

/-- Generated rule-list package at sample `K`. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedCanonicalPackageExactLearner G obs)
    (K : Finset (Word α)) :
    SampleGeneratedRuleListPackage G obs K :=
  (L.exactPackage K).ruleLists

/-- Generated working grammar shell at sample `K`. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedCanonicalPackageExactLearner G obs)
    (K : Finset (Word α)) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      (L.ruleLists K).ruleSkeleton.skeleton) α :=
  (L.exactPackage K).grammar

/-- Canonical package at sample `K`. -/
noncomputable def canonicalPackage
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedCanonicalPackageExactLearner G obs)
    (K : Finset (Word α)) :
    CanonicalLearnerGrammarPackage G obs K :=
  (L.exactPackage K).canonicalPackage

/-- Exact canonical-package certificate at sample `K`. -/
noncomputable def canonicalExact
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedCanonicalPackageExactLearner G obs)
    (K : Finset (Word α)) :
    CanonicalLearnerGrammarExactForGrammar (L.canonicalPackage K) :=
  (L.exactPackage K).toCanonicalExact

/-- Generated learner-side word language at sample `K`. -/
noncomputable def wordLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedCanonicalPackageExactLearner G obs)
    (K : Finset (Word α)) : Set (Word α) :=
  (L.exactPackage K).wordLanguage

/-- Each generated grammar shell is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedCanonicalPackageExactLearner G obs)
    (K : Finset (Word α)) :
    (L.grammar K).SemanticWorkingConditions := by
  exact (L.exactPackage K).grammar_semanticWorkingConditions

/-- Each finite sample is positive for the generated word language. -/
theorem sample_subset_wordLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedCanonicalPackageExactLearner G obs)
    (K : Finset (Word α)) :
    PositiveForLanguage K (L.wordLanguage K) := by
  exact (L.exactPackage K).sample_subset_wordLanguage

/-- Pointwise generation by the generated word language. -/
theorem sample_word_generated
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedCanonicalPackageExactLearner G obs)
    (K : Finset (Word α)) {x : Word α} (hx : x ∈ K) :
    x ∈ L.wordLanguage K := by
  exact (L.exactPackage K).sample_word_generated hx

/-- Pointwise generation through the canonical package view. -/
theorem canonicalPackage_sample_word_generated
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedCanonicalPackageExactLearner G obs)
    (K : Finset (Word α)) {x : Word α} (hx : x ∈ K) :
    x ∈ (L.canonicalPackage K).wordLanguage := by
  exact (L.exactPackage K).canonicalPackage_sample_word_generated hx

/-- Exact approximation-distribution equality at sample `K`. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedCanonicalPackageExactLearner G obs)
    (K : Finset (Word α)) {d : Nat} (x : Tuple α d) :
    (L.canonicalPackage K).ApproxDistribution x =
      NamedDistribution G.StringLanguage x := by
  exact (L.exactPackage K).approxDistribution_exact x

/-- Sample words are target-language members, by the supplied exactness data. -/
theorem sample_word_in_target
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedCanonicalPackageExactLearner G obs)
    (K : Finset (Word α)) (w : Word α) (hw : w ∈ K) :
    w ∈ G.StringLanguage := by
  exact (L.exactPackage K).sample_word_in_target w hw

/-- The sample is positive for the target grammar at every finite sample. -/
theorem positiveSample_target
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedCanonicalPackageExactLearner G obs)
    (K : Finset (Word α)) :
    PositiveSample G K := by
  exact (L.exactPackage K).positiveSample_target

end SampleGeneratedCanonicalPackageExactLearner

/-- Build an exact canonical-package learner from a semantics-bridge learner and
one target-side exactness/start-witness certificate for each finite sample. -/
noncomputable def SampleGeneratedCanonicalPackageExactLearner.ofBridgeLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (L : SampleGeneratedPackageSemanticsBridgeLearner G obs)
    (H : (K : Finset (Word α)) →
      ConcreteExtractedSampleExactContextWordStartForGrammar
        (L.bridge K).extractedData) :
    SampleGeneratedCanonicalPackageExactLearner G obs :=
  { exactPackage := fun K =>
      { bridge := L.bridge K
        exact_start := H K } }

end SampleGeneratedCanonicalPackageExactLearner

end FIv21
