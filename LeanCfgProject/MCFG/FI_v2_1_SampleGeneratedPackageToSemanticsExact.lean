import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedPackageToSemantics

/-!
# FI v2.1 Lean experiment: exact bridge to word semantics

This layer packages the previous semantics bridge in an exact-style record.  It
keeps the generated `WorkingMCFG`, the induced concrete extracted sample data,
and the canonical learner-package view synchronized.
-/

namespace FIv21

universe u v w

section SampleGeneratedPackageToSemanticsExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact-style package for the sample-generated semantics bridge. -/
structure SampleGeneratedPackageSemanticsBridgeExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  bridge : SampleGeneratedPackageSemanticsBridge G obs K

namespace SampleGeneratedPackageSemanticsBridgeExact

/-- The generated consistency package. -/
def package
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPackageSemanticsBridgeExact G obs K) :
    SampleGeneratedConsistencyPackage G obs K :=
  E.bridge.package

/-- The generated rule skeleton. -/
def ruleSkeleton
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPackageSemanticsBridgeExact G obs K) :
    SampleGeneratedRuleSkeleton G obs K :=
  E.bridge.ruleSkeleton

/-- The generated rule-list package. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPackageSemanticsBridgeExact G obs K) :
    SampleGeneratedRuleListPackage G obs K :=
  E.bridge.ruleLists

/-- The generated working grammar shell. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPackageSemanticsBridgeExact G obs K) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      E.ruleLists.ruleSkeleton.skeleton) α :=
  E.bridge.grammar

/-- The induced concrete extracted sample data. -/
noncomputable def extractedData
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPackageSemanticsBridgeExact G obs K) :
    ConcreteExtractedSampleData G obs K :=
  E.bridge.extractedData

/-- The generated learner-side word language. -/
noncomputable def wordLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPackageSemanticsBridgeExact G obs K) : Set (Word α) :=
  E.bridge.wordLanguage

/-- The generated grammar shell is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPackageSemanticsBridgeExact G obs K) :
    E.grammar.SemanticWorkingConditions := by
  exact E.bridge.grammar_semanticWorkingConditions

/-- The generated learner-side word language contains the sample. -/
theorem positiveForWordLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPackageSemanticsBridgeExact G obs K) :
    PositiveForLanguage K E.wordLanguage := by
  exact E.bridge.sample_subset_wordLanguage

/-- The induced finite hypothesis is positive for the generated word language. -/
theorem finiteHypothesis_positiveForWordLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPackageSemanticsBridgeExact G obs K) :
    PositiveForLanguage E.extractedData.toFiniteLearnerHypothesis.sampleSet
      E.wordLanguage := by
  exact E.bridge.finiteHypothesis_positiveForWordLanguage

/-- Packaged learner-side word-semantics certificate. -/
noncomputable def toWordSemanticsCertificate
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPackageSemanticsBridgeExact G obs K) :
    ConcreteExtractedSampleWordSemanticsCertificate E.extractedData :=
  E.bridge.toWordSemanticsCertificate

/-- Canonical learner grammar package obtained from the generated grammar shell. -/
noncomputable def toCanonicalLearnerGrammarPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPackageSemanticsBridgeExact G obs K) :
    CanonicalLearnerGrammarPackage G obs K :=
  E.bridge.toCanonicalLearnerGrammarPackage

/-- Pointwise sample generation through the generated word language. -/
theorem sample_word_generated
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPackageSemanticsBridgeExact G obs K)
    {x : Word α} (hx : x ∈ K) :
    x ∈ E.wordLanguage := by
  exact E.bridge.sample_word_generated hx

/-- Pointwise sample generation through the canonical package view. -/
theorem canonicalPackage_sample_word_generated
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedPackageSemanticsBridgeExact G obs K)
    {x : Word α} (hx : x ∈ K) :
    x ∈ E.toCanonicalLearnerGrammarPackage.wordLanguage := by
  exact E.bridge.canonicalPackage_sample_word_generated hx

end SampleGeneratedPackageSemanticsBridgeExact

/-- Build the exact semantics bridge from an exact generated-consistency package. -/
def SampleGeneratedPackageSemanticsBridgeExact.ofConsistencyPackageExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedConsistencyPackageExact G obs K) :
    SampleGeneratedPackageSemanticsBridgeExact G obs K :=
  { bridge := { package := P.package } }

/-- Concrete enumerated exact bridge. -/
noncomputable def enumeratedSampleGeneratedPackageSemanticsBridgeExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (F : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M)
      (enumeratedSampleGeneratedWordParseWitnessConstructionExact
        G obs K f hfanout hG).ruleSkeleton) :
    SampleGeneratedPackageSemanticsBridgeExact G obs K :=
  { bridge :=
      enumeratedSampleGeneratedPackageSemanticsBridge G obs K f hfanout hG F }

/-- The concrete enumerated exact bridge gives a semantically well-formed output
grammar. -/
theorem enumeratedSampleGeneratedPackageSemanticsBridgeExact_semantic
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (F : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M)
      (enumeratedSampleGeneratedWordParseWitnessConstructionExact
        G obs K f hfanout hG).ruleSkeleton) :
    (enumeratedSampleGeneratedPackageSemanticsBridgeExact
      G obs K f hfanout hG F).grammar.SemanticWorkingConditions := by
  exact (enumeratedSampleGeneratedPackageSemanticsBridgeExact
    G obs K f hfanout hG F).grammar_semanticWorkingConditions

end SampleGeneratedPackageToSemanticsExact

end FIv21
