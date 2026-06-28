import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedConsistencyToPackageGold
import LeanCfgProject.MCFG.FI_v2_1_CanonicalLearnerGrammarInterface

/-!
# FI v2.1 Lean experiment: from sample-generated packages to word semantics

The previous layer produced a generated `WorkingMCFG` shell and packaged the
fact that its string language contains the finite sample.  Earlier layers used
an abstract learner-side word-semantics interface, and canonical learner
grammar packages expect such a semantics certificate.

This file bridges those two lines: the generated grammar's `StringLanguage` is
now used as the learner-side word language for the concrete extracted sample
data induced by the sample-generated skeleton.  Thus the new constructive
sample-generated branch can instantiate the older canonical-package interface.
-/

namespace FIv21

universe u v w

section SampleGeneratedPackageToSemantics

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Bridge from a sample-generated consistency package to the older learner-side
word-semantics interface.

The extracted data is the concrete sample-extraction data already available from
the underlying subword/unit-edge enumeration.  The learner-side word language is
the `StringLanguage` of the generated terminal+concat `WorkingMCFG` shell. -/
structure SampleGeneratedPackageSemanticsBridge
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  package : SampleGeneratedConsistencyPackage G obs K

namespace SampleGeneratedPackageSemanticsBridge

/-- The rule skeleton underlying the generated grammar. -/
def ruleSkeleton
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (B : SampleGeneratedPackageSemanticsBridge G obs K) :
    SampleGeneratedRuleSkeleton G obs K :=
  B.package.ruleSkeleton

/-- The generated finite rule-list package. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (B : SampleGeneratedPackageSemanticsBridge G obs K) :
    SampleGeneratedRuleListPackage G obs K :=
  B.package.ruleLists

/-- The generated working grammar shell. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (B : SampleGeneratedPackageSemanticsBridge G obs K) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      B.ruleLists.ruleSkeleton.skeleton) α :=
  B.package.grammar

/-- The concrete extracted sample data induced by the same sample-generated
subword/unit-edge enumeration. -/
noncomputable def extractedData
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (B : SampleGeneratedPackageSemanticsBridge G obs K) :
    ConcreteExtractedSampleData G obs K :=
  B.ruleSkeleton.skeleton.data.toSubwordContextDecompositionData.toConcreteExtractedSampleData

/-- The generated learner-side word language. -/
noncomputable def wordLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (B : SampleGeneratedPackageSemanticsBridge G obs K) : Set (Word α) :=
  B.package.language

/-- The generated grammar shell is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (B : SampleGeneratedPackageSemanticsBridge G obs K) :
    B.grammar.SemanticWorkingConditions := by
  exact B.package.semanticWorkingConditions

/-- The generated language contains the original finite sample. -/
theorem sample_subset_wordLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (B : SampleGeneratedPackageSemanticsBridge G obs K) :
    PositiveForLanguage K B.wordLanguage := by
  exact B.package.positiveForLanguage

/-- The same positivity statement, rewritten along the sample set of the induced
finite learner hypothesis. -/
theorem finiteHypothesis_positiveForWordLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (B : SampleGeneratedPackageSemanticsBridge G obs K) :
    PositiveForLanguage B.extractedData.toFiniteLearnerHypothesis.sampleSet
      B.wordLanguage := by
  rw [B.extractedData.finiteHypothesis_sampleSet]
  exact B.sample_subset_wordLanguage

/-- The generated word language is a valid learner-side word-semantics
certificate for the induced concrete extracted sample data. -/
noncomputable def toWordSemanticsCertificate
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (B : SampleGeneratedPackageSemanticsBridge G obs K) :
    ConcreteExtractedSampleWordSemanticsCertificate B.extractedData :=
  { wordLanguage := B.wordLanguage
    sample_consistent := B.finiteHypothesis_positiveForWordLanguage }

/-- The bridge instantiates the earlier canonical learner grammar package
interface. -/
noncomputable def toCanonicalLearnerGrammarPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (B : SampleGeneratedPackageSemanticsBridge G obs K) :
    CanonicalLearnerGrammarPackage G obs K :=
  { data := B.extractedData
    semantics := B.toWordSemanticsCertificate }

/-- The canonical package uses the generated grammar shell's language as its
learner-side word language. -/
theorem canonicalPackage_wordLanguage_eq
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (B : SampleGeneratedPackageSemanticsBridge G obs K) :
    B.toCanonicalLearnerGrammarPackage.wordLanguage = B.wordLanguage := by
  rfl

/-- Pointwise sample generation through the generated semantics bridge. -/
theorem sample_word_generated
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (B : SampleGeneratedPackageSemanticsBridge G obs K)
    {x : Word α} (hx : x ∈ K) :
    x ∈ B.wordLanguage := by
  exact B.sample_subset_wordLanguage x hx

/-- Pointwise sample generation through the canonical package view. -/
theorem canonicalPackage_sample_word_generated
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (B : SampleGeneratedPackageSemanticsBridge G obs K)
    {x : Word α} (hx : x ∈ K) :
    x ∈ B.toCanonicalLearnerGrammarPackage.wordLanguage := by
  exact B.toCanonicalLearnerGrammarPackage.sample_word_generated x hx

end SampleGeneratedPackageSemanticsBridge

/-- Build the semantics bridge from a generated consistency package. -/
def SampleGeneratedPackageSemanticsBridge.ofConsistencyPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedConsistencyPackage G obs K) :
    SampleGeneratedPackageSemanticsBridge G obs K :=
  { package := P }

/-- Concrete enumerated bridge for a fixed fanout bound, once the nonempty
prefix-enumeration family is supplied. -/
noncomputable def enumeratedSampleGeneratedPackageSemanticsBridge
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (F : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M)
      (enumeratedSampleGeneratedWordParseWitnessConstructionExact
        G obs K f hfanout hG).ruleSkeleton) :
    SampleGeneratedPackageSemanticsBridge G obs K :=
  { package :=
      enumeratedSampleGeneratedConsistencyPackage G obs K f hfanout hG F }

/-- The concrete enumerated bridge yields a canonical learner package. -/
noncomputable def enumeratedSampleGeneratedCanonicalPackage
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (F : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M)
      (enumeratedSampleGeneratedWordParseWitnessConstructionExact
        G obs K f hfanout hG).ruleSkeleton) :
    CanonicalLearnerGrammarPackage G obs K :=
  (enumeratedSampleGeneratedPackageSemanticsBridge
    G obs K f hfanout hG F).toCanonicalLearnerGrammarPackage

/-- The concrete enumerated canonical package generates every sampled word in
its learner-side word language. -/
theorem enumeratedSampleGeneratedCanonicalPackage_sample_word_generated
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (F : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M)
      (enumeratedSampleGeneratedWordParseWitnessConstructionExact
        G obs K f hfanout hG).ruleSkeleton)
    {x : Word α} (hx : x ∈ K) :
    x ∈ (enumeratedSampleGeneratedCanonicalPackage
      G obs K f hfanout hG F).wordLanguage := by
  exact (enumeratedSampleGeneratedCanonicalPackage
    G obs K f hfanout hG F).sample_word_generated x hx

end SampleGeneratedPackageToSemantics

end FIv21
