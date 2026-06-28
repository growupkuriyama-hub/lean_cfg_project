import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedNonemptySampleConsistencyGold

/-!
# FI v2.1 Lean experiment: packaging sample-generated consistency

The previous layer proved that, under a nonempty-word side condition and a
prefix-enumeration family, the sample-generated terminal+concat `WorkingMCFG`
contains every word of the finite sample.  This file packages that conclusion
as an explicit word-language certificate attached to the generated grammar.

This is a small but useful bridge: downstream layers can now refer to a single
package whose language is the generated grammar's `StringLanguage` and whose
main certified property is `PositiveForLanguage K language`.
-/

namespace FIv21

universe u v w

section SampleGeneratedConsistencyToPackage

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A word-language certificate extracted from a generated working grammar. -/
structure SampleGeneratedWordLanguageCertificate
    (K : Finset (Word α)) where
  language : Set (Word α)
  positive : PositiveForLanguage K language

namespace SampleGeneratedWordLanguageCertificate

/-- Pointwise membership for sample words. -/
theorem word_mem
    {K : Finset (Word α)}
    (C : SampleGeneratedWordLanguageCertificate (α := α) K)
    {w : Word α} (hw : w ∈ K) :
    w ∈ C.language := by
  exact C.positive w hw

/-- Repackage a pointwise sample-inclusion proof as a word-language certificate. -/
def ofPositive
    {K : Finset (Word α)} {L : Set (Word α)}
    (h : PositiveForLanguage K L) :
    SampleGeneratedWordLanguageCertificate (α := α) K :=
  { language := L
    positive := h }

end SampleGeneratedWordLanguageCertificate

/-- Main package tying together the nonempty sample-consistency exact package,
the generated working grammar, and the induced positive-language certificate. -/
structure SampleGeneratedConsistencyPackage
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  exactPackage : SampleGeneratedNonemptySampleConsistencyExact G obs K

namespace SampleGeneratedConsistencyPackage

/-- The rule skeleton underlying the generated grammar. -/
def ruleSkeleton
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedConsistencyPackage G obs K) :
    SampleGeneratedRuleSkeleton G obs K :=
  P.exactPackage.ruleSkeleton

/-- The generated finite rule-list package. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedConsistencyPackage G obs K) :
    SampleGeneratedRuleListPackage G obs K :=
  P.exactPackage.ruleLists

/-- The generated working grammar shell. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedConsistencyPackage G obs K) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      P.ruleLists.ruleSkeleton.skeleton) α :=
  P.exactPackage.toWorkingMCFG

/-- The generated language. -/
noncomputable def language
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedConsistencyPackage G obs K) : Set (Word α) :=
  P.grammar.StringLanguage

/-- The generated grammar shell is semantically well-formed. -/
theorem semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedConsistencyPackage G obs K) :
    P.grammar.SemanticWorkingConditions := by
  exact P.exactPackage.semanticWorkingConditions

/-- The sample has no empty words, as required by the terminal+concat branch. -/
def nonemptySample
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedConsistencyPackage G obs K) :
    NonemptyWordSample K :=
  P.exactPackage.nonemptySample

/-- Every sample word lies in the generated language. -/
theorem sample_subset_language
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedConsistencyPackage G obs K) :
    ∀ w : Word α, w ∈ K → w ∈ P.language := by
  intro w hw
  exact P.exactPackage.word_mem_stringLanguage_of_mem hw

/-- The generated language is positive for the finite sample. -/
theorem positiveForLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedConsistencyPackage G obs K) :
    PositiveForLanguage K P.language := by
  exact P.sample_subset_language

/-- A compact language certificate for the generated grammar. -/
noncomputable def toWordLanguageCertificate
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedConsistencyPackage G obs K) :
    SampleGeneratedWordLanguageCertificate (α := α) K :=
  { language := P.language
    positive := P.positiveForLanguage }

/-- Pointwise sample generation through the package certificate. -/
theorem word_mem_generatedLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedConsistencyPackage G obs K)
    {w : Word α} (hw : w ∈ K) :
    w ∈ P.language := by
  exact P.sample_subset_language w hw

end SampleGeneratedConsistencyPackage

/-- Build the bridge package from the previous exact nonempty sample-consistency
package. -/
def SampleGeneratedConsistencyPackage.ofExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedNonemptySampleConsistencyExact G obs K) :
    SampleGeneratedConsistencyPackage G obs K :=
  { exactPackage := E }

/-- Concrete enumerated bridge package for a fixed fanout bound, once the
nonempty prefix-enumeration family is supplied. -/
noncomputable def enumeratedSampleGeneratedConsistencyPackage
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (F : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M)
      (enumeratedSampleGeneratedWordParseWitnessConstructionExact
        G obs K f hfanout hG).ruleSkeleton) :
    SampleGeneratedConsistencyPackage G obs K :=
  { exactPackage :=
      enumeratedSampleGeneratedNonemptySampleConsistencyExact
        G obs K f hfanout hG F }

/-- The concrete enumerated bridge package has a semantically well-formed output
grammar. -/
theorem enumeratedSampleGeneratedConsistencyPackage_semantic
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (F : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M)
      (enumeratedSampleGeneratedWordParseWitnessConstructionExact
        G obs K f hfanout hG).ruleSkeleton) :
    (enumeratedSampleGeneratedConsistencyPackage
      G obs K f hfanout hG F).grammar.SemanticWorkingConditions := by
  exact (enumeratedSampleGeneratedConsistencyPackage
    G obs K f hfanout hG F).semanticWorkingConditions

end SampleGeneratedConsistencyToPackage

end FIv21
