import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedPackageToSemanticsGold
import LeanCfgProject.MCFG.FI_v2_1_CanonicalLearnerGrammarExact

/-!
# FI v2.1 Lean experiment: sample-generated canonical packages with exactness

The previous layer connected the constructive sample-generated branch to the
older `CanonicalLearnerGrammarPackage` interface: the generated `WorkingMCFG`
shell supplies the learner-side word language for the induced concrete extracted
sample data.

This layer records the remaining target-side exactness/start-witness obligation
next to that bridge.  When that obligation is supplied, the sample-generated
canonical package becomes an instance of the earlier
`CanonicalLearnerGrammarExactForGrammar` interface.

This is deliberately honest: the file does not prove the target-side exactness
obligation.  It shows that the newly constructed sample-generated package is now
in the right shape to consume that obligation.
-/

namespace FIv21

universe u v w

section SampleGeneratedCanonicalPackageExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A sample-generated canonical learner package together with the target-side
exactness/start-witness certificate required by the older canonical exactness
interface.

The bridge supplies the generated grammar shell, its word language, the induced
concrete extracted sample data, and the canonical package view.  The field
`exact_start` is precisely the nonconstructive target-side obligation that has
not yet been derived from the concrete sample-generated grammar. -/
structure SampleGeneratedCanonicalPackageExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  bridge : SampleGeneratedPackageSemanticsBridge G obs K
  exact_start : ConcreteExtractedSampleExactContextWordStartForGrammar
    bridge.extractedData

namespace SampleGeneratedCanonicalPackageExact

/-- The underlying sample-generated consistency package. -/
def package
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K) :
    SampleGeneratedConsistencyPackage G obs K :=
  E.bridge.package

/-- The rule skeleton underlying the generated package. -/
def ruleSkeleton
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K) :
    SampleGeneratedRuleSkeleton G obs K :=
  E.bridge.ruleSkeleton

/-- The generated finite rule-list package. -/
noncomputable def ruleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K) :
    SampleGeneratedRuleListPackage G obs K :=
  E.bridge.ruleLists

/-- The generated working grammar shell. -/
noncomputable def grammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal
      E.ruleLists.ruleSkeleton.skeleton) α :=
  E.bridge.grammar

/-- The induced concrete extracted sample data. -/
noncomputable def extractedData
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K) :
    ConcreteExtractedSampleData G obs K :=
  E.bridge.extractedData

/-- The generated learner-side word language. -/
noncomputable def wordLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K) : Set (Word α) :=
  E.bridge.wordLanguage

/-- The canonical learner package induced by the generated grammar shell. -/
noncomputable def canonicalPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K) :
    CanonicalLearnerGrammarPackage G obs K :=
  E.bridge.toCanonicalLearnerGrammarPackage

/-- The sample-generated package is an exact canonical package once the
remaining target-side exactness/start-witness certificate is supplied. -/
noncomputable def toCanonicalExact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K) :
    CanonicalLearnerGrammarExactForGrammar E.canonicalPackage :=
  { exact_start := E.exact_start }

/-- The generated grammar shell is semantically well-formed. -/
theorem grammar_semanticWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K) :
    E.grammar.SemanticWorkingConditions := by
  exact E.bridge.grammar_semanticWorkingConditions

/-- The generated learner-side language contains the input finite sample. -/
theorem sample_subset_wordLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K) :
    PositiveForLanguage K E.wordLanguage := by
  exact E.bridge.sample_subset_wordLanguage

/-- Pointwise sample generation by the generated grammar's word language. -/
theorem sample_word_generated
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K)
    {x : Word α} (hx : x ∈ K) :
    x ∈ E.wordLanguage := by
  exact E.bridge.sample_word_generated hx

/-- Pointwise sample generation through the canonical-package view. -/
theorem canonicalPackage_sample_word_generated
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K)
    {x : Word α} (hx : x ∈ K) :
    x ∈ E.canonicalPackage.wordLanguage := by
  exact E.bridge.canonicalPackage_sample_word_generated hx

/-- Exact equality between the package approximate distribution and the target
named-context distribution. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K)
    {d : Nat} (x : Tuple α d) :
    E.canonicalPackage.ApproxDistribution x =
      NamedDistribution G.StringLanguage x := by
  exact E.toCanonicalExact.approxDistribution_exact x

/-- Exact context-membership form for the canonical package. -/
theorem licensed_iff_target_context
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d) :
    c ∈ E.canonicalPackage.ApproxDistribution x ↔
      c ∈ NamedDistribution G.StringLanguage x := by
  exact E.toCanonicalExact.licensed_iff_target_context x c

/-- Target-language membership of sampled words, obtained from the supplied
exactness/start-witness certificate. -/
theorem sample_word_in_target
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K)
    (w : Word α) (hw : w ∈ K) :
    w ∈ G.StringLanguage := by
  exact E.toCanonicalExact.sample_word_in_target w hw

/-- Target-side start derivation witness for sampled words. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact E.toCanonicalExact.sample_word_start_derives w hw

/-- The finite sample is positive for the target grammar. -/
theorem positiveSample_target
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K) :
    PositiveSample G K := by
  exact E.toCanonicalExact.positiveSample

/-- The canonical package inherits learner-word consistency from the generated
semantics bridge. -/
theorem learner_word_consistent
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleGeneratedCanonicalPackageExact G obs K) :
    ConcreteExtractedSampleLearnerWordConsistent
      E.canonicalPackage.data E.canonicalPackage.wordLanguage := by
  exact E.toCanonicalExact.learner_word_consistent

end SampleGeneratedCanonicalPackageExact

/-- Build an exact sample-generated canonical package from a semantics bridge
and the remaining target-side exactness/start-witness certificate. -/
noncomputable def SampleGeneratedCanonicalPackageExact.ofBridge
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (B : SampleGeneratedPackageSemanticsBridge G obs K)
    (H : ConcreteExtractedSampleExactContextWordStartForGrammar B.extractedData) :
    SampleGeneratedCanonicalPackageExact G obs K :=
  { bridge := B
    exact_start := H }

/-- Concrete enumerated exact package, parameterized by the nonempty prefix
family and the remaining target-side exactness/start-witness certificate. -/
noncomputable def enumeratedSampleGeneratedCanonicalPackageExact
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    (F : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M)
      (enumeratedSampleGeneratedWordParseWitnessConstructionExact
        G obs K f hfanout hG).ruleSkeleton)
    (H : ConcreteExtractedSampleExactContextWordStartForGrammar
      (enumeratedSampleGeneratedPackageSemanticsBridge
        G obs K f hfanout hG F).extractedData) :
    SampleGeneratedCanonicalPackageExact G obs K :=
  { bridge := enumeratedSampleGeneratedPackageSemanticsBridge
      G obs K f hfanout hG F
    exact_start := H }

end SampleGeneratedCanonicalPackageExact

end FIv21
