import LeanCfgProject.MCFG.FI_v2_1_ActualRefinedRuleListsSummary

/-!
# FI v2.1 Lean experiment: sample-extracted rule lists

This file starts replacing the older abstract concrete-extraction field by the
actual finite-monoid refined rule lists constructed in
`FI_v2_1_ActualRefinedRuleLists`.

The sample side is still represented by finite support data and a safe-unit-edge
certificate: extracting those tuples, contexts, and unit edges from the raw
positive sample is the next vertical step.  However, the grammar-side refined
terminal, binary, and start rule lists are now no longer supplied by hand.  They
are generated from the base working grammar and the finite observation monoid.
-/

namespace FIv21

universe u v w

section SampleExtractedRuleLists

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Implementation-facing sample extraction in which the sample-derived finite
support is supplied, but the grammar-side refined rule lists are the actual
finite-monoid lists generated from the base grammar.

Compared with `ConcreteExtractedSampleData`, this removes one abstract field:
`concreteRules` is now determined by `G`, `obs`, and the semantic working
conditions of `G`. -/
structure SampleExtractedRuleLists
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  f : Nat
  support : FiniteLearnerSupport α
  sample_eq : support.sample = K
  safeEdges : support.ListedUnitEdgesAreSafe obs f
  semanticWorking : G.SemanticWorkingConditions

namespace SampleExtractedRuleLists

/-- The actual finite-monoid concrete refined-rule enumeration associated with
sample-extracted rule-list data. -/
noncomputable def concreteRules
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K) :
    FintypeConcreteRuleEnumeration G obs :=
  actualFintypeConcreteRuleEnumeration G obs E.semanticWorking

/-- Forget sample-extracted rule-list data to the existing concrete extracted
sample-data interface.  The key point is that the `concreteRules` field is filled
by the actual refined rule lists, not by an external certificate. -/
noncomputable def toConcreteExtractedSampleData
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K) :
    ConcreteExtractedSampleData G obs K :=
  { f := E.f
    support := E.support
    sample_eq := E.sample_eq
    safeEdges := E.safeEdges
    concreteRules := E.concreteRules }

/-- The finite learner hypothesis determined by the sample-extracted data. -/
noncomputable def toFiniteLearnerHypothesis
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K) :
    FiniteLearnerHypothesis α M :=
  E.toConcreteExtractedSampleData.toFiniteLearnerHypothesis

/-- The finite hypothesis uses exactly the external sample `K`. -/
theorem finiteHypothesis_sampleSet
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K) :
    E.toFiniteLearnerHypothesis.sampleSet = K := by
  exact E.toConcreteExtractedSampleData.finiteHypothesis_sampleSet

/-- Approximate distribution induced by sample-extracted rule-list data. -/
noncomputable def ApproxDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K)
    {d : Nat} (x : Tuple α d) : Set (NamedSentenceContext α d) :=
  E.toConcreteExtractedSampleData.ApproxDistribution x

/-- Unit reachability induced by sample-extracted rule-list data. -/
noncomputable def UnitReach
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K)
    {d : Nat} (x y : Tuple α d) : Prop :=
  E.toConcreteExtractedSampleData.UnitReach x y

/-- A listed unit edge gives unit reachability in the extracted data. -/
theorem listedEdge_reach
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K)
    {d : Nat} {x y : Tuple α d}
    (hxy : E.support.SupportsUnitEdge x y) :
    E.UnitReach x y := by
  exact E.toConcreteExtractedSampleData.listedEdge_reach hxy

/-- The grammar-side refined rule enumeration is the actual finite-monoid one. -/
theorem concreteRules_eq_actual
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K) :
    E.concreteRules = actualFintypeConcreteRuleEnumeration G obs E.semanticWorking := by
  rfl

/-- The actual refined rule lists contain all ordinary output-type rule
refinements. -/
theorem concrete_containsAllOrdinaryRuleRefinements
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K) :
    E.concreteRules.toFintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact actualFintypeConcreteRuleEnumeration_containsAll G obs E.semanticWorking

/-- The listed actual refined rules are supported by the canonical finite-monoid
rule-enumeration plan. -/
theorem concreteRules_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K) :
    E.concreteRules.grammar.AllRulesSupportedByPlan
      (FiniteRuleEnumerationPlan.ofFintype G obs) := by
  exact actualFintypeConcreteRuleEnumeration_supportedByPlan G obs E.semanticWorking

/-- Distributional soundness of the finite hypothesis encoded by the
sample-extracted data. -/
theorem approxDistribution_sound_for_language
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K)
    {L : Set (Word α)}
    (hK : PositiveForLanguage E.toFiniteLearnerHypothesis.sampleSet L)
    (hL : FixedNamedTupleSubstitutable E.f obs L)
    {d : Nat} (x : Tuple α d) :
    E.ApproxDistribution x ⊆ NamedDistribution L x := by
  exact E.toConcreteExtractedSampleData.approxDistribution_sound_for_language
    hK hL x

/-- Refined tuple language carried by the actual grammar-side enumeration. -/
noncomputable def RefinedTupleLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K)
    (A : RefinedNonterminal G M) : Set (Tuple α (G.arity A.base)) :=
  E.toConcreteExtractedSampleData.RefinedTupleLanguage A

/-- Soundness of the actual grammar-side refined tuple language. -/
theorem refinedTupleLanguage_sound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K)
    (A : RefinedNonterminal G M) :
    E.RefinedTupleLanguage A ⊆ OutputTypedTupleLanguage G obs A := by
  intro x hx
  exact E.toConcreteExtractedSampleData.refinedTupleLanguage_sound A hx

/-- Forgetting output types maps the actual grammar-side refined language into
the base tuple language. -/
theorem refinedTupleLanguage_forgets_to_base
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K)
    (A : RefinedNonterminal G M) :
    E.RefinedTupleLanguage A ⊆ FIv21.TupleLanguage G A.base := by
  intro x hx
  exact E.toConcreteExtractedSampleData.refinedTupleLanguage_forgets_to_base A hx

/-- Tuples generated by the actual grammar-side refined lists have the advertised
output type. -/
theorem refinedTupleLanguage_has_output_type
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleExtractedRuleLists G obs K)
    (A : RefinedNonterminal G M)
    {x : Tuple α (G.arity A.base)}
    (hx : x ∈ E.RefinedTupleLanguage A) :
    tupleType obs x = A.outTy := by
  exact E.toConcreteExtractedSampleData.refinedTupleLanguage_has_output_type A hx

end SampleExtractedRuleLists

end SampleExtractedRuleLists

end FIv21
