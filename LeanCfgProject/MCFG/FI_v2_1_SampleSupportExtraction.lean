import LeanCfgProject.MCFG.FI_v2_1_SampleExtractedRuleListsGold

/-!
# FI v2.1 Lean experiment: extracting the basic finite support from a sample

This file begins the next vertical step after `SampleExtractedRuleLists`.

The previous layer still accepted an externally supplied `FiniteLearnerSupport`.
Here we remove one more external field by defining a canonical *sample-only*
finite support: its sample component is the given finite positive sample, and
its tuple/context/unit-edge lists are initially empty.  This is intentionally
minimal.  It does not yet extract observed tuple and context atoms from raw
sample decompositions; that is a later derivation/occurrence step.  However, it
is a genuine construction of a `FiniteLearnerSupport` from the sample itself,
and it plugs into the actual refined-rule-list pipeline.
-/

namespace FIv21

universe u v w

section SampleSupportExtraction

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- The minimal finite learner support canonically determined by a finite sample.

It records the sample exactly and starts with no tuple atoms, no context atoms,
and no listed unit edges.  Later extraction layers can replace the empty lists by
lists obtained from actual sample decompositions. -/
def sampleOnlySupport (K : Finset (Word α)) : FiniteLearnerSupport α :=
  { sample := K
    tuples := []
    contexts := []
    unitEdges := [] }

namespace sampleOnlySupport

/-- The sample component of the sample-only support is exactly the input sample. -/
theorem sample_eq (K : Finset (Word α)) :
    (sampleOnlySupport (α := α) K).sample = K := by
  rfl

/-- The sample-only support contains no tuple atoms. -/
theorem no_tuples (K : Finset (Word α))
    {d : Nat} {x : Tuple α d} :
    ¬ (sampleOnlySupport (α := α) K).SupportsTuple x := by
  intro h
  simpa [sampleOnlySupport, FiniteLearnerSupport.SupportsTuple] using h

/-- The sample-only support contains no context atoms. -/
theorem no_contexts (K : Finset (Word α))
    {d : Nat} {c : NamedSentenceContext α d} :
    ¬ (sampleOnlySupport (α := α) K).SupportsContext c := by
  intro h
  simpa [sampleOnlySupport, FiniteLearnerSupport.SupportsContext] using h

/-- The sample-only support contains no listed unit edges. -/
theorem no_unitEdges (K : Finset (Word α))
    {d : Nat} {x y : Tuple α d} :
    ¬ (sampleOnlySupport (α := α) K).SupportsUnitEdge x y := by
  intro h
  simpa [sampleOnlySupport, FiniteLearnerSupport.SupportsUnitEdge] using h

/-- Because there are no listed unit edges, the listed-edge safety condition is
vacuously satisfied. -/
theorem listedUnitEdgesAreSafe
    (K : Finset (Word α)) (obs : α → M) (f : Nat) :
    (sampleOnlySupport (α := α) K).ListedUnitEdgesAreSafe obs f := by
  intro d x y hxy
  exact False.elim ((no_unitEdges (α := α) K) hxy)

end sampleOnlySupport

/-- Sample-support extraction data.

This is the minimal sample-derived version of `SampleExtractedRuleLists`: the
finite support is no longer supplied as a field, but is the canonical
`sampleOnlySupport K`.  The grammar-side refined rule lists are still the actual
finite-monoid lists constructed earlier. -/
structure SampleSupportExtraction
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  f : Nat
  semanticWorking : G.SemanticWorkingConditions

namespace SampleSupportExtraction

/-- The finite support extracted at this layer. -/
def support
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (_E : SampleSupportExtraction G obs K) : FiniteLearnerSupport α :=
  sampleOnlySupport K

/-- The extracted support has exactly the input sample. -/
theorem support_sample_eq
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K) :
    E.support.sample = K := by
  rfl

/-- The extracted support has no listed unit edges at this minimal stage. -/
theorem support_no_unitEdges
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K)
    {d : Nat} {x y : Tuple α d} :
    ¬ E.support.SupportsUnitEdge x y := by
  exact sampleOnlySupport.no_unitEdges (α := α) K

/-- The safe-edge certificate for the minimal extracted support. -/
theorem support_safeEdges
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K) :
    E.support.ListedUnitEdgesAreSafe obs E.f := by
  exact sampleOnlySupport.listedUnitEdgesAreSafe (α := α) K obs E.f

/-- Convert minimal sample-support extraction into the previous
`SampleExtractedRuleLists` interface. -/
noncomputable def toSampleExtractedRuleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K) :
    SampleExtractedRuleLists G obs K :=
  { f := E.f
    support := E.support
    sample_eq := E.support_sample_eq
    safeEdges := E.support_safeEdges
    semanticWorking := E.semanticWorking }

/-- Forget further to concrete extracted sample data. -/
noncomputable def toConcreteExtractedSampleData
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K) :
    ConcreteExtractedSampleData G obs K :=
  E.toSampleExtractedRuleLists.toConcreteExtractedSampleData

/-- The induced finite learner hypothesis. -/
noncomputable def toFiniteLearnerHypothesis
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K) :
    FiniteLearnerHypothesis α M :=
  E.toSampleExtractedRuleLists.toFiniteLearnerHypothesis

/-- The induced finite hypothesis uses exactly the input sample. -/
theorem finiteHypothesis_sampleSet
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K) :
    E.toFiniteLearnerHypothesis.sampleSet = K := by
  exact E.toSampleExtractedRuleLists.finiteHypothesis_sampleSet

/-- The actual refined-rule enumeration inherited from the sample-extracted rule
list layer. -/
noncomputable def concreteRules
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K) :
    FintypeConcreteRuleEnumeration G obs :=
  E.toSampleExtractedRuleLists.concreteRules

/-- The grammar-side concrete rules are the actual finite-monoid refined-rule
lists. -/
theorem concreteRules_eq_actual
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K) :
    E.concreteRules = actualFintypeConcreteRuleEnumeration G obs E.semanticWorking := by
  rfl

/-- The actual refined rule lists contain all ordinary output-type refinements. -/
theorem concrete_containsAllOrdinaryRuleRefinements
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K) :
    E.concreteRules.toFintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact E.toSampleExtractedRuleLists.concrete_containsAllOrdinaryRuleRefinements

/-- The actual refined rule lists are supported by the canonical finite-monoid
rule-enumeration plan. -/
theorem concreteRules_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K) :
    E.concreteRules.grammar.AllRulesSupportedByPlan
      (FiniteRuleEnumerationPlan.ofFintype G obs) := by
  exact E.toSampleExtractedRuleLists.concreteRules_supportedByPlan

/-- Approximate distribution induced by the minimal sample-support extraction. -/
noncomputable def ApproxDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K)
    {d : Nat} (x : Tuple α d) : Set (NamedSentenceContext α d) :=
  E.toSampleExtractedRuleLists.ApproxDistribution x

/-- Unit reachability induced by the minimal sample-support extraction. -/
noncomputable def UnitReach
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K)
    {d : Nat} (x y : Tuple α d) : Prop :=
  E.toSampleExtractedRuleLists.UnitReach x y

/-- Soundness of the approximation under the usual positivity and
fixed-substitutability assumptions. -/
theorem approxDistribution_sound_for_language
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K)
    {L : Set (Word α)}
    (hK : PositiveForLanguage E.toFiniteLearnerHypothesis.sampleSet L)
    (hL : FixedNamedTupleSubstitutable E.f obs L)
    {d : Nat} (x : Tuple α d) :
    E.ApproxDistribution x ⊆ NamedDistribution L x := by
  exact E.toSampleExtractedRuleLists.approxDistribution_sound_for_language
    hK hL x

/-- Refined tuple language carried by the actual grammar-side rule lists. -/
noncomputable def RefinedTupleLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K)
    (A : RefinedNonterminal G M) : Set (Tuple α (G.arity A.base)) :=
  E.toSampleExtractedRuleLists.RefinedTupleLanguage A

/-- Soundness of the actual grammar-side refined tuple language. -/
theorem refinedTupleLanguage_sound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K)
    (A : RefinedNonterminal G M) :
    E.RefinedTupleLanguage A ⊆ OutputTypedTupleLanguage G obs A := by
  intro x hx
  exact E.toSampleExtractedRuleLists.refinedTupleLanguage_sound A hx

/-- Forgetting output types maps the refined language into the base tuple
language. -/
theorem refinedTupleLanguage_forgets_to_base
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K)
    (A : RefinedNonterminal G M) :
    E.RefinedTupleLanguage A ⊆ FIv21.TupleLanguage G A.base := by
  intro x hx
  exact E.toSampleExtractedRuleLists.refinedTupleLanguage_forgets_to_base A hx

/-- Tuples generated by the actual grammar-side refined lists have the advertised
output type. -/
theorem refinedTupleLanguage_has_output_type
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : SampleSupportExtraction G obs K)
    (A : RefinedNonterminal G M)
    {x : Tuple α (G.arity A.base)}
    (hx : x ∈ E.RefinedTupleLanguage A) :
    tupleType obs x = A.outTy := by
  exact E.toSampleExtractedRuleLists.refinedTupleLanguage_has_output_type A hx

end SampleSupportExtraction

end SampleSupportExtraction

end FIv21
