import LeanCfgProject.MCFG.FI_v2_1_SampleSupportExtractionGold

/-!
# FI v2.1 Lean experiment: observed sample atoms

This file is the next vertical step after the minimal `sampleOnlySupport` layer.

The previous layer constructed a finite support from a sample, but used empty
lists for tuple atoms, context atoms, and unit edges.  Here we introduce an
implementation-facing extraction layer in which these atom lists are supplied
explicitly and are assembled into a genuine `FiniteLearnerSupport`.  This does
not yet parse raw words into all possible named-context decompositions.  It is,
however, the point at which sample-observed tuple/context/unit-edge candidates
become the finite support used by the learner pipeline.
-/

namespace FIv21

universe u v w

section ObservedSampleAtoms

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Assemble finite support from a finite sample and explicitly listed observed
atoms. -/
def supportOfObservedAtoms
    (K : Finset (Word α))
    (tupleAtoms : List (TupleAtom α))
    (contextAtoms : List (ContextAtom α))
    (unitEdgeAtoms : List (UnitEdgeAtom α)) : FiniteLearnerSupport α :=
  { sample := K
    tuples := tupleAtoms
    contexts := contextAtoms
    unitEdges := unitEdgeAtoms }

namespace supportOfObservedAtoms

/-- The support assembled from observed atoms records the original sample
exactly. -/
theorem sample_eq
    (K : Finset (Word α))
    (tupleAtoms : List (TupleAtom α))
    (contextAtoms : List (ContextAtom α))
    (unitEdgeAtoms : List (UnitEdgeAtom α)) :
    (supportOfObservedAtoms (α := α) K tupleAtoms contextAtoms unitEdgeAtoms).sample = K := by
  rfl

/-- Tuple membership in the assembled support is exactly membership in the
listed tuple atoms. -/
theorem supportsTuple_iff
    (K : Finset (Word α))
    (tupleAtoms : List (TupleAtom α))
    (contextAtoms : List (ContextAtom α))
    (unitEdgeAtoms : List (UnitEdgeAtom α))
    {d : Nat} (x : Tuple α d) :
    (supportOfObservedAtoms (α := α) K tupleAtoms contextAtoms unitEdgeAtoms).SupportsTuple x ↔
      (Sigma.mk d x : TupleAtom α) ∈ tupleAtoms := by
  rfl

/-- Context membership in the assembled support is exactly membership in the
listed context atoms. -/
theorem supportsContext_iff
    (K : Finset (Word α))
    (tupleAtoms : List (TupleAtom α))
    (contextAtoms : List (ContextAtom α))
    (unitEdgeAtoms : List (UnitEdgeAtom α))
    {d : Nat} (c : NamedSentenceContext α d) :
    (supportOfObservedAtoms (α := α) K tupleAtoms contextAtoms unitEdgeAtoms).SupportsContext c ↔
      (Sigma.mk d c : ContextAtom α) ∈ contextAtoms := by
  rfl

/-- Unit-edge membership in the assembled support is exactly membership in the
listed unit-edge atoms. -/
theorem supportsUnitEdge_iff
    (K : Finset (Word α))
    (tupleAtoms : List (TupleAtom α))
    (contextAtoms : List (ContextAtom α))
    (unitEdgeAtoms : List (UnitEdgeAtom α))
    {d : Nat} (x y : Tuple α d) :
    (supportOfObservedAtoms (α := α) K tupleAtoms contextAtoms unitEdgeAtoms).SupportsUnitEdge x y ↔
      (Sigma.mk d (x, y) : UnitEdgeAtom α) ∈ unitEdgeAtoms := by
  rfl

end supportOfObservedAtoms

/-- Sample-atom extraction data.

This layer removes another external object from the previous `SampleExtractedRuleLists`
interface: instead of supplying a whole `FiniteLearnerSupport`, it supplies the
three finite atom lists from which the support is assembled.  Safety of listed
unit edges is still a certificate field, because deciding the sample-safe merge
condition is a later algorithmic layer. -/
structure ObservedSampleAtoms
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  f : Nat
  tupleAtoms : List (TupleAtom α)
  contextAtoms : List (ContextAtom α)
  unitEdgeAtoms : List (UnitEdgeAtom α)
  safeEdges :
    (supportOfObservedAtoms (α := α) K tupleAtoms contextAtoms unitEdgeAtoms).ListedUnitEdgesAreSafe obs f
  semanticWorking : G.SemanticWorkingConditions

namespace ObservedSampleAtoms

/-- The finite support assembled from the observed atom lists. -/
def support
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K) : FiniteLearnerSupport α :=
  supportOfObservedAtoms K E.tupleAtoms E.contextAtoms E.unitEdgeAtoms

/-- The assembled support records exactly the input sample. -/
theorem support_sample_eq
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K) :
    E.support.sample = K := by
  rfl

/-- Tuple support is membership in the extracted tuple-atom list. -/
theorem supportsTuple_iff_mem_tupleAtoms
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K)
    {d : Nat} (x : Tuple α d) :
    E.support.SupportsTuple x ↔ (Sigma.mk d x : TupleAtom α) ∈ E.tupleAtoms := by
  rfl

/-- Context support is membership in the extracted context-atom list. -/
theorem supportsContext_iff_mem_contextAtoms
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K)
    {d : Nat} (c : NamedSentenceContext α d) :
    E.support.SupportsContext c ↔ (Sigma.mk d c : ContextAtom α) ∈ E.contextAtoms := by
  rfl

/-- Unit-edge support is membership in the extracted unit-edge atom list. -/
theorem supportsUnitEdge_iff_mem_unitEdgeAtoms
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K)
    {d : Nat} (x y : Tuple α d) :
    E.support.SupportsUnitEdge x y ↔
      (Sigma.mk d (x, y) : UnitEdgeAtom α) ∈ E.unitEdgeAtoms := by
  rfl

/-- A listed tuple atom is supported. -/
theorem supportsTuple_of_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K)
    {a : TupleAtom α}
    (ha : a ∈ E.tupleAtoms) :
    E.support.SupportsTuple a.2 := by
  simpa [support, supportOfObservedAtoms, FiniteLearnerSupport.SupportsTuple] using ha

/-- A listed context atom is supported. -/
theorem supportsContext_of_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K)
    {a : ContextAtom α}
    (ha : a ∈ E.contextAtoms) :
    E.support.SupportsContext a.2 := by
  simpa [support, supportOfObservedAtoms, FiniteLearnerSupport.SupportsContext] using ha

/-- A listed unit-edge atom is supported. -/
theorem supportsUnitEdge_of_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K)
    {a : UnitEdgeAtom α}
    (ha : a ∈ E.unitEdgeAtoms) :
    E.support.SupportsUnitEdge a.2.1 a.2.2 := by
  simpa [support, supportOfObservedAtoms, FiniteLearnerSupport.SupportsUnitEdge] using ha

/-- Safety of the listed unit edges in the assembled support. -/
theorem support_safeEdges
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K) :
    E.support.ListedUnitEdgesAreSafe obs E.f := by
  exact E.safeEdges

/-- Forget observed-atom extraction to the sample-extracted actual rule-list
layer. -/
noncomputable def toSampleExtractedRuleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K) :
    SampleExtractedRuleLists G obs K :=
  { f := E.f
    support := E.support
    sample_eq := by rfl
    safeEdges := E.support_safeEdges
    semanticWorking := E.semanticWorking }

/-- Forget observed-atom extraction to concrete extracted sample data. -/
noncomputable def toConcreteExtractedSampleData
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K) :
    ConcreteExtractedSampleData G obs K :=
  E.toSampleExtractedRuleLists.toConcreteExtractedSampleData

/-- The induced finite learner hypothesis. -/
noncomputable def toFiniteLearnerHypothesis
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K) :
    FiniteLearnerHypothesis α M :=
  E.toSampleExtractedRuleLists.toFiniteLearnerHypothesis

/-- The finite hypothesis uses exactly the input sample. -/
theorem finiteHypothesis_sampleSet
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K) :
    E.toFiniteLearnerHypothesis.sampleSet = K := by
  exact E.toSampleExtractedRuleLists.finiteHypothesis_sampleSet

/-- The actual finite-monoid concrete refined-rule enumeration. -/
noncomputable def concreteRules
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K) :
    FintypeConcreteRuleEnumeration G obs :=
  E.toSampleExtractedRuleLists.concreteRules

/-- The grammar-side concrete rules are the actual finite-monoid refined-rule
lists. -/
theorem concreteRules_eq_actual
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K) :
    E.concreteRules = actualFintypeConcreteRuleEnumeration G obs E.semanticWorking := by
  rfl

/-- The actual refined rule lists contain all ordinary output-type refinements. -/
theorem concrete_containsAllOrdinaryRuleRefinements
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K) :
    E.concreteRules.toFintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact E.toSampleExtractedRuleLists.concrete_containsAllOrdinaryRuleRefinements

/-- The actual refined rule lists are supported by the canonical finite-monoid
rule-enumeration plan. -/
theorem concreteRules_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K) :
    E.concreteRules.grammar.AllRulesSupportedByPlan
      (FiniteRuleEnumerationPlan.ofFintype G obs) := by
  exact E.toSampleExtractedRuleLists.concreteRules_supportedByPlan

/-- A listed unit edge gives unit reachability in the induced finite
hypothesis. -/
theorem listedEdge_reach
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K)
    {d : Nat} {x y : Tuple α d}
    (hxy : E.support.SupportsUnitEdge x y) :
    E.toSampleExtractedRuleLists.UnitReach x y := by
  exact E.toSampleExtractedRuleLists.listedEdge_reach hxy

/-- Approximate distribution induced by observed-atom extraction. -/
noncomputable def ApproxDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K)
    {d : Nat} (x : Tuple α d) : Set (NamedSentenceContext α d) :=
  E.toSampleExtractedRuleLists.ApproxDistribution x

/-- Distributional soundness of observed-atom extraction under positivity and
fixed-substitutability. -/
theorem approxDistribution_sound_for_language
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K)
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
    (E : ObservedSampleAtoms G obs K)
    (A : RefinedNonterminal G M) : Set (Tuple α (G.arity A.base)) :=
  E.toSampleExtractedRuleLists.RefinedTupleLanguage A

/-- Soundness of the actual grammar-side refined tuple language. -/
theorem refinedTupleLanguage_sound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K)
    (A : RefinedNonterminal G M) :
    E.RefinedTupleLanguage A ⊆ OutputTypedTupleLanguage G obs A := by
  intro x hx
  exact E.toSampleExtractedRuleLists.refinedTupleLanguage_sound A hx

/-- Forgetting output types maps the refined tuple language into the base tuple
language. -/
theorem refinedTupleLanguage_forgets_to_base
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K)
    (A : RefinedNonterminal G M) :
    E.RefinedTupleLanguage A ⊆ FIv21.TupleLanguage G A.base := by
  intro x hx
  exact E.toSampleExtractedRuleLists.refinedTupleLanguage_forgets_to_base A hx

/-- Tuples generated by the actual refined rule lists have the advertised output
type. -/
theorem refinedTupleLanguage_has_output_type
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ObservedSampleAtoms G obs K)
    (A : RefinedNonterminal G M)
    {x : Tuple α (G.arity A.base)}
    (hx : x ∈ E.RefinedTupleLanguage A) :
    tupleType obs x = A.outTy := by
  exact E.toSampleExtractedRuleLists.refinedTupleLanguage_has_output_type A hx

end ObservedSampleAtoms

end ObservedSampleAtoms

end FIv21
