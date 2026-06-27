import LeanCfgProject.MCFG.FI_v2_1_FintypeConcreteRuleEnumeration
import LeanCfgProject.MCFG.FI_v2_1_FiniteHypothesisGold

/-!
# FI v2.1 Lean experiment: relative sample-extraction interface

This twenty-ninth layer begins to connect two previously separate strands of
this Lean companion.

* The finite-hypothesis strand packages the sample-derived tuple/context/unit
  edge support and proves distributional soundness of transported contexts.
* The finite refined-grammar strand packages finite output-type refined rule
  enumerations in the finite-monoid case.

The present file does not yet implement the canonical learner.  Instead, it
records the certificate interface that a sample-based extraction procedure
should return relative to a working grammar presentation: a finite learner
hypothesis supported by the sample, together with a concrete finite-monoid
refined-rule enumeration.
-/

namespace FIv21

universe u v w

section RelativeSampleExtraction

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A relative sample-extraction certificate for a fixed working grammar and
fixed finite-monoid observation.

The parameter `K` is the positive sample from which the finite support is meant
to be extracted.  The field `sample_eq` records that the internal finite support
really has `K` as its sample component.  The field `concreteRules` records the
finite output-type refined rule-enumeration certificate on the grammar side.
-/
structure RelativeSampleExtraction
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  f : Nat
  support : FiniteLearnerSupport α
  sample_eq : support.sample = K
  safeEdges : support.ListedUnitEdgesAreSafe obs f
  concreteRules : FintypeConcreteRuleEnumeration G obs

namespace RelativeSampleExtraction

/-- The finite learner hypothesis obtained by forgetting the grammar-side
refined-rule enumeration. -/
def toFiniteLearnerHypothesis
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : RelativeSampleExtraction G obs K) :
    FiniteLearnerHypothesis α M :=
  { f := E.f
    obs := obs
    support := E.support
    safeEdges := E.safeEdges }

/-- The finite learner hypothesis indeed uses the sample `K`. -/
theorem finiteHypothesis_sampleSet
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : RelativeSampleExtraction G obs K) :
    E.toFiniteLearnerHypothesis.sampleSet = K := by
  change E.support.sample = K
  exact E.sample_eq

/-- The approximate distribution induced by the sample-extraction certificate. -/
def ApproxDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : RelativeSampleExtraction G obs K)
    {d : Nat} (x : Tuple α d) : Set (NamedSentenceContext α d) :=
  E.toFiniteLearnerHypothesis.ApproxDistribution x

/-- The unit-reachability relation induced by the sample-extraction certificate. -/
def UnitReach
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : RelativeSampleExtraction G obs K)
    {d : Nat} (x y : Tuple α d) : Prop :=
  E.toFiniteLearnerHypothesis.UnitReach x y

/-- A listed edge in the finite support gives unit reachability. -/
theorem listedEdge_reach
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : RelativeSampleExtraction G obs K)
    {d : Nat} {x y : Tuple α d}
    (hxy : E.support.SupportsUnitEdge x y) :
    E.UnitReach x y := by
  exact E.toFiniteLearnerHypothesis.listedEdge_reach hxy

/-- Distributional soundness of the sample-extracted finite hypothesis. -/
theorem approxDistribution_sound_for_language
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : RelativeSampleExtraction G obs K)
    {L : Set (Word α)}
    (hK : PositiveForLanguage E.toFiniteLearnerHypothesis.sampleSet L)
    (hL : FixedNamedTupleSubstitutable E.f obs L)
    {d : Nat} (x : Tuple α d) :
    E.ApproxDistribution x ⊆ NamedDistribution L x := by
  exact E.toFiniteLearnerHypothesis.approxDistribution_sound_for_language hK hL x

/-- The concrete finite-monoid refined rule enumeration contains all ordinary
output-type rule refinements. -/
theorem concrete_containsAllOrdinaryRuleRefinements
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : RelativeSampleExtraction G obs K) :
    E.concreteRules.toFintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact FintypeConcreteRuleEnumeration.containsAllOrdinaryRuleRefinements E.concreteRules

/-- Tuple language of the grammar-side concrete refined-rule enumeration. -/
noncomputable def RefinedTupleLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : RelativeSampleExtraction G obs K)
    (A : RefinedNonterminal G M) : Set (Tuple α (G.arity A.base)) :=
  E.concreteRules.TupleLanguage A

/-- Soundness of the grammar-side concrete refined-rule enumeration. -/
theorem refinedTupleLanguage_sound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : RelativeSampleExtraction G obs K)
    (A : RefinedNonterminal G M) :
    E.RefinedTupleLanguage A ⊆ OutputTypedTupleLanguage G obs A := by
  intro x hx
  exact FintypeConcreteRuleEnumeration.tupleLanguage_sound E.concreteRules A hx

/-- Forgetting output types maps the grammar-side refined language into the
ordinary tuple language. -/
theorem refinedTupleLanguage_forgets_to_base
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : RelativeSampleExtraction G obs K)
    (A : RefinedNonterminal G M) :
    E.RefinedTupleLanguage A ⊆ FIv21.TupleLanguage G A.base := by
  intro x hx
  exact FintypeConcreteRuleEnumeration.tupleLanguage_forgets_to_base E.concreteRules A hx

/-- Grammar-side refined derivations have the advertised output type. -/
theorem refinedTupleLanguage_has_output_type
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : RelativeSampleExtraction G obs K)
    (A : RefinedNonterminal G M)
    {x : Tuple α (G.arity A.base)}
    (hx : x ∈ E.RefinedTupleLanguage A) :
    tupleType obs x = A.outTy := by
  exact FintypeConcreteRuleEnumeration.tupleLanguage_has_output_type E.concreteRules A hx

end RelativeSampleExtraction

end RelativeSampleExtraction

end FIv21
