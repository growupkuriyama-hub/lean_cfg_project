import LeanCfgProject.MCFG.FI_v2_1_RelativeSampleExtractionGold

/-!
# FI v2.1 Lean experiment: concrete extracted sample data

This thirty-second layer repackages the relative sample-extraction interface in
an implementation-facing form.

The previous files defined `RelativeSampleExtraction` directly.  This file
introduces a more concrete certificate shape: a finite support extracted from a
sample, a proof that the support really uses that sample, a sample-safe unit-edge
certificate, and a finite-monoid concrete refined-rule enumeration.  The file
then shows that such concrete extracted data immediately induces the relative
sample-extraction certificate already connected to exactness and Gold-style
stabilization.
-/

namespace FIv21

universe u v w

section ConcreteExtractedSampleData

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Concrete extracted data from a finite positive sample, relative to a working
MCFG presentation and a finite-monoid observation.

This is intentionally still a certificate interface rather than an algorithm:
a later list-producing extractor should construct the `support` and
`concreteRules` fields from the sample. -/
structure ConcreteExtractedSampleData
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  f : Nat
  support : FiniteLearnerSupport α
  sample_eq : support.sample = K
  safeEdges : support.ListedUnitEdgesAreSafe obs f
  concreteRules : FintypeConcreteRuleEnumeration G obs

namespace ConcreteExtractedSampleData

/-- Forget the concrete data to the already-checked relative extraction
interface. -/
def toRelativeSampleExtraction
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) :
    RelativeSampleExtraction G obs K :=
  { f := E.f
    support := E.support
    sample_eq := E.sample_eq
    safeEdges := E.safeEdges
    concreteRules := E.concreteRules }

/-- The finite learner hypothesis determined by the extracted data. -/
def toFiniteLearnerHypothesis
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) :
    FiniteLearnerHypothesis α M :=
  E.toRelativeSampleExtraction.toFiniteLearnerHypothesis

/-- The finite hypothesis uses exactly the external sample `K`. -/
theorem finiteHypothesis_sampleSet
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) :
    E.toFiniteLearnerHypothesis.sampleSet = K := by
  exact E.toRelativeSampleExtraction.finiteHypothesis_sampleSet

/-- Approximate distribution induced by concrete extracted data. -/
def ApproxDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K)
    {d : Nat} (x : Tuple α d) : Set (NamedSentenceContext α d) :=
  E.toRelativeSampleExtraction.ApproxDistribution x

/-- Unit reachability induced by concrete extracted data. -/
def UnitReach
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K)
    {d : Nat} (x y : Tuple α d) : Prop :=
  E.toRelativeSampleExtraction.UnitReach x y

/-- A listed unit edge gives unit reachability in the extracted data. -/
theorem listedEdge_reach
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K)
    {d : Nat} {x y : Tuple α d}
    (hxy : E.support.SupportsUnitEdge x y) :
    E.UnitReach x y := by
  exact E.toRelativeSampleExtraction.listedEdge_reach hxy

/-- Distributional soundness of the finite hypothesis encoded by concrete
extracted data. -/
theorem approxDistribution_sound_for_language
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K)
    {L : Set (Word α)}
    (hK : PositiveForLanguage E.toFiniteLearnerHypothesis.sampleSet L)
    (hL : FixedNamedTupleSubstitutable E.f obs L)
    {d : Nat} (x : Tuple α d) :
    E.ApproxDistribution x ⊆ NamedDistribution L x := by
  exact E.toRelativeSampleExtraction.approxDistribution_sound_for_language
    hK hL x

/-- Concrete refined-rule enumeration associated with the extracted data. -/
def concreteRulesCertificate
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) :
    FintypeConcreteRuleEnumeration G obs :=
  E.concreteRules

/-- The associated concrete refined grammar contains all ordinary output-type
rule refinements. -/
theorem concrete_containsAllOrdinaryRuleRefinements
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) :
    E.concreteRules.toFintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact E.toRelativeSampleExtraction.concrete_containsAllOrdinaryRuleRefinements

/-- Refined tuple language carried by the grammar-side concrete enumeration. -/
noncomputable def RefinedTupleLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K)
    (A : RefinedNonterminal G M) : Set (Tuple α (G.arity A.base)) :=
  E.toRelativeSampleExtraction.RefinedTupleLanguage A

/-- Soundness of the grammar-side concrete refined language. -/
theorem refinedTupleLanguage_sound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K)
    (A : RefinedNonterminal G M) :
    E.RefinedTupleLanguage A ⊆ OutputTypedTupleLanguage G obs A := by
  intro x hx
  exact E.toRelativeSampleExtraction.refinedTupleLanguage_sound A hx

/-- Forgetting output types maps the grammar-side refined language into the base
tuple language. -/
theorem refinedTupleLanguage_forgets_to_base
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K)
    (A : RefinedNonterminal G M) :
    E.RefinedTupleLanguage A ⊆ FIv21.TupleLanguage G A.base := by
  intro x hx
  exact E.toRelativeSampleExtraction.refinedTupleLanguage_forgets_to_base A hx

/-- Grammar-side refined derivations have the advertised output type. -/
theorem refinedTupleLanguage_has_output_type
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K)
    (A : RefinedNonterminal G M)
    {x : Tuple α (G.arity A.base)}
    (hx : x ∈ E.RefinedTupleLanguage A) :
    tupleType obs x = A.outTy := by
  exact E.toRelativeSampleExtraction.refinedTupleLanguage_has_output_type A hx

end ConcreteExtractedSampleData

end ConcreteExtractedSampleData

end FIv21
