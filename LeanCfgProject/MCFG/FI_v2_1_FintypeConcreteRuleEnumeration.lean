import LeanCfgProject.MCFG.FI_v2_1_ConcreteRuleEnumerationCertificate

/-!
# FI v2.1 Lean experiment: concrete rule enumeration in the finite-monoid case

This twenty-eighth layer specializes the concrete refined-rule enumeration
certificate to the canonical finite-monoid rule-enumeration plan.

It is still certificate-oriented: the actual nested list construction of all
refined rules is left to a later file.  The point of this layer is to connect
such a future concrete construction with the `[Fintype M]` output-type
enumeration already checked by CI.
-/

namespace FIv21

universe u v w

section FintypeConcreteRuleEnumeration

variable {N : Type w} {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- A concrete refined-rule enumeration for the canonical finite-monoid plan. -/
structure FintypeConcreteRuleEnumeration
    (G : WorkingMCFG N α) (obs : α → M) where
  concrete : ConcreteRefinedRuleEnumeration
    (FiniteRuleEnumerationPlan.ofFintype G obs)

namespace FintypeConcreteRuleEnumeration

/-- The finite rule-enumeration plan underlying a finite-monoid concrete
enumeration. -/
noncomputable def plan
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeConcreteRuleEnumeration G obs) :
    FiniteRuleEnumerationPlan G obs :=
  FiniteRuleEnumerationPlan.ofFintype G obs

/-- The finite refined grammar listed by the concrete enumeration. -/
def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeConcreteRuleEnumeration G obs) :
    FiniteOutputTypeRefinedGrammar G obs :=
  C.concrete.grammar

/-- Convert to the previously defined finite-monoid output-type refinement
certificate. -/
noncomputable def toFintypeOutputTypeRefinementCertificate
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeConcreteRuleEnumeration G obs) :
    FintypeOutputTypeRefinementCertificate G obs :=
  { refinement := C.concrete.toFiniteOutputTypeRefinementCertificate }

/-- Convert to the bundled finite output-type enumeration certificate. -/
noncomputable def toFiniteOutputTypeEnumerationCertificate
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeConcreteRuleEnumeration G obs) :
    FiniteOutputTypeEnumerationCertificate G obs :=
  C.toFintypeOutputTypeRefinementCertificate.toEnumerationCertificate

/-- The associated predicate-style refined grammar contains all ordinary rule
refinements. -/
theorem containsAllOrdinaryRuleRefinements
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeConcreteRuleEnumeration G obs) :
    C.toFintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact C.toFintypeOutputTypeRefinementCertificate.containsAllOrdinaryRuleRefinements

/-- Every listed refined rule is supported by the canonical finite-monoid plan. -/
theorem allRulesSupportedByPlan
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeConcreteRuleEnumeration G obs) :
    C.grammar.AllRulesSupportedByPlan (FiniteRuleEnumerationPlan.ofFintype G obs) := by
  exact C.concrete.allRulesSupportedByPlan

/-- Tuple language of a finite-monoid concrete refined-rule enumeration. -/
noncomputable def TupleLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeConcreteRuleEnumeration G obs)
    (A : RefinedNonterminal G M) : Set (Tuple α (G.arity A.base)) :=
  C.toFintypeOutputTypeRefinementCertificate.TupleLanguage A

/-- Soundness of a finite-monoid concrete refined-rule enumeration. -/
theorem tupleLanguage_sound
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeConcreteRuleEnumeration G obs)
    (A : RefinedNonterminal G M) :
    C.TupleLanguage A ⊆ OutputTypedTupleLanguage G obs A := by
  intro x hx
  exact C.toFintypeOutputTypeRefinementCertificate.tupleLanguage_sound A hx

/-- Forgetting output types maps the concrete finite-monoid refined language
into the ordinary base tuple language. -/
theorem tupleLanguage_forgets_to_base
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeConcreteRuleEnumeration G obs)
    (A : RefinedNonterminal G M) :
    C.TupleLanguage A ⊆ FIv21.TupleLanguage G A.base := by
  intro x hx
  exact C.toFintypeOutputTypeRefinementCertificate.tupleLanguage_forgets_to_base A hx

/-- Generated tuples have the advertised output type. -/
theorem tupleLanguage_has_output_type
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeConcreteRuleEnumeration G obs)
    (A : RefinedNonterminal G M)
    {x : Tuple α (G.arity A.base)}
    (hx : x ∈ C.TupleLanguage A) :
    tupleType obs x = A.outTy := by
  exact C.toFintypeOutputTypeRefinementCertificate.tupleLanguage_has_output_type A hx

end FintypeConcreteRuleEnumeration

end FintypeConcreteRuleEnumeration

end FIv21
