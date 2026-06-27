import LeanCfgProject.MCFG.FI_v2_1_ConcreteRuleEnumerationSkeleton

/-!
# FI v2.1 Lean experiment: concrete refined-rule enumeration certificates

This twenty-seventh layer packages the intended output of a concrete refined
rule-list enumerator.

The enumerator is not implemented here.  Instead, the file defines the exact
certificate it must return: finite refined-rule lists, proof that they cover all
ordinary output-type refinements, and the finite plan from which the lists are
regarded as produced.  Once this certificate is present, all previously proved
finite refined-grammar soundness theorems apply.
-/

namespace FIv21

universe u v w

section ConcreteRuleEnumerationCertificate

variable {N : Type w} {α : Type u}
variable {M : Type v} [Monoid M]

/-- A concrete refined-rule enumeration certificate relative to a finite plan.

The field `coversAll` is the essential correctness obligation for a future
`List.bind` implementation: every ordinary terminal, binary, and start rule
refinement must occur in the explicit finite lists. -/
structure ConcreteRefinedRuleEnumeration
    {G : WorkingMCFG N α} {obs : α → M}
    (P : FiniteRuleEnumerationPlan G obs) where
  grammar : FiniteOutputTypeRefinedGrammar G obs
  coversAll : grammar.CoversAllOrdinaryRuleRefinements

namespace ConcreteRefinedRuleEnumeration

/-- The listed refined rules are automatically supported by the finite plan. -/
theorem allRulesSupportedByPlan
    {G : WorkingMCFG N α} {obs : α → M}
    {P : FiniteRuleEnumerationPlan G obs}
    (C : ConcreteRefinedRuleEnumeration P) :
    C.grammar.AllRulesSupportedByPlan P := by
  exact C.grammar.allRulesSupportedByPlan P

/-- Convert a concrete enumeration certificate into the finite refined-grammar
certificate used by the semantic layers. -/
def toFiniteOutputTypeRefinementCertificate
    {G : WorkingMCFG N α} {obs : α → M}
    {P : FiniteRuleEnumerationPlan G obs}
    (C : ConcreteRefinedRuleEnumeration P) :
    FiniteOutputTypeRefinementCertificate G obs :=
  { grammar := C.grammar
    coversAll := C.coversAll }

/-- Convert a concrete enumeration certificate into a bundled output-type
enumeration certificate, using the output-type lists of the plan. -/
def toFiniteOutputTypeEnumerationCertificate
    {G : WorkingMCFG N α} {obs : α → M}
    {P : FiniteRuleEnumerationPlan G obs}
    (C : ConcreteRefinedRuleEnumeration P) :
    FiniteOutputTypeEnumerationCertificate G obs :=
  FiniteOutputTypeEnumerationCertificate.ofCompleteEnumeration
    P.outputTypes C.toFiniteOutputTypeRefinementCertificate

/-- The associated predicate-style refined grammar. -/
def toOutputTypeRefinedGrammar
    {G : WorkingMCFG N α} {obs : α → M}
    {P : FiniteRuleEnumerationPlan G obs}
    (C : ConcreteRefinedRuleEnumeration P) :
    OutputTypeRefinedGrammar G obs :=
  C.toFiniteOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar

/-- Concrete enumerations contain all ordinary output-type rule refinements. -/
theorem containsAllOrdinaryRuleRefinements
    {G : WorkingMCFG N α} {obs : α → M}
    {P : FiniteRuleEnumerationPlan G obs}
    (C : ConcreteRefinedRuleEnumeration P) :
    C.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact C.toFiniteOutputTypeRefinementCertificate.containsAllOrdinaryRuleRefinements

/-- Tuple language of the concrete refined-rule enumeration. -/
def TupleLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    {P : FiniteRuleEnumerationPlan G obs}
    (C : ConcreteRefinedRuleEnumeration P)
    (A : RefinedNonterminal G M) : Set (Tuple α (G.arity A.base)) :=
  C.toFiniteOutputTypeRefinementCertificate.TupleLanguage A

/-- Soundness of a concrete refined-rule enumeration. -/
theorem tupleLanguage_sound
    {G : WorkingMCFG N α} {obs : α → M}
    {P : FiniteRuleEnumerationPlan G obs}
    (C : ConcreteRefinedRuleEnumeration P)
    (A : RefinedNonterminal G M) :
    C.TupleLanguage A ⊆ OutputTypedTupleLanguage G obs A := by
  intro x hx
  exact C.toFiniteOutputTypeRefinementCertificate.tupleLanguage_sound A hx

/-- Forgetting output types maps concrete refined derivations into the base
tuple language. -/
theorem tupleLanguage_forgets_to_base
    {G : WorkingMCFG N α} {obs : α → M}
    {P : FiniteRuleEnumerationPlan G obs}
    (C : ConcreteRefinedRuleEnumeration P)
    (A : RefinedNonterminal G M) :
    C.TupleLanguage A ⊆ FIv21.TupleLanguage G A.base := by
  intro x hx
  exact C.toFiniteOutputTypeRefinementCertificate.tupleLanguage_forgets_to_base A hx

/-- Concrete refined derivations have the advertised output type. -/
theorem tupleLanguage_has_output_type
    {G : WorkingMCFG N α} {obs : α → M}
    {P : FiniteRuleEnumerationPlan G obs}
    (C : ConcreteRefinedRuleEnumeration P)
    (A : RefinedNonterminal G M)
    {x : Tuple α (G.arity A.base)}
    (hx : x ∈ C.TupleLanguage A) :
    tupleType obs x = A.outTy := by
  exact C.toFiniteOutputTypeRefinementCertificate.tupleLanguage_has_output_type A hx

end ConcreteRefinedRuleEnumeration

end ConcreteRuleEnumerationCertificate

end FIv21
