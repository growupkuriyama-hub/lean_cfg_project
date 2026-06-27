import LeanCfgProject.MCFG.FI_v2_1_FintypeOutputEnumeration

/-!
# FI v2.1 Lean experiment: bundled finite-monoid enumeration certificates

This twenty-second layer packages the previous construction into the form used
by the finite refined-grammar certificates.

A `FiniteOutputTypeRefinementCertificate` already contains explicit finite
lists of refined rules and a proof that those lists cover all ordinary rule
refinements.  When the observation monoid is a `Fintype`, the preceding layer
constructs a complete finite enumeration of all output-type vectors.  This file
bundles those two ingredients and re-exports the main soundness statements.
-/

namespace FIv21

universe u v w

section FintypeEnumerationCertificate

variable {N : Type w} {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- A finite-monoid output-type refinement certificate.

The only nontrivial data is the finite refined-grammar certificate.  The
output-type enumeration itself is supplied canonically from `[Fintype M]`. -/
structure FintypeOutputTypeRefinementCertificate
    (G : WorkingMCFG N α) (obs : α → M) where
  refinement : FiniteOutputTypeRefinementCertificate G obs

namespace FintypeOutputTypeRefinementCertificate

/-- The complete output-type enumeration attached to the finite monoid. -/
noncomputable def outputTypes
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeOutputTypeRefinementCertificate G obs) :
    OutputTypeEnumeration M :=
  OutputTypeEnumeration.ofFintype M

/-- The finite refined grammar contained in the certificate. -/
def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeOutputTypeRefinementCertificate G obs) :
    FiniteOutputTypeRefinedGrammar G obs :=
  C.refinement.grammar

/-- Convert to the previous bundled finite enumeration certificate. -/
noncomputable def toEnumerationCertificate
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeOutputTypeRefinementCertificate G obs) :
    FiniteOutputTypeEnumerationCertificate G obs :=
  FiniteOutputTypeEnumerationCertificate.ofCompleteEnumeration
    (OutputTypeEnumeration.ofFintype M) C.refinement

/-- Convert to the predicate-style output-type refined grammar. -/
noncomputable def toOutputTypeRefinedGrammar
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeOutputTypeRefinementCertificate G obs) :
    OutputTypeRefinedGrammar G obs :=
  C.toEnumerationCertificate.toOutputTypeRefinedGrammar

/-- The associated predicate-style refined grammar contains all ordinary rule
refinements. -/
theorem containsAllOrdinaryRuleRefinements
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeOutputTypeRefinementCertificate G obs) :
    C.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact C.toEnumerationCertificate.containsAllOrdinaryRuleRefinements

/-- Listed binary rules have child type choices listed by the `Fintype` output
enumeration. -/
theorem listedBinaryRule_supported
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeOutputTypeRefinementCertificate G obs)
    (ρ : RefinedBinaryRule G obs)
    (hρ : ρ ∈ C.grammar.binaryRules) :
    C.outputTypes.SupportsRefinedBinaryRule ρ := by
  exact C.toEnumerationCertificate.listedBinaryRule_supported ρ hρ

/-- Listed start rules have child type choices listed by the `Fintype` output
enumeration. -/
theorem listedStartRule_supported
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeOutputTypeRefinementCertificate G obs)
    (ρ : RefinedStartRule G obs)
    (hρ : ρ ∈ C.grammar.startRules) :
    C.outputTypes.SupportsRefinedStartRule ρ := by
  exact C.toEnumerationCertificate.listedStartRule_supported ρ hρ

/-- Every refined nonterminal output type is listed by the `Fintype` output
enumeration. -/
theorem refinedNonterminal_supported
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeOutputTypeRefinementCertificate G obs)
    (A : RefinedNonterminal G M) :
    A.outTy ∈ C.outputTypes.types (G.arity A.base) := by
  exact C.toEnumerationCertificate.refinedNonterminal_supported A

/-- Tuple language of the finite-monoid output-type refinement certificate. -/
noncomputable def TupleLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeOutputTypeRefinementCertificate G obs)
    (A : RefinedNonterminal G M) : Set (Tuple α (G.arity A.base)) :=
  C.toEnumerationCertificate.TupleLanguage A

/-- Soundness of the finite-monoid certificate. -/
theorem tupleLanguage_sound
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeOutputTypeRefinementCertificate G obs)
    (A : RefinedNonterminal G M) :
    C.TupleLanguage A ⊆ OutputTypedTupleLanguage G obs A := by
  intro x hx
  exact C.toEnumerationCertificate.tupleLanguage_sound A hx

/-- Forgetting output types maps generated tuples into the ordinary base tuple
language. -/
theorem tupleLanguage_forgets_to_base
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeOutputTypeRefinementCertificate G obs)
    (A : RefinedNonterminal G M) :
    C.TupleLanguage A ⊆ FIv21.TupleLanguage G A.base := by
  intro x hx
  exact C.toEnumerationCertificate.tupleLanguage_forgets_to_base A hx

/-- Generated tuples have the output type advertised by their refined
nonterminal. -/
theorem tupleLanguage_has_output_type
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FintypeOutputTypeRefinementCertificate G obs)
    (A : RefinedNonterminal G M)
    {x : Tuple α (G.arity A.base)}
    (hx : x ∈ C.TupleLanguage A) :
    tupleType obs x = A.outTy := by
  exact C.toEnumerationCertificate.tupleLanguage_has_output_type A hx

end FintypeOutputTypeRefinementCertificate

end FintypeEnumerationCertificate

end FIv21
