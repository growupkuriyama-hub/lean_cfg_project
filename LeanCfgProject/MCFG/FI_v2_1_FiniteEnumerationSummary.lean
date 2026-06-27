import LeanCfgProject.MCFG.FI_v2_1_FiniteOutputTypeEnumeration

/-!
# FI v2.1 Lean experiment: finite enumeration summary certificates

This twentieth layer bundles two independent finite ingredients:

* a complete finite enumeration of output-type vectors, and
* a finite output-type refined grammar certificate.

The result is a compact certificate object saying that the output-type refined
skeleton has been represented by finite lists and that all output-type choices
in those lists are supported by the finite output-type enumeration.  This is
still not the full algorithm constructing the lists, but it is the exact target
specification for that algorithm.
-/

namespace FIv21

universe u v w

section FiniteEnumerationSummary

variable {N : Type w} {α : Type u}
variable {M : Type v} [Monoid M]

/-- A finite refined grammar whose listed type choices are supported by a given
output-type enumeration. -/
def FiniteRefinedGrammarSupportedByEnumeration
    {G : WorkingMCFG N α} {obs : α → M}
    (E : OutputTypeEnumeration M)
    (C : FiniteOutputTypeRefinementCertificate G obs) : Prop :=
  (∀ ρ : RefinedBinaryRule G obs,
      ρ ∈ C.grammar.binaryRules →
        E.SupportsRefinedBinaryRule ρ) ∧
  (∀ ρ : RefinedStartRule G obs,
      ρ ∈ C.grammar.startRules →
        E.SupportsRefinedStartRule ρ) ∧
  (∀ A : RefinedNonterminal G M,
      A.outTy ∈ E.types (G.arity A.base))

/-- Completeness of an output-type enumeration automatically supports every
listed type choice in any finite refined-grammar certificate. -/
theorem finiteRefinedGrammar_supported_by_completeEnumeration
    {G : WorkingMCFG N α} {obs : α → M}
    (E : OutputTypeEnumeration M)
    (C : FiniteOutputTypeRefinementCertificate G obs) :
    FiniteRefinedGrammarSupportedByEnumeration E C := by
  constructor
  · intro ρ hρ
    exact E.supports_refinedBinaryRule ρ
  constructor
  · intro ρ hρ
    exact E.supports_refinedStartRule ρ
  · intro A
    exact E.complete A.outTy

/-- A bundled finite enumeration certificate for output-type refinement. -/
structure FiniteOutputTypeEnumerationCertificate
    (G : WorkingMCFG N α) (obs : α → M) where
  outputTypes : OutputTypeEnumeration M
  refinement : FiniteOutputTypeRefinementCertificate G obs
  supported : FiniteRefinedGrammarSupportedByEnumeration outputTypes refinement

namespace FiniteOutputTypeEnumerationCertificate

/-- Build the bundled certificate from any complete output-type enumeration and
any finite output-type refinement certificate. -/
def ofCompleteEnumeration
    {G : WorkingMCFG N α} {obs : α → M}
    (E : OutputTypeEnumeration M)
    (C : FiniteOutputTypeRefinementCertificate G obs) :
    FiniteOutputTypeEnumerationCertificate G obs :=
  { outputTypes := E
    refinement := C
    supported := finiteRefinedGrammar_supported_by_completeEnumeration E C }

/-- The underlying finite refined grammar. -/
def grammar
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FiniteOutputTypeEnumerationCertificate G obs) :
    FiniteOutputTypeRefinedGrammar G obs :=
  C.refinement.grammar

/-- The associated predicate-style refined grammar. -/
def toOutputTypeRefinedGrammar
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FiniteOutputTypeEnumerationCertificate G obs) :
    OutputTypeRefinedGrammar G obs :=
  C.refinement.toOutputTypeRefinedGrammar

/-- The bundled certificate still contains every ordinary rule refinement. -/
theorem containsAllOrdinaryRuleRefinements
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FiniteOutputTypeEnumerationCertificate G obs) :
    C.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements :=
  C.refinement.containsAllOrdinaryRuleRefinements

/-- Listed binary rules have child output types supported by the enumeration. -/
theorem listedBinaryRule_supported
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FiniteOutputTypeEnumerationCertificate G obs)
    (ρ : RefinedBinaryRule G obs)
    (hρ : ρ ∈ C.grammar.binaryRules) :
    C.outputTypes.SupportsRefinedBinaryRule ρ :=
  C.supported.1 ρ hρ

/-- Listed start rules have child output types supported by the enumeration. -/
theorem listedStartRule_supported
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FiniteOutputTypeEnumerationCertificate G obs)
    (ρ : RefinedStartRule G obs)
    (hρ : ρ ∈ C.grammar.startRules) :
    C.outputTypes.SupportsRefinedStartRule ρ :=
  C.supported.2.1 ρ hρ

/-- Every refined nonterminal output type is listed by the bundled enumeration. -/
theorem refinedNonterminal_supported
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FiniteOutputTypeEnumerationCertificate G obs)
    (A : RefinedNonterminal G M) :
    A.outTy ∈ C.outputTypes.types (G.arity A.base) :=
  C.supported.2.2 A

/-- Tuple language of the bundled finite refined grammar. -/
def TupleLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FiniteOutputTypeEnumerationCertificate G obs)
    (A : RefinedNonterminal G M) : Set (Tuple α (G.arity A.base)) :=
  C.refinement.TupleLanguage A

/-- Soundness follows from the underlying finite refinement certificate. -/
theorem tupleLanguage_sound
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FiniteOutputTypeEnumerationCertificate G obs)
    (A : RefinedNonterminal G M) :
    C.TupleLanguage A ⊆ OutputTypedTupleLanguage G obs A := by
  intro x hx
  exact C.refinement.tupleLanguage_sound A hx

/-- Forgetting output types maps the bundled finite refined language into the
ordinary base tuple language. -/
theorem tupleLanguage_forgets_to_base
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FiniteOutputTypeEnumerationCertificate G obs)
    (A : RefinedNonterminal G M) :
    C.TupleLanguage A ⊆ FIv21.TupleLanguage G A.base := by
  intro x hx
  exact C.refinement.tupleLanguage_forgets_to_base A hx

/-- Every tuple generated at a refined nonterminal has the advertised output
vector. -/
theorem tupleLanguage_has_output_type
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FiniteOutputTypeEnumerationCertificate G obs)
    (A : RefinedNonterminal G M)
    {x : Tuple α (G.arity A.base)}
    (hx : x ∈ C.TupleLanguage A) :
    tupleType obs x = A.outTy := by
  exact C.refinement.tupleLanguage_has_output_type A hx

end FiniteOutputTypeEnumerationCertificate

end FiniteEnumerationSummary

end FIv21
