import LeanCfgProject.MCFG.FI_v2_1_PolynomialBoundInterface

/-!
# FI v2.1 Lean experiment: exact canonical packages with polynomial-bound witnesses

This sixty-third layer combines exact canonical learner grammar packages,
enumeration bounds, and abstract polynomial-bound witnesses.

The layer is intentionally semantic-light: exactness is inherited from the
existing canonical package certificates, while the polynomial information is a
separate opaque witness attached to the enumeration bounds.
-/

namespace FIv21

universe u v w

noncomputable section

section PolynomialBoundExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact canonical learner grammar package equipped with abstract
polynomial-bound witnesses for its enumeration bounds. -/
structure CanonicalLearnerGrammarExactWithPolynomialBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  exactWithBounds : CanonicalLearnerGrammarExactWithEnumerationBounds P
  polynomialBounds : CanonicalPolynomialBounds P

namespace CanonicalLearnerGrammarExactWithPolynomialBounds

/-- Equip an exact-with-enumeration-bounds package with tautological polynomial
witnesses. -/
def ofExactWithEnumerationBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithEnumerationBounds P) :
    CanonicalLearnerGrammarExactWithPolynomialBounds P :=
  { exactWithBounds := C
    polynomialBounds := CanonicalPolynomialBounds.trivialForPackage P }

/-- Equip an exact canonical package with exact bounds and tautological
polynomial witnesses. -/
def ofExactPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactForGrammar P) :
    CanonicalLearnerGrammarExactWithPolynomialBounds P :=
  ofExactWithEnumerationBounds
    (CanonicalLearnerGrammarExactWithEnumerationBounds.ofExactPackage C)

/-- Forget to the exact-with-enumeration-bounds certificate. -/
def toExactWithEnumerationBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPolynomialBounds P) :
    CanonicalLearnerGrammarExactWithEnumerationBounds P :=
  C.exactWithBounds

/-- Forget to the polynomial-bound certificate. -/
def toPolynomialBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPolynomialBounds P) :
    CanonicalPolynomialBounds P :=
  C.polynomialBounds

/-- Exact equality of approximate and target named-context distributions. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPolynomialBounds P)
    {d : Nat} (x : Tuple α d) :
    P.ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact C.exactWithBounds.approxDistribution_exact x

/-- Learner-side generation of a sampled word. -/
theorem sample_word_generated_by_learner
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPolynomialBounds P)
    (w : Word α) (hw : w ∈ K) :
    w ∈ P.wordLanguage := by
  exact C.exactWithBounds.sample_word_generated_by_learner w hw

/-- Target-side start derivation witness for a sampled word. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPolynomialBounds P)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact C.exactWithBounds.sample_word_start_derives w hw

/-- Rule-list coverage inherited from the exact package. -/
theorem refinedRuleLists_coverAll
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPolynomialBounds P) :
    P.finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact C.exactWithBounds.refinedRuleLists_coverAll

/-- Rule-list plan support inherited from the exact package. -/
theorem refinedRuleLists_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPolynomialBounds P) :
    P.finiteRefinedGrammar.AllRulesSupportedByPlan P.ruleEnumerationPlan := by
  exact C.exactWithBounds.refinedRuleLists_supportedByPlan

/-- The total refined-rule count is bounded by a polynomially witnessed bound. -/
theorem refinedRuleCount_le_polynomialBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPolynomialBounds P) :
    P.refinedRuleCount ≤ C.polynomialBounds.bounds.totalBound := by
  exact C.polynomialBounds.refinedRuleCount_le_polynomialBound

/-- The total bound carries an abstract polynomial witness. -/
def totalPolynomialWitness
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPolynomialBounds P) :
    PolynomialBoundWitness C.polynomialBounds.bounds.totalBound :=
  C.polynomialBounds.totalPolynomialWitness

end CanonicalLearnerGrammarExactWithPolynomialBounds

end PolynomialBoundExact

end

end FIv21
