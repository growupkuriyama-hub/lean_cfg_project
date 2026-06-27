import LeanCfgProject.MCFG.FI_v2_1_ParameterProfileInterface

/-!
# FI v2.1 Lean experiment: exact canonical packages with parameter profiles

This sixty-sixth layer bundles exact canonical learner grammar packages with the
parameter-profile interface from the previous file.

The semantic content is inherited from `CanonicalLearnerGrammarExactWithPolynomialBounds`.
The new information is only the named parameter profile used by later complexity
and size summaries.
-/

namespace FIv21

universe u v w

noncomputable section

section ParameterProfileExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact canonical learner grammar package equipped with a parameter profile. -/
structure CanonicalLearnerGrammarExactWithParameterProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  exactWithPolynomialBounds : CanonicalLearnerGrammarExactWithPolynomialBounds P
  profile : CanonicalParameterProfile P

namespace CanonicalLearnerGrammarExactWithParameterProfile

/-- Equip an exact-with-polynomial-bounds package with the tautological parameter
profile. -/
def ofExactWithPolynomialBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPolynomialBounds P) :
    CanonicalLearnerGrammarExactWithParameterProfile P :=
  { exactWithPolynomialBounds := C
    profile := CanonicalParameterProfile.trivialForPackage P }

/-- Equip an exact canonical package with tautological bounds and parameters. -/
def ofExactPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactForGrammar P) :
    CanonicalLearnerGrammarExactWithParameterProfile P :=
  ofExactWithPolynomialBounds
    (CanonicalLearnerGrammarExactWithPolynomialBounds.ofExactPackage C)

/-- Forget to the exact-with-polynomial-bounds certificate. -/
def toExactWithPolynomialBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithParameterProfile P) :
    CanonicalLearnerGrammarExactWithPolynomialBounds P :=
  C.exactWithPolynomialBounds

/-- Forget to the parameter profile. -/
def toParameterProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithParameterProfile P) :
    CanonicalParameterProfile P :=
  C.profile

/-- Exact equality of approximate and target named-context distributions. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithParameterProfile P)
    {d : Nat} (x : Tuple α d) :
    P.ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact C.exactWithPolynomialBounds.approxDistribution_exact x

/-- Learner-side generation of a sampled word. -/
theorem sample_word_generated_by_learner
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithParameterProfile P)
    (w : Word α) (hw : w ∈ K) :
    w ∈ P.wordLanguage := by
  exact C.exactWithPolynomialBounds.sample_word_generated_by_learner w hw

/-- Target-side start derivation witness for a sampled word. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithParameterProfile P)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact C.exactWithPolynomialBounds.sample_word_start_derives w hw

/-- Rule-list coverage inherited from the exact package. -/
theorem refinedRuleLists_coverAll
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithParameterProfile P) :
    P.finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact C.exactWithPolynomialBounds.refinedRuleLists_coverAll

/-- Rule-list plan support inherited from the exact package. -/
theorem refinedRuleLists_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithParameterProfile P) :
    P.finiteRefinedGrammar.AllRulesSupportedByPlan P.ruleEnumerationPlan := by
  exact C.exactWithPolynomialBounds.refinedRuleLists_supportedByPlan

/-- The refined-rule count is bounded by the profile's total enumeration bound. -/
theorem refinedRuleCount_le_totalEnumerationBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithParameterProfile P) :
    P.refinedRuleCount ≤ C.profile.totalEnumerationBound := by
  exact C.profile.refinedRuleCount_le_totalEnumerationBound

/-- The profile records the size of the finite sample. -/
theorem sampleSize_eq_card
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithParameterProfile P) :
    C.profile.sampleSize = K.card := by
  exact C.profile.sampleSize_eq_card

/-- The profile records the finite cardinality of the observation monoid. -/
theorem monoidCardinality_eq_fintypeCard
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithParameterProfile P) :
    C.profile.monoidCardinality = Fintype.card M := by
  exact C.profile.monoidCardinality_eq_fintypeCard

/-- The profile's total bound carries an abstract polynomial witness. -/
def totalPolynomialWitness
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithParameterProfile P) :
    PolynomialBoundWitness C.profile.polynomialBounds.bounds.totalBound :=
  C.profile.totalPolynomialWitness

end CanonicalLearnerGrammarExactWithParameterProfile

end ParameterProfileExact

end

end FIv21
