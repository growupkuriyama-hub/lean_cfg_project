import LeanCfgProject.MCFG.FI_v2_1_ShapeProfileInterface

/-!
# FI v2.1 Lean experiment: exact canonical packages with shape profiles

This sixty-ninth layer bundles exact canonical learner grammar packages with the
shape-profile interface.

The semantic exactness theorem is inherited from the parameter-profile layer.
The new data is the placeholder bounded-shape certificate that will later host
bounded-spine or bounded-derivation-shape hypotheses.
-/

namespace FIv21

universe u v w

noncomputable section

section ShapeProfileExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact canonical learner grammar package equipped with a shape profile. -/
structure CanonicalLearnerGrammarExactWithShapeProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  exactWithParameterProfile : CanonicalLearnerGrammarExactWithParameterProfile P
  shapeProfile : CanonicalShapeProfile P
  parameterProfile_agrees :
    shapeProfile.parameterProfile = exactWithParameterProfile.profile

namespace CanonicalLearnerGrammarExactWithShapeProfile

/-- Equip an exact-with-parameter-profile package with the tautological shape
profile over its parameter profile. -/
def ofExactWithParameterProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithParameterProfile P) :
    CanonicalLearnerGrammarExactWithShapeProfile P :=
  { exactWithParameterProfile := C
    shapeProfile := CanonicalShapeProfile.trivialForProfile C.profile
    parameterProfile_agrees := rfl }

/-- Equip an exact canonical package with tautological parameters and shape
bounds. -/
def ofExactPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactForGrammar P) :
    CanonicalLearnerGrammarExactWithShapeProfile P :=
  ofExactWithParameterProfile
    (CanonicalLearnerGrammarExactWithParameterProfile.ofExactPackage C)

/-- Forget to the exact-with-parameter-profile certificate. -/
def toExactWithParameterProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithShapeProfile P) :
    CanonicalLearnerGrammarExactWithParameterProfile P :=
  C.exactWithParameterProfile

/-- Forget to the shape profile. -/
def toShapeProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithShapeProfile P) :
    CanonicalShapeProfile P :=
  C.shapeProfile

/-- Exact equality of approximate and target named-context distributions. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithShapeProfile P)
    {d : Nat} (x : Tuple α d) :
    P.ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact C.exactWithParameterProfile.approxDistribution_exact x

/-- Learner-side generation of a sampled word. -/
theorem sample_word_generated_by_learner
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithShapeProfile P)
    (w : Word α) (hw : w ∈ K) :
    w ∈ P.wordLanguage := by
  exact C.exactWithParameterProfile.sample_word_generated_by_learner w hw

/-- Target-side start derivation witness for a sampled word. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithShapeProfile P)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact C.exactWithParameterProfile.sample_word_start_derives w hw

/-- Rule-list coverage inherited from the exact package. -/
theorem refinedRuleLists_coverAll
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithShapeProfile P) :
    P.finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact C.exactWithParameterProfile.refinedRuleLists_coverAll

/-- Rule-list plan support inherited from the exact package. -/
theorem refinedRuleLists_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithShapeProfile P) :
    P.finiteRefinedGrammar.AllRulesSupportedByPlan P.ruleEnumerationPlan := by
  exact C.exactWithParameterProfile.refinedRuleLists_supportedByPlan

/-- The refined-rule count is bounded by the shape profile's total shape bound. -/
theorem refinedRuleCount_le_totalShapeBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithShapeProfile P) :
    P.refinedRuleCount ≤ C.shapeProfile.totalShapeBound := by
  exact C.shapeProfile.refinedRuleCount_le_totalShapeBound

/-- The profile records the size of the finite sample. -/
theorem sampleSize_eq_card
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithShapeProfile P) :
    C.exactWithParameterProfile.profile.sampleSize = K.card := by
  exact C.exactWithParameterProfile.sampleSize_eq_card

/-- The shape profile records the finite cardinality of the observation monoid
through its underlying parameter profile. -/
theorem monoidCardinality_eq_fintypeCard
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithShapeProfile P) :
    C.shapeProfile.parameterProfile.monoidCardinality = Fintype.card M := by
  exact C.shapeProfile.monoidCardinality_eq_fintypeCard

end CanonicalLearnerGrammarExactWithShapeProfile

end ShapeProfileExact

end

end FIv21
