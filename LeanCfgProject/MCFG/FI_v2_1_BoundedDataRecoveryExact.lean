import LeanCfgProject.MCFG.FI_v2_1_BoundedDataRecoveryInterface

/-!
# FI v2.1 Lean experiment: exact packages with bounded-data recovery profiles

This seventy-second layer bundles exact canonical learner grammar packages with
 bounded-data recovery profiles.

The semantic facts are inherited from the shape-profile exact layer.  The new
 data is a stable recovery-bound certificate that can later be replaced by a
 genuine bounded-spine or bounded-data construction.
-/

namespace FIv21

universe u v w

noncomputable section

section BoundedDataRecoveryExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact canonical learner grammar package equipped with bounded-data recovery
information. -/
structure CanonicalLearnerGrammarExactWithBoundedDataRecovery
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  exactWithShapeProfile : CanonicalLearnerGrammarExactWithShapeProfile P
  recoveryProfile : CanonicalBoundedDataRecoveryProfile P
  recovery_shape_agrees :
    recoveryProfile.shapeProfile = exactWithShapeProfile.shapeProfile

namespace CanonicalLearnerGrammarExactWithBoundedDataRecovery

/-- Equip an exact-with-shape-profile package with the tautological recovery
profile over its shape profile. -/
def ofExactWithShapeProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithShapeProfile P) :
    CanonicalLearnerGrammarExactWithBoundedDataRecovery P :=
  { exactWithShapeProfile := C
    recoveryProfile :=
      CanonicalBoundedDataRecoveryProfile.trivialForShape C.shapeProfile
    recovery_shape_agrees := rfl }

/-- Equip an exact canonical package with tautological parameters, shape data,
 and recovery bounds. -/
def ofExactPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactForGrammar P) :
    CanonicalLearnerGrammarExactWithBoundedDataRecovery P :=
  ofExactWithShapeProfile
    (CanonicalLearnerGrammarExactWithShapeProfile.ofExactPackage C)

/-- Forget to the exact-with-shape-profile certificate. -/
def toExactWithShapeProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithBoundedDataRecovery P) :
    CanonicalLearnerGrammarExactWithShapeProfile P :=
  C.exactWithShapeProfile

/-- Forget to the bounded-data recovery profile. -/
def toRecoveryProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithBoundedDataRecovery P) :
    CanonicalBoundedDataRecoveryProfile P :=
  C.recoveryProfile

/-- Exact equality of approximate and target named-context distributions. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithBoundedDataRecovery P)
    {d : Nat} (x : Tuple α d) :
    P.ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact C.exactWithShapeProfile.approxDistribution_exact x

/-- Learner-side generation of a sampled word. -/
theorem sample_word_generated_by_learner
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithBoundedDataRecovery P)
    (w : Word α) (hw : w ∈ K) :
    w ∈ P.wordLanguage := by
  exact C.exactWithShapeProfile.sample_word_generated_by_learner w hw

/-- Target-side start derivation witness for a sampled word. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithBoundedDataRecovery P)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact C.exactWithShapeProfile.sample_word_start_derives w hw

/-- Rule-list coverage inherited from the exact package. -/
theorem refinedRuleLists_coverAll
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithBoundedDataRecovery P) :
    P.finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact C.exactWithShapeProfile.refinedRuleLists_coverAll

/-- Plan support for all listed refined rules inherited from the exact package. -/
theorem refinedRuleLists_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithBoundedDataRecovery P) :
    P.finiteRefinedGrammar.AllRulesSupportedByPlan P.ruleEnumerationPlan := by
  exact C.exactWithShapeProfile.refinedRuleLists_supportedByPlan

/-- The refined-rule count is bounded by the displayed total recovery bound. -/
theorem refinedRuleCount_le_totalRecoveryBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithBoundedDataRecovery P) :
    P.refinedRuleCount ≤ C.recoveryProfile.totalRecoveryBound := by
  exact C.recoveryProfile.refinedRuleCount_le_totalRecoveryBound

/-- The refined-rule count is also bounded by the underlying total shape bound. -/
theorem refinedRuleCount_le_totalShapeBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithBoundedDataRecovery P) :
    P.refinedRuleCount ≤ C.recoveryProfile.shapeProfile.totalShapeBound := by
  exact C.recoveryProfile.refinedRuleCount_le_totalShapeBound

/-- The recovery profile records the size of the finite sample through its
underlying shape profile. -/
theorem sampleSize_eq_card
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithBoundedDataRecovery P) :
    C.recoveryProfile.shapeProfile.parameterProfile.sampleSize = K.card := by
  exact C.recoveryProfile.sampleSize_eq_card

/-- The recovery profile records the finite cardinality of the observation
monoid through its underlying shape profile. -/
theorem monoidCardinality_eq_fintypeCard
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithBoundedDataRecovery P) :
    C.recoveryProfile.shapeProfile.parameterProfile.monoidCardinality =
      Fintype.card M := by
  exact C.recoveryProfile.monoidCardinality_eq_fintypeCard

end CanonicalLearnerGrammarExactWithBoundedDataRecovery

end BoundedDataRecoveryExact

end

end FIv21
