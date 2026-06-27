import LeanCfgProject.MCFG.FI_v2_1_PresentationRecoveryInterface

/-!
# FI v2.1 Lean experiment: exact packages with presentation-relative recovery

This seventy-fifth layer bundles exact canonical learner grammar packages with
presentation-relative recovery profiles.

The semantic facts are inherited from the bounded-data recovery exact layer. The
new data is a presentation-side bound certificate, intended as the interface for
future theorems extracting finite recovery data from a witnessing presentation.
-/

namespace FIv21

universe u v w

noncomputable section

section PresentationRecoveryExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact canonical learner grammar package equipped with presentation-relative
recovery information. -/
structure CanonicalLearnerGrammarExactWithPresentationRecovery
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  exactWithRecovery : CanonicalLearnerGrammarExactWithBoundedDataRecovery P
  presentationProfile : CanonicalPresentationRecoveryProfile P
  presentation_recovery_agrees :
    presentationProfile.recoveryProfile = exactWithRecovery.recoveryProfile

namespace CanonicalLearnerGrammarExactWithPresentationRecovery

/-- Equip an exact-with-recovery package with the tautological
presentation-relative profile over its recovery profile. -/
def ofExactWithRecovery
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithBoundedDataRecovery P) :
    CanonicalLearnerGrammarExactWithPresentationRecovery P :=
  { exactWithRecovery := C
    presentationProfile :=
      CanonicalPresentationRecoveryProfile.trivialForRecovery C.recoveryProfile
    presentation_recovery_agrees := rfl }

/-- Equip an exact canonical package with tautological recovery and
presentation-relative bounds. -/
def ofExactPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactForGrammar P) :
    CanonicalLearnerGrammarExactWithPresentationRecovery P :=
  ofExactWithRecovery
    (CanonicalLearnerGrammarExactWithBoundedDataRecovery.ofExactPackage C)

/-- Forget to the exact-with-bounded-data-recovery certificate. -/
def toExactWithRecovery
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPresentationRecovery P) :
    CanonicalLearnerGrammarExactWithBoundedDataRecovery P :=
  C.exactWithRecovery

/-- Forget to the presentation-relative recovery profile. -/
def toPresentationProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPresentationRecovery P) :
    CanonicalPresentationRecoveryProfile P :=
  C.presentationProfile

/-- Exact equality of approximate and target named-context distributions. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPresentationRecovery P)
    {d : Nat} (x : Tuple α d) :
    P.ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact C.exactWithRecovery.approxDistribution_exact x

/-- Learner-side generation of a sampled word. -/
theorem sample_word_generated_by_learner
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPresentationRecovery P)
    (w : Word α) (hw : w ∈ K) :
    w ∈ P.wordLanguage := by
  exact C.exactWithRecovery.sample_word_generated_by_learner w hw

/-- Target-side start derivation witness for a sampled word. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPresentationRecovery P)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact C.exactWithRecovery.sample_word_start_derives w hw

/-- Rule-list coverage inherited from the exact package. -/
theorem refinedRuleLists_coverAll
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPresentationRecovery P) :
    P.finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact C.exactWithRecovery.refinedRuleLists_coverAll

/-- Plan support for all listed refined rules inherited from the exact package. -/
theorem refinedRuleLists_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPresentationRecovery P) :
    P.finiteRefinedGrammar.AllRulesSupportedByPlan P.ruleEnumerationPlan := by
  exact C.exactWithRecovery.refinedRuleLists_supportedByPlan

/-- Refined-rule count bounded by the total presentation bound. -/
theorem refinedRuleCount_le_totalPresentationBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPresentationRecovery P) :
    P.refinedRuleCount ≤ C.presentationProfile.totalPresentationBound := by
  exact C.presentationProfile.refinedRuleCount_le_totalPresentationBound

/-- Refined-rule count bounded by the total bounded-data recovery bound. -/
theorem refinedRuleCount_le_totalRecoveryBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPresentationRecovery P) :
    P.refinedRuleCount ≤ C.presentationProfile.recoveryProfile.totalRecoveryBound := by
  exact C.presentationProfile.refinedRuleCount_le_totalRecoveryBound

/-- The recovery bound is bounded by the total presentation bound. -/
theorem totalRecoveryBound_le_totalPresentationBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPresentationRecovery P) :
    C.presentationProfile.recoveryProfile.totalRecoveryBound ≤
      C.presentationProfile.totalPresentationBound := by
  exact C.presentationProfile.totalRecoveryBound_le_totalPresentationBound

/-- The presentation profile records the finite sample size. -/
theorem sampleSize_eq_card
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPresentationRecovery P) :
    C.presentationProfile.recoveryProfile.shapeProfile.parameterProfile.sampleSize =
      K.card := by
  exact C.presentationProfile.sampleSize_eq_card

/-- The presentation profile records the finite cardinality of the observation
monoid. -/
theorem monoidCardinality_eq_fintypeCard
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPresentationRecovery P) :
    C.presentationProfile.recoveryProfile.shapeProfile.parameterProfile.monoidCardinality =
      Fintype.card M := by
  exact C.presentationProfile.monoidCardinality_eq_fintypeCard

/-- The total presentation bound carries an abstract polynomial witness. -/
def totalPresentationPolynomialWitness
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithPresentationRecovery P) :
    PolynomialBoundWitness C.presentationProfile.totalPresentationBound :=
  C.presentationProfile.totalPresentationPolynomialWitness

end CanonicalLearnerGrammarExactWithPresentationRecovery

end PresentationRecoveryExact

end

end FIv21
