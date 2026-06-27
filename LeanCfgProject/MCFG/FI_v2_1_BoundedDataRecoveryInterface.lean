import LeanCfgProject.MCFG.FI_v2_1_ShapeProfileGold

/-!
# FI v2.1 Lean experiment: bounded-data recovery interface

This seventy-first layer adds a conservative bounded-data recovery interface on
 top of the shape-profile infrastructure.

The paper eventually wants a bounded-spine / bounded-data recovery theorem.  We
 do **not** define that theorem here.  Instead, this file packages the numerical
 data that such a theorem should eventually provide: a finite recovery bound,
 together with the already checked shape profile and a proof that the refined
 rule count is below the displayed recovery bound.

This keeps the semantic reconstruction layers independent of the eventual
 encoding of bounded-spine width, derivation shape, or concrete data-compression
 estimates.
-/

namespace FIv21

universe u v w

noncomputable section

section BoundedDataRecoveryInterface

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Bounded-data recovery data attached to a canonical learner grammar package.

The fields are deliberately numerical and certificate-style.  The profile records
 an underlying shape profile, a sample-side bound, a rule-side bound, and a total
 recovery bound.  The mathematically important checked fact is that the package's
 refined-rule count is below the total recovery bound. -/
structure CanonicalBoundedDataRecoveryProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  shapeProfile : CanonicalShapeProfile P
  recoverySampleBound : Nat
  recoveryRuleBound : Nat
  totalRecoveryBound : Nat
  refinedRuleCount_le_totalRecoveryBound :
    P.refinedRuleCount ≤ totalRecoveryBound
  shapeBound_le_totalRecoveryBound :
    shapeProfile.totalShapeBound ≤ totalRecoveryBound
  totalRecoveryPolynomial : PolynomialBoundWitness totalRecoveryBound

namespace CanonicalBoundedDataRecoveryProfile

/-- Tautological bounded-data recovery profile over an existing shape profile.

Before genuine bounded-spine bounds are formalized, the total recovery bound is
 simply the total shape bound. -/
def trivialForShape
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalShapeProfile P) :
    CanonicalBoundedDataRecoveryProfile P :=
  { shapeProfile := S
    recoverySampleBound := S.parameterProfile.sampleSize
    recoveryRuleBound := P.refinedRuleCount
    totalRecoveryBound := S.totalShapeBound
    refinedRuleCount_le_totalRecoveryBound :=
      S.refinedRuleCount_le_totalShapeBound
    shapeBound_le_totalRecoveryBound := Nat.le_refl _
    totalRecoveryPolynomial := PolynomialBoundWitness.trivial _ }

/-- Tautological bounded-data recovery profile for a package. -/
def trivialForPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) :
    CanonicalBoundedDataRecoveryProfile P :=
  trivialForShape (CanonicalShapeProfile.trivialForPackage P)

/-- Forget bounded-data recovery data to the underlying shape profile. -/
def toShapeProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalBoundedDataRecoveryProfile P) :
    CanonicalShapeProfile P :=
  R.shapeProfile

/-- Forget bounded-data recovery data to the underlying parameter profile. -/
def toParameterProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalBoundedDataRecoveryProfile P) :
    CanonicalParameterProfile P :=
  R.shapeProfile.toParameterProfile

/-- Forget bounded-data recovery data to the underlying polynomial-bound
certificate. -/
def toPolynomialBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalBoundedDataRecoveryProfile P) :
    CanonicalPolynomialBounds P :=
  R.shapeProfile.toPolynomialBounds

/-- Forget bounded-data recovery data to the underlying enumeration-bound
certificate. -/
def toEnumerationBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalBoundedDataRecoveryProfile P) :
    CanonicalEnumerationBounds P :=
  R.shapeProfile.toEnumerationBounds

/-- The refined-rule count is also below the shape bound. -/
theorem refinedRuleCount_le_totalShapeBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalBoundedDataRecoveryProfile P) :
    P.refinedRuleCount ≤ R.shapeProfile.totalShapeBound := by
  exact R.shapeProfile.refinedRuleCount_le_totalShapeBound

/-- The sample-size parameter is inherited through the shape profile. -/
theorem sampleSize_eq_card
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalBoundedDataRecoveryProfile P) :
    R.shapeProfile.parameterProfile.sampleSize = K.card := by
  exact R.shapeProfile.sampleSize_eq_card

/-- The monoid-cardinality parameter is inherited through the shape profile. -/
theorem monoidCardinality_eq_fintypeCard
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalBoundedDataRecoveryProfile P) :
    R.shapeProfile.parameterProfile.monoidCardinality = Fintype.card M := by
  exact R.shapeProfile.monoidCardinality_eq_fintypeCard

/-- The displayed total recovery bound carries an abstract polynomial witness. -/
def totalRecoveryPolynomialWitness
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalBoundedDataRecoveryProfile P) :
    PolynomialBoundWitness R.totalRecoveryBound :=
  R.totalRecoveryPolynomial

end CanonicalBoundedDataRecoveryProfile

end BoundedDataRecoveryInterface

end

end FIv21
