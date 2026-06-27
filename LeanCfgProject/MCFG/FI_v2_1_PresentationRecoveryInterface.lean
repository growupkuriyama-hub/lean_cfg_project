import LeanCfgProject.MCFG.FI_v2_1_BoundedDataRecoveryGold

/-!
# FI v2.1 Lean experiment: presentation-relative recovery interface

This seventy-fourth layer adds a presentation-relative recovery interface on top
of the bounded-data recovery profile.

The paper's final theorem is presentation-relative: a witnessing working MCFG
presentation supplies finite data from which the learner eventually recovers the
right distributional behavior.  We still do **not** construct that presentation-
relative characteristic sample here.  Instead, this file packages the numerical
and certificate-style information that such a theorem should provide: a
presentation-side bound dominating the already checked recovery bound and the
finite refined-rule count.

The layer is intentionally conservative.  It records a safe bridge between the
current bounded-data recovery infrastructure and the eventual
presentation-relative theorem statement.
-/

namespace FIv21

universe u v w

noncomputable section

section PresentationRecoveryInterface

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Presentation-relative recovery data attached to a canonical learner grammar
package.

The profile sits above `CanonicalBoundedDataRecoveryProfile`.  It records a
presentation rule bound, a presentation interface bound, and a total presentation
bound.  The checked obligations are deliberately weak but useful: the total
presentation bound dominates both the refined-rule count of the package and the
already displayed bounded-data recovery bound. -/
structure CanonicalPresentationRecoveryProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  recoveryProfile : CanonicalBoundedDataRecoveryProfile P
  presentationRuleBound : Nat
  presentationInterfaceBound : Nat
  totalPresentationBound : Nat
  refinedRuleCount_le_totalPresentationBound :
    P.refinedRuleCount ≤ totalPresentationBound
  recoveryBound_le_totalPresentationBound :
    recoveryProfile.totalRecoveryBound ≤ totalPresentationBound
  totalPresentationPolynomial : PolynomialBoundWitness totalPresentationBound

namespace CanonicalPresentationRecoveryProfile

/-- Tautological presentation-relative profile over an existing bounded-data
recovery profile.

Before the genuine presentation-relative construction is formalized, the total
presentation bound is simply the total recovery bound. -/
def trivialForRecovery
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalBoundedDataRecoveryProfile P) :
    CanonicalPresentationRecoveryProfile P :=
  { recoveryProfile := R
    presentationRuleBound := P.refinedRuleCount
    presentationInterfaceBound := R.recoverySampleBound
    totalPresentationBound := R.totalRecoveryBound
    refinedRuleCount_le_totalPresentationBound :=
      R.refinedRuleCount_le_totalRecoveryBound
    recoveryBound_le_totalPresentationBound := Nat.le_refl _
    totalPresentationPolynomial := R.totalRecoveryPolynomialWitness }

/-- Tautological presentation-relative recovery profile for a package. -/
def trivialForPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) :
    CanonicalPresentationRecoveryProfile P :=
  trivialForRecovery (CanonicalBoundedDataRecoveryProfile.trivialForPackage P)

/-- Forget presentation-relative data to bounded-data recovery data. -/
def toRecoveryProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalPresentationRecoveryProfile P) :
    CanonicalBoundedDataRecoveryProfile P :=
  R.recoveryProfile

/-- Forget presentation-relative data to the underlying shape profile. -/
def toShapeProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalPresentationRecoveryProfile P) :
    CanonicalShapeProfile P :=
  R.recoveryProfile.toShapeProfile

/-- Forget presentation-relative data to the underlying parameter profile. -/
def toParameterProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalPresentationRecoveryProfile P) :
    CanonicalParameterProfile P :=
  R.recoveryProfile.toParameterProfile

/-- Forget presentation-relative data to the underlying polynomial-bound
certificate. -/
def toPolynomialBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalPresentationRecoveryProfile P) :
    CanonicalPolynomialBounds P :=
  R.recoveryProfile.toPolynomialBounds

/-- Forget presentation-relative data to the underlying enumeration-bound
certificate. -/
def toEnumerationBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalPresentationRecoveryProfile P) :
    CanonicalEnumerationBounds P :=
  R.recoveryProfile.toEnumerationBounds

/-- The refined-rule count is below the underlying bounded-data recovery bound. -/
theorem refinedRuleCount_le_totalRecoveryBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalPresentationRecoveryProfile P) :
    P.refinedRuleCount ≤ R.recoveryProfile.totalRecoveryBound := by
  exact R.recoveryProfile.refinedRuleCount_le_totalRecoveryBound

/-- The refined-rule count is also below the underlying total shape bound. -/
theorem refinedRuleCount_le_totalShapeBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalPresentationRecoveryProfile P) :
    P.refinedRuleCount ≤ R.recoveryProfile.shapeProfile.totalShapeBound := by
  exact R.recoveryProfile.refinedRuleCount_le_totalShapeBound

/-- Transitive form: the refined-rule count is bounded by the total presentation
bound. -/
theorem refinedRuleCount_le_totalPresentationBound'
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalPresentationRecoveryProfile P) :
    P.refinedRuleCount ≤ R.totalPresentationBound := by
  exact R.refinedRuleCount_le_totalPresentationBound

/-- The recovery bound is dominated by the total presentation bound. -/
theorem totalRecoveryBound_le_totalPresentationBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalPresentationRecoveryProfile P) :
    R.recoveryProfile.totalRecoveryBound ≤ R.totalPresentationBound := by
  exact R.recoveryBound_le_totalPresentationBound

/-- The sample-size parameter is inherited from the recovery profile. -/
theorem sampleSize_eq_card
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalPresentationRecoveryProfile P) :
    R.recoveryProfile.shapeProfile.parameterProfile.sampleSize = K.card := by
  exact R.recoveryProfile.sampleSize_eq_card

/-- The monoid-cardinality parameter is inherited from the recovery profile. -/
theorem monoidCardinality_eq_fintypeCard
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalPresentationRecoveryProfile P) :
    R.recoveryProfile.shapeProfile.parameterProfile.monoidCardinality =
      Fintype.card M := by
  exact R.recoveryProfile.monoidCardinality_eq_fintypeCard

/-- The displayed total presentation bound carries an abstract polynomial
witness. -/
def totalPresentationPolynomialWitness
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (R : CanonicalPresentationRecoveryProfile P) :
    PolynomialBoundWitness R.totalPresentationBound :=
  R.totalPresentationPolynomial

end CanonicalPresentationRecoveryProfile

end PresentationRecoveryInterface

end

end FIv21
