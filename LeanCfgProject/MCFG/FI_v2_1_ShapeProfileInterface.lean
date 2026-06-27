import LeanCfgProject.MCFG.FI_v2_1_ParameterProfileGold

/-!
# FI v2.1 Lean experiment: canonical shape-profile interface

This sixty-eighth layer adds a conservative shape-profile interface on top of
parameter profiles.

The paper ultimately needs structural restrictions such as bounded spine width
or bounded derivation-shape complexity for polynomial-data statements.  This
file does **not** define those notions yet.  Instead it provides a stable
certificate interface recording numerical shape parameters attached to a
canonical learner package, together with elementary domination by a total shape
bound.

The interface is intentionally weak but useful: later files can replace the
placeholder fields by genuine bounded-spine definitions while keeping the
post-threshold exactness and Gold wrappers unchanged.
-/

namespace FIv21

universe u v w

noncomputable section

section ShapeProfileInterface

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Shape-profile data attached to a canonical learner grammar package.

The three shape parameters are placeholders for later bounded-spine and
bounded-shape infrastructure.  The current file only records that they are
bounded by a total shape bound and that the existing total enumeration bound is
also below that total shape bound. -/
structure CanonicalShapeProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  parameterProfile : CanonicalParameterProfile P
  spineWidthBound : Nat
  derivationDepthBound : Nat
  interfaceWidthBound : Nat
  totalShapeBound : Nat
  spineWidth_le_totalShapeBound : spineWidthBound ≤ totalShapeBound
  derivationDepth_le_totalShapeBound : derivationDepthBound ≤ totalShapeBound
  interfaceWidth_le_totalShapeBound : interfaceWidthBound ≤ totalShapeBound
  totalEnumerationBound_le_totalShapeBound :
    parameterProfile.totalEnumerationBound ≤ totalShapeBound

namespace CanonicalShapeProfile

/-- Tautological shape profile over an already chosen parameter profile.

The genuine structural parameters are not formalized yet, so the default values
are zero and the total shape bound is the existing total enumeration bound. -/
def trivialForProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalParameterProfile P) :
    CanonicalShapeProfile P :=
  { parameterProfile := S
    spineWidthBound := 0
    derivationDepthBound := 0
    interfaceWidthBound := 0
    totalShapeBound := S.totalEnumerationBound
    spineWidth_le_totalShapeBound := Nat.zero_le _
    derivationDepth_le_totalShapeBound := Nat.zero_le _
    interfaceWidth_le_totalShapeBound := Nat.zero_le _
    totalEnumerationBound_le_totalShapeBound := Nat.le_refl _ }

/-- Tautological shape profile for a canonical learner package. -/
def trivialForPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) :
    CanonicalShapeProfile P :=
  trivialForProfile (CanonicalParameterProfile.trivialForPackage P)

/-- Forget a shape profile to the underlying parameter profile. -/
def toParameterProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalShapeProfile P) :
    CanonicalParameterProfile P :=
  S.parameterProfile

/-- Forget a shape profile to the underlying polynomial-bound certificate. -/
def toPolynomialBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalShapeProfile P) :
    CanonicalPolynomialBounds P :=
  S.parameterProfile.toPolynomialBounds

/-- Forget a shape profile to the underlying enumeration-bound certificate. -/
def toEnumerationBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalShapeProfile P) :
    CanonicalEnumerationBounds P :=
  S.parameterProfile.toEnumerationBounds

/-- The refined-rule count is bounded by the displayed total shape bound. -/
theorem refinedRuleCount_le_totalShapeBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalShapeProfile P) :
    P.refinedRuleCount ≤ S.totalShapeBound := by
  have h₁ : P.refinedRuleCount ≤ S.parameterProfile.totalEnumerationBound :=
    CanonicalParameterProfile.refinedRuleCount_le_totalEnumerationBound
      S.parameterProfile
  exact Nat.le_trans h₁ S.totalEnumerationBound_le_totalShapeBound

/-- The sample-size parameter is inherited from the underlying parameter
profile. -/
theorem sampleSize_eq_card
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalShapeProfile P) :
    S.parameterProfile.sampleSize = K.card := by
  exact S.parameterProfile.sampleSize_eq_card

/-- The monoid-cardinality parameter is inherited from the underlying parameter
profile. -/
theorem monoidCardinality_eq_fintypeCard
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalShapeProfile P) :
    S.parameterProfile.monoidCardinality = Fintype.card M := by
  exact S.parameterProfile.monoidCardinality_eq_fintypeCard

/-- The attached total enumeration bound has an abstract polynomial witness. -/
def totalPolynomialWitness
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalShapeProfile P) :
    PolynomialBoundWitness S.parameterProfile.polynomialBounds.bounds.totalBound :=
  S.parameterProfile.totalPolynomialWitness

end CanonicalShapeProfile

end ShapeProfileInterface

end

end FIv21
