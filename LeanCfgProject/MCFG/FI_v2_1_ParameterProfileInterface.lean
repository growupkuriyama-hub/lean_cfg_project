import LeanCfgProject.MCFG.FI_v2_1_PolynomialBoundGold

/-!
# FI v2.1 Lean experiment: canonical parameter-profile interface

This sixty-fifth layer adds a small parameter-profile interface on top of the
abstract polynomial-bound certificates.

The previous files attach opaque polynomial-bound witnesses to enumeration
bounds.  This file records the numerical parameters with which later complexity
statements will be expressed: sample size, ordinary rule count, monoid
cardinality, a fan-out parameter placeholder, and the total enumeration bound.

No concrete asymptotic theorem is proved here.  The profile is deliberately a
certificate interface: later files may replace the placeholder fan-out and bound
fields by sharper expressions while preserving the semantic API already checked.
-/

namespace FIv21

universe u v w

noncomputable section

section ParameterProfileInterface

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Numerical parameter profile attached to a canonical learner grammar package.

The fields are intentionally plain natural numbers.  The equations identify the
stable parameters already available in the formalization, while
`fanoutParameter` is kept as a placeholder for later fan-out-bound work.  The
profile also carries the existing abstract polynomial-bound certificate. -/
structure CanonicalParameterProfile
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  sampleSize : Nat
  ordinaryRuleCount : Nat
  monoidCardinality : Nat
  fanoutParameter : Nat
  totalEnumerationBound : Nat
  polynomialBounds : CanonicalPolynomialBounds P
  sampleSize_eq : sampleSize = K.card
  ordinaryRuleCount_eq : ordinaryRuleCount = P.ordinaryRuleCount
  monoidCardinality_eq : monoidCardinality = Fintype.card M
  totalEnumerationBound_eq :
    totalEnumerationBound = polynomialBounds.bounds.totalBound

namespace CanonicalParameterProfile

/-- Tautological parameter profile for a package.

This uses the actual sample size, ordinary rule count, finite monoid cardinality,
and the tautological polynomial-bound package from the previous layer.  The
fan-out parameter is left as `0`; it is not used by any theorem in this
interface and can be replaced by a genuine fan-out certificate later. -/
def trivialForPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) :
    CanonicalParameterProfile P :=
  let B := CanonicalPolynomialBounds.trivialForPackage P
  { sampleSize := K.card
    ordinaryRuleCount := P.ordinaryRuleCount
    monoidCardinality := Fintype.card M
    fanoutParameter := 0
    totalEnumerationBound := B.bounds.totalBound
    polynomialBounds := B
    sampleSize_eq := rfl
    ordinaryRuleCount_eq := rfl
    monoidCardinality_eq := rfl
    totalEnumerationBound_eq := rfl }

/-- Forget the profile to its polynomial-bound certificate. -/
def toPolynomialBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalParameterProfile P) :
    CanonicalPolynomialBounds P :=
  S.polynomialBounds

/-- Forget the profile to its enumeration-bound certificate. -/
def toEnumerationBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalParameterProfile P) :
    CanonicalEnumerationBounds P :=
  S.polynomialBounds.toEnumerationBounds

/-- The displayed sample-size parameter is the cardinality of the finite sample. -/
theorem sampleSize_eq_card
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalParameterProfile P) :
    S.sampleSize = K.card := by
  exact S.sampleSize_eq

/-- The displayed ordinary-rule parameter is the package's ordinary-rule count. -/
theorem ordinaryRuleCount_eq_package
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalParameterProfile P) :
    S.ordinaryRuleCount = P.ordinaryRuleCount := by
  exact S.ordinaryRuleCount_eq

/-- The displayed monoid-size parameter is Lean's finite cardinality of `M`. -/
theorem monoidCardinality_eq_fintypeCard
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalParameterProfile P) :
    S.monoidCardinality = Fintype.card M := by
  exact S.monoidCardinality_eq

/-- The displayed total enumeration bound is the total bound from the attached
polynomial-bound certificate. -/
theorem totalEnumerationBound_eq_polynomialTotal
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalParameterProfile P) :
    S.totalEnumerationBound = S.polynomialBounds.bounds.totalBound := by
  exact S.totalEnumerationBound_eq

/-- The refined-rule count is bounded by the displayed total enumeration
parameter. -/
theorem refinedRuleCount_le_totalEnumerationBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalParameterProfile P) :
    P.refinedRuleCount ≤ S.totalEnumerationBound := by
  have h := S.polynomialBounds.refinedRuleCount_le_polynomialBound
  simpa [S.totalEnumerationBound_eq] using h

/-- The attached total bound has an abstract polynomial witness. -/
def totalPolynomialWitness
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (S : CanonicalParameterProfile P) :
    PolynomialBoundWitness S.polynomialBounds.bounds.totalBound :=
  S.polynomialBounds.totalPolynomialWitness

end CanonicalParameterProfile

end ParameterProfileInterface

end

end FIv21
