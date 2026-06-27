import LeanCfgProject.MCFG.FI_v2_1_CanonicalEnumerationBoundGold

/-!
# FI v2.1 Lean experiment: abstract polynomial-bound interface

This sixty-second layer adds a deliberately conservative interface for later
polynomial-size statements.

The preceding files record concrete natural-number bounds for the finite data
carried by a canonical learner grammar package.  This file does not attempt to
prove that any particular closed-form expression is polynomial.  Instead, it
introduces a small abstract witness type saying that a natural-number bound has
a polynomial-bound justification.  The witness is intentionally opaque: later
complexity files may replace the trivial placeholder witnesses by genuine
polynomial expressions and proofs, while all semantic reconstruction interfaces
can continue to depend only on this stable certificate shape.
-/

namespace FIv21

universe u v w

noncomputable section

section PolynomialBoundInterface

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Abstract witness that the natural number `bound` is controlled by some
polynomial-size estimate.

The current Lean companion deliberately keeps this as an interface rather than
as a concrete polynomial library.  A witness consists of an opaque proposition
and a proof of it.  This is enough to thread polynomial-bound information
through the reconstruction certificates without committing to a final encoding
of polynomial expressions. -/
structure PolynomialBoundWitness (bound : Nat) where
  certificate : Prop
  certified : certificate

namespace PolynomialBoundWitness

/-- Tautological placeholder witness for any bound.  This is the safe default
used before concrete complexity estimates are formalized. -/
def trivial (bound : Nat) : PolynomialBoundWitness bound :=
  { certificate := True
    certified := True.intro }

/-- Forget the opaque certificate proposition. -/
theorem holds {bound : Nat} (W : PolynomialBoundWitness bound) : W.certificate := by
  exact W.certified

end PolynomialBoundWitness

/-- Enumeration bounds together with abstract polynomial witnesses for the
main bound components.

This packages the statement: the canonical package has finite enumeration
bounds, and each displayed bound is equipped with a polynomial-size witness.
No concrete polynomial arithmetic is claimed here. -/
structure CanonicalPolynomialBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  bounds : CanonicalEnumerationBounds P
  terminalPolynomial : PolynomialBoundWitness bounds.terminalBound
  binaryPolynomial : PolynomialBoundWitness bounds.binaryBound
  startPolynomial : PolynomialBoundWitness bounds.startBound
  totalPolynomial : PolynomialBoundWitness bounds.totalBound
  ordinaryPolynomial : PolynomialBoundWitness bounds.ordinaryBound

namespace CanonicalPolynomialBounds

/-- Tautological polynomial-bound package obtained from the exact enumeration
bounds of a package. -/
def trivialForPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) :
    CanonicalPolynomialBounds P :=
  let B := CanonicalEnumerationBounds.exactForPackage P
  { bounds := B
    terminalPolynomial := PolynomialBoundWitness.trivial B.terminalBound
    binaryPolynomial := PolynomialBoundWitness.trivial B.binaryBound
    startPolynomial := PolynomialBoundWitness.trivial B.startBound
    totalPolynomial := PolynomialBoundWitness.trivial B.totalBound
    ordinaryPolynomial := PolynomialBoundWitness.trivial B.ordinaryBound }

/-- Forget to the underlying enumeration-bound certificate. -/
def toEnumerationBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (B : CanonicalPolynomialBounds P) :
    CanonicalEnumerationBounds P :=
  B.bounds

/-- The total refined-rule count is below the polynomially witnessed total
bound. -/
theorem refinedRuleCount_le_polynomialBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (B : CanonicalPolynomialBounds P) :
    P.refinedRuleCount ≤ B.bounds.totalBound := by
  exact B.bounds.refinedRuleCount_le

/-- The terminal refined-rule count is below the polynomially witnessed terminal
bound. -/
theorem refinedTerminalRuleCount_le_polynomialBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (B : CanonicalPolynomialBounds P) :
    P.refinedTerminalRuleCount ≤ B.bounds.terminalBound := by
  exact B.bounds.refinedTerminalRuleCount_le

/-- The binary refined-rule count is below the polynomially witnessed binary
bound. -/
theorem refinedBinaryRuleCount_le_polynomialBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (B : CanonicalPolynomialBounds P) :
    P.refinedBinaryRuleCount ≤ B.bounds.binaryBound := by
  exact B.bounds.refinedBinaryRuleCount_le

/-- The start refined-rule count is below the polynomially witnessed start
bound. -/
theorem refinedStartRuleCount_le_polynomialBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (B : CanonicalPolynomialBounds P) :
    P.refinedStartRuleCount ≤ B.bounds.startBound := by
  exact B.bounds.refinedStartRuleCount_le

/-- The ordinary rule count is below the polynomially witnessed ordinary-rule
bound. -/
theorem ordinaryRuleCount_le_polynomialBound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (B : CanonicalPolynomialBounds P) :
    P.ordinaryRuleCount ≤ B.bounds.ordinaryBound := by
  exact B.bounds.ordinaryRuleCount_le

/-- The total bound carries an abstract polynomial witness. -/
def totalPolynomialWitness
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (B : CanonicalPolynomialBounds P) :
    PolynomialBoundWitness B.bounds.totalBound :=
  B.totalPolynomial

end CanonicalPolynomialBounds

end PolynomialBoundInterface

end

end FIv21
