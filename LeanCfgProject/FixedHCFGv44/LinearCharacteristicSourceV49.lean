import LeanCfgProject.FixedHCFGv44.LinearCharacteristicRetainedV49
import LeanCfgProject.FixedHCFGv44.LinearNormalizationReachableBudgetV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Source-grammar specialization of the retained-state characteristic-data bound.

This closes the size bridge needed by the manuscript's linear-subclass theorem:
Appendix A gives a polynomial bound on the actually retained yield-typed states,
Appendix B gives linear-length canonical witnesses in that retained-state count,
and `LinearCharacteristicRetainedV49` turns those witnesses into a finite sample
norm bound.  The resulting expression is polynomial in the source linear grammar
for fixed observer `h` and fixed finite alphabet.

As elsewhere in the v49 normalization layer, this is an output-size/semantic
bound.  It does not by itself formalize a concrete machine-level running-time
model for preprocessing or normalization.
-/

/-- Explicit source-level envelope for the characteristic reconstruction data. -/
def sourceNormalizedCharacteristicBudgetV49
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma)
    (sourceRules : List (SourceLinearRule N Sigma)) : Nat :=
  let B := sourceLinearNormalizationPolynomial sourceRules * Fintype.card Obs.M
  (B + B * Fintype.card Sigma + B ^ 3 + 1) * (4 * B + 1)

/--
For the explicit v49 normalization, the exact canonical characteristic sample
has polynomial encoded norm in the source linear grammar representation.
-/
theorem sourceNormalized_characteristic_norm_le_sourcePolynomial_v49
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N)
    (epsilonStart : Prop) :
    letI := sourceNormalizedKeptStateFintypeV49 Obs sourceRules S
    canonicalCSNormRetainedV49
        (Obs := Obs)
        (terminal := SourceNormalizedTerminalV49 sourceRules S)
        (binary := SourceNormalizedBinaryV49 sourceRules S)
        (start := SourceNormalizedStartV49 sourceRules S)
        epsilonStart ≤
      sourceNormalizedCharacteristicBudgetV49 Obs sourceRules := by
  classical
  letI := sourceNormalizedKeptStateFintypeV49 Obs sourceRules S
  let n : Nat := Fintype.card (KeptState Obs
    (SourceNormalizedTerminalV49 sourceRules S)
    (SourceNormalizedBinaryV49 sourceRules S)
    (SourceNormalizedStartV49 sourceRules S))
  let B : Nat := sourceLinearNormalizationPolynomial sourceRules * Fintype.card Obs.M
  let s : Nat := Fintype.card Sigma

  have hLocal := canonicalCSNormRetainedV49_polynomial_le
    (Obs := Obs)
    (terminal := SourceNormalizedTerminalV49 sourceRules S)
    (binary := SourceNormalizedBinaryV49 sourceRules S)
    (start := SourceNormalizedStartV49 sourceRules S)
    epsilonStart
    (sourceNormalizedTypedLinearSpineShapeV49 Obs sourceRules S)
  have hLocal' :
      canonicalCSNormRetainedV49
          (Obs := Obs)
          (terminal := SourceNormalizedTerminalV49 sourceRules S)
          (binary := SourceNormalizedBinaryV49 sourceRules S)
          (start := SourceNormalizedStartV49 sourceRules S)
          epsilonStart ≤
        (n + n * s + n ^ 3 + 1) * (4 * n + 1) := by
    simpa [n, s] using hLocal

  have hCard := sourceNormalized_keptState_card_le_sourcePolynomial_v49
    Obs sourceRules S
  have hn : n ≤ B := by
    simpa [n, B] using hCard

  have hSquare : n * n ≤ B * B := Nat.mul_le_mul hn hn
  have hCubeRaw : (n * n) * n ≤ (B * B) * B := Nat.mul_le_mul hSquare hn
  have hCube : n ^ 3 ≤ B ^ 3 := by
    simpa [pow_succ, Nat.mul_assoc] using hCubeRaw
  have hSigma : n * s ≤ B * s := Nat.mul_le_mul_right s hn
  have hDataFactor :
      n + n * s + n ^ 3 + 1 ≤ B + B * s + B ^ 3 + 1 := by
    omega
  have hLengthFactor : 4 * n + 1 ≤ 4 * B + 1 := by
    omega
  have hEnvelope :
      (n + n * s + n ^ 3 + 1) * (4 * n + 1) ≤
        (B + B * s + B ^ 3 + 1) * (4 * B + 1) :=
    Nat.mul_le_mul hDataFactor hLengthFactor

  exact le_trans hLocal' (by
    simpa [sourceNormalizedCharacteristicBudgetV49, B, s] using hEnvelope)

end FixedHCFGv44
end LeanCfgProject
