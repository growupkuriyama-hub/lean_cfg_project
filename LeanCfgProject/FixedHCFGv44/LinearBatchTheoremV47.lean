import LeanCfgProject.FixedHCFGv44.LinearCharacteristicSizeV47
import LeanCfgProject.FixedHCFGv44.CanonicalReconstruction
import LeanCfgProject.FixedHCFGv44.ComplexityBounds
import LeanCfgProject.FixedHCFGv44.SampleConsistency

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Assembly layer for the revised v47 linear theorem.  The manuscript separates
four ingredients: polynomial characteristic-data size, exact reconstruction,
sample consistency, and conservative Gold convergence.  This file packages
those already verified components at one target presentation.
-/

/--
The characteristic-data norm bound can be stated directly in terms of the
underlying non-start symbol count and the fixed monoid size, using
`|V_typed| <= |N| |M|`.
-/
theorem canonicalCSNorm_original_factor_polynomial_le_v47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop)
    (S : TypedLinearSpineShape Obs terminal binary start) :
    canonicalCSNormV47 (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart ≤
      ((Fintype.card N * Fintype.card Obs.M) +
        (Fintype.card N * Fintype.card Obs.M) * Fintype.card Sigma +
        (Fintype.card N * Fintype.card Obs.M) ^ 3 + 1) *
      (4 * (Fintype.card N * Fintype.card Obs.M) + 1) := by
  let n := Fintype.card (KeptState Obs terminal binary start)
  let p := Fintype.card N * Fintype.card Obs.M
  let s := Fintype.card Sigma
  have hnp : n ≤ p := by
    simpa [n, p] using
      (kept_state_card_le
        (Obs := Obs) (terminal := terminal) (binary := binary) (start := start))
  have hns : n * s ≤ p * s := Nat.mul_le_mul_right s hnp
  have hn2 : n * n ≤ p * p := Nat.mul_le_mul hnp hnp
  have hn3 : n ^ 3 ≤ p ^ 3 := by
    calc
      n ^ 3 = n * n * n := by ring
      _ ≤ p * p * p := Nat.mul_le_mul hn2 hnp
      _ = p ^ 3 := by ring
  have hpoly : n + n * s + n ^ 3 + 1 ≤ p + p * s + p ^ 3 + 1 := by
    omega
  have hfour : 4 * n ≤ 4 * p := Nat.mul_le_mul_left 4 hnp
  have hlen : 4 * n + 1 ≤ 4 * p + 1 := by omega
  have hNorm := canonicalCSNorm_polynomial_le_v47
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
    epsilonStart S
  have hProduct :
      (n + n * s + n ^ 3 + 1) * (4 * n + 1) ≤
        (p + p * s + p ^ 3 + 1) * (4 * p + 1) :=
    Nat.mul_le_mul hpoly hlen
  exact le_trans (by simpa [n, s] using hNorm)
    (by simpa [p, s] using hProduct)

/--
Core theorem package matching v47 Theorem `thm:linear-poly`, apart from the
low-level implementation-cost interpretation of polynomial construction time.
The latter is represented separately by `v44BuildEnvelope_degree_five`.
-/
theorem linear_batch_reconstruction_core_v47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (S : TypedLinearSpineShape Obs terminal binary start)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart)) :
    canonicalCSNormV47 (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart ≤
      ((Fintype.card N * Fintype.card Obs.M) +
        (Fintype.card N * Fintype.card Obs.M) * Fintype.card Sigma +
        (Fintype.card N * Fintype.card Obs.M) ^ 3 + 1) *
      (4 * (Fintype.card N * Fintype.card Obs.M) + 1) ∧
    (∀ K : Language Sigma,
      CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
          (start := start) epsilonStart ⊆ K →
      K ⊆ UntypedStartLanguage terminal binary start epsilonStart →
      HypLanguage Obs K = UntypedStartLanguage terminal binary start epsilonStart) ∧
    (∀ K : Language Sigma, K ⊆ HypLanguage Obs K) ∧
    (∀ text : Nat → Word Sigma,
      TextFor (UntypedStartLanguage terminal binary start epsilonStart) text →
      ∃ N₀ : Nat, ∀ n : Nat, N₀ ≤ n →
        ConservativeHyp Obs text n =
          UntypedStartLanguage terminal binary start epsilonStart) := by
  constructor
  · exact canonicalCSNorm_original_factor_polynomial_le_v47
      (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
      epsilonStart S
  constructor
  · intro K hWK hKL
    exact canonical_exact_reconstruction_from_ssbnf
      Obs terminal binary start epsilonStart K hWK hKL hSub
  constructor
  · intro K
    exact lemma_sample_consistency Obs K
  · intro text hText
    exact canonical_gold_identification_from_ssbnf
      Obs terminal binary start epsilonStart hSub text hText

/-- v47 name for the already verified degree-five explicit-output envelope. -/
theorem v47BuildEnvelope_degree_five
    {sampleSize stateCount c : Nat}
    (hSample : 1 ≤ sampleSize)
    (hStates : stateCount ≤ c * sampleSize ^ 2) :
    v44BuildEnvelope sampleSize stateCount ≤
      (2 * c ^ 2 + c + 4) * sampleSize ^ 5 :=
  v44BuildEnvelope_degree_five hSample hStates

end FixedHCFGv44
end LeanCfgProject
