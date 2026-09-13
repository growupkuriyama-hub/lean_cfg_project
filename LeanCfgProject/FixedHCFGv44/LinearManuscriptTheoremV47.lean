import LeanCfgProject.FixedHCFGv44.LinearBatchTheoremV47

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Manuscript-facing assembly theorem for the current TCS v47 linear result.

The revised paper uses the yield-only typed refinement `(A, μ)`, so the
retained typed-state count is bounded by `|N| * |M|`.  This theorem collects
in one place the two quantitative conclusions used in Section 7 (uniform
canonical-word length and characteristic-sample norm) together with exact
reconstruction, sample consistency, and conservative Gold convergence.
-/

/--
A single theorem-level contract matching the current v47 linear learning
package.  The polynomial construction-time envelope is recorded separately as
`v47BuildEnvelope_degree_five` because it is a statement about the learner's
finite-sample implementation parameters rather than about a fixed target.
-/
theorem linear_manuscript_package_v47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (S : TypedLinearSpineShape Obs terminal binary start)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart)) :
    (∀ z : Word Sigma,
      CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
          (start := start) epsilonStart z →
      z.length ≤ 4 * (Fintype.card N * Fintype.card Obs.M)) ∧
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
  · intro z hz
    exact canonicalCS_word_length_le_original_state_factor_v47
      epsilonStart S hz
  · exact linear_batch_reconstruction_core_v47
      Obs terminal binary start epsilonStart S hSub

end FixedHCFGv44
end LeanCfgProject
