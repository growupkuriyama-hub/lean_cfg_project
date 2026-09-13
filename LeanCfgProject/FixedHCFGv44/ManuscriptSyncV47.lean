import LeanCfgProject.FixedHCFGv44.WitnessSetV47
import LeanCfgProject.FixedHCFGv44.LinearManuscriptTheoremV47
import LeanCfgProject.FixedHCFGv44.BoundaryObstructionsV47

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Thin manuscript-synchronization layer for the current TCS v47 source.

The underlying proofs intentionally retain their stable internal names.  This
file exposes theorem names and the witness-set notation used by the revised
manuscript, so the formalization can be audited directly against the labels in
v47 without duplicating any mathematical argument.
-/

/-- Manuscript Proposition `prop:typed-core`: language preservation and yield typing. -/
theorem proposition_typed_core_v47
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    (∀ w : Word Sigma,
      TrimmedTypedStartLanguage Obs terminal binary start epsilonStart w ↔
        UntypedStartLanguage terminal binary start epsilonStart w) ∧
    (∀ (X : TypedNT N Obs) (w : Word Sigma),
      KeptDerives Obs terminal binary start X w →
        obsValue Obs w = X.yieldType) := by
  constructor
  · intro w
    exact typed_refinement_language_iff
      Obs terminal binary start epsilonStart w
  · intro X w d
    exact kept_yield_invariant Obs terminal binary start d

/-- Manuscript Lemma `lem:sample-consistency`. -/
theorem lemma_sample_consistency_v47
    {Sigma : Type u} (Obs : Observer Sigma) (K : Language Sigma) :
    K ⊆ HypLanguage Obs K :=
  lemma_sample_consistency Obs K

/-- Manuscript Theorem `thm:soundness`. -/
theorem theorem_soundness_v47
    {Sigma : Type u} (Obs : Observer Sigma)
    (K L : Language Sigma)
    (hKL : K ⊆ L)
    (hSub : HSubstitutable Obs L) :
    HypLanguage Obs K ⊆ L :=
  theorem_soundness Obs K L hKL hSub

/--
Manuscript Theorem `thm:reconstruction-fixed-h`, stated with the current
witness notation `W(\widetilde G)` rather than the legacy internal name
`CanonicalCS`.
-/
theorem theorem_reconstruction_fixed_h_v47
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (K : Language Sigma)
    (hWK : WitnessSetV47 (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart ⊆ K)
    (hKL : K ⊆ UntypedStartLanguage terminal binary start epsilonStart)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart)) :
    HypLanguage Obs K =
      UntypedStartLanguage terminal binary start epsilonStart := by
  exact canonical_exact_reconstruction_from_ssbnf
    Obs terminal binary start epsilonStart K
    (by simpa [WitnessSetV47] using hWK) hKL hSub

/-- Manuscript Corollary `cor:ilt`, conservative positive-data identification. -/
theorem corollary_ilt_v47
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    [Finite N] [Finite Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart))
    (text : Nat → Word Sigma)
    (hText : TextFor
      (UntypedStartLanguage terminal binary start epsilonStart) text) :
    ∃ N₀ : Nat, ∀ n : Nat, N₀ ≤ n →
      ConservativeHyp Obs text n =
        UntypedStartLanguage terminal binary start epsilonStart :=
  canonical_gold_identification_from_ssbnf
    Obs terminal binary start epsilonStart hSub text hText

/--
Manuscript Theorem `thm:linear-poly`, synchronized to the v47 witness-set
notation.  The substantive proof is the already verified linear package.
-/
theorem theorem_linear_poly_v47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (S : TypedLinearSpineShape Obs terminal binary start)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart)) :
    (∀ z : Word Sigma,
      WitnessSetV47 (Obs := Obs) (terminal := terminal) (binary := binary)
          (start := start) epsilonStart z →
      z.length ≤ 4 * (Fintype.card N * Fintype.card Obs.M)) ∧
    canonicalCSNormV47 (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart ≤
      ((Fintype.card N * Fintype.card Obs.M) +
        (Fintype.card N * Fintype.card Obs.M) * Fintype.card Sigma +
        (Fintype.card N * Fintype.card Obs.M) ^ 3 + 1) *
      (4 * (Fintype.card N * Fintype.card Obs.M) + 1) ∧
    (∀ K : Language Sigma,
      WitnessSetV47 (Obs := Obs) (terminal := terminal) (binary := binary)
          (start := start) epsilonStart ⊆ K →
      K ⊆ UntypedStartLanguage terminal binary start epsilonStart →
      HypLanguage Obs K = UntypedStartLanguage terminal binary start epsilonStart) ∧
    (∀ K : Language Sigma, K ⊆ HypLanguage Obs K) ∧
    (∀ text : Nat → Word Sigma,
      TextFor (UntypedStartLanguage terminal binary start epsilonStart) text →
      ∃ N₀ : Nat, ∀ n : Nat, N₀ ≤ n →
        ConservativeHyp Obs text n =
          UntypedStartLanguage terminal binary start epsilonStart) := by
  simpa [WitnessSetV47] using
    (linear_manuscript_package_v47
      Obs terminal binary start epsilonStart S hSub)

end FixedHCFGv44
end LeanCfgProject
