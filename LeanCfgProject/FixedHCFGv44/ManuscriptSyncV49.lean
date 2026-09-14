import LeanCfgProject.FixedHCFGv44.MainTheoremCoreV49
import LeanCfgProject.FixedHCFGv44.DyckObstructionV47
import LeanCfgProject.FixedHCFGv44.LukasiewiczObstructionV47

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Thin synchronization layer for TCS manuscript v49.

The stable internal development still lives in the historical `FixedHCFGv44`
namespace and several deep linear/boundary files retain `V47` in their file
names.  This file exposes v49-facing theorem names without duplicating the
mathematics.  In particular it reflects the v49 manuscript order:

* the batch reconstruction operator and conservative learner are defined first;
* yield-only target typing is introduced only for completeness;
* `W(\widetilde G)` is first a finite witness set, becoming a characteristic
  reconstruction sample only after exact reconstruction;
* the Gold corollary records the explicit at-most-one-later-trigger property.

The Clark congruential comparison proposition is not claimed here; it remains a
separate formalization target.
-/

/-- TCS v49 Proposition `prop:typed-core`. -/
theorem proposition_typed_core_v49
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

/-- TCS v49 Lemma `lem:sample-consistency`. -/
theorem lemma_sample_consistency_v49
    {Sigma : Type u} (Obs : Observer Sigma) (K : Language Sigma) :
    K ⊆ HypLanguage Obs K :=
  lemma_sample_consistency Obs K

/-- TCS v49 Theorem `thm:soundness`. -/
theorem theorem_soundness_v49
    {Sigma : Type u} (Obs : Observer Sigma)
    (K L : Language Sigma)
    (hKL : K ⊆ L)
    (hSub : HSubstitutable Obs L) :
    HypLanguage Obs K ⊆ L :=
  theorem_soundness Obs K L hKL hSub

/-- TCS v49 Theorem `thm:reconstruction-fixed-h`. -/
theorem theorem_reconstruction_fixed_h_v49
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (K : Language Sigma)
    (hWK : WitnessSetV49 (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart ⊆ K)
    (hKL : K ⊆ UntypedStartLanguage terminal binary start epsilonStart)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart)) :
    HypLanguage Obs K =
      UntypedStartLanguage terminal binary start epsilonStart := by
  exact canonical_exact_reconstruction_from_ssbnf
    Obs terminal binary start epsilonStart K
    (by simpa [WitnessSetV49] using hWK) hKL hSub

/-- Eventual semantic Gold identification, TCS v49 Corollary `cor:ilt`. -/
theorem corollary_ilt_v49
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
The explicit v49 refinement of `cor:ilt`: after witness coverage, there is at
most one later conservative trigger/rebuild.
-/
theorem corollary_ilt_one_change_v49
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart))
    (text : Nat → Word Sigma)
    (hText : TextFor
      (UntypedStartLanguage terminal binary start epsilonStart) text)
    (n0 : Nat)
    (hCover : WitnessSetV49 (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart ⊆ Seen text n0) :
    ∀ n m : Nat,
      n0 ≤ n → n0 ≤ m →
      text n ∉ ConservativeHyp Obs text n →
      text m ∉ ConservativeHyp Obs text m →
      n = m :=
  theorem_gold_one_change_core_v49
    Obs terminal binary start epsilonStart hSub text hText n0 hCover

/-- TCS v49 Theorem `thm:linear-poly`, using the v49 witness-set name. -/
theorem theorem_linear_poly_v49
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (S : TypedLinearSpineShape Obs terminal binary start)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart)) :
    (∀ z : Word Sigma,
      WitnessSetV49 (Obs := Obs) (terminal := terminal) (binary := binary)
          (start := start) epsilonStart z →
      z.length ≤ 4 * (Fintype.card N * Fintype.card Obs.M)) ∧
    canonicalCSNormV47 (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart ≤
      ((Fintype.card N * Fintype.card Obs.M) +
        (Fintype.card N * Fintype.card Obs.M) * Fintype.card Sigma +
        (Fintype.card N * Fintype.card Obs.M) ^ 3 + 1) *
      (4 * (Fintype.card N * Fintype.card Obs.M) + 1) ∧
    (∀ K : Language Sigma,
      WitnessSetV49 (Obs := Obs) (terminal := terminal) (binary := binary)
          (start := start) epsilonStart ⊆ K →
      K ⊆ UntypedStartLanguage terminal binary start epsilonStart →
      HypLanguage Obs K = UntypedStartLanguage terminal binary start epsilonStart) ∧
    (∀ K : Language Sigma, K ⊆ HypLanguage Obs K) ∧
    (∀ text : Nat → Word Sigma,
      TextFor (UntypedStartLanguage terminal binary start epsilonStart) text →
      ∃ N₀ : Nat, ∀ n : Nat, N₀ ≤ n →
        ConservativeHyp Obs text n =
          UntypedStartLanguage terminal binary start epsilonStart) := by
  simpa [WitnessSetV49] using
    (linear_manuscript_package_v47
      Obs terminal binary start epsilonStart S hSub)

/-- TCS v49 Lemma `lem:finite-monoid-obstruction`. -/
theorem lemma_finite_monoid_obstruction_v49
    {Sigma : Type u} (L : Language Sigma) (Xi : Set (Word Sigma))
    (hXi : Xi.Infinite)
    (hInternal : ∀ x : Word Sigma, x ∈ Xi → Internal x)
    (hSeparate : ∀ x : Word Sigma, x ∈ Xi →
      ∀ y : Word Sigma, y ∈ Xi → x ≠ y →
        ShareContext L x y ∧ ¬ SameDistribution L x y) :
    ¬ RecognizablySubstitutableAt.{u, v} L :=
  finite_monoid_obstruction_v47 L Xi hXi hInternal hSeparate

/-- TCS v49 Corollary `cor:dyck-not-rs`. -/
theorem corollary_dyck_not_rs_v49 :
    ¬ RecognizablySubstitutableAt.{0, v} Dyck1 :=
  corollary_dyck_not_rs_v47

/-- TCS v49 Lemma `lem:rs-fixed-quotient`. -/
theorem lemma_rs_fixed_quotient_v49
    {Sigma : Type u} (Obs : Observer Sigma) (L : Language Sigma)
    (z : Word Sigma)
    (hSub : HSubstitutable Obs L) :
    HSubstitutable Obs (RightQuotient L z) :=
  hSubstitutable_rightQuotient_v47 Obs L z hSub

/-- TCS v49 Lukasiewicz-language obstruction obtained by fixed-word quotient. -/
theorem corollary_lukasiewicz_not_rs_v49 :
    ¬ RecognizablySubstitutableAt.{0, v} LukasiewiczV47 :=
  corollary_lukasiewicz_not_rs_v47

end FixedHCFGv44
end LeanCfgProject
