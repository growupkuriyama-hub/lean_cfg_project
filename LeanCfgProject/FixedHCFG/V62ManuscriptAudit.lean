import LeanCfgProject.FixedHCFG.V60Summary

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
# TCS v62 manuscript audit

The current TCS revision v62 keeps the exact nonempty-factor learner kernel,
yield-only typed refinement, canonical finite witness set, and conservative
Gold wrapper that were formalized in the manuscript-faithful `V60*` layer.

This file restates the current v62 theorem-facing claims with v62 names.  It is
not a second implementation: each result below is discharged by the exact
kernel already checked in the `V60*` chain.  The purpose is to make manuscript
version drift explicit and CI-auditable.

Current v62 correspondence:

* Proposition `typed-core`          -> yield-only typing/language preservation;
* Lemma `sample-consistency`        -> positive sample is generated;
* Theorem `soundness`               -> strong R1--R4 invariant + R5;
* Theorem `complete`                -> finite canonical witness simulation;
* Theorem `reconstruction-fixed-h`  -> exact finite-sample reconstruction;
* Corollary `ilt`                   -> at most one later rebuild and Gold convergence;
* Lemma `window-typed-yield`        -> constructive fixed-window typed-yield
  bounds from base thickness, including the separate zero-window endpoint;
* Lemma `window-context`            -> constructive canonical context and
  characteristic-witness bounds from those yield bounds.
-/

/-- v62 Proposition `typed-core`, yield invariant. -/
theorem v62_typed_core_yield_invariant
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma) (binary : V60BinaryRules N)
    {X : V60TypedNT N Obs} {w : Word Sigma}
    (d : V60YieldTypedDerives Obs terminal binary X w) :
    Obs.value w = X.yieldType := by
  exact v60_yield_typed_invariant Obs terminal binary d

/-- v62 Proposition `typed-core`, language preservation before trimming. -/
theorem v62_typed_core_language_preservation
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma) (binary : V60BinaryRules N)
    (start : V60StartRules N) (epsilonStart : Prop)
    (w : Word Sigma) :
    V60FullTypedStartLanguage Obs terminal binary start epsilonStart w ↔
      V60UntypedStartLanguage terminal binary start epsilonStart w := by
  exact v60_full_typed_language_iff_untyped
    Obs terminal binary start epsilonStart w

/-- v62 Lemma `sample-consistency`. -/
theorem v62_sample_consistency
    {Sigma : Type u} (Obs : Observer Sigma) (K : Language Sigma) :
    K ⊆ fun w => V60StartDerives Obs K w := by
  exact v60_sample_consistency Obs K

/-- v62 Theorem `soundness` for the exact nonempty-factor R1--R5 kernel. -/
theorem v62_soundness
    {Sigma : Type u}
    (Obs : Observer Sigma)
    (K L : Language Sigma)
    (hKL : K ⊆ L)
    (hSub : HSubstitutableV60 Obs L)
    {w : Word Sigma}
    (hstart : V60StartDerives Obs K w) :
    w ∈ L := by
  exact v60_start_soundness Obs K L hKL hSub hstart

/-- v62 Theorem `complete`: the finite canonical witnesses simulate the target. -/
theorem v62_completeness_from_finite_witnesses
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W)
    (K : Language Sigma)
    (hWK : B.witnessSet ⊆ K)
    {w : Word Sigma}
    (hw : V60BasisLanguage B w) :
    V60StartDerives Obs K w := by
  exact v60_completeness B K hWK hw

/-- v62 Theorem `reconstruction-fixed-h`. -/
theorem v62_exact_finite_sample_reconstruction
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W)
    (K : Language Sigma)
    (hWK : B.witnessSet ⊆ K)
    (hKL : K ⊆ V60BasisLanguage B)
    (hSub : HSubstitutableV60 Obs (V60BasisLanguage B))
    (w : Word Sigma) :
    V60StartDerives Obs K w ↔ V60BasisLanguage B w := by
  exact v60_exact_reconstruction B K hWK hKL hSub w

/--
v62 Corollary `ilt`, direct mind-change formulation: after the witness set has
appeared, two distinct later rebuilds are impossible.
-/
theorem v62_at_most_one_rebuild_after_witness
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W)
    (hSub : HSubstitutableV60 Obs (V60BasisLanguage B))
    (text : Nat → Word Sigma)
    (hText : TextFor (V60BasisLanguage B) text)
    (n0 n m : Nat)
    (hWitness0 : B.witnessSet ⊆ PrefixSample text n0)
    (hn0 : n0 ≤ n)
    (hnm : n < m)
    (hnRebuild : V60RebuildsAt Obs text n) :
    ¬ V60RebuildsAt Obs text m := by
  exact v60_at_most_one_rebuild_after_witness
    B hSub text hText n0 n m hWitness0 hn0 hnm hnRebuild

/-- v62 Corollary `ilt`, Gold convergence. -/
theorem v62_gold_identification
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W)
    (hWitnessFinite : B.witnessSet.Finite)
    (hWitnessTarget : B.witnessSet ⊆ V60BasisLanguage B)
    (hSub : HSubstitutableV60 Obs (V60BasisLanguage B))
    (text : Nat → Word Sigma)
    (hText : TextFor (V60BasisLanguage B) text) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      V60ConservativeHypothesis Obs text n = V60BasisLanguage B := by
  exact v60_gold_identification
    B hWitnessFinite hWitnessTarget hSub text hText

/-- Concrete SSBNF-to-learner instance of v62 exact reconstruction. -/
theorem v62_end_to_end_exact_reconstruction
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop)
    (K : Language Sigma)
    (hWitness :
      V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start) epsilonStart ⊆ K)
    (hKL : K ⊆ V60UntypedStartLanguage terminal binary start epsilonStart)
    (hSub : HSubstitutableV60 Obs
      (V60UntypedStartLanguage terminal binary start epsilonStart))
    (w : Word Sigma) :
    V60StartDerives Obs K w ↔
      V60UntypedStartLanguage terminal binary start epsilonStart w := by
  exact v60_end_to_end_exact_reconstruction
    Obs terminal binary start epsilonStart K hWitness hKL hSub w

/-- Concrete SSBNF-to-learner instance of v62 Gold identification. -/
theorem v62_end_to_end_gold_identification
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    [Finite N] [Finite Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop)
    (hSub : HSubstitutableV60 Obs
      (V60UntypedStartLanguage terminal binary start epsilonStart))
    (text : Nat → Word Sigma)
    (hText : TextFor
      (V60UntypedStartLanguage terminal binary start epsilonStart) text) :
    ∃ N0 : Nat, ∀ n : Nat, N0 ≤ n →
      V60ConservativeHypothesis Obs text n =
        V60UntypedStartLanguage terminal binary start epsilonStart := by
  exact v60_end_to_end_gold_identification
    Obs terminal binary start epsilonStart hSub text hText

/--
v62 Lemma `window-typed-yield`, positive-window case.  The former structural
certificate premise has been eliminated: base SSBNF thickness plus fixed-window
observer compatibility construct the bounded typed yield directly.
-/
theorem v62_window_typed_yield_positive
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (k l tau : Nat)
    (hr : k + l ≠ 0)
    (hObserver : V60WindowObserverCompatible Obs k l)
    (hThickness : V60BaseThicknessBound terminal binary tau) :
    ∀ X : V60KeptState Obs terminal binary start,
      ∃ z : Word Sigma,
        V60YieldTypedDerives Obs terminal binary X.1 z ∧
          z.length ≤
            V60WindowYieldBound (k + l) (Fintype.card N) tau := by
  exact v60_window_typed_yield_candidate_from_thickness
    Obs terminal binary start k l tau hr hObserver hThickness

/-- v62 Lemma `window-typed-yield`, endpoint `(k,l)=(0,0)`. -/
theorem v62_window_typed_yield_zero
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (tau : Nat)
    (hObserver : V60NonemptyObserverTrivial Obs)
    (hThickness : V60BaseThicknessBound terminal binary tau) :
    ∀ X : V60KeptState Obs terminal binary start,
      ∃ z : Word Sigma,
        V60YieldTypedDerives Obs terminal binary X.1 z ∧ z.length ≤ tau := by
  simpa [V60WindowYieldBound] using
    (v60_window_zero_typed_yield_candidate
      Obs terminal binary start (Fintype.card N) tau hObserver hThickness)

/-- v62 Lemma `window-context`, positive-window canonical-context bound. -/
theorem v62_window_context_bound_positive
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (k l tau : Nat)
    (hr : k + l ≠ 0)
    (hObserver : V60WindowObserverCompatible Obs k l)
    (hThickness : V60BaseThicknessBound terminal binary tau) :
    ∀ X : V60KeptState Obs terminal binary start,
      (v60CanonicalLeftCtx X).length +
        (v60CanonicalRightCtx X).length ≤
          Fintype.card (V60KeptState Obs terminal binary start) *
            V60WindowYieldBound (k + l) (Fintype.card N) tau := by
  exact v60_window_canonical_context_bound_from_thickness
    Obs terminal binary start k l tau hr hObserver hThickness

/-- v62 Lemma `window-context`, zero-window canonical-context bound. -/
theorem v62_window_context_bound_zero
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (tau : Nat)
    (hObserver : V60NonemptyObserverTrivial Obs)
    (hThickness : V60BaseThicknessBound terminal binary tau) :
    ∀ X : V60KeptState Obs terminal binary start,
      (v60CanonicalLeftCtx X).length +
        (v60CanonicalRightCtx X).length ≤
          Fintype.card (V60KeptState Obs terminal binary start) * tau := by
  have hYield := v60_window_zero_typed_yield_candidate
    Obs terminal binary start (Fintype.card N) tau hObserver hThickness
  simpa [V60WindowYieldBound] using
    (v60_window_canonical_context_bound_from_yields
      Obs terminal binary start 0 (Fintype.card N) tau hYield)

/-- v62 Lemma `window-context`, positive-window characteristic-witness bound. -/
theorem v62_window_witness_bound_positive
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop)
    (k l tau : Nat)
    (hr : k + l ≠ 0)
    (hObserver : V60WindowObserverCompatible Obs k l)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {z : Word Sigma}
    (hz : V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart z) :
    z.length ≤
      (Fintype.card (V60KeptState Obs terminal binary start) + 2) *
        V60WindowYieldBound (k + l) (Fintype.card N) tau + 1 := by
  exact v60_window_witness_bound_from_thickness
    Obs terminal binary start epsilonStart
    k l tau hr hObserver hThickness hz

/-- v62 Lemma `window-context`, zero-window characteristic-witness bound. -/
theorem v62_window_witness_bound_zero
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop)
    (tau : Nat)
    (hObserver : V60NonemptyObserverTrivial Obs)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {z : Word Sigma}
    (hz : V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart z) :
    z.length ≤
      (Fintype.card (V60KeptState Obs terminal binary start) + 2) * tau + 1 := by
  exact v60_window_zero_witness_bound
    Obs terminal binary start epsilonStart
    (Fintype.card N) tau hObserver hThickness hz

end FixedHCFG
end LeanCfgProject
