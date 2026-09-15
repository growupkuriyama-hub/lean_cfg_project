import LeanCfgProject.FixedHCFG.V60CanonicalBasis

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
End-to-end manuscript-facing theorems for the exact v60 development.

This file closes the chain

SSBNF -> yield-only typed refinement -> trim -> canonical witness set
      -> exact batch reconstruction -> conservative Gold identification.
-/

/-- The canonical reconstruction basis denotes exactly the original SSBNF language. -/
theorem v60_canonical_basis_language_eq_untyped
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop) :
    V60BasisLanguage
        (v60CanonicalReconstructionBasis Obs terminal binary start epsilonStart) =
      V60UntypedStartLanguage terminal binary start epsilonStart := by
  ext w
  exact v60_canonical_basis_language_iff_untyped
    Obs terminal binary start epsilonStart w

/--
Exact finite-sample reconstruction for the concrete v60 characteristic witness
set extracted from an SSBNF target grammar.
-/
theorem v60_end_to_end_exact_reconstruction
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
  let B := v60CanonicalReconstructionBasis
    Obs terminal binary start epsilonStart
  have hEq : V60BasisLanguage B =
      V60UntypedStartLanguage terminal binary start epsilonStart := by
    simpa [B] using
      v60_canonical_basis_language_eq_untyped
        Obs terminal binary start epsilonStart
  have hWB : B.witnessSet ⊆ K := by
    simpa [B, v60CanonicalReconstructionBasis] using hWitness
  have hKB : K ⊆ V60BasisLanguage B := by
    intro z hz
    rw [hEq]
    exact hKL hz
  have hSubB : HSubstitutableV60 Obs (V60BasisLanguage B) := by
    rw [hEq]
    exact hSub
  have hExact := v60_exact_reconstruction B K hWB hKB hSubB w
  rw [hEq] at hExact
  exact hExact

/--
Corollary 5.8, fully instantiated with the concrete canonical v60 witness set:
on every positive text for the SSBNF target language, the conservative learner
eventually stabilizes at that target language.
-/
theorem v60_end_to_end_gold_identification
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
  let B := v60CanonicalReconstructionBasis
    Obs terminal binary start epsilonStart
  have hEq : V60BasisLanguage B =
      V60UntypedStartLanguage terminal binary start epsilonStart := by
    simpa [B] using
      v60_canonical_basis_language_eq_untyped
        Obs terminal binary start epsilonStart
  have hFinite : B.witnessSet.Finite := by
    simpa [B, v60CanonicalReconstructionBasis] using
      v60_canonical_witness_finite
        Obs terminal binary start epsilonStart
  have hWitnessTarget : B.witnessSet ⊆ V60BasisLanguage B := by
    intro z hz
    rw [hEq]
    apply v60_canonical_witness_subset_untyped
      Obs terminal binary start epsilonStart
    simpa [B, v60CanonicalReconstructionBasis] using hz
  have hSubB : HSubstitutableV60 Obs (V60BasisLanguage B) := by
    rw [hEq]
    exact hSub
  have hTextB : TextFor (V60BasisLanguage B) text := by
    rw [hEq]
    exact hText
  obtain ⟨N0, hN0⟩ :=
    v60_gold_identification B hFinite hWitnessTarget hSubB text hTextB
  refine ⟨N0, ?_⟩
  intro n hn
  exact (hN0 n hn).trans hEq

end FixedHCFG
end LeanCfgProject
