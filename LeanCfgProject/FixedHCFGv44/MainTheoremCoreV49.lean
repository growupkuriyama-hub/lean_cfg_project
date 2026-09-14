import LeanCfgProject.FixedHCFGv44.CompletenessV49
import LeanCfgProject.FixedHCFGv44.SequentialOneChangeV49
import LeanCfgProject.FixedHCFGv44.LinearManuscriptTheoremV47
import LeanCfgProject.FixedHCFGv44.ComplexityBounds

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Manuscript-facing assembly for the semantic/combinatorial core of TCS v49.

Version 49 defines the batch reconstruction operator before introducing the
target-side yield-typed refinement, and strengthens the Gold corollary with an
explicit one-change-after-cover statement.  The underlying mathematical
objects are unchanged, so this file reuses the stable core while exposing the
current manuscript order and notation.

As before, the operational complexity claims are represented by the verified
combinatorial degree-five envelope and update dichotomy.  This does not claim
a machine-level cost semantics for parser or string-table implementation.
-/

/-- Semantic core of TCS v49 Theorem `thm:main`. -/
theorem theorem_main_semantic_core_v49
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    [Finite N] [Finite Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart)) :
    (WitnessSetV49 (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart).Finite ∧
    WitnessSetV49 (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart ⊆
      UntypedStartLanguage terminal binary start epsilonStart ∧
    (∀ K : Language Sigma, K ⊆ HypLanguage Obs K) ∧
    (∀ K : Language Sigma,
      WitnessSetV49 (Obs := Obs) (terminal := terminal) (binary := binary)
          (start := start) epsilonStart ⊆ K →
      K ⊆ UntypedStartLanguage terminal binary start epsilonStart →
      HypLanguage Obs K =
        UntypedStartLanguage terminal binary start epsilonStart) ∧
    (∀ text : Nat → Word Sigma,
      TextFor (UntypedStartLanguage terminal binary start epsilonStart) text →
      ∃ N₀ : Nat, ∀ n : Nat, N₀ ≤ n →
        ConservativeHyp Obs text n =
          UntypedStartLanguage terminal binary start epsilonStart) := by
  constructor
  · exact witnessSetV49_finite
      (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart
  constructor
  · exact witnessSetV49_subset_untyped
      Obs terminal binary start epsilonStart
  constructor
  · intro K
    exact lemma_sample_consistency Obs K
  constructor
  · intro K hWK hKL
    exact canonical_exact_reconstruction_from_ssbnf
      Obs terminal binary start epsilonStart K
      (by simpa [WitnessSetV49] using hWK) hKL hSub
  · intro text hText
    exact canonical_gold_identification_from_ssbnf
      Obs terminal binary start epsilonStart hSub text hText

/--
The strengthened v49 Gold clause: after the finite witness set has appeared,
there is at most one later conservative trigger/rebuild stage.
-/
theorem theorem_gold_one_change_core_v49
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
  canonical_at_most_one_trigger_after_witness_cover_v49
    Obs terminal binary start epsilonStart hSub text hText n0 hCover

/-- Arithmetic core supporting TCS v49 Theorem `thm:poly-build`. -/
theorem theorem_poly_build_envelope_v49
    {N V c : Nat}
    (hN : 1 ≤ N)
    (hV : V ≤ c * N ^ 2) :
    v44BuildEnvelope N V ≤ (2 * c ^ 2 + c + 4) * N ^ 5 :=
  v44BuildEnvelope_degree_five hN hV

/-- Semantic branch used by TCS v49 Corollary `cor:poly-update`. -/
theorem corollary_poly_update_dichotomy_v49
    {Sigma : Type u}
    (Obs : Observer Sigma) (text : Nat → Word Sigma) (n : Nat) :
    ConservativeHyp Obs text (n + 1) = ConservativeHyp Obs text n ∨
    ConservativeHyp Obs text (n + 1) =
      HypLanguage Obs (Seen text (n + 1)) := by
  classical
  have hStep :
      ConservativeHyp Obs text (n + 1) =
        (if text n ∈ ConservativeHyp Obs text n then
          ConservativeHyp Obs text n
        else
          HypLanguage Obs (Seen text (n + 1))) := by
    rw [ConservativeHyp]
  by_cases hKeep : text n ∈ ConservativeHyp Obs text n
  · left
    rw [hStep, if_pos hKeep]
  · right
    rw [hStep, if_neg hKeep]

end FixedHCFGv44
end LeanCfgProject
