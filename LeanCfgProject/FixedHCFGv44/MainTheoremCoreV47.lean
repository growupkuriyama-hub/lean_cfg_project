import LeanCfgProject.FixedHCFGv44.CompletenessV47
import LeanCfgProject.FixedHCFGv44.LinearManuscriptTheoremV47
import LeanCfgProject.FixedHCFGv44.ComplexityBounds

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Manuscript-facing assembly for the semantic/combinatorial core of the current
TCS v47 main theorem.

The paper's operational claims `thm:poly-build` and `cor:poly-update` are
complexity statements about an implementation.  The existing Lean development
verifies their combinatorial degree-five envelope, but deliberately does not
pretend to provide a machine-level cost semantics for parsing/string tables.
Accordingly, this file cleanly separates:

* the fully formalized semantic learning claims;
* the arithmetic polynomial envelope supporting the implementation argument;
* the conservative update dichotomy used in the update-time proof.
-/

/--
Semantic core of manuscript Theorem `thm:main` for a fixed reduced SSBNF
target representation.

It packages finiteness/positivity of the witness set, sample consistency,
exact reconstruction once the witnesses have appeared, and conservative Gold
identification.  No polynomial bound on the size of the witness set is claimed
for an arbitrary CFG representation.
-/
theorem theorem_main_semantic_core_v47
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    [Finite N] [Finite Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart)) :
    (WitnessSetV47 (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart).Finite ∧
    WitnessSetV47 (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart ⊆
      UntypedStartLanguage terminal binary start epsilonStart ∧
    (∀ K : Language Sigma, K ⊆ HypLanguage Obs K) ∧
    (∀ K : Language Sigma,
      WitnessSetV47 (Obs := Obs) (terminal := terminal) (binary := binary)
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
  · exact witnessSetV47_finite
      (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart
  constructor
  · exact witnessSetV47_subset_untyped
      Obs terminal binary start epsilonStart
  constructor
  · intro K
    exact lemma_sample_consistency Obs K
  constructor
  · intro K hWK hKL
    exact canonical_exact_reconstruction_from_ssbnf
      Obs terminal binary start epsilonStart K
      (by simpa [WitnessSetV47] using hWK) hKL hSub
  · intro text hText
    exact canonical_gold_identification_from_ssbnf
      Obs terminal binary start epsilonStart hSub text hText

/--
Arithmetic core of manuscript Theorem `thm:poly-build`: once the number `V`
of observed learner states is bounded by `c N^2`, the explicit-output build
envelope is bounded by a fixed multiple of `N^5`.
-/
theorem theorem_poly_build_envelope_v47
    {N V c : Nat}
    (hN : 1 ≤ N)
    (hV : V ≤ c * N ^ 2) :
    v44BuildEnvelope N V ≤ (2 * c ^ 2 + c + 4) * N ^ 5 :=
  v44BuildEnvelope_degree_five hN hV

/--
Semantic branching fact used by manuscript Corollary `cor:poly-update`: an
update either keeps the previous hypothesis or rebuilds exactly from the
accumulated positive data.
-/
theorem corollary_poly_update_dichotomy_v47
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
