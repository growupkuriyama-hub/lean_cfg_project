import LeanCfgProject.FixedHCFG.V60EndToEnd
import LeanCfgProject.FixedHCFG.V60WindowYieldBridge

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Exact manuscript baseline for TCS working revision v61.

Revision v61 keeps the corrected fixed-h reconstruction core introduced in the
v60 development: nonempty internal fragments, yield-only target typing,
canonical positive witnesses, exact set-driven reconstruction, and the
conservative Gold wrapper.  The genuinely new proof obligation in v61 is the
polynomial thickness-preserving normalization from an arbitrary reduced CFG to
SSBNF (Proposition `thick-ssbnf-normal`) and its use in the fixed-window
complexity transfer.

The two theorem wrappers below deliberately reuse the already checked exact-v60
core rather than duplicating it.  New v61-specific normalization work lives in
separate files and must not be confused with the older exploratory v60 marked-
leaf files.
-/

/-- v61 reuses the exact finite-sample reconstruction theorem unchanged. -/
theorem v61_end_to_end_exact_reconstruction
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

/-- v61 also reuses the corrected conservative Gold convergence theorem. -/
theorem v61_end_to_end_gold_identification
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

end FixedHCFG
end LeanCfgProject
