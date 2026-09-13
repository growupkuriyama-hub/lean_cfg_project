import LeanCfgProject.FixedHCFGv44.WitnessSetV47
import LeanCfgProject.FixedHCFGv44.CanonicalReconstruction

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Manuscript-facing completeness theorem for the current TCS v47 source.

This is the Lean counterpart of Theorem `thm:complete`.  In particular, the
statement intentionally assumes only inclusion of the finite witness set in
the positive sample.  It does **not** assume sample consistency `K ⊆ L` and
does **not** assume fixed-`h` substitutability.  Those hypotheses belong only
to the soundness/exact-reconstruction step.
-/

/--
Manuscript Theorem `thm:complete`: completeness from the finite witnesses.
-/
theorem theorem_complete_v47
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (K : Language Sigma)
    (hWK : WitnessSetV47 (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart ⊆ K) :
    UntypedStartLanguage terminal binary start epsilonStart ⊆
      HypLanguage Obs K := by
  let B := canonicalReconstructionBasis Obs terminal binary start epsilonStart
  have hCSK : B.CS ⊆ K := by
    simpa [B, canonicalReconstructionBasis, WitnessSetV47] using hWK
  have hBasisComplete : BasisLanguage B ⊆ HypLanguage Obs K :=
    theorem_completeness B K hCSK
  intro w hw
  apply hBasisComplete
  have hLangEq :
      BasisLanguage B = UntypedStartLanguage terminal binary start epsilonStart := by
    simpa [B] using
      (canonicalBasisLanguage_eq_untyped
        Obs terminal binary start epsilonStart)
  rw [hLangEq]
  exact hw

end FixedHCFGv44
end LeanCfgProject
