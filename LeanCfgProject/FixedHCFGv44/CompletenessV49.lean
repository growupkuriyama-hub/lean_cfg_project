import LeanCfgProject.FixedHCFGv44.WitnessSetV49
import LeanCfgProject.FixedHCFGv44.CanonicalReconstruction

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Manuscript-facing completeness theorem for TCS v49.

This matches Theorem `thm:complete` in the revised order: the batch operator
and learner have already been defined before the target-side yield-typed
refinement is introduced.  The statement intentionally assumes only that the
finite witness set is contained in the positive sample.  It does not assume
`K ⊆ L` and does not assume fixed-`h` substitutability; those hypotheses enter
only in soundness/exact reconstruction.
-/

/-- TCS v49 Theorem `thm:complete`: completeness from the finite witnesses. -/
theorem theorem_complete_v49
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (K : Language Sigma)
    (hWK : WitnessSetV49 (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart ⊆ K) :
    Set.Subset
      (UntypedStartLanguage terminal binary start epsilonStart)
      (HypLanguage Obs K) := by
  let B := canonicalReconstructionBasis Obs terminal binary start epsilonStart
  have hCSK : B.CS ⊆ K := by
    simpa [B, canonicalReconstructionBasis, WitnessSetV49] using hWK
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
