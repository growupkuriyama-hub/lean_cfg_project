import LeanCfgProject.FixedHCFGv44.LinearSpineWrapperContextV47
import LeanCfgProject.FixedHCFGv44.CharacteristicDataBounds

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
End-to-end length theorem for the v47 linear characteristic reconstruction
data.  The hypotheses are exactly the retained typed linear-spine shape; the
canonical witness families themselves are the general Section 4 families.
-/

/-- Every canonical witness word has length at most four times the retained typed-state count. -/
theorem canonicalCS_word_length_le_actual_v47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop)
    (S : TypedLinearSpineShape Obs terminal binary start)
    {z : Word Sigma}
    (hz : CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart z) :
    z.length ≤ 4 * Fintype.card (KeptState Obs terminal binary start) := by
  rcases short_canonical_witnesses_from_typed_shape_v47 S with ⟨hOmega, hCtx⟩
  have hn : 0 < Fintype.card (KeptState Obs terminal binary start) := by
    rcases hz with hAnchor | hTerminal | hBinary | hEps
    · rcases hAnchor with ⟨X, hX⟩
      exact Fintype.card_pos_iff.mpr ⟨X⟩
    · rcases hTerminal with ⟨X, a, hRule, hX⟩
      exact Fintype.card_pos_iff.mpr ⟨X⟩
    · rcases hBinary with ⟨X, Y, Z, hRule, hX⟩
      exact Fintype.card_pos_iff.mpr ⟨X⟩
    · rcases hEps with ⟨hEmpty, hEpsilon⟩
      -- In the epsilon-only endpoint there may be no retained non-start state.
      subst z
      simp
  exact canonicalCS_word_length_le_four_mul epsilonStart hn hOmega hCtx hz

/--
For non-epsilon canonical witnesses, the preceding bound composes directly
with the yield-only state-count estimate `n_t <= |N||M|`.
-/
theorem canonicalCS_nonempty_word_length_le_original_state_factor_v47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop)
    (S : TypedLinearSpineShape Obs terminal binary start)
    {z : Word Sigma}
    (hz : CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart z)
    (hzNonempty : z ≠ []) :
    z.length ≤ 4 * (Fintype.card N * Fintype.card Obs.M) := by
  have hTyped := canonicalCS_word_length_le_actual_v47 epsilonStart S hz
  have hCard : Fintype.card (KeptState Obs terminal binary start) ≤
      Fintype.card N * Fintype.card Obs.M := kept_state_card_le
  exact le_trans hTyped (Nat.mul_le_mul_left 4 hCard)

end FixedHCFGv44
end LeanCfgProject
