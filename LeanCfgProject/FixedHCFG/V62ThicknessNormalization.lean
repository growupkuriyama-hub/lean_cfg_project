import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60WindowEnvelope

namespace LeanCfgProject
namespace FixedHCFG

/-!
Arithmetic and theorem-facing transfer layer for v62 Proposition
`thick-ssbnf-normal` and Corollary `window-transfer`.

The appendix normalization itself is an algorithmic CFG transformation.  This
file isolates the quantitative obligations that matter downstream:

* the one-mark path estimate `1 + |V_B| tau_B` remains polynomial when both
  `|V_B|` and `tau_B` have the bounds stated in the appendix;
* the fixed-window yield bound is monotone in the grammar-state count and
  thickness parameter;
* therefore the canonical-witness bound transfers monotonically through any
  normalization satisfying the manuscript's polynomial size/thickness bounds.

This is deliberately separated from a future executable formalization of the
terminal-isolation, binarization, nullable elimination, unit closure, and trim
algorithms themselves.
-/

/-- A convenient explicit polynomial envelope for the normalized grammar size. -/
def V62SSBNFSizeEnvelope (c n : Nat) : Nat :=
  c * (n + 1) ^ 2

/-- A convenient explicit polynomial envelope for normalized thickness. -/
def V62SSBNFThicknessEnvelope (c n tau : Nat) : Nat :=
  c * (n + 1) ^ 2 * (tau + 1)

/--
The key arithmetic in Appendix `thick-ssbnf`: if the binarized grammar has
linearly many nonterminals and thickness `O(n (tau+1))`, then the shortest
nonempty yield obtained from a simple root-to-terminal path has length
`O(n^2 (tau+1))`.
-/
theorem v62_short_nonempty_yield_polynomial_envelope
    {n tau nB tauB cV cT : Nat}
    (hVB : nB ≤ cV * (n + 1))
    (hTauB : tauB ≤ cT * (n + 1) * (tau + 1)) :
    1 + nB * tauB ≤
      (cV * cT + 1) * (n + 1) ^ 2 * (tau + 1) := by
  have hProd :
      nB * tauB ≤
        (cV * (n + 1)) * (cT * (n + 1) * (tau + 1)) :=
    Nat.mul_le_mul hVB hTauB
  have hBaseNe : (n + 1) ^ 2 * (tau + 1) ≠ 0 := by
    positivity
  have hBase : 1 ≤ (n + 1) ^ 2 * (tau + 1) :=
    Nat.one_le_iff_ne_zero.mpr hBaseNe
  calc
    1 + nB * tauB ≤
        (n + 1) ^ 2 * (tau + 1) +
          (cV * (n + 1)) * (cT * (n + 1) * (tau + 1)) :=
      Nat.add_le_add hBase hProd
    _ = (cV * cT + 1) * (n + 1) ^ 2 * (tau + 1) := by
      ring

/-- The manuscript fixed-window yield envelope is monotone in `N` and `tau`. -/
theorem v60WindowYieldBound_mono
    {r N1 N2 tau1 tau2 : Nat}
    (hN : N1 ≤ N2) (hTau : tau1 ≤ tau2) :
    V60WindowYieldBound r N1 tau1 ≤ V60WindowYieldBound r N2 tau2 := by
  by_cases hr : r = 0
  · simpa [V60WindowYieldBound, hr] using hTau
  · simp only [V60WindowYieldBound, hr, if_false]
    exact Nat.add_le_add_left
      (Nat.mul_le_mul (Nat.mul_le_mul_left (2 * r - 1) hN) hTau) r

/-- The complete canonical-witness length envelope used in `window-context`. -/
def V62WindowWitnessEnvelope (r N tau Nt : Nat) : Nat :=
  (Nt + 2) * V60WindowYieldBound r N tau + 1

/-- The complete witness envelope is monotone in all grammar-side parameters. -/
theorem v62WindowWitnessEnvelope_mono
    {r N1 N2 tau1 tau2 Nt1 Nt2 : Nat}
    (hN : N1 ≤ N2) (hTau : tau1 ≤ tau2) (hNt : Nt1 ≤ Nt2) :
    V62WindowWitnessEnvelope r N1 tau1 Nt1 ≤
      V62WindowWitnessEnvelope r N2 tau2 Nt2 := by
  have hB := v60WindowYieldBound_mono (r := r) hN hTau
  have hNt2 : Nt1 + 2 ≤ Nt2 + 2 := Nat.add_le_add_right hNt 2
  unfold V62WindowWitnessEnvelope
  exact Nat.add_le_add_right (Nat.mul_le_mul hNt2 hB) 1

/--
Quantitative transfer used by v62 Corollary `window-transfer`.

`NG` and `tauG` are the size/thickness parameters of the normalized SSBNF
grammar, `Nt` is its retained typed-state count, and `m` is a fixed finite
observer factor bounding typed copies per base nonterminal.  Any witness bound
proved after normalization is therefore bounded by an explicit polynomial
expression in the original size `n` and thickness `tau` once the constants and
fixed observer are fixed.
-/
theorem v62_fixed_window_normalization_transfer
    {r n tau NG tauG Nt m cSize cTau zlen : Nat}
    (hNG : NG ≤ V62SSBNFSizeEnvelope cSize n)
    (hTauG : tauG ≤ V62SSBNFThicknessEnvelope cTau n tau)
    (hNt : Nt ≤ NG * m)
    (hz : zlen ≤ V62WindowWitnessEnvelope r NG tauG Nt) :
    zlen ≤
      V62WindowWitnessEnvelope r
        (V62SSBNFSizeEnvelope cSize n)
        (V62SSBNFThicknessEnvelope cTau n tau)
        (V62SSBNFSizeEnvelope cSize n * m) := by
  have hTyped :
      Nt ≤ V62SSBNFSizeEnvelope cSize n * m := by
    exact hNt.trans (Nat.mul_le_mul_right m hNG)
  exact hz.trans
    (v62WindowWitnessEnvelope_mono hNG hTauG hTyped)

end FixedHCFG
end LeanCfgProject
