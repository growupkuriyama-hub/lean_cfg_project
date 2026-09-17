import LeanCfgProject.FixedHCFG.V62WindowThickData

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
# v62 fixed-window theorem audit aliases

This file gives manuscript-facing names to the explicit encoded-data bounds now
proved for reduced SSBNF grammars.  It also records the quantitative transfer
used by Corollary `window-transfer` under the polynomial normalization bounds.

Important: the executable arbitrary-CFG -> reduced-SSBNF normalization
algorithm of Proposition `thick-ssbnf-normal` is not asserted here.  Only the
already formalized downstream arithmetic transfer is restated.
-/

/--
v62 Theorem `window-thick`, positive-window quantitative core for a reduced
SSBNF grammar.  The bound is on the manuscript encoded characteristic-data
size `sum_{w in W} (|w|+1)`.
-/
theorem v62_window_thick_encoded_positive
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop)
    (k l tau : Nat)
    (hr : k + l ≠ 0)
    (hObserver : V60WindowObserverCompatible Obs k l)
    (hThickness : V60BaseThicknessBound terminal binary tau) :
    V62EncodedSampleSize
        (V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start) epsilonStart)
        (v60_canonical_witness_finite
          Obs terminal binary start epsilonStart) ≤
      V62WindowDataEnvelope (k + l) (Fintype.card N) tau
        (Fintype.card Obs.M) (Fintype.card Sigma) := by
  exact v62_window_thick_data_positive
    Obs terminal binary start epsilonStart
    k l tau hr hObserver hThickness

/-- v62 Theorem `window-thick`, endpoint `(k,l)=(0,0)`. -/
theorem v62_window_thick_encoded_zero
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop)
    (tau : Nat)
    (hObserver : V60NonemptyObserverTrivial Obs)
    (hThickness : V60BaseThicknessBound terminal binary tau) :
    V62EncodedSampleSize
        (V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start) epsilonStart)
        (v60_canonical_witness_finite
          Obs terminal binary start epsilonStart) ≤
      V62WindowDataEnvelope 0 (Fintype.card N) tau
        (Fintype.card Obs.M) (Fintype.card Sigma) := by
  exact v62_window_thick_data_zero
    Obs terminal binary start epsilonStart tau hObserver hThickness

/--
v62 Corollary `window-transfer`, quantitative arithmetic after an SSBNF
normalization satisfying the manuscript polynomial size/thickness bounds.
This theorem intentionally does not construct that normalization.
-/
theorem v62_window_transfer_arithmetic
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
  exact v62_fixed_window_normalization_transfer hNG hTauG hNt hz

end FixedHCFG
end LeanCfgProject
