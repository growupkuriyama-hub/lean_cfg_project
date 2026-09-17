import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V62WindowSampleBounds
import LeanCfgProject.FixedHCFG.V60WindowCompressionConstructive

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
# Encoded fixed-window thick data for v62

This file combines the two quantitative halves already formalized for Section 7:

* every canonical witness has the `window-context` length bound; and
* the actual canonical witness set has polynomially many potential slots.

For a fixed observer and alphabet this gives an explicit polynomial envelope
for the encoded characteristic-data size of a reduced SSBNF grammar.  The
separate CFG-to-SSBNF normalization algorithm is not asserted here.
-/

/-- The coarse witness-slot envelope is monotone in the retained-state count. -/
theorem v62WindowWitnessCountEnvelope_mono_state
    {Nt1 Nt2 sigmaCard : Nat}
    (hNt : Nt1 <= Nt2) :
    V62WindowWitnessCountEnvelope Nt1 sigmaCard <=
      V62WindowWitnessCountEnvelope Nt2 sigmaCard := by
  have hLinear : Nt1 * sigmaCard <= Nt2 * sigmaCard :=
    Nat.mul_le_mul_right sigmaCard hNt
  have hSquare : Nt1 * Nt1 <= Nt2 * Nt2 :=
    Nat.mul_le_mul hNt hNt
  have hCube : Nt1 * (Nt1 * Nt1) <= Nt2 * (Nt2 * Nt2) :=
    Nat.mul_le_mul hNt hSquare
  unfold V62WindowWitnessCountEnvelope
  exact Nat.add_le_add hNt
    (Nat.add_le_add hLinear (Nat.add_le_add_right hCube 1))

/--
Explicit polynomial encoded-data envelope.  `m` is the fixed observer size and
`sigmaCard` the fixed ambient alphabet size.  The factor `+1` after the witness
length is exactly the manuscript's encoded-sample convention.
-/
def V62WindowDataEnvelope
    (r N tau m sigmaCard : Nat) : Nat :=
  V62WindowWitnessCountEnvelope (N * m) sigmaCard *
    (V62WindowWitnessEnvelope r N tau (N * m) + 1)

/--
Generic combination theorem: once all canonical words obey the manuscript
witness-length envelope, the actual encoded sample is bounded by the explicit
fixed-window polynomial envelope.
-/
theorem v62_canonical_witness_encoded_size_le_window_data
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop)
    (r tau : Nat)
    (hLen : forall z,
      z ∈ V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart ->
      z.length <=
        V62WindowWitnessEnvelope r (Fintype.card N) tau
          (Fintype.card (V60KeptState Obs terminal binary start))) :
    V62EncodedSampleSize
        (V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start) epsilonStart)
        (v60_canonical_witness_finite
          Obs terminal binary start epsilonStart) <=
      V62WindowDataEnvelope r (Fintype.card N) tau
        (Fintype.card Obs.M) (Fintype.card Sigma) := by
  let Nt := Fintype.card (V60KeptState Obs terminal binary start)
  let NtMax := Fintype.card N * Fintype.card Obs.M
  have hRaw :=
    v62_canonical_witness_encoded_size_le
      Obs terminal binary start epsilonStart hLen
  have hNt : Nt <= NtMax := by
    simpa [Nt, NtMax] using
      (v62_kept_state_card_le_base_times_observer
        Obs terminal binary start)
  have hCount :
      V62WindowWitnessCountEnvelope Nt (Fintype.card Sigma) <=
        V62WindowWitnessCountEnvelope NtMax (Fintype.card Sigma) :=
    v62WindowWitnessCountEnvelope_mono_state hNt
  have hWitness :
      V62WindowWitnessEnvelope r (Fintype.card N) tau Nt <=
        V62WindowWitnessEnvelope r (Fintype.card N) tau NtMax :=
    v62WindowWitnessEnvelope_mono (r := r) (Nat.le_refl _) (Nat.le_refl _) hNt
  have hProduct :
      V62WindowWitnessCountEnvelope Nt (Fintype.card Sigma) *
          (V62WindowWitnessEnvelope r (Fintype.card N) tau Nt + 1) <=
        V62WindowWitnessCountEnvelope NtMax (Fintype.card Sigma) *
          (V62WindowWitnessEnvelope r (Fintype.card N) tau NtMax + 1) :=
    Nat.mul_le_mul hCount (Nat.add_le_add_right hWitness 1)
  exact hRaw.trans (by
    simpa [V62WindowDataEnvelope, Nt, NtMax] using hProduct)

/--
Positive-window quantitative core of manuscript Theorem `window-thick` for a
reduced SSBNF grammar: base thickness alone yields the full encoded-data bound.
-/
theorem v62_window_thick_data_positive
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop)
    (k l tau : Nat)
    (hr : k + l != 0)
    (hObserver : V60WindowObserverCompatible Obs k l)
    (hThickness : V60BaseThicknessBound terminal binary tau) :
    V62EncodedSampleSize
        (V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start) epsilonStart)
        (v60_canonical_witness_finite
          Obs terminal binary start epsilonStart) <=
      V62WindowDataEnvelope (k + l) (Fintype.card N) tau
        (Fintype.card Obs.M) (Fintype.card Sigma) := by
  apply v62_canonical_witness_encoded_size_le_window_data
    Obs terminal binary start epsilonStart (k + l) tau
  intro z hz
  simpa [V62WindowWitnessEnvelope] using
    (v60_window_witness_bound_from_thickness
      Obs terminal binary start epsilonStart
      k l tau hr hObserver hThickness hz)

/--
Zero-window endpoint of the same encoded-data theorem.  This uses the separate
nonempty-type collapse required by the manuscript at `(k,l)=(0,0)`.
-/
theorem v62_window_thick_data_zero
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
          Obs terminal binary start epsilonStart) <=
      V62WindowDataEnvelope 0 (Fintype.card N) tau
        (Fintype.card Obs.M) (Fintype.card Sigma) := by
  apply v62_canonical_witness_encoded_size_le_window_data
    Obs terminal binary start epsilonStart 0 tau
  intro z hz
  simpa [V62WindowWitnessEnvelope, V60WindowYieldBound] using
    (v60_window_zero_witness_bound
      Obs terminal binary start epsilonStart
      (Fintype.card N) tau hObserver hThickness hz)

end FixedHCFG
end LeanCfgProject
