import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60CanonicalBasis
import LeanCfgProject.FixedHCFG.V62ThicknessNormalization

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
# v62 fixed-window sample-count bounds

This file supplies the finite-cardinality part of manuscript Theorem
`window-thick`.  The constructive Section-7 development already bounds the
length of every canonical witness.  Here we discharge the remaining displayed
state-count estimate

`N_t <= N * |M|`

for the actual retained yield-typed state space, and record a polynomial slot
count for the four kinds of canonical witnesses (anchors, terminal-rule
witnesses, binary-rule witnesses, and the optional empty word).  We then pass
from the slot count and a uniform word-length bound to the manuscript's encoded
sample-size convention `sum_{w in W} (|w|+1)`.
-/

/--
Actual retained typed states inject into an underlying nonterminal together
with one observer value.  This is the manuscript estimate `N_t <= N |M|`.
-/
theorem v62_kept_state_card_le_base_times_observer
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N) :
    Fintype.card (V60KeptState Obs terminal binary start) <=
      Fintype.card N * Fintype.card Obs.M := by
  classical
  let encode : V60KeptState Obs terminal binary start -> N × Obs.M :=
    fun X => v60TypedNTKey X.1
  have hInjective : Function.Injective encode := by
    intro X Y hXY
    apply Subtype.ext
    apply v60TypedNTKey_injective
    simpa [encode] using hXY
  simpa using Fintype.card_le_of_injective encode hInjective

/--
A grammar-independent superset of the canonical-witness indexing slots.
Rule predicates only remove slots, so this deliberately overcounts and is
sufficient for the polynomial-data theorem.
-/
abbrev V62CanonicalWitnessSlot (W : Type v) (Sigma : Type u) :=
  W ⊕ ((W × Sigma) ⊕ ((W × W × W) ⊕ Unit))

/-- Polynomial envelope for the number of canonical-witness slots. -/
def V62WindowWitnessCountEnvelope (Nt sigmaCard : Nat) : Nat :=
  Nt + (Nt * sigmaCard + (Nt * (Nt * Nt) + 1))

/-- The witness-slot type has exactly the displayed polynomial cardinality. -/
theorem v62_canonical_witness_slot_card
    {W : Type v} {Sigma : Type u}
    [Fintype W] [Fintype Sigma] :
    Fintype.card (V62CanonicalWitnessSlot W Sigma) =
      V62WindowWitnessCountEnvelope (Fintype.card W) (Fintype.card Sigma) := by
  simp [V62CanonicalWitnessSlot, V62WindowWitnessCountEnvelope]

/-- Forget rule predicates and map every potential slot to its canonical word. -/
noncomputable def v62CanonicalWitnessWordOfSlot
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N) :
    V62CanonicalWitnessSlot
        (V60KeptState Obs terminal binary start) Sigma -> Word Sigma
  | Sum.inl X => v60CanonicalAnchorWord X
  | Sum.inr (Sum.inl p) => v60CanonicalTerminalWord p.1 p.2
  | Sum.inr (Sum.inr (Sum.inl p)) =>
      v60CanonicalBinaryWord p.1 p.2.1 p.2.2
  | Sum.inr (Sum.inr (Sum.inr _)) => []

/-- Every actual canonical witness is represented by one potential slot. -/
theorem v62_canonical_witness_subset_slot_range
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop) :
    V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart ⊆
      Set.range (v62CanonicalWitnessWordOfSlot Obs terminal binary start) := by
  intro z hz
  rcases hz with hAnchor | hTerminal | hBinary | hEps
  · rcases hAnchor with ⟨X, rfl⟩
    exact ⟨Sum.inl X, rfl⟩
  · rcases hTerminal with ⟨X, a, hRule, rfl⟩
    exact ⟨Sum.inr (Sum.inl (X, a)), rfl⟩
  · rcases hBinary with ⟨X, Y, Z, hRule, rfl⟩
    exact ⟨Sum.inr (Sum.inr (Sum.inl (X, Y, Z))), rfl⟩
  · rcases hEps with ⟨rfl, hStart⟩
    exact ⟨Sum.inr (Sum.inr (Sum.inr ())), rfl⟩

/--
The actual canonical witness set has at most the polynomial number of potential
slots.  Duplicate witness words can only make the actual set smaller.
-/
theorem v62_canonical_witness_ncard_le_slot_envelope
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop) :
    (V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart).ncard <=
      V62WindowWitnessCountEnvelope
        (Fintype.card (V60KeptState Obs terminal binary start))
        (Fintype.card Sigma) := by
  classical
  let encode := v62CanonicalWitnessWordOfSlot Obs terminal binary start
  have hSubset :
      V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start) epsilonStart ⊆
        Set.range encode := by
    simpa [encode] using
      (v62_canonical_witness_subset_slot_range
        Obs terminal binary start epsilonStart)
  have hRangeFinite : (Set.range encode).Finite := Set.finite_range _
  calc
    (V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart).ncard
        <= (Set.range encode).ncard :=
      Set.ncard_le_ncard hSubset hRangeFinite
    _ <= Fintype.card
        (V62CanonicalWitnessSlot
          (V60KeptState Obs terminal binary start) Sigma) := by
      rw [← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
      exact Nat.card_range_le encode
    _ = V62WindowWitnessCountEnvelope
        (Fintype.card (V60KeptState Obs terminal binary start))
        (Fintype.card Sigma) :=
      v62_canonical_witness_slot_card

/-- Encoded size convention used in Theorem `window-thick`. -/
noncomputable def V62EncodedSampleSize
    {Sigma : Type u} (S : Set (Word Sigma)) (hS : S.Finite) : Nat :=
  ∑ z ∈ hS.toFinset, z.length + 1

/--
A finite sample with at most `C` words, each of length at most `L`, has encoded
size at most `C * (L+1)`.
-/
theorem v62_encoded_sample_size_le
    {Sigma : Type u} (S : Set (Word Sigma)) (hS : S.Finite)
    {C L : Nat}
    (hCard : S.ncard <= C)
    (hLen : ∀ z, z ∈ S -> z.length <= L) :
    V62EncodedSampleSize S hS <= C * (L + 1) := by
  classical
  have hPoint : ∀ z ∈ hS.toFinset, z.length + 1 <= L + 1 := by
    intro z hz
    have hzS : z ∈ S := by simpa using hz
    exact Nat.add_le_add_right (hLen z hzS) 1
  have hSum :
      (∑ z ∈ hS.toFinset, z.length + 1) <=
        hS.toFinset.card * (L + 1) := by
    simpa [Nat.nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul hS.toFinset
        (fun z => z.length + 1) (L + 1) hPoint)
  unfold V62EncodedSampleSize
  calc
    (∑ z ∈ hS.toFinset, z.length + 1)
        <= hS.toFinset.card * (L + 1) := hSum
    _ = S.ncard * (L + 1) := by
      rw [Set.ncard_eq_toFinset_card S hS]
    _ <= C * (L + 1) := Nat.mul_le_mul_right (L + 1) hCard

/--
Canonical-sample specialization: slot count times any common witness-length
bound controls the complete encoded characteristic-data size.
-/
theorem v62_canonical_witness_encoded_size_le
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop)
    {L : Nat}
    (hLen : ∀ z,
      z ∈ V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart -> z.length <= L) :
    V62EncodedSampleSize
        (V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start) epsilonStart)
        (v60_canonical_witness_finite
          Obs terminal binary start epsilonStart) <=
      V62WindowWitnessCountEnvelope
          (Fintype.card (V60KeptState Obs terminal binary start))
          (Fintype.card Sigma) *
        (L + 1) := by
  exact v62_encoded_sample_size_le
    (V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart)
    (v60_canonical_witness_finite Obs terminal binary start epsilonStart)
    (v62_canonical_witness_ncard_le_slot_envelope
      Obs terminal binary start epsilonStart)
    hLen

end FixedHCFG
end LeanCfgProject
