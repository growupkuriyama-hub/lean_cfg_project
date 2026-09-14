import LeanCfgProject.FixedHCFGv44.LinearRetainedCardBridgeV49
import LeanCfgProject.FixedHCFGv44.LinearCharacteristicSizeV47

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Retained-state version of the linear characteristic-data size argument for
TCS v49.

The explicit Appendix A normalization uses the ambient type `LinearNormNT`,
which is intentionally infinite because a stage state stores an arbitrary
remaining spine program.  The characteristic set, however, only mentions
retained yield-typed states and retained productions.  This file therefore
rebuilds the finite-index/norm argument assuming finiteness only of
`KeptState`, not of the ambient nonterminal type.
-/

/-- A local finite structure for retained terminal productions needs only the
retained-state type and the terminal alphabet to be finite. -/
noncomputable def keptTerminalProductionFintypeRetainedV49
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype Sigma] [Fintype (KeptState Obs terminal binary start)] :
    Fintype (KeptTerminalProduction (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start)) := by
  classical
  exact Fintype.ofFinite _

/-- A local finite structure for retained binary productions needs only the
retained-state type to be finite. -/
noncomputable def keptBinaryProductionFintypeRetainedV49
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype (KeptState Obs terminal binary start)] :
    Fintype (KeptBinaryProduction (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start)) := by
  classical
  exact Fintype.ofFinite _

/-- Retained terminal productions inject into retained-state/letter pairs. -/
theorem keptTerminalProduction_card_le_retained_v49
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype Sigma] [Fintype (KeptState Obs terminal binary start)] :
    letI := keptTerminalProductionFintypeRetainedV49
      (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
    Fintype.card
        (KeptTerminalProduction (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start)) ≤
      Fintype.card (KeptState Obs terminal binary start) * Fintype.card Sigma := by
  classical
  letI := keptTerminalProductionFintypeRetainedV49
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
  apply Fintype.card_le_of_injective
    (fun p : KeptTerminalProduction (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) => p.1)
  intro p q hpq
  exact Subtype.ext hpq

/-- Retained binary productions inject into triples of retained states. -/
theorem keptBinaryProduction_card_le_retained_v49
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype (KeptState Obs terminal binary start)] :
    letI := keptBinaryProductionFintypeRetainedV49
      (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
    Fintype.card
        (KeptBinaryProduction (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start)) ≤
      Fintype.card (KeptState Obs terminal binary start) ^ 3 := by
  classical
  letI := keptBinaryProductionFintypeRetainedV49
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
  calc
    Fintype.card
        (KeptBinaryProduction (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start)) ≤
        Fintype.card
          (KeptState Obs terminal binary start ×
            KeptState Obs terminal binary start ×
            KeptState Obs terminal binary start) := by
      apply Fintype.card_le_of_injective
        (fun p : KeptBinaryProduction (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start) => p.1)
      intro p q hpq
      exact Subtype.ext hpq
    _ = Fintype.card (KeptState Obs terminal binary start) ^ 3 := by
      simp [pow_succ, Nat.mul_assoc]

/--
Cardinality of the exact four-family index envelope, using only retained-state
finiteness.
-/
theorem canonicalCSIndex_card_polynomial_le_retained_v49
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype Sigma] [Fintype (KeptState Obs terminal binary start)] :
    letI := keptTerminalProductionFintypeRetainedV49
      (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
    letI := keptBinaryProductionFintypeRetainedV49
      (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
    Fintype.card
        (CanonicalCSIndex (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start)) ≤
      Fintype.card (KeptState Obs terminal binary start) +
      Fintype.card (KeptState Obs terminal binary start) * Fintype.card Sigma +
      Fintype.card (KeptState Obs terminal binary start) ^ 3 + 1 := by
  classical
  letI := keptTerminalProductionFintypeRetainedV49
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
  letI := keptBinaryProductionFintypeRetainedV49
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
  have ht := keptTerminalProduction_card_le_retained_v49
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
  have hb := keptBinaryProduction_card_le_retained_v49
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
  simp only [CanonicalCSIndex, Fintype.card_sum, Fintype.card_unit]
  omega

/-- Finite image of all four-family characteristic-data indices. -/
noncomputable def canonicalCSCoverRetainedV49
    {N : Type v} {Sigma : Type u}
    [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype (KeptState Obs terminal binary start)] : Finset (Word Sigma) := by
  classical
  letI := keptTerminalProductionFintypeRetainedV49
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
  letI := keptBinaryProductionFintypeRetainedV49
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
  exact Finset.univ.image
    (fun i : CanonicalCSIndex (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) => canonicalCSIndexWord i)

/-- Every canonical characteristic word belongs to the retained-state cover. -/
theorem canonicalCS_mem_cover_retained_v49
    {N : Type v} {Sigma : Type u}
    [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype (KeptState Obs terminal binary start)]
    (epsilonStart : Prop) {z : Word Sigma}
    (hz : CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart z) :
    z ∈ canonicalCSCoverRetainedV49 (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) := by
  classical
  rcases canonicalCS_covered_by_index epsilonStart hz with ⟨i, rfl⟩
  simp [canonicalCSCoverRetainedV49]

/-- Exact finite characteristic set under retained-state finiteness. -/
noncomputable def canonicalCSFinsetRetainedV49
    {N : Type v} {Sigma : Type u}
    [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype (KeptState Obs terminal binary start)]
    (epsilonStart : Prop) : Finset (Word Sigma) := by
  classical
  exact (canonicalCSCoverRetainedV49 (Obs := Obs) (terminal := terminal)
    (binary := binary) (start := start)).filter
      (fun z => CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart z)

/-- Membership in the finite representation is exactly `CanonicalCS`. -/
theorem mem_canonicalCSFinsetRetainedV49_iff
    {N : Type v} {Sigma : Type u}
    [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype (KeptState Obs terminal binary start)]
    (epsilonStart : Prop) (z : Word Sigma) :
    z ∈ canonicalCSFinsetRetainedV49 (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart ↔
      CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart z := by
  classical
  simp only [canonicalCSFinsetRetainedV49, Finset.mem_filter]
  constructor
  · intro hz
    exact hz.2
  · intro hz
    exact ⟨canonicalCS_mem_cover_retained_v49 epsilonStart hz, hz⟩

/-- Manuscript sample norm `sum (|w|+1)` of the exact retained-state sample. -/
noncomputable def canonicalCSNormRetainedV49
    {N : Type v} {Sigma : Type u}
    [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype (KeptState Obs terminal binary start)]
    (epsilonStart : Prop) : Nat :=
  Finset.sum
    (canonicalCSFinsetRetainedV49 (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart)
    (fun z => z.length + 1)

/--
Polynomial norm envelope in the retained-state cardinality `n_t`.  This is the
v49 form needed for the explicit Appendix A normalization.
-/
theorem canonicalCSNormRetainedV49_polynomial_le
    {N : Type v} {Sigma : Type u}
    [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype (KeptState Obs terminal binary start)]
    (epsilonStart : Prop)
    (S : TypedLinearSpineShape Obs terminal binary start) :
    canonicalCSNormRetainedV49 (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart ≤
      (Fintype.card (KeptState Obs terminal binary start) +
        Fintype.card (KeptState Obs terminal binary start) * Fintype.card Sigma +
        Fintype.card (KeptState Obs terminal binary start) ^ 3 + 1) *
      (4 * Fintype.card (KeptState Obs terminal binary start) + 1) := by
  classical
  letI := keptTerminalProductionFintypeRetainedV49
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
  letI := keptBinaryProductionFintypeRetainedV49
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
  let indexCover : Finset (Word Sigma) :=
    Finset.univ.image
      (fun i : CanonicalCSIndex (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start) => canonicalCSIndexWord i)
  have hSubset :
      canonicalCSFinsetRetainedV49 (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start) epsilonStart ⊆ indexCover := by
    intro z hz
    have hzCover : z ∈ canonicalCSCoverRetainedV49 (Obs := Obs)
        (terminal := terminal) (binary := binary) (start := start) := by
      exact (Finset.mem_filter.mp hz).1
    simpa [indexCover, canonicalCSCoverRetainedV49] using hzCover
  have hFilter :
      canonicalCSNormRetainedV49 (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start) epsilonStart ≤
        Finset.sum indexCover (fun z => z.length + 1) := by
    unfold canonicalCSNormRetainedV49
    exact Finset.sum_le_sum_of_subset hSubset
  have hImage :
      Finset.sum indexCover (fun z => z.length + 1) ≤
        Finset.sum (Finset.univ : Finset
          (CanonicalCSIndex (Obs := Obs) (terminal := terminal)
            (binary := binary) (start := start)))
          (fun i => (canonicalCSIndexWord i).length + 1) := by
    simpa [indexCover] using
      (sum_image_le_sum_nat_v47
        (Finset.univ : Finset
          (CanonicalCSIndex (Obs := Obs) (terminal := terminal)
            (binary := binary) (start := start)))
        (fun i => canonicalCSIndexWord i)
        (fun z : Word Sigma => z.length + 1))
  have hEach :
      Finset.sum (Finset.univ : Finset
          (CanonicalCSIndex (Obs := Obs) (terminal := terminal)
            (binary := binary) (start := start)))
          (fun i => (canonicalCSIndexWord i).length + 1) ≤
        Fintype.card
            (CanonicalCSIndex (Obs := Obs) (terminal := terminal)
              (binary := binary) (start := start)) *
          (4 * Fintype.card (KeptState Obs terminal binary start) + 1) := by
    calc
      _ ≤ Finset.sum (Finset.univ : Finset
            (CanonicalCSIndex (Obs := Obs) (terminal := terminal)
              (binary := binary) (start := start)))
            (fun _ => 4 * Fintype.card (KeptState Obs terminal binary start) + 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hCanonical := canonicalCSIndexWord_mem_true_v47
          (Obs := Obs) (terminal := terminal) (binary := binary) (start := start) i
        have hLen := canonicalCS_word_length_le_retained_card_v49
          (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
          True S hCanonical
        omega
      _ = _ := by simp
  have hCard := canonicalCSIndex_card_polynomial_le_retained_v49
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
  exact le_trans hFilter (le_trans hImage
    (le_trans hEach
      (Nat.mul_le_mul_right
        (4 * Fintype.card (KeptState Obs terminal binary start) + 1) hCard)))

end FixedHCFGv44
end LeanCfgProject
