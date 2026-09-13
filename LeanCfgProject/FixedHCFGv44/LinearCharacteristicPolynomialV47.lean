import LeanCfgProject.FixedHCFGv44.LinearWitnessEndToEndV47

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Polynomial cardinality envelope for the v47 linear characteristic
reconstruction data.  This is deliberately a coarse bound: actual retained
terminal productions inject into `W × Sigma`, and actual retained binary
productions inject into `W × W × W`.  Together with `|W| <= |N||M|`, this is
already polynomial in a finite target presentation for fixed `h`.
-/

/-- Retained terminal productions are a subtype of state/letter pairs. -/
theorem keptTerminalProduction_card_le_v47
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype N] [Fintype Sigma] :
    Fintype.card
        (KeptTerminalProduction (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start)) ≤
      Fintype.card (KeptState Obs terminal binary start) * Fintype.card Sigma := by
  classical
  calc
    Fintype.card
        (KeptTerminalProduction (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start)) ≤
        Fintype.card (KeptState Obs terminal binary start × Sigma) := by
      apply Fintype.card_le_of_injective
        (fun p : KeptTerminalProduction (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start) => p.1)
      intro p q h
      exact Subtype.ext h
    _ = Fintype.card (KeptState Obs terminal binary start) *
        Fintype.card Sigma := by simp

/-- Retained binary productions are a subtype of triples of retained states. -/
theorem keptBinaryProduction_card_le_v47
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype N] :
    Fintype.card
        (KeptBinaryProduction (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start)) ≤
      Fintype.card (KeptState Obs terminal binary start) ^ 3 := by
  classical
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
      intro p q h
      exact Subtype.ext h
    _ = Fintype.card (KeptState Obs terminal binary start) ^ 3 := by
      simp [pow_succ, Nat.mul_assoc]

/-- Coarse polynomial size bound for the exact canonical-witness index family. -/
theorem canonicalCSIndex_card_polynomial_le_v47
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype N] [Fintype Sigma] :
    Fintype.card
        (CanonicalCSIndex (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start)) ≤
      Fintype.card (KeptState Obs terminal binary start) +
      Fintype.card (KeptState Obs terminal binary start) * Fintype.card Sigma +
      Fintype.card (KeptState Obs terminal binary start) ^ 3 + 1 := by
  rw [canonicalCSIndex_card]
  have ht := keptTerminalProduction_card_le_v47
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
  have hb := keptBinaryProduction_card_le_v47
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add le_rfl ht) hb) le_rfl

/-- Finite image cover of all exact canonical witness words. -/
noncomputable def canonicalCSCoverV47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N} : Finset (Word Sigma) := by
  classical
  exact Finset.univ.image canonicalCSIndexWord

/-- Every canonical witness belongs to the finite index-image cover. -/
theorem canonicalCS_mem_cover_v47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop) {z : Word Sigma}
    (hz : CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart z) :
    z ∈ canonicalCSCoverV47 (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) := by
  classical
  rcases canonicalCS_covered_by_index epsilonStart hz with ⟨i, hi⟩
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_univ i, hi⟩

/-- The finite cover itself is no larger than the canonical index family. -/
theorem canonicalCSCover_card_le_index_v47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N} :
    (canonicalCSCoverV47 (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start)).card ≤
      Fintype.card
        (CanonicalCSIndex (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start)) := by
  classical
  simpa [canonicalCSCoverV47] using
    (Finset.card_image_le
      (s := (Finset.univ : Finset
        (CanonicalCSIndex (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start))))
      (f := canonicalCSIndexWord))

/-- Polynomial cardinality bound for a finite cover of all canonical witnesses. -/
theorem canonicalCSCover_card_polynomial_le_v47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma]
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N} :
    (canonicalCSCoverV47 (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start)).card ≤
      Fintype.card (KeptState Obs terminal binary start) +
      Fintype.card (KeptState Obs terminal binary start) * Fintype.card Sigma +
      Fintype.card (KeptState Obs terminal binary start) ^ 3 + 1 := by
  exact le_trans canonicalCSCover_card_le_index_v47
    canonicalCSIndex_card_polynomial_le_v47

end FixedHCFGv44
end LeanCfgProject
