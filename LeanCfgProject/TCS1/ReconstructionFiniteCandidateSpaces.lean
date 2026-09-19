import LeanCfgProject.TCS1.ReconstructionComplexityCounts

/-!
# TCS #1: finite candidate spaces for reconstruction

This module turns the polynomial counts into actual finite indexing types.
For each sample word, two cut positions give a generous factor/context slot
and three cut positions give a generous binary-split slot.  These spaces are
slightly larger than the valid R1--R5 candidate sets, which is exactly what is
needed for an upper bound.

The cardinalities are the concrete quadratic/cubic sums used in the
reconstruction-complexity proof; pairing two factor slots gives the quartic
space behind Rules R2 and R3.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section ReconstructionFiniteCandidateSpaces

variable {α : Type u}
variable [DecidableEq α]

/-- A sample word together with its proof of occurrence in K. -/
abbrev ReconstructionSampleWord
    (K : Finset (Word α)) :=
  {w : Word α // w ∈ K}

/-- Two cut positions in one sampled word. -/
abbrev ReconstructionFactorSlot
    (K : Finset (Word α)) :=
  Sigma (fun w : ReconstructionSampleWord K =>
    Fin (w.1.length + 1) ×
      Fin (w.1.length + 1))

/-- Three cut positions in one sampled word. -/
abbrev ReconstructionSplitSlot
    (K : Finset (Word α)) :=
  Sigma (fun w : ReconstructionSampleWord K =>
    Fin (w.1.length + 1) ×
      (Fin (w.1.length + 1) ×
        Fin (w.1.length + 1)))

/-- Pair space used to over-approximate R2/R3 candidates. -/
abbrev ReconstructionFactorPairSlot
    (K : Finset (Word α)) :=
  ReconstructionFactorSlot K ×
    ReconstructionFactorSlot K

/-- Exact cardinality of the two-cut candidate space. -/
theorem reconstructionFactorSlot_card_eq
    (K : Finset (Word α)) :
    Fintype.card (ReconstructionFactorSlot K) =
      reconstructionFactorSlotCount K := by
  classical
  simp only [ReconstructionFactorSlot,
    ReconstructionSampleWord,
    Fintype.card_sigma,
    Fintype.card_prod,
    Fintype.card_fin]
  rw [Finset.sum_attach K
    (fun w : Word α =>
      (w.length + 1) * (w.length + 1))]
  simp [reconstructionFactorSlotCount, pow_two]

/-- Exact cardinality of the three-cut candidate space. -/
theorem reconstructionSplitSlot_card_eq
    (K : Finset (Word α)) :
    Fintype.card (ReconstructionSplitSlot K) =
      reconstructionSplitSlotCount K := by
  classical
  simp only [ReconstructionSplitSlot,
    ReconstructionSampleWord,
    Fintype.card_sigma,
    Fintype.card_prod,
    Fintype.card_fin]
  rw [Finset.sum_attach K
    (fun w : Word α =>
      (w.length + 1) *
        ((w.length + 1) * (w.length + 1)))]
  simp [reconstructionSplitSlotCount,
    pow_succ, Nat.mul_assoc]

/-- Exact cardinality of the factor-pair candidate space. -/
theorem reconstructionFactorPairSlot_card_eq
    (K : Finset (Word α)) :
    Fintype.card (ReconstructionFactorPairSlot K) =
      reconstructionFactorSlotCount K *
        reconstructionFactorSlotCount K := by
  classical
  rw [Fintype.card_prod]
  rw [reconstructionFactorSlot_card_eq]
  rw [reconstructionFactorSlot_card_eq]

/-- The actual two-cut finite space is quadratically bounded by ||K||. -/
theorem reconstructionFactorSlot_card_le_sq
    (K : Finset (Word α)) :
    Fintype.card (ReconstructionFactorSlot K) ≤
      (reconstructionSampleNorm K) ^ 2 := by
  rw [reconstructionFactorSlot_card_eq]
  exact reconstructionFactorSlotCount_le_sq K

/-- The actual three-cut finite space is cubically bounded by ||K||. -/
theorem reconstructionSplitSlot_card_le_cube
    (K : Finset (Word α)) :
    Fintype.card (ReconstructionSplitSlot K) ≤
      (reconstructionSampleNorm K) ^ 3 := by
  rw [reconstructionSplitSlot_card_eq]
  exact reconstructionSplitSlotCount_le_cube K

/-- The actual paired-factor finite space is quartically bounded by ||K||. -/
theorem reconstructionFactorPairSlot_card_le_fourth
    (K : Finset (Word α)) :
    Fintype.card (ReconstructionFactorPairSlot K) ≤
      (reconstructionSampleNorm K) ^ 4 := by
  rw [reconstructionFactorPairSlot_card_eq]
  exact reconstructionFactorPairCount_le_fourth K

end ReconstructionFiniteCandidateSpaces

end TCS1
end LeanCfgProject
