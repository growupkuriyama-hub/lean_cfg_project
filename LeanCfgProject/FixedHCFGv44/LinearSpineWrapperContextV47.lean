import LeanCfgProject.FixedHCFGv44.LinearSpineContextCoreV47

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Wrapper-side completion of the v47 linear short-witness proof.

A reachable wrapper cannot lie on the continuing spine.  Its last occurrence
step therefore exposes the parent spine state and the unique sibling spine
state directly.  This module formalizes that local fact without dependent
elimination on a pre-existing subtype witness.
-/

/-- A reachable/productive wrapper occurs as the wrapper child of its final binary step. -/
theorem wrapper_occurs_has_parent_v47
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (S : TypedLinearSpineShape Obs terminal binary start)
    {X : TypedNT N Obs} {u v z : Word Sigma}
    (hOcc : TypedOccurs Obs terminal binary start X u v)
    (d : TypedDerives Obs terminal binary X z)
    (hWrap : S.isWrapper X) :
    ∃ hKeep : TypedKept Obs terminal binary start X,
      let Xs : KeptState Obs terminal binary start := ⟨X, hKeep⟩
      (∃ P Y : KeptState Obs terminal binary start,
        keptBinary P Xs Y ∧ ¬ S.isWrapper P.1 ∧ ¬ S.isWrapper Y.1) ∨
      (∃ P Y : KeptState Obs terminal binary start,
        keptBinary P Y Xs ∧ ¬ S.isWrapper P.1 ∧ ¬ S.isWrapper Y.1) := by
  cases hOcc with
  | @start A mu hStart =>
      have hKeep : TypedKept Obs terminal binary start
          { label := A, yieldType := mu } := by
        constructor
        · exact ⟨z, d⟩
        · exact ⟨[], [], TypedOccurs.start (mu := mu) hStart⟩
      let Xs : KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := mu }, hKeep⟩
      have hNot : ¬ S.isWrapper Xs.1 :=
        S.start_not_wrapper Xs (by simpa [keptStart] using hStart)
      exact (hNot (by simpa [Xs] using hWrap)).elim
  | @left A B C mu nu u v y parent hrule rightDeriv =>
      have hCurrentKeep : TypedKept Obs terminal binary start
          { label := B, yieldType := mu } := by
        constructor
        · exact ⟨z, d⟩
        · exact ⟨u, y ++ v, TypedOccurs.left parent hrule rightDeriv⟩
      have hParentDeriv : TypedDerives Obs terminal binary
          { label := A, yieldType := Obs.mul mu nu } (z ++ y) :=
        TypedDerives.binary hrule d rightDeriv
      have hParentKeep : TypedKept Obs terminal binary start
          { label := A, yieldType := Obs.mul mu nu } := by
        constructor
        · exact ⟨z ++ y, hParentDeriv⟩
        · exact ⟨u, v, parent⟩
      have hSiblingOcc : TypedOccurs Obs terminal binary start
          { label := C, yieldType := nu } (u ++ z) v :=
        TypedOccurs.right parent hrule d
      have hSiblingKeep : TypedKept Obs terminal binary start
          { label := C, yieldType := nu } := by
        constructor
        · exact ⟨y, rightDeriv⟩
        · exact ⟨u ++ z, v, hSiblingOcc⟩
      let Xs : KeptState Obs terminal binary start :=
        ⟨{ label := B, yieldType := mu }, hCurrentKeep⟩
      let P : KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := Obs.mul mu nu }, hParentKeep⟩
      let Y : KeptState Obs terminal binary start :=
        ⟨{ label := C, yieldType := nu }, hSiblingKeep⟩
      have hRule : keptBinary P Xs Y := ⟨hrule, rfl⟩
      have hShape := S.binary_shape P Xs Y hRule
      have hWrapXs : S.isWrapper Xs.1 := by simpa [Xs] using hWrap
      rcases hShape.2 with hGood | hBad
      · refine ⟨hCurrentKeep, ?_⟩
        exact Or.inl ⟨P, Y, hRule, hShape.1, hGood.2⟩
      · exact (hBad.1 hWrapXs).elim
  | @right A B C mu nu u v x parent hrule leftDeriv =>
      have hCurrentKeep : TypedKept Obs terminal binary start
          { label := C, yieldType := nu } := by
        constructor
        · exact ⟨z, d⟩
        · exact ⟨u ++ x, v, TypedOccurs.right parent hrule leftDeriv⟩
      have hParentDeriv : TypedDerives Obs terminal binary
          { label := A, yieldType := Obs.mul mu nu } (x ++ z) :=
        TypedDerives.binary hrule leftDeriv d
      have hParentKeep : TypedKept Obs terminal binary start
          { label := A, yieldType := Obs.mul mu nu } := by
        constructor
        · exact ⟨x ++ z, hParentDeriv⟩
        · exact ⟨u, v, parent⟩
      have hSiblingOcc : TypedOccurs Obs terminal binary start
          { label := B, yieldType := mu } u (z ++ v) :=
        TypedOccurs.left parent hrule d
      have hSiblingKeep : TypedKept Obs terminal binary start
          { label := B, yieldType := mu } := by
        constructor
        · exact ⟨x, leftDeriv⟩
        · exact ⟨u, z ++ v, hSiblingOcc⟩
      let Xs : KeptState Obs terminal binary start :=
        ⟨{ label := C, yieldType := nu }, hCurrentKeep⟩
      let P : KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := Obs.mul mu nu }, hParentKeep⟩
      let Y : KeptState Obs terminal binary start :=
        ⟨{ label := B, yieldType := mu }, hSiblingKeep⟩
      have hRule : keptBinary P Y Xs := ⟨hrule, rfl⟩
      have hShape := S.binary_shape P Y Xs hRule
      have hWrapXs : S.isWrapper Xs.1 := by simpa [Xs] using hWrap
      rcases hShape.2 with hBad | hGood
      · exact (hBad.2 hWrapXs).elim
      · refine ⟨hCurrentKeep, ?_⟩
        exact Or.inr ⟨P, Y, hRule, hShape.1, hGood.1⟩

/-- Kept-state form of the wrapper-parent decomposition. -/
theorem wrapper_has_spine_parent_v47
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (S : TypedLinearSpineShape Obs terminal binary start)
    (X : KeptState Obs terminal binary start)
    (hWrap : S.isWrapper X.1) :
    (∃ P Y : KeptState Obs terminal binary start,
      keptBinary P X Y ∧ ¬ S.isWrapper P.1 ∧ ¬ S.isWrapper Y.1) ∨
    (∃ P Y : KeptState Obs terminal binary start,
      keptBinary P Y X ∧ ¬ S.isWrapper P.1 ∧ ¬ S.isWrapper Y.1) := by
  rcases wrapper_occurs_has_parent_v47 S (canonicalChi_spec X)
      (canonicalOmega_spec X) hWrap with ⟨hKeep, hParent⟩
  let X' : KeptState Obs terminal binary start := ⟨X.1, hKeep⟩
  have hEq : X' = X := by
    apply Subtype.ext
    rfl
  simpa [X', hEq] using hParent

/-- The v47 wrapper/spine argument gives the full canonical context bound. -/
theorem canonicalChi_length_le_two_typed_state_card_v47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (S : TypedLinearSpineShape Obs terminal binary start)
    (X : KeptState Obs terminal binary start) :
    (canonicalLeftCtx X).length + (canonicalRightCtx X).length ≤
      2 * Fintype.card (KeptState Obs terminal binary start) := by
  let n := Fintype.card (KeptState Obs terminal binary start)
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨X⟩
  by_cases hWrap : S.isWrapper X.1
  · rcases wrapper_has_spine_parent_v47 S X hWrap with hLeft | hRight
    · rcases hLeft with ⟨P, Y, hRule, hPNon, hYNon⟩
      have hPCtx := canonicalChi_spine_length_le_v47 S P hPNon
      have hYYield := canonicalOmega_length_le_typed_state_card S Y
      have hParentEq : P.1 =
          { label := P.1.label,
            yieldType := Obs.mul X.1.yieldType Y.1.yieldType } := by
        apply typedNT_eq_of_components
        · rfl
        · exact hRule.2.symm
      have hParentOcc : TypedOccurs Obs terminal binary start
          { label := P.1.label,
            yieldType := Obs.mul X.1.yieldType Y.1.yieldType }
          (canonicalLeftCtx P) (canonicalRightCtx P) := by
        rw [← hParentEq]
        exact canonicalChi_spec P
      have hOccX : TypedOccurs Obs terminal binary start X.1
          (canonicalLeftCtx P) (canonicalOmega Y ++ canonicalRightCtx P) :=
        TypedOccurs.left hParentOcc hRule.1 (canonicalOmega_spec Y)
      have hCan := canonicalChi_total_length_le_of_occurs X hOccX
      have hConstructed :
          (canonicalLeftCtx P).length +
              (canonicalOmega Y ++ canonicalRightCtx P).length < 2 * n := by
        apply wrapper_right_context_length_lt_two_mul hn
        · simpa [n] using hPCtx
        · simpa [n] using hYYield
      exact le_trans hCan (Nat.le_of_lt hConstructed)
    · rcases hRight with ⟨P, Y, hRule, hPNon, hYNon⟩
      have hPCtx := canonicalChi_spine_length_le_v47 S P hPNon
      have hYYield := canonicalOmega_length_le_typed_state_card S Y
      have hParentEq : P.1 =
          { label := P.1.label,
            yieldType := Obs.mul Y.1.yieldType X.1.yieldType } := by
        apply typedNT_eq_of_components
        · rfl
        · exact hRule.2.symm
      have hParentOcc : TypedOccurs Obs terminal binary start
          { label := P.1.label,
            yieldType := Obs.mul Y.1.yieldType X.1.yieldType }
          (canonicalLeftCtx P) (canonicalRightCtx P) := by
        rw [← hParentEq]
        exact canonicalChi_spec P
      have hOccX : TypedOccurs Obs terminal binary start X.1
          (canonicalLeftCtx P ++ canonicalOmega Y) (canonicalRightCtx P) :=
        TypedOccurs.right hParentOcc hRule.1 (canonicalOmega_spec Y)
      have hCan := canonicalChi_total_length_le_of_occurs X hOccX
      have hConstructed :
          (canonicalLeftCtx P ++ canonicalOmega Y).length +
              (canonicalRightCtx P).length < 2 * n := by
        apply wrapper_left_context_length_lt_two_mul hn
        · simpa [n] using hPCtx
        · simpa [n] using hYYield
      exact le_trans hCan (Nat.le_of_lt hConstructed)
  · have hSpine := canonicalChi_spine_length_le_v47 S X hWrap
    have hBound : n - 1 ≤ 2 * n := by omega
    exact le_trans (by simpa [n] using hSpine) hBound

/-- V47 short canonical witnesses from the actual retained typed spine shape. -/
theorem short_canonical_witnesses_from_typed_shape_v47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (S : TypedLinearSpineShape Obs terminal binary start) :
    (∀ X : KeptState Obs terminal binary start,
      (canonicalOmega X).length ≤
        Fintype.card (KeptState Obs terminal binary start)) ∧
    (∀ X : KeptState Obs terminal binary start,
      (canonicalLeftCtx X).length + (canonicalRightCtx X).length ≤
        2 * Fintype.card (KeptState Obs terminal binary start)) := by
  constructor
  · exact canonicalOmega_length_le_typed_state_card S
  · exact canonicalChi_length_le_two_typed_state_card_v47 S

end FixedHCFGv44
end LeanCfgProject
