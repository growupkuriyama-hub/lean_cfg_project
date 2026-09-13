import LeanCfgProject.FixedHCFGv44.LinearSpineTypedBridge

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Context-side completion of the v46 linear-spine bridge.

This file contracts typed reaching contexts to the verified strict-linear
occurrence calculus and expands them back.  It then handles the one extra case
from the appendix: a terminal wrapper is reached through its parent spine
symbol plus a shortest completion of the sibling spine child.
-/

/-- Every contracted strict-linear occurrence expands to a typed occurrence. -/
theorem spineOccurs_to_typed
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (S : TypedLinearSpineShape Obs terminal binary start)
    {X : KeptState Obs terminal binary start}
    {sp : List (KeptState Obs terminal binary start)}
    {u v : Word Sigma}
    (d : FixedHCFG.LinearOccursSpine (typedSpineGrammar S) X sp u v) :
    TypedOccurs Obs terminal binary start X.1 u v := by
  induction d with
  | @start X hStart =>
      exact keptStart_occurs_empty X hStart
  | @left X Y a sp u v parent hStep ih =>
      rcases hStep with ⟨W, hWrap, hBinary, hTerminal⟩
      have hW := keptTerminal_derives W a hTerminal
      have hOcc := TypedOccurs.right ih hBinary.1 hW
      simpa [hBinary.2] using hOcc
  | @right X Y a sp u v parent hStep ih =>
      rcases hStep with ⟨W, hWrap, hBinary, hTerminal⟩
      have hW := keptTerminal_derives W a hTerminal
      have hOcc := TypedOccurs.left ih hBinary.1 hW
      simpa [hBinary.2] using hOcc

/--
A typed reaching occurrence of a non-wrapper state contracts to a strict-linear
occurrence, provided we also supply a terminal derivation of that state.  The
latter is used only to certify productivity of the states on the path.
-/
theorem typedOccurs_to_spine
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (S : TypedLinearSpineShape Obs terminal binary start)
    {X : TypedNT N Obs} {u v z : Word Sigma}
    (hOcc : TypedOccurs Obs terminal binary start X u v)
    (d : TypedDerives Obs terminal binary X z)
    (hNon : ¬ S.isWrapper X) :
    ∃ (hKeep : TypedKept Obs terminal binary start X)
      (sp : List (KeptState Obs terminal binary start)),
      FixedHCFG.LinearOccursSpine (typedSpineGrammar S)
        (⟨X, hKeep⟩ : KeptState Obs terminal binary start) sp u v := by
  induction hOcc generalizing z with
  | @start A mu hStart =>
      have hKeep : TypedKept Obs terminal binary start
          { label := A, yieldType := mu } := by
        constructor
        · exact ⟨z, d⟩
        · exact ⟨[], [], TypedOccurs.start (mu := mu) hStart⟩
      refine ⟨hKeep, [⟨{ label := A, yieldType := mu }, hKeep⟩], ?_⟩
      exact FixedHCFG.LinearOccursSpine.start hStart
  | @left A B C mu nu u v y parent hrule rightDeriv ih =>
      have hParentDeriv : TypedDerives Obs terminal binary
          { label := A, yieldType := Obs.mul mu nu } (z ++ y) :=
        TypedDerives.binary hrule d rightDeriv
      have hCurrentKeep : TypedKept Obs terminal binary start
          { label := B, yieldType := mu } := by
        constructor
        · exact ⟨z, d⟩
        · exact ⟨u, y ++ v, TypedOccurs.left parent hrule rightDeriv⟩
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
      let P : KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := Obs.mul mu nu }, hParentKeep⟩
      let Xs : KeptState Obs terminal binary start :=
        ⟨{ label := B, yieldType := mu }, hCurrentKeep⟩
      let W : KeptState Obs terminal binary start :=
        ⟨{ label := C, yieldType := nu }, hSiblingKeep⟩
      have hRule : keptBinary P Xs W := ⟨hrule, rfl⟩
      have hShape := S.binary_shape P Xs W hRule
      have hXNon : ¬ S.isWrapper Xs.1 := by simpa [Xs] using hNon
      rcases hShape.2 with hBad | hGood
      · exact (hXNon hBad.1).elim
      · rcases hGood with ⟨hXsNon, hWWrap⟩
        have hParentNon := hShape.1
        have hSiblingKeptDeriv := successful_derivation_survives
          Obs terminal binary start hSiblingOcc rightDeriv
        rcases wrapper_keptDerives_terminal S hWWrap hSiblingKeptDeriv with
          ⟨hWKeep', a, hy, hTerminal⟩
        rcases ih hParentDeriv hParentNon with ⟨hPKeep', sp, hParentSpine⟩
        have hPEq : (⟨P.1, hPKeep'⟩ : KeptState Obs terminal binary start) = P := by
          apply Subtype.ext
          rfl
        have hWEq : (⟨W.1, hWKeep'⟩ : KeptState Obs terminal binary start) = W := by
          apply Subtype.ext
          rfl
        have hParentSpine' : FixedHCFG.LinearOccursSpine
            (typedSpineGrammar S) P sp u v := by
          simpa [hPEq] using hParentSpine
        have hStep : (typedSpineGrammar S).rightRule P Xs a := by
          refine ⟨W, hWWrap, hRule, ?_⟩
          simpa [hWEq] using hTerminal
        refine ⟨hCurrentKeep, sp.concat Xs, ?_⟩
        have hLin := FixedHCFG.LinearOccursSpine.right hParentSpine' hStep
        simpa [hy, Xs] using hLin
  | @right A B C mu nu u v x parent hrule leftDeriv ih =>
      have hParentDeriv : TypedDerives Obs terminal binary
          { label := A, yieldType := Obs.mul mu nu } (x ++ z) :=
        TypedDerives.binary hrule leftDeriv d
      have hCurrentKeep : TypedKept Obs terminal binary start
          { label := C, yieldType := nu } := by
        constructor
        · exact ⟨z, d⟩
        · exact ⟨u ++ x, v, TypedOccurs.right parent hrule leftDeriv⟩
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
      let P : KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := Obs.mul mu nu }, hParentKeep⟩
      let W : KeptState Obs terminal binary start :=
        ⟨{ label := B, yieldType := mu }, hSiblingKeep⟩
      let Xs : KeptState Obs terminal binary start :=
        ⟨{ label := C, yieldType := nu }, hCurrentKeep⟩
      have hRule : keptBinary P W Xs := ⟨hrule, rfl⟩
      have hShape := S.binary_shape P W Xs hRule
      have hXNon : ¬ S.isWrapper Xs.1 := by simpa [Xs] using hNon
      rcases hShape.2 with hGood | hBad
      · rcases hGood with ⟨hWWrap, hXsNon⟩
        have hParentNon := hShape.1
        have hSiblingKeptDeriv := successful_derivation_survives
          Obs terminal binary start hSiblingOcc leftDeriv
        rcases wrapper_keptDerives_terminal S hWWrap hSiblingKeptDeriv with
          ⟨hWKeep', a, hx, hTerminal⟩
        rcases ih hParentDeriv hParentNon with ⟨hPKeep', sp, hParentSpine⟩
        have hPEq : (⟨P.1, hPKeep'⟩ : KeptState Obs terminal binary start) = P := by
          apply Subtype.ext
          rfl
        have hWEq : (⟨W.1, hWKeep'⟩ : KeptState Obs terminal binary start) = W := by
          apply Subtype.ext
          rfl
        have hParentSpine' : FixedHCFG.LinearOccursSpine
            (typedSpineGrammar S) P sp u v := by
          simpa [hPEq] using hParentSpine
        have hStep : (typedSpineGrammar S).leftRule P a Xs := by
          refine ⟨W, hWWrap, hRule, ?_⟩
          simpa [hWEq] using hTerminal
        refine ⟨hCurrentKeep, sp.concat Xs, ?_⟩
        have hLin := FixedHCFG.LinearOccursSpine.left hParentSpine' hStep
        simpa [hx, Xs] using hLin
      · exact (hXNon hBad.2).elim

/-- Canonical context bound for a retained spine state. -/
theorem canonicalChi_spine_length_le
    {N : Type v} {Sigma : Type u}
    [Fintype N] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (S : TypedLinearSpineShape Obs terminal binary start)
    (X : KeptState Obs terminal binary start)
    (hNon : ¬ S.isWrapper X.1) :
    (canonicalLeftCtx X).length + (canonicalRightCtx X).length ≤
      Fintype.card (KeptState Obs terminal binary start) - 1 := by
  have hOcc := canonicalChi_spec X
  have hDeriv := canonicalOmega_spec X
  rcases typedOccurs_to_spine S hOcc hDeriv hNon with
    ⟨hKeep, sp, hSpineOcc⟩
  let X' : KeptState Obs terminal binary start := ⟨X.1, hKeep⟩
  have hXX' : X' = X := by
    apply Subtype.ext
    rfl
  have hOccLin : FixedHCFG.LinearOccurs (typedSpineGrammar S) X'
      (canonicalLeftCtx X) (canonicalRightCtx X) :=
    ⟨sp, by simpa [X'] using hSpineOcc⟩
  have hMin : FixedHCFG.LinearContextMinimal (typedSpineGrammar S) X'
      (canonicalLeftCtx X) (canonicalRightCtx X) := by
    constructor
    · exact hOccLin
    · intro l r hlr
      rcases hlr with ⟨sp', hsp'⟩
      have hTyped := spineOccurs_to_typed S hsp'
      have hTypedX : TypedOccurs Obs terminal binary start X.1 l r := by
        simpa [X', hXX'] using hTyped
      exact canonicalChi_total_length_le_of_occurs X hTypedX
  exact section7_spine_context_bound hMin

/-- A reachable retained wrapper appears as a wrapper child of a retained binary rule. -/
theorem wrapper_has_spine_parent
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
  have hOcc := canonicalChi_spec X
  have hXDeriv := canonicalOmega_spec X
  cases hOcc with
  | @start A mu hStart =>
      exact (S.start_not_wrapper X (by simpa [keptStart] using hStart) hWrap).elim
  | @left A B C mu nu u v y parent hrule rightDeriv =>
      have hParentDeriv : TypedDerives Obs terminal binary
          { label := A, yieldType := Obs.mul mu nu }
          (canonicalOmega X ++ y) :=
        TypedDerives.binary hrule hXDeriv rightDeriv
      have hParentKeep : TypedKept Obs terminal binary start
          { label := A, yieldType := Obs.mul mu nu } := by
        constructor
        · exact ⟨canonicalOmega X ++ y, hParentDeriv⟩
        · exact ⟨u, v, parent⟩
      have hSiblingOcc : TypedOccurs Obs terminal binary start
          { label := C, yieldType := nu }
          (u ++ canonicalOmega X) v :=
        TypedOccurs.right parent hrule hXDeriv
      have hSiblingKeep : TypedKept Obs terminal binary start
          { label := C, yieldType := nu } := by
        constructor
        · exact ⟨y, rightDeriv⟩
        · exact ⟨u ++ canonicalOmega X, v, hSiblingOcc⟩
      let P : KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := Obs.mul mu nu }, hParentKeep⟩
      let Y : KeptState Obs terminal binary start :=
        ⟨{ label := C, yieldType := nu }, hSiblingKeep⟩
      have hRule : keptBinary P X Y := by
        exact ⟨hrule, rfl⟩
      have hShape := S.binary_shape P X Y hRule
      rcases hShape.2 with hGood | hBad
      · exact Or.inl ⟨P, Y, hRule, hShape.1, hGood.2⟩
      · exact (hBad.1 hWrap).elim
  | @right A B C mu nu u v x parent hrule leftDeriv =>
      have hParentDeriv : TypedDerives Obs terminal binary
          { label := A, yieldType := Obs.mul mu nu }
          (x ++ canonicalOmega X) :=
        TypedDerives.binary hrule leftDeriv hXDeriv
      have hParentKeep : TypedKept Obs terminal binary start
          { label := A, yieldType := Obs.mul mu nu } := by
        constructor
        · exact ⟨x ++ canonicalOmega X, hParentDeriv⟩
        · exact ⟨u, v, parent⟩
      have hSiblingOcc : TypedOccurs Obs terminal binary start
          { label := B, yieldType := mu }
          u (canonicalOmega X ++ v) :=
        TypedOccurs.left parent hrule hXDeriv
      have hSiblingKeep : TypedKept Obs terminal binary start
          { label := B, yieldType := mu } := by
        constructor
        · exact ⟨x, leftDeriv⟩
        · exact ⟨u, canonicalOmega X ++ v, hSiblingOcc⟩
      let P : KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := Obs.mul mu nu }, hParentKeep⟩
      let Y : KeptState Obs terminal binary start :=
        ⟨{ label := B, yieldType := mu }, hSiblingKeep⟩
      have hRule : keptBinary P Y X := by
        exact ⟨hrule, rfl⟩
      have hShape := S.binary_shape P Y X hRule
      rcases hShape.2 with hBad | hGood
      · exact (hBad.2 hWrap).elim
      · exact Or.inr ⟨P, Y, hRule, hShape.1, hGood.1⟩

/-- The second inequality of the v46 short-canonical-witness lemma. -/
theorem canonicalChi_length_le_two_typed_state_card
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
  · rcases wrapper_has_spine_parent S X hWrap with hLeft | hRight
    · rcases hLeft with ⟨P, Y, hRule, hPNon, hYNon⟩
      have hPCtx := canonicalChi_spine_length_le S P hPNon
      have hYYield := canonicalOmega_length_le_typed_state_card S Y
      have hOccX : TypedOccurs Obs terminal binary start X.1
          (canonicalLeftCtx P) (canonicalOmega Y ++ canonicalRightCtx P) :=
        TypedOccurs.left (canonicalChi_spec P) hRule.1 (canonicalOmega_spec Y)
      have hCan := canonicalChi_total_length_le_of_occurs X hOccX
      have hConstructed :
          (canonicalLeftCtx P).length +
              (canonicalOmega Y ++ canonicalRightCtx P).length < 2 * n := by
        apply wrapper_right_context_length_lt_two_mul hn
        · simpa [n] using hPCtx
        · simpa [n] using hYYield
      exact le_trans hCan (Nat.le_of_lt hConstructed)
    · rcases hRight with ⟨P, Y, hRule, hPNon, hYNon⟩
      have hPCtx := canonicalChi_spine_length_le S P hPNon
      have hYYield := canonicalOmega_length_le_typed_state_card S Y
      have hOccX : TypedOccurs Obs terminal binary start X.1
          (canonicalLeftCtx P ++ canonicalOmega Y) (canonicalRightCtx P) :=
        TypedOccurs.right (canonicalChi_spec P) hRule.1 (canonicalOmega_spec Y)
      have hCan := canonicalChi_total_length_le_of_occurs X hOccX
      have hConstructed :
          (canonicalLeftCtx P ++ canonicalOmega Y).length +
              (canonicalRightCtx P).length < 2 * n := by
        apply wrapper_left_context_length_lt_two_mul hn
        · simpa [n] using hPCtx
        · simpa [n] using hYYield
      exact le_trans hCan (Nat.le_of_lt hConstructed)
  · have hSpine := canonicalChi_spine_length_le S X hWrap
    have hBound : n - 1 ≤ 2 * n := by omega
    exact le_trans (by simpa [n] using hSpine) hBound

/--
The v46 short-canonical-witness lemma obtained from the concrete retained
linear-spine rule shape, with `n_t` represented by the retained state count.
-/
theorem short_canonical_witnesses_from_typed_shape
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
  · exact canonicalChi_length_le_two_typed_state_card S

/-- Every v46 canonical witness word is linearly bounded in `n_t`. -/
theorem canonicalCS_word_length_le_from_typed_shape
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
  rcases short_canonical_witnesses_from_typed_shape S with ⟨hOmega, hCtx⟩
  have hn : 0 < Fintype.card (KeptState Obs terminal binary start) := by
    rcases hz with hAnchor | hTerminal | hBinary | hEps
    · rcases hAnchor with ⟨X, hX⟩
      exact Fintype.card_pos_iff.mpr ⟨X⟩
    · rcases hTerminal with ⟨X, a, hRule, hX⟩
      exact Fintype.card_pos_iff.mpr ⟨X⟩
    · rcases hBinary with ⟨X, Y, Z, hRule, hX⟩
      exact Fintype.card_pos_iff.mpr ⟨X⟩
    · rcases hEps with ⟨rfl, hEps⟩
      simp
  exact canonicalCS_word_length_le_four_mul epsilonStart hn hOmega hCtx hz

end FixedHCFGv44
end LeanCfgProject
