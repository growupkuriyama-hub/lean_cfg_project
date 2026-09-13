import LeanCfgProject.FixedHCFGv44.LinearSpineTypedBridge

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
V47 context-side bridge for the linear subclass.

This module isolates the non-wrapper part first.  It contracts actual retained
yield-typed occurrences to the already verified strict-linear occurrence
calculus and expands them back.  The wrapper-context case is kept separate so
that the central spine bound can be checked independently.
-/

/-- Extensionality for the concrete yield-typed state record. -/
theorem typedNT_eq_of_components
    {N : Type v} {Sigma : Type u} {Obs : Observer Sigma}
    {X Y : TypedNT N Obs}
    (hLabel : X.label = Y.label)
    (hYield : X.yieldType = Y.yieldType) : X = Y := by
  cases X with
  | mk xl xy =>
      cases Y with
      | mk yl yy =>
          cases hLabel
          cases hYield
          rfl

/-- Every contracted strict-linear occurrence expands to a typed occurrence. -/
theorem spineOccurs_to_typed_v47
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
      have hParentEq : X.1 =
          { label := X.1.label,
            yieldType := Obs.mul W.1.yieldType Y.1.yieldType } := by
        apply typedNT_eq_of_components
        · rfl
        · exact hBinary.2.symm
      have ih' : TypedOccurs Obs terminal binary start
          { label := X.1.label,
            yieldType := Obs.mul W.1.yieldType Y.1.yieldType } u v := by
        rw [← hParentEq]
        exact ih
      have hW := keptTerminal_derives W a hTerminal
      have hOcc := TypedOccurs.right ih' hBinary.1 hW
      simpa using hOcc
  | @right X Y a sp u v parent hStep ih =>
      rcases hStep with ⟨W, hWrap, hBinary, hTerminal⟩
      have hParentEq : X.1 =
          { label := X.1.label,
            yieldType := Obs.mul Y.1.yieldType W.1.yieldType } := by
        apply typedNT_eq_of_components
        · rfl
        · exact hBinary.2.symm
      have ih' : TypedOccurs Obs terminal binary start
          { label := X.1.label,
            yieldType := Obs.mul Y.1.yieldType W.1.yieldType } u v := by
        rw [← hParentEq]
        exact ih
      have hW := keptTerminal_derives W a hTerminal
      have hOcc := TypedOccurs.left ih' hBinary.1 hW
      simpa using hOcc

/--
A typed occurrence of a non-wrapper state contracts to a strict-linear
occurrence.  Productivity of the current subtree is supplied explicitly.
-/
theorem typedOccurs_to_spine_v47
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

/-- Actual canonical context bound for every retained non-wrapper spine state. -/
theorem canonicalChi_spine_length_le_v47
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
  rcases typedOccurs_to_spine_v47 S hOcc hDeriv hNon with
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
      have hTyped := spineOccurs_to_typed_v47 S hsp'
      have hTypedX : TypedOccurs Obs terminal binary start X.1 l r := by
        simpa [X', hXX'] using hTyped
      exact canonicalChi_total_length_le_of_occurs X hTypedX
  exact section7_spine_context_bound hMin

end FixedHCFGv44
end LeanCfgProject
