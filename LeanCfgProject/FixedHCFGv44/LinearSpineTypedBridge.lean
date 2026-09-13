import LeanCfgProject.FixedHCFGv44.LinearShortWitness

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
A concrete bridge between the revised paper's retained yield-typed grammar and
the already verified strict-linear spine calculus.

The only paper-specific input is the wrapper/spine shape guaranteed by the
linear-spine SSBNF normalization: every retained binary production has a
non-wrapper parent and exactly one wrapper child.  Wrapper children therefore
cannot themselves carry a binary continuation.
-/

/-- The retained typed rule-shape supplied by linear-spine SSBNF normalization. -/
structure TypedLinearSpineShape
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) where
  isWrapper : TypedNT N Obs → Prop
  start_not_wrapper : ∀ X : KeptState Obs terminal binary start,
    keptStart X → ¬ isWrapper X.1
  binary_shape : ∀ X Y Z : KeptState Obs terminal binary start,
    keptBinary X Y Z →
      ¬ isWrapper X.1 ∧
        ((isWrapper Y.1 ∧ ¬ isWrapper Z.1) ∨
         (¬ isWrapper Y.1 ∧ isWrapper Z.1))

/--
The strict-linear grammar obtained by contracting each terminal-wrapper child
into the terminal emitted by its parent spine step.
-/
def typedSpineGrammar
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (S : TypedLinearSpineShape Obs terminal binary start) :
    FixedHCFG.StrictLinearGrammar
      (KeptState Obs terminal binary start) Sigma where
  leftRule := fun X a Y =>
    ∃ W : KeptState Obs terminal binary start,
      S.isWrapper W.1 ∧ keptBinary X W Y ∧ keptTerminal W a
  rightRule := fun X Y a =>
    ∃ W : KeptState Obs terminal binary start,
      S.isWrapper W.1 ∧ keptBinary X Y W ∧ keptTerminal W a
  terminalRule := keptTerminal
  startState := keptStart
  hasEpsilon := False

/-- A retained wrapper derivation must be a single terminal rule. -/
theorem wrapper_keptDerives_terminal
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (S : TypedLinearSpineShape Obs terminal binary start)
    {X : TypedNT N Obs} {w : Word Sigma}
    (hWrap : S.isWrapper X)
    (d : KeptDerives Obs terminal binary start X w) :
    ∃ (hKeep : TypedKept Obs terminal binary start X) (a : Sigma),
      w = [a] ∧ keptTerminal (⟨X, hKeep⟩ : KeptState Obs terminal binary start) a := by
  cases d with
  | @terminal A a hrule hkeep =>
      refine ⟨hkeep, a, rfl, ?_⟩
      exact ⟨hrule, rfl⟩
  | @binary A B C mu nu x y hrule hkeep left right =>
      let Xs : KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := Obs.mul mu nu }, hkeep⟩
      let Ys : KeptState Obs terminal binary start :=
        ⟨{ label := B, yieldType := mu },
          keptDerives_root_kept Obs terminal binary start left⟩
      let Zs : KeptState Obs terminal binary start :=
        ⟨{ label := C, yieldType := nu },
          keptDerives_root_kept Obs terminal binary start right⟩
      have hRule : keptBinary Xs Ys Zs := ⟨hrule, rfl⟩
      have hNot := (S.binary_shape Xs Ys Zs hRule).1
      exact (hNot (by simpa [Xs] using hWrap)).elim

/-- Every strict-linear contracted derivation expands to a typed derivation. -/
theorem spineDerives_to_typed
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (S : TypedLinearSpineShape Obs terminal binary start)
    {X : KeptState Obs terminal binary start}
    {sp : List (KeptState Obs terminal binary start)} {w : Word Sigma}
    (d : FixedHCFG.LinearDerivesSpine (typedSpineGrammar S) X sp w) :
    TypedDerives Obs terminal binary X.1 w := by
  induction d with
  | @terminal X a hRule =>
      exact keptTerminal_derives X a hRule
  | @left X Y a sp w hStep child ih =>
      rcases hStep with ⟨W, hWrap, hBinary, hTerminal⟩
      have hW := keptTerminal_derives W a hTerminal
      have h := TypedDerives.binary (Obs := Obs)
        (terminal := terminal) (binary := binary)
        hBinary.1 hW ih
      simpa [hBinary.2] using h
  | @right X Y a sp w hStep child ih =>
      rcases hStep with ⟨W, hWrap, hBinary, hTerminal⟩
      have hW := keptTerminal_derives W a hTerminal
      have h := TypedDerives.binary (Obs := Obs)
        (terminal := terminal) (binary := binary)
        hBinary.1 ih hW
      simpa [hBinary.2] using h

/--
A retained derivation from a spine symbol contracts to a derivation in the
verified strict-linear grammar.
-/
theorem keptDerives_to_spine
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (S : TypedLinearSpineShape Obs terminal binary start)
    {X : TypedNT N Obs} {w : Word Sigma}
    (d : KeptDerives Obs terminal binary start X w)
    (hNon : ¬ S.isWrapper X) :
    ∃ (hKeep : TypedKept Obs terminal binary start X)
      (sp : List (KeptState Obs terminal binary start)),
      FixedHCFG.LinearDerivesSpine (typedSpineGrammar S)
        (⟨X, hKeep⟩ : KeptState Obs terminal binary start) sp w := by
  induction d with
  | @terminal A a hrule hkeep =>
      refine ⟨hkeep, [⟨{ label := A, yieldType := obsValue Obs [a] }, hkeep⟩], ?_⟩
      exact FixedHCFG.LinearDerivesSpine.terminal ⟨hrule, rfl⟩
  | @binary A B C mu nu x y hrule hkeep left right ihLeft ihRight =>
      let Xs : KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := Obs.mul mu nu }, hkeep⟩
      let hYKeep := keptDerives_root_kept Obs terminal binary start left
      let hZKeep := keptDerives_root_kept Obs terminal binary start right
      let Ys : KeptState Obs terminal binary start :=
        ⟨{ label := B, yieldType := mu }, hYKeep⟩
      let Zs : KeptState Obs terminal binary start :=
        ⟨{ label := C, yieldType := nu }, hZKeep⟩
      have hRule : keptBinary Xs Ys Zs := ⟨hrule, rfl⟩
      have hShape := S.binary_shape Xs Ys Zs hRule
      have hParentNon : ¬ S.isWrapper Xs.1 := hShape.1
      have hNonXs : ¬ S.isWrapper Xs.1 := by
        simpa [Xs] using hNon
      rcases hShape.2 with hLeftWrap | hRightWrap
      · rcases hLeftWrap with ⟨hYWrap, hZNon⟩
        rcases wrapper_keptDerives_terminal S hYWrap left with
          ⟨hYKeep', a, hx, hTerminal⟩
        rcases ihRight hZNon with ⟨hZKeep', sp, hSpine⟩
        have hYEq : (⟨{ label := B, yieldType := mu }, hYKeep'⟩ :
            KeptState Obs terminal binary start) = Ys := by
          apply Subtype.ext
          rfl
        have hZEq : (⟨{ label := C, yieldType := nu }, hZKeep'⟩ :
            KeptState Obs terminal binary start) = Zs := by
          apply Subtype.ext
          rfl
        have hStep : (typedSpineGrammar S).leftRule Xs a Zs := by
          refine ⟨Ys, hYWrap, hRule, ?_⟩
          simpa [hYEq] using hTerminal
        refine ⟨hkeep, Xs :: sp, ?_⟩
        have hLin := FixedHCFG.LinearDerivesSpine.left hStep (by simpa [hZEq] using hSpine)
        simpa [hx] using hLin
      · rcases hRightWrap with ⟨hYNon, hZWrap⟩
        rcases wrapper_keptDerives_terminal S hZWrap right with
          ⟨hZKeep', a, hy, hTerminal⟩
        rcases ihLeft hYNon with ⟨hYKeep', sp, hSpine⟩
        have hYEq : (⟨{ label := B, yieldType := mu }, hYKeep'⟩ :
            KeptState Obs terminal binary start) = Ys := by
          apply Subtype.ext
          rfl
        have hZEq : (⟨{ label := C, yieldType := nu }, hZKeep'⟩ :
            KeptState Obs terminal binary start) = Zs := by
          apply Subtype.ext
          rfl
        have hStep : (typedSpineGrammar S).rightRule Xs Ys a := by
          refine ⟨Zs, hZWrap, hRule, ?_⟩
          simpa [hZEq] using hTerminal
        refine ⟨hkeep, Xs :: sp, ?_⟩
        have hLin := FixedHCFG.LinearDerivesSpine.right hStep (by simpa [hYEq] using hSpine)
        simpa [hy] using hLin

/--
For a non-wrapper retained state, canonical shortlex minimality becomes the
minimum-length hypothesis required by the verified strict-linear spine lemma.
-/
theorem canonicalOmega_spine_length_le
    {N : Type v} {Sigma : Type u}
    [Fintype N] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (S : TypedLinearSpineShape Obs terminal binary start)
    (X : KeptState Obs terminal binary start)
    (hNon : ¬ S.isWrapper X.1) :
    (canonicalOmega X).length ≤
      Fintype.card (KeptState Obs terminal binary start) := by
  have hOcc := canonicalChi_spec X
  have hKept := successful_derivation_survives Obs terminal binary start
    hOcc (canonicalOmega_spec X)
  rcases keptDerives_to_spine S hKept hNon with ⟨hKeep, sp, hSpine⟩
  let X' : KeptState Obs terminal binary start := ⟨X.1, hKeep⟩
  have hXX' : X' = X := by
    apply Subtype.ext
    rfl
  have hDeriv : FixedHCFG.LinearDerives (typedSpineGrammar S) X'
      (canonicalOmega X) := ⟨sp, by simpa [X'] using hSpine⟩
  have hMin : FixedHCFG.LinearYieldMinimal (typedSpineGrammar S) X'
      (canonicalOmega X) := by
    constructor
    · exact hDeriv
    · intro z hz
      rcases hz with ⟨spz, dz⟩
      have hTyped := spineDerives_to_typed S dz
      have hTypedX : TypedDerives Obs terminal binary X.1 z := by
        simpa [X', hXX'] using hTyped
      exact canonicalOmega_length_le_of_derives X hTypedX
  exact section7_spine_yield_bound hMin

/--
The first inequality of the v46 short-canonical-witness lemma, now derived
from the actual retained typed rule shape rather than assumed as a certificate.
-/
theorem canonicalOmega_length_le_typed_state_card
    {N : Type v} {Sigma : Type u}
    [Fintype N] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (S : TypedLinearSpineShape Obs terminal binary start)
    (X : KeptState Obs terminal binary start) :
    (canonicalOmega X).length ≤
      Fintype.card (KeptState Obs terminal binary start) := by
  by_cases hWrap : S.isWrapper X.1
  · have hKept := successful_derivation_survives Obs terminal binary start
      (canonicalChi_spec X) (canonicalOmega_spec X)
    rcases wrapper_keptDerives_terminal S hWrap hKept with
      ⟨hKeep, a, hWord, hTerminal⟩
    have hLen : (canonicalOmega X).length = 1 := by
      simpa [hWord]
    have hPos : 0 < Fintype.card (KeptState Obs terminal binary start) :=
      Fintype.card_pos_iff.mpr ⟨X⟩
    rw [hLen]
    exact Nat.succ_le_iff.mpr hPos
  · exact canonicalOmega_spine_length_le S X hWrap

end FixedHCFGv44
end LeanCfgProject
