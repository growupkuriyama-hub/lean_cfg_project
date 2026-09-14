import LeanCfgProject.FixedHCFGv44.LinearSpineWrapperContextV47
import LeanCfgProject.FixedHCFGv44.CharacteristicDataBounds

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Finite-retained-state bridge for the v49 linear normalization.

The older linear witness files obtain finiteness of retained yield-typed states
from a global `[Fintype N]` instance on the ambient nonterminal type.  The
explicit v49 normalization intentionally uses an ambient `LinearNormNT` type
with unrestricted stage lists, so that ambient type is not finite even though
only finitely many normalized states are reachable and retained.

This file isolates the mathematically necessary hypothesis: finiteness of the
*retained typed state type itself*.  The strict-linear cycle-deletion arguments
only count those retained states, so no ambient nonterminal finiteness is
needed.  A later active-state lemma can therefore instantiate these theorems
for the explicit Appendix A normalization without reindexing the whole grammar.
-/

/--
Canonical yields are bounded by the number of retained typed states, assuming
that retained state type itself is finite.
-/
theorem canonicalOmega_length_le_retained_card_v49
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype (KeptState Obs terminal binary start)]
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
  · have hOcc := canonicalChi_spec X
    have hKept := successful_derivation_survives Obs terminal binary start
      hOcc (canonicalOmega_spec X)
    rcases keptDerives_to_spine S hKept hWrap with ⟨hKeep, sp, hSpine⟩
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
For a retained non-wrapper spine state, the canonical reaching context has
length at most `n_t - 1`, with `n_t` the retained-state cardinality.
-/
theorem canonicalChi_spine_length_le_retained_card_v49
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype (KeptState Obs terminal binary start)]
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

/--
The wrapper/spine decomposition yields the manuscript's full `2 n_t`
canonical-context bound under retained-state finiteness alone.
-/
theorem canonicalChi_length_le_two_retained_card_v49
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype (KeptState Obs terminal binary start)]
    (S : TypedLinearSpineShape Obs terminal binary start)
    (X : KeptState Obs terminal binary start) :
    (canonicalLeftCtx X).length + (canonicalRightCtx X).length ≤
      2 * Fintype.card (KeptState Obs terminal binary start) := by
  let n := Fintype.card (KeptState Obs terminal binary start)
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨X⟩
  by_cases hWrap : S.isWrapper X.1
  · rcases wrapper_has_spine_parent_v47 S X hWrap with hLeft | hRight
    · rcases hLeft with ⟨P, Y, hRule, hPNon, hYNon⟩
      have hPCtx := canonicalChi_spine_length_le_retained_card_v49 S P hPNon
      have hYYield := canonicalOmega_length_le_retained_card_v49 S Y
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
      have hPCtx := canonicalChi_spine_length_le_retained_card_v49 S P hPNon
      have hYYield := canonicalOmega_length_le_retained_card_v49 S Y
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
  · have hSpine := canonicalChi_spine_length_le_retained_card_v49 S X hWrap
    have hBound : n - 1 ≤ 2 * n := by omega
    exact le_trans (by simpa [n] using hSpine) hBound

/-- The two short-canonical-witness inequalities using only retained-state finiteness. -/
theorem short_canonical_witnesses_from_retained_finite_shape_v49
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype (KeptState Obs terminal binary start)]
    (S : TypedLinearSpineShape Obs terminal binary start) :
    (∀ X : KeptState Obs terminal binary start,
      (canonicalOmega X).length ≤
        Fintype.card (KeptState Obs terminal binary start)) ∧
    (∀ X : KeptState Obs terminal binary start,
      (canonicalLeftCtx X).length + (canonicalRightCtx X).length ≤
        2 * Fintype.card (KeptState Obs terminal binary start)) := by
  constructor
  · exact canonicalOmega_length_le_retained_card_v49 S
  · exact canonicalChi_length_le_two_retained_card_v49 S

/-- Every exact canonical witness word has length at most `4 n_t`. -/
theorem canonicalCS_word_length_le_retained_card_v49
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype (KeptState Obs terminal binary start)]
    (epsilonStart : Prop)
    (S : TypedLinearSpineShape Obs terminal binary start)
    {z : Word Sigma}
    (hz : CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart z) :
    z.length ≤ 4 * Fintype.card (KeptState Obs terminal binary start) := by
  rcases short_canonical_witnesses_from_retained_finite_shape_v49 S with
    ⟨hOmega, hCtx⟩
  rcases hz with hAnchor | hTerminal | hBinary | hEps
  · rcases hAnchor with ⟨X, rfl⟩
    have ho := hOmega X
    have hc := hCtx X
    simp only [canonicalAnchorWord, List.length_append]
    omega
  · rcases hTerminal with ⟨X, a, hRule, rfl⟩
    have hc := hCtx X
    have hn : 0 < Fintype.card (KeptState Obs terminal binary start) :=
      Fintype.card_pos_iff.mpr ⟨X⟩
    simp only [canonicalTerminalObservationWord, List.length_append,
      List.length_singleton]
    omega
  · rcases hBinary with ⟨X, Y, Z, hRule, rfl⟩
    have hc := hCtx X
    have hy := hOmega Y
    have hz' := hOmega Z
    simp only [canonicalBinaryObservationWord, List.length_append]
    omega
  · rcases hEps with ⟨rfl, hEpsilon⟩
    simp

end FixedHCFGv44
end LeanCfgProject
