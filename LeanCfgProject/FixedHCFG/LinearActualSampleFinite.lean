import LeanCfgProject.FixedHCFG.LinearActualSample
import LeanCfgProject.FixedHCFG.LinearBounds

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
Finite indexing for the *actual* manuscript characteristic sample `CS_lin(H)`.

The epsilon slot is genuinely optional here: unlike the generic `+1` envelope,
we index it by a subtype of `Unit` carrying the proposition `H.hasEpsilon`.
This avoids introducing a spurious empty word when the target grammar has no
epsilon rule.
-/

/-- Optional epsilon index for the actual reduced typed linear grammar. -/
abbrev ActualLinearEpsilonSlot
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :=
  {_ : Unit // (ActualLinearGrammar Obs G).hasEpsilon}

/-- Exact finite index family: retained-state anchors, realised rules, optional epsilon. -/
abbrev ActualLinearSampleIndex
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :=
  Sum (ActualLinearState Obs G)
    (Sum (ActualLinearRuleSlot Obs G) (ActualLinearEpsilonSlot Obs G))

/-- Anchor word attached to an actual retained typed state. -/
noncomputable def actualLinearAnchorWitness
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (X : ActualLinearState Obs G) : Word Sigma :=
  let F := fullTypedLinearGrammar Obs G
  trimLinearLeftCtx F X ++ trimLinearOmega F X ++ trimLinearRightCtx F X

/-- The exact sample word associated with one actual finite sample index. -/
noncomputable def actualLinearSampleWord
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :
    ActualLinearSampleIndex Obs G → Word Sigma
  | Sum.inl X => actualLinearAnchorWitness Obs G X
  | Sum.inr (Sum.inl s) => actualLinearRuleWitness Obs G s
  | Sum.inr (Sum.inr _) => []

/-- Every realised rule slot really is one of the local rule observations in `CS_lin(H)`. -/
theorem actualLinearRuleWitness_mem_CS
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (s : ActualLinearRuleSlot Obs G) :
    actualLinearRuleWitness Obs G s ∈ ActualLinearCS Obs G := by
  let F := fullTypedLinearGrammar Obs G
  let H := ActualLinearGrammar Obs G
  let X := actualLinearSlotParentState Obs G s
  cases hshape : G.rhs s.1.1 with
  | terminal a =>
      have hruleF : F.terminalRule X.1 a := by
        change
          ((∃ r : P,
              G.lhs r = (linearSlotParent Obs G s.1).label ∧
              G.rhs r = LinearRHS.terminal a) ∧
            Obs.value [a] = (linearSlotParent Obs G s.1).yieldType)
        constructor
        · refine ⟨s.1.1, ?_, hshape⟩
          simp [linearSlotParent, hshape]
        · simp [linearSlotParent, hshape]
      have hruleH : H.terminalRule X a := by
        simpa [H, ActualLinearGrammar, F, trimStrictLinearGrammar] using hruleF
      have hz : ActualLinearCS Obs G
          (trimLinearLeftCtx F X ++ [a] ++ trimLinearRightCtx F X) :=
        Or.inr (Or.inl ⟨X, a, hruleH, rfl⟩)
      unfold actualLinearRuleWitness
      rw [hshape]
      simpa [F, X] using hz
  | left a B =>
      let Y := actualLinearLeftSlotChildState Obs G s a B hshape
      have hruleF : F.leftRule X.1 a Y.1 := by
        change
          ((∃ r : P,
              G.lhs r = (linearSlotParent Obs G s.1).label ∧
              G.rhs r = LinearRHS.left a Y.1.label) ∧
            (linearSlotParent Obs G s.1).yieldType =
              Obs.mul (Obs.value [a]) Y.1.yieldType ∧
            Y.1.leftType =
              Obs.mul (linearSlotParent Obs G s.1).leftType (Obs.value [a]) ∧
            Y.1.rightType = (linearSlotParent Obs G s.1).rightType)
        constructor
        · refine ⟨s.1.1, ?_, ?_⟩
          · simp [linearSlotParent, hshape]
          · simpa [Y, actualLinearLeftSlotChildState] using hshape
        · constructor
          · simp [linearSlotParent, Y, actualLinearLeftSlotChildState, hshape]
          · constructor <;>
              simp [linearSlotParent, Y, actualLinearLeftSlotChildState, hshape]
      have hruleH : H.leftRule X a Y := by
        simpa [H, ActualLinearGrammar, F, trimStrictLinearGrammar] using hruleF
      have hz : ActualLinearCS Obs G
          (trimLinearLeftCtx F X ++ [a] ++ trimLinearOmega F Y ++
            trimLinearRightCtx F X) :=
        Or.inr (Or.inr (Or.inl ⟨X, Y, a, hruleH, rfl⟩))
      unfold actualLinearRuleWitness
      rw [hshape]
      simpa [F, X, Y] using hz
  | right B a =>
      let Y := actualLinearRightSlotChildState Obs G s B a hshape
      have hruleF : F.rightRule X.1 Y.1 a := by
        change
          ((∃ r : P,
              G.lhs r = (linearSlotParent Obs G s.1).label ∧
              G.rhs r = LinearRHS.right Y.1.label a) ∧
            (linearSlotParent Obs G s.1).yieldType =
              Obs.mul Y.1.yieldType (Obs.value [a]) ∧
            Y.1.leftType = (linearSlotParent Obs G s.1).leftType ∧
            Y.1.rightType =
              Obs.mul (Obs.value [a]) (linearSlotParent Obs G s.1).rightType)
        constructor
        · refine ⟨s.1.1, ?_, ?_⟩
          · simp [linearSlotParent, hshape]
          · simpa [Y, actualLinearRightSlotChildState] using hshape
        · constructor
          · simp [linearSlotParent, Y, actualLinearRightSlotChildState, hshape]
          · constructor <;>
              simp [linearSlotParent, Y, actualLinearRightSlotChildState, hshape]
      have hruleH : H.rightRule X Y a := by
        simpa [H, ActualLinearGrammar, F, trimStrictLinearGrammar] using hruleF
      have hz : ActualLinearCS Obs G
          (trimLinearLeftCtx F X ++ trimLinearOmega F Y ++ [a] ++
            trimLinearRightCtx F X) :=
        Or.inr (Or.inr (Or.inr (Or.inl ⟨X, Y, a, hruleH, rfl⟩)))
      unfold actualLinearRuleWitness
      rw [hshape]
      simpa [F, X, Y] using hz

/-- Every finitely indexed actual sample word belongs to the manuscript sample language. -/
theorem actualLinearSampleWord_mem_CS
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (i : ActualLinearSampleIndex Obs G) :
    actualLinearSampleWord Obs G i ∈ ActualLinearCS Obs G := by
  cases i with
  | inl X =>
      exact Or.inl ⟨X, rfl⟩
  | inr rest =>
      cases rest with
      | inl s =>
          exact actualLinearRuleWitness_mem_CS Obs G s
      | inr e =>
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.2, rfl⟩)))

/-- Every actual anchor has the manuscript bound `2|W|`. -/
theorem actualLinearAnchorWitness_length_le
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    [Fintype (ActualLinearState Obs G)]
    (X : ActualLinearState Obs G) :
    (actualLinearAnchorWitness Obs G X).length ≤
      2 * Fintype.card (ActualLinearState Obs G) := by
  let F := fullTypedLinearGrammar Obs G
  exact linear_anchor_length_le_two_states
    (trimLinearLeftCtx F X) (trimLinearOmega F X) (trimLinearRightCtx F X)
    (trimLinearChi_length_le F X)
    (trimLinearOmega_length_le F X)

/-- Every actual realised-rule witness has the manuscript bound `2|W|`. -/
theorem actualLinearRuleWitness_length_le
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    [Fintype (ActualLinearState Obs G)]
    (s : ActualLinearRuleSlot Obs G) :
    (actualLinearRuleWitness Obs G s).length ≤
      2 * Fintype.card (ActualLinearState Obs G) := by
  let F := fullTypedLinearGrammar Obs G
  let X := actualLinearSlotParentState Obs G s
  have hstate : 1 ≤ Fintype.card (ActualLinearState Obs G) := by
    exact Fintype.card_pos_iff.mpr ⟨X⟩
  have hctx := trimLinearChi_length_le F X
  cases hshape : G.rhs s.1.1 with
  | terminal a =>
      have h := linear_rule_witness_length_le_two_states
        (trimLinearLeftCtx F X) ([] : Word Sigma) (trimLinearRightCtx F X) a
        hstate hctx (Nat.zero_le _)
      unfold actualLinearRuleWitness
      rw [hshape]
      simpa [F, X] using h
  | left a B =>
      let Y := actualLinearLeftSlotChildState Obs G s a B hshape
      have hy := trimLinearOmega_length_le F Y
      have h := linear_rule_witness_length_le_two_states
        (trimLinearLeftCtx F X) (trimLinearOmega F Y) (trimLinearRightCtx F X) a
        hstate hctx hy
      unfold actualLinearRuleWitness
      rw [hshape]
      simpa [F, X, Y] using h
  | right B a =>
      let Y := actualLinearRightSlotChildState Obs G s B a hshape
      have hy := trimLinearOmega_length_le F Y
      have h := linear_rule_witness_right_length_le_two_states
        (trimLinearLeftCtx F X) (trimLinearOmega F Y) (trimLinearRightCtx F X) a
        hstate hctx hy
      unfold actualLinearRuleWitness
      rw [hshape]
      simpa [F, X, Y] using h

/-- Uniform `2|W|` bound for the exact actual finite sample indexing. -/
theorem actualLinearSampleWord_length_le
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    [Fintype (ActualLinearState Obs G)]
    (i : ActualLinearSampleIndex Obs G) :
    (actualLinearSampleWord Obs G i).length ≤
      2 * Fintype.card (ActualLinearState Obs G) := by
  cases i with
  | inl X =>
      exact actualLinearAnchorWitness_length_le Obs G X
  | inr rest =>
      cases rest with
      | inl s =>
          exact actualLinearRuleWitness_length_le Obs G s
      | inr e =>
          simp [actualLinearSampleWord]

end FixedHCFG
end LeanCfgProject
