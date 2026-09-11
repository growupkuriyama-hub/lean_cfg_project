import LeanCfgProject.FixedHCFG.LinearActualSampleExact

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
Exact finite representation of the manuscript characteristic sample
`CS_lin(H)`.  The key bridge is surjectivity of realised source slots onto the
retained terminal/left/right rules of the reduced typed linear grammar.
-/

/-- Every retained left-linear rule comes from a realised finite source slot. -/
theorem exists_actualLinearRuleSlot_left
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    [Fintype (ActualLinearState Obs G)]
    (X Y : ActualLinearState Obs G) (a : Sigma)
    (hrule : (ActualLinearGrammar Obs G).leftRule X a Y) :
    ∃ s : ActualLinearRuleSlot Obs G,
      ∃ hshape : G.rhs s.1.1 = LinearRHS.left a Y.1.label,
        actualLinearSlotParentState Obs G s = X ∧
        actualLinearLeftSlotChildState Obs G s a Y.1.label hshape = Y := by
  have hruleF :
      (fullTypedLinearGrammar Obs G).leftRule X.1 a Y.1 := by
    simpa [ActualLinearGrammar, trimStrictLinearGrammar] using hrule
  rcases hruleF.1 with ⟨r, hlhs, hrhs⟩
  let raw : LinearTypedRuleSlot Obs P :=
    (r, Y.1.yieldType, X.1.leftType, X.1.rightType)
  have hparent : linearSlotParent Obs G raw = X.1 := by
    apply encodeTypedNT_injective Obs
    simp [encodeTypedNT, linearSlotParent, raw, hrhs, hlhs, hruleF.2.1]
  let childVal : TypedNT N Obs :=
    ⟨Y.1.label, Y.1.yieldType,
      Obs.mul X.1.leftType (Obs.value [a]), X.1.rightType⟩
  have hchildVal : childVal = Y.1 := by
    apply encodeTypedNT_injective Obs
    simp [childVal, encodeTypedNT, hruleF.2.2.1, hruleF.2.2.2]
  have hchild : actualLinearSlotChild? Obs G raw = some Y.1 := by
    simpa [actualLinearSlotChild?, linearSlotChild?, raw, hrhs, childVal] using
      congrArg some hchildVal
  have hreal : ActualLinearSlotRealized Obs G raw := by
    change
      match actualLinearSlotChild? Obs G raw with
      | none =>
          StrictLinearKept (fullTypedLinearGrammar Obs G)
            (linearSlotParent Obs G raw)
      | some Z =>
          StrictLinearKept (fullTypedLinearGrammar Obs G)
              (linearSlotParent Obs G raw) ∧
            StrictLinearKept (fullTypedLinearGrammar Obs G) Z
    rw [hchild, hparent]
    exact ⟨X.2, Y.2⟩
  let s : ActualLinearRuleSlot Obs G := ⟨raw, hreal⟩
  have hsShape : G.rhs s.1.1 = LinearRHS.left a Y.1.label := by
    simpa [s, raw] using hrhs
  refine ⟨s, hsShape, ?_, ?_⟩
  · apply Subtype.ext
    simpa [s, actualLinearSlotParentState] using hparent
  · apply Subtype.ext
    simpa [s, raw, actualLinearLeftSlotChildState, childVal] using hchildVal

/-- Every retained right-linear rule comes from a realised finite source slot. -/
theorem exists_actualLinearRuleSlot_right
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    [Fintype (ActualLinearState Obs G)]
    (X Y : ActualLinearState Obs G) (a : Sigma)
    (hrule : (ActualLinearGrammar Obs G).rightRule X Y a) :
    ∃ s : ActualLinearRuleSlot Obs G,
      ∃ hshape : G.rhs s.1.1 = LinearRHS.right Y.1.label a,
        actualLinearSlotParentState Obs G s = X ∧
        actualLinearRightSlotChildState Obs G s Y.1.label a hshape = Y := by
  have hruleF :
      (fullTypedLinearGrammar Obs G).rightRule X.1 Y.1 a := by
    simpa [ActualLinearGrammar, trimStrictLinearGrammar] using hrule
  rcases hruleF.1 with ⟨r, hlhs, hrhs⟩
  let raw : LinearTypedRuleSlot Obs P :=
    (r, Y.1.yieldType, X.1.leftType, X.1.rightType)
  have hparent : linearSlotParent Obs G raw = X.1 := by
    apply encodeTypedNT_injective Obs
    simp [encodeTypedNT, linearSlotParent, raw, hrhs, hlhs, hruleF.2.1]
  let childVal : TypedNT N Obs :=
    ⟨Y.1.label, Y.1.yieldType, X.1.leftType,
      Obs.mul (Obs.value [a]) X.1.rightType⟩
  have hchildVal : childVal = Y.1 := by
    apply encodeTypedNT_injective Obs
    simp [childVal, encodeTypedNT, hruleF.2.2.1, hruleF.2.2.2]
  have hchild : actualLinearSlotChild? Obs G raw = some Y.1 := by
    simpa [actualLinearSlotChild?, linearSlotChild?, raw, hrhs, childVal] using
      congrArg some hchildVal
  have hreal : ActualLinearSlotRealized Obs G raw := by
    change
      match actualLinearSlotChild? Obs G raw with
      | none =>
          StrictLinearKept (fullTypedLinearGrammar Obs G)
            (linearSlotParent Obs G raw)
      | some Z =>
          StrictLinearKept (fullTypedLinearGrammar Obs G)
              (linearSlotParent Obs G raw) ∧
            StrictLinearKept (fullTypedLinearGrammar Obs G) Z
    rw [hchild, hparent]
    exact ⟨X.2, Y.2⟩
  let s : ActualLinearRuleSlot Obs G := ⟨raw, hreal⟩
  have hsShape : G.rhs s.1.1 = LinearRHS.right Y.1.label a := by
    simpa [s, raw] using hrhs
  refine ⟨s, hsShape, ?_, ?_⟩
  · apply Subtype.ext
    simpa [s, actualLinearSlotParentState] using hparent
  · apply Subtype.ext
    simpa [s, raw, actualLinearRightSlotChildState, childVal] using hchildVal

/-- The exact finite image of all anchor, realised-rule, and genuine epsilon indices. -/
noncomputable def actualLinearSampleFinset
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    [Fintype (ActualLinearState Obs G)]
    [Fintype (ActualLinearRuleSlot Obs G)] : Finset (Word Sigma) := by
  classical
  letI : Fintype (ActualLinearEpsilonSlot Obs G) := Fintype.ofFinite _
  exact Finset.univ.image (actualLinearSampleWord Obs G)

/-- The finite image is exactly the manuscript observation language `CS_lin(H)`. -/
theorem actualLinearCS_iff_mem_actualLinearSampleFinset
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    [Fintype (ActualLinearState Obs G)]
    [Fintype (ActualLinearRuleSlot Obs G)]
    (z : Word Sigma) :
    z ∈ ActualLinearCS Obs G ↔ z ∈ actualLinearSampleFinset Obs G := by
  classical
  constructor
  · intro hz
    simp only [actualLinearSampleFinset, Finset.mem_image, Finset.mem_univ,
      true_and]
    rcases hz with hAnchor | hTerm | hLeft | hRight | hEps
    · rcases hAnchor with ⟨X, hz⟩
      refine ⟨Sum.inl X, ?_⟩
      simpa [actualLinearSampleWord, actualLinearAnchorWitness] using hz.symm
    · rcases hTerm with ⟨X, a, hrule, hz⟩
      rcases exists_actualLinearRuleSlot_terminal Obs G X a hrule with
        ⟨s, hsParent, hsShape⟩
      refine ⟨Sum.inr (Sum.inl s), ?_⟩
      have hword := actualLinearRuleObservation_word_terminal Obs G s a hsShape
      rw [hsParent] at hword
      have hEq : (actualLinearRuleObservation Obs G s).word = z :=
        hword.trans hz.symm
      simpa [actualLinearSampleWord] using hEq
    · rcases hLeft with ⟨X, Y, a, hrule, hz⟩
      rcases exists_actualLinearRuleSlot_left Obs G X Y a hrule with
        ⟨s, hsShape, hsParent, hsChild⟩
      refine ⟨Sum.inr (Sum.inl s), ?_⟩
      have hword := actualLinearRuleObservation_word_left Obs G s a Y.1.label hsShape
      rw [hsParent, hsChild] at hword
      have hEq : (actualLinearRuleObservation Obs G s).word = z :=
        hword.trans hz.symm
      simpa [actualLinearSampleWord] using hEq
    · rcases hRight with ⟨X, Y, a, hrule, hz⟩
      rcases exists_actualLinearRuleSlot_right Obs G X Y a hrule with
        ⟨s, hsShape, hsParent, hsChild⟩
      refine ⟨Sum.inr (Sum.inl s), ?_⟩
      have hword := actualLinearRuleObservation_word_right Obs G s Y.1.label a hsShape
      rw [hsParent, hsChild] at hword
      have hEq : (actualLinearRuleObservation Obs G s).word = z :=
        hword.trans hz.symm
      simpa [actualLinearSampleWord] using hEq
    · rcases hEps with ⟨heps, hz⟩
      let e : ActualLinearEpsilonSlot Obs G := ⟨(), heps⟩
      refine ⟨Sum.inr (Sum.inr e), ?_⟩
      simpa [actualLinearSampleWord] using hz.symm
  · intro hz
    simp only [actualLinearSampleFinset, Finset.mem_image, Finset.mem_univ,
      true_and] at hz
    rcases hz with ⟨i, rfl⟩
    exact actualLinearSampleWord_mem_CS Obs G i

end FixedHCFG
end LeanCfgProject
