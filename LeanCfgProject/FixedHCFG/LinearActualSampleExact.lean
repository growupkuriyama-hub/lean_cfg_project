import LeanCfgProject.FixedHCFG.LinearActualSampleFinite

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
Branch specifications for the finite realised-rule observations.
These lemmas expose the concrete manuscript word selected by each source-rule
shape through the certified `shape` field of `actualLinearRuleObservation`.
-/

/-- Terminal realised slots select exactly the terminal local observation word. -/
theorem actualLinearRuleObservation_word_terminal
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    [Fintype (ActualLinearState Obs G)]
    (s : ActualLinearRuleSlot Obs G) (a : Sigma)
    (hshape : G.rhs s.1.1 = LinearRHS.terminal a) :
    (actualLinearRuleObservation Obs G s).word =
      trimLinearLeftCtx (fullTypedLinearGrammar Obs G)
          (actualLinearSlotParentState Obs G s) ++
        [a] ++
        trimLinearRightCtx (fullTypedLinearGrammar Obs G)
          (actualLinearSlotParentState Obs G s) := by
  rcases (actualLinearRuleObservation Obs G s).shape with hterm | hrest
  · rcases hterm with ⟨b, hb, hword⟩
    have hba : b = a := by
      injection hb.symm.trans hshape
    subst b
    exact hword
  · rcases hrest with hleft | hright
    · rcases hleft with ⟨b, B, hb, _⟩
      cases hb.symm.trans hshape
    · rcases hright with ⟨B, b, hb, _⟩
      cases hb.symm.trans hshape

/-- Left-linear realised slots select exactly the corresponding local observation word. -/
theorem actualLinearRuleObservation_word_left
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    [Fintype (ActualLinearState Obs G)]
    (s : ActualLinearRuleSlot Obs G) (a : Sigma) (B : N)
    (hshape : G.rhs s.1.1 = LinearRHS.left a B) :
    (actualLinearRuleObservation Obs G s).word =
      let F := fullTypedLinearGrammar Obs G
      let X := actualLinearSlotParentState Obs G s
      let Y := actualLinearLeftSlotChildState Obs G s a B hshape
      trimLinearLeftCtx F X ++ [a] ++ trimLinearOmega F Y ++
        trimLinearRightCtx F X := by
  rcases (actualLinearRuleObservation Obs G s).shape with hterm | hrest
  · rcases hterm with ⟨b, hb, _⟩
    cases hb.symm.trans hshape
  · rcases hrest with hleft | hright
    · rcases hleft with ⟨b, C, hb, hword⟩
      have hEq : LinearRHS.left b C = LinearRHS.left a B := hb.symm.trans hshape
      injection hEq with hab hCB
      subst b
      subst C
      simpa using hword
    · rcases hright with ⟨C, b, hb, _⟩
      cases hb.symm.trans hshape

/-- Right-linear realised slots select exactly the corresponding local observation word. -/
theorem actualLinearRuleObservation_word_right
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    [Fintype (ActualLinearState Obs G)]
    (s : ActualLinearRuleSlot Obs G) (B : N) (a : Sigma)
    (hshape : G.rhs s.1.1 = LinearRHS.right B a) :
    (actualLinearRuleObservation Obs G s).word =
      let F := fullTypedLinearGrammar Obs G
      let X := actualLinearSlotParentState Obs G s
      let Y := actualLinearRightSlotChildState Obs G s B a hshape
      trimLinearLeftCtx F X ++ trimLinearOmega F Y ++ [a] ++
        trimLinearRightCtx F X := by
  rcases (actualLinearRuleObservation Obs G s).shape with hterm | hrest
  · rcases hterm with ⟨b, hb, _⟩
    cases hb.symm.trans hshape
  · rcases hrest with hleft | hright
    · rcases hleft with ⟨b, C, hb, _⟩
      cases hb.symm.trans hshape
    · rcases hright with ⟨C, b, hb, hword⟩
      have hEq : LinearRHS.right C b = LinearRHS.right B a := hb.symm.trans hshape
      injection hEq with hCB hba
      subst C
      subst b
      simpa using hword

end FixedHCFG
end LeanCfgProject
