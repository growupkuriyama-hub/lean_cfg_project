import LeanCfgProject.FixedHCFG.LinearActualSampleFinite

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
Branch specifications for the finite realised-rule observations.
These lemmas expose the concrete manuscript word selected by each source-rule
shape while keeping the dependent shape proof encapsulated in
`actualLinearRuleObservation`.
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
  simp [actualLinearRuleObservation, hshape]

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
  simp [actualLinearRuleObservation, hshape]

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
  simp [actualLinearRuleObservation, hshape]

end FixedHCFG
end LeanCfgProject
