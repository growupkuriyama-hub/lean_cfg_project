import LeanCfgProject.FixedHCFG.LinearBasisExtraction
import LeanCfgProject.FixedHCFG.LinearRuleSlots

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
Concrete finite rule slots and characteristic-sample witnesses for the actual
Section-7 grammar `H = trim(fullTypedLinearGrammar Obs G)`.

A slot records a source SSLNF production together with the three genuinely free
monoid coordinates `(q,m,n)`.  Realisation additionally requires the parent and,
when present, the unique child typed state to survive reachable/productive
trimming.  This is the concrete finite indexing family needed to remove the
remaining abstract rule/sample index from the Theorem-7.9 envelope.
-/

/-- The child typed state prescribed by a source slot, when the source rule is nonterminal-bearing. -/
def actualLinearSlotChild?
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (s : LinearTypedRuleSlot Obs P) : Option (TypedNT N Obs) :=
  linearSlotChild? Obs G s

/-- A finite source slot is realised exactly when all typed states used by its rule survive trimming. -/
def ActualLinearSlotRealized
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (s : LinearTypedRuleSlot Obs P) : Prop :=
  let F := fullTypedLinearGrammar Obs G
  let X := linearSlotParent Obs G s
  match actualLinearSlotChild? Obs G s with
  | none => StrictLinearKept F X
  | some Y => StrictLinearKept F X ∧ StrictLinearKept F Y

/-- Realised typed non-start rules, indexed by source production and `(q,m,n)`. -/
abbrev ActualLinearRuleSlot
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :=
  {s : LinearTypedRuleSlot Obs P // ActualLinearSlotRealized Obs G s}

/-- The realised-slot encoding into `P × M^3` is just the subtype projection. -/
def actualLinearRuleEncode
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :
    ActualLinearRuleSlot Obs G → P × Obs.M × Obs.M × Obs.M :=
  fun s => s.1

/-- The concrete rule-slot encoding is injective. -/
theorem actualLinearRuleEncode_injective
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :
    Function.Injective (actualLinearRuleEncode Obs G) := by
  intro s t h
  exact Subtype.ext h

/-- Proposition 7.7(ii) for the actual realised rule-slot family. -/
theorem actualLinearRuleSlot_card_le
    {N : Type v} {Sigma : Type u} {P : Type w}
    [Fintype P]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    [Fintype (ActualLinearRuleSlot Obs G)] :
    Fintype.card (ActualLinearRuleSlot Obs G) ≤
      Fintype.card P * Fintype.card Obs.M ^ 3 := by
  exact linear_typed_rule_card_le
    (actualLinearRuleEncode Obs G)
    (actualLinearRuleEncode_injective Obs G)

/-- Every realised slot has a retained parent typed state. -/
theorem actualLinearSlot_parent_kept
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (s : ActualLinearRuleSlot Obs G) :
    StrictLinearKept (fullTypedLinearGrammar Obs G)
      (linearSlotParent Obs G s.1) := by
  have hs := s.2
  cases hchild : actualLinearSlotChild? Obs G s.1 with
  | none =>
      simpa [ActualLinearSlotRealized, hchild] using hs
  | some Y =>
      have hp :
          StrictLinearKept (fullTypedLinearGrammar Obs G)
              (linearSlotParent Obs G s.1) ∧
            StrictLinearKept (fullTypedLinearGrammar Obs G) Y := by
        simpa [ActualLinearSlotRealized, hchild] using hs
      exact hp.1

/-- If the slot has a child, that child is retained as well. -/
theorem actualLinearSlot_child_kept_of_some
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (s : ActualLinearRuleSlot Obs G) {Y : TypedNT N Obs}
    (hchild : actualLinearSlotChild? Obs G s.1 = some Y) :
    StrictLinearKept (fullTypedLinearGrammar Obs G) Y := by
  have hs := s.2
  have hp :
      StrictLinearKept (fullTypedLinearGrammar Obs G)
          (linearSlotParent Obs G s.1) ∧
        StrictLinearKept (fullTypedLinearGrammar Obs G) Y := by
    simpa [ActualLinearSlotRealized, hchild] using hs
  exact hp.2

/-- Parent state as an element of the actual retained state family `W`. -/
def actualLinearSlotParentState
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (s : ActualLinearRuleSlot Obs G) : ActualLinearState Obs G :=
  ⟨linearSlotParent Obs G s.1, actualLinearSlot_parent_kept Obs G s⟩

/-- Retained child state for a realised left rule slot. -/
def actualLinearLeftSlotChildState
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (s : ActualLinearRuleSlot Obs G)
    (a : Sigma) (B : N)
    (hshape : G.rhs s.1.1 = LinearRHS.left a B) :
    ActualLinearState Obs G := by
  let Y : TypedNT N Obs :=
    ⟨B, s.1.2.1, Obs.mul s.1.2.2.1 (Obs.value [a]), s.1.2.2.2⟩
  refine ⟨Y, ?_⟩
  apply actualLinearSlot_child_kept_of_some Obs G s
  simp [actualLinearSlotChild?, linearSlotChild?, hshape, Y]

/-- Retained child state for a realised right rule slot. -/
def actualLinearRightSlotChildState
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (s : ActualLinearRuleSlot Obs G)
    (B : N) (a : Sigma)
    (hshape : G.rhs s.1.1 = LinearRHS.right B a) :
    ActualLinearState Obs G := by
  let Y : TypedNT N Obs :=
    ⟨B, s.1.2.1, s.1.2.2.1, Obs.mul (Obs.value [a]) s.1.2.2.2⟩
  refine ⟨Y, ?_⟩
  apply actualLinearSlot_child_kept_of_some Obs G s
  simp [actualLinearSlotChild?, linearSlotChild?, hshape, Y]

/-- The exact Section-7 rule-observation word selected by a realised source slot. -/
noncomputable def actualLinearRuleWitness
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (s : ActualLinearRuleSlot Obs G) : Word Sigma :=
  let F := fullTypedLinearGrammar Obs G
  let X := actualLinearSlotParentState Obs G s
  match hshape : G.rhs s.1.1 with
  | LinearRHS.terminal a =>
      trimLinearLeftCtx F X ++ [a] ++ trimLinearRightCtx F X
  | LinearRHS.left a B =>
      let Y := actualLinearLeftSlotChildState Obs G s a B hshape
      trimLinearLeftCtx F X ++ [a] ++ trimLinearOmega F Y ++
        trimLinearRightCtx F X
  | LinearRHS.right B a =>
      let Y := actualLinearRightSlotChildState Obs G s B a hshape
      trimLinearLeftCtx F X ++ trimLinearOmega F Y ++ [a] ++
        trimLinearRightCtx F X

end FixedHCFG
end LeanCfgProject
