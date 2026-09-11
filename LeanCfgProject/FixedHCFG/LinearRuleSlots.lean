import LeanCfgProject.FixedHCFG.LinearTypedRefinement

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
Finite realised-rule envelope for Proposition 7.7(ii).

The correct three monoid coordinates for a unary linear production are the
child yield type `q` and the two outer context types `m,n`.  The parent yield
coordinate is then determined by multiplication with the fixed terminal value.
This avoids any cancellation assumption on the finite monoid.
-/

/-- Parent typed state represented by a source-production slot `(r,q,m,n)`. -/
def linearSlotParent
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (s : LinearTypedRuleSlot Obs P) : TypedNT N Obs :=
  let r := s.1
  let q := s.2.1
  let m := s.2.2.1
  let n := s.2.2.2
  match G.rhs r with
  | LinearRHS.terminal a =>
      { label := G.lhs r, yieldType := Obs.value [a], leftType := m, rightType := n }
  | LinearRHS.left a _ =>
      { label := G.lhs r,
        yieldType := Obs.mul (Obs.value [a]) q,
        leftType := m, rightType := n }
  | LinearRHS.right _ a =>
      { label := G.lhs r,
        yieldType := Obs.mul q (Obs.value [a]),
        leftType := m, rightType := n }

/-- Child typed state represented by a nonterminal-bearing rule slot. -/
def linearSlotChild?
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (s : LinearTypedRuleSlot Obs P) : Option (TypedNT N Obs) :=
  let r := s.1
  let q := s.2.1
  let m := s.2.2.1
  let n := s.2.2.2
  match G.rhs r with
  | LinearRHS.terminal _ => none
  | LinearRHS.left a B =>
      some { label := B, yieldType := q,
        leftType := Obs.mul m (Obs.value [a]), rightType := n }
  | LinearRHS.right B a =>
      some { label := B, yieldType := q,
        leftType := m, rightType := Obs.mul (Obs.value [a]) n }

/--
A slot is retained when its parent is retained and, for a unary rule, its child
is retained.  Terminal slots use the canonical dummy coordinate `q = 1`, so a
terminal production contributes only `|M|^2` slots inside the common
`|M|^3` envelope.
-/
def LinearRuleSlotActive
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (s : LinearTypedRuleSlot Obs P) : Prop :=
  LinearTypedKept Obs G (linearSlotParent Obs G s) ∧
    match G.rhs s.1, linearSlotChild? Obs G s with
    | LinearRHS.terminal _, none => s.2.1 = Obs.one
    | LinearRHS.left _ _, some Y => LinearTypedKept Obs G Y
    | LinearRHS.right _ _, some Y => LinearTypedKept Obs G Y
    | _, _ => False

/-- Realised non-start typed rule slots of the reduced linear refinement. -/
abbrev LinearRealizedRule
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :=
  {s : LinearTypedRuleSlot Obs P // LinearRuleSlotActive Obs G s}

/-- Proposition 7.7(ii), as an exact finite-cardinality envelope. -/
theorem proposition_7_7_ii_rule_bound
    {N : Type v} {Sigma : Type u} {P : Type w}
    [Fintype P]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    [Fintype (LinearRealizedRule Obs G)] :
    Fintype.card (LinearRealizedRule Obs G) ≤
      Fintype.card P * Fintype.card Obs.M ^ 3 := by
  calc
    Fintype.card (LinearRealizedRule Obs G) ≤
        Fintype.card (LinearTypedRuleSlot Obs P) :=
      Fintype.card_le_of_injective
        (fun r : LinearRealizedRule Obs G => r.1)
        Subtype.val_injective
    _ = Fintype.card P * Fintype.card Obs.M ^ 3 :=
      linearTypedRuleSlot_card Obs

/-- Every active terminal slot is an actual terminal rule of the full typed refinement. -/
theorem active_terminal_slot_rule
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    {s : LinearTypedRuleSlot Obs P} {a : Sigma}
    (hshape : G.rhs s.1 = LinearRHS.terminal a)
    (hactive : LinearRuleSlotActive Obs G s) :
    (fullTypedLinearGrammar Obs G).terminalRule
      (linearSlotParent Obs G s) a := by
  rcases s with ⟨r, q, m, n⟩
  simp only [LinearRuleSlotActive] at hactive
  simp [linearSlotParent, fullTypedLinearGrammar, hshape]
  exact ⟨r, rfl, hshape⟩

/-- Every active left-linear slot is an actual typed rule. -/
theorem active_left_slot_rule
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    {s : LinearTypedRuleSlot Obs P} {a : Sigma} {B : N}
    (hshape : G.rhs s.1 = LinearRHS.left a B)
    (hactive : LinearRuleSlotActive Obs G s) :
    ∃ Y : TypedNT N Obs,
      linearSlotChild? Obs G s = some Y ∧
      (fullTypedLinearGrammar Obs G).leftRule
        (linearSlotParent Obs G s) a Y := by
  rcases s with ⟨r, q, m, n⟩
  let Y : TypedNT N Obs :=
    { label := B, yieldType := q,
      leftType := Obs.mul m (Obs.value [a]), rightType := n }
  refine ⟨Y, ?_, ?_⟩
  · simp [linearSlotChild?, hshape, Y]
  · simp [linearSlotParent, fullTypedLinearGrammar, hshape, Y]
    exact ⟨r, rfl, hshape⟩

/-- Every active right-linear slot is an actual typed rule. -/
theorem active_right_slot_rule
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    {s : LinearTypedRuleSlot Obs P} {a : Sigma} {B : N}
    (hshape : G.rhs s.1 = LinearRHS.right B a)
    (hactive : LinearRuleSlotActive Obs G s) :
    ∃ Y : TypedNT N Obs,
      linearSlotChild? Obs G s = some Y ∧
      (fullTypedLinearGrammar Obs G).rightRule
        (linearSlotParent Obs G s) Y a := by
  rcases s with ⟨r, q, m, n⟩
  let Y : TypedNT N Obs :=
    { label := B, yieldType := q,
      leftType := m, rightType := Obs.mul (Obs.value [a]) n }
  refine ⟨Y, ?_, ?_⟩
  · simp [linearSlotChild?, hshape, Y]
  · simp [linearSlotParent, fullTypedLinearGrammar, hshape, Y]
    exact ⟨r, rfl, hshape⟩

end FixedHCFG
end LeanCfgProject
