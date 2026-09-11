import LeanCfgProject.FixedHCFG.LinearTypedRefinement

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
Finite typed-rule slots for Proposition 7.7(ii).

For a source rule `A -> aB` or `A -> Ba`, the correct three free monoid
coordinates are the child yield type `q` and the two parent outer-context
types `m,n`.  The parent yield type is then determined *forward* as
`h(a)q` or `qh(a)`.  No cancellation property of the finite monoid is used.

This is important because the manuscript phrase "q determined by h(a)" when
`p,m,n` are chosen is not valid for an arbitrary finite monoid.  The counting
bound itself survives unchanged after using `(q,m,n)` as the coordinates.
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
      ⟨G.lhs r, Obs.value [a], m, n⟩
  | LinearRHS.left a _ =>
      ⟨G.lhs r, Obs.mul (Obs.value [a]) q, m, n⟩
  | LinearRHS.right _ a =>
      ⟨G.lhs r, Obs.mul q (Obs.value [a]), m, n⟩

/-- Child typed state represented by a nonterminal-bearing source slot. -/
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
      some ⟨B, q, Obs.mul m (Obs.value [a]), n⟩
  | LinearRHS.right B a =>
      some ⟨B, q, m, Obs.mul (Obs.value [a]) n⟩

/--
The full slot family has one source-production coordinate and three monoid
coordinates.  It is an overcount for terminal rules, where `q` is unnecessary,
but that is harmless for the manuscript's upper bound.
-/
theorem linear_full_rule_slot_card
    {Sigma : Type u} {P : Type w} [Fintype P]
    (Obs : Observer Sigma) :
    Fintype.card (LinearTypedRuleSlot Obs P) =
      Fintype.card P * Fintype.card Obs.M ^ 3 :=
  linearTypedRuleSlot_card Obs

/--
Any retained subfamily of typed rule slots has cardinality at most
`|P| |M|^3`.  This is the exact finite-cardinality form of Proposition 7.7(ii):
reachable/productive reduction only selects a subcollection of the full slots.
-/
theorem proposition_7_7_ii_rule_bound
    {Sigma : Type u} {P : Type w} [Fintype P]
    (Obs : Observer Sigma)
    (keep : LinearTypedRuleSlot Obs P → Prop)
    [Fintype {s : LinearTypedRuleSlot Obs P // keep s}] :
    Fintype.card {s : LinearTypedRuleSlot Obs P // keep s} ≤
      Fintype.card P * Fintype.card Obs.M ^ 3 := by
  calc
    Fintype.card {s : LinearTypedRuleSlot Obs P // keep s} ≤
        Fintype.card (LinearTypedRuleSlot Obs P) :=
      Fintype.card_le_of_injective
        (fun s : {s : LinearTypedRuleSlot Obs P // keep s} => s.1)
        Subtype.val_injective
    _ = Fintype.card P * Fintype.card Obs.M ^ 3 :=
      linear_full_rule_slot_card Obs

/-- The left-linear slot has exactly the paper's typed rule equations. -/
theorem linear_left_slot_equations
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (r : P) (q m n : Obs.M) (a : Sigma) (B : N)
    (hshape : G.rhs r = LinearRHS.left a B) :
    let s : LinearTypedRuleSlot Obs P := (r, q, m, n)
    let X := linearSlotParent Obs G s
    let Y := linearSlotChild? Obs G s
    X.label = G.lhs r ∧
      X.yieldType = Obs.mul (Obs.value [a]) q ∧
      X.leftType = m ∧ X.rightType = n ∧
      Y = some ⟨B, q, Obs.mul m (Obs.value [a]), n⟩ := by
  simp [linearSlotParent, linearSlotChild?, hshape]

/-- The right-linear slot has exactly the paper's typed rule equations. -/
theorem linear_right_slot_equations
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (r : P) (q m n : Obs.M) (a : Sigma) (B : N)
    (hshape : G.rhs r = LinearRHS.right B a) :
    let s : LinearTypedRuleSlot Obs P := (r, q, m, n)
    let X := linearSlotParent Obs G s
    let Y := linearSlotChild? Obs G s
    X.label = G.lhs r ∧
      X.yieldType = Obs.mul q (Obs.value [a]) ∧
      X.leftType = m ∧ X.rightType = n ∧
      Y = some ⟨B, q, m, Obs.mul (Obs.value [a]) n⟩ := by
  simp [linearSlotParent, linearSlotChild?, hshape]

end FixedHCFG
end LeanCfgProject
