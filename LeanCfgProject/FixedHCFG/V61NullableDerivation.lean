import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V61Baseline

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Nullable binary derivations for the v61 thickness-preserving SSBNF
normalization proof.

Appendix A of working revision v61 performs terminal isolation and binarization
*before* eliminating non-start lambda rules.  The intermediate grammar `B`
therefore differs from the exact SSBNF derivation model used elsewhere in this
formalization in two ways:

* off-path siblings may be nullable and contribute the empty word; and
* ordinary unit rules may still be present until the later unit-closure step.

The second point is important: the manuscript explicitly eliminates unit rules
only after epsilon elimination.  This file therefore models epsilon, terminal,
unit, and binary productions from the start.
-/

/-- Non-start epsilon rules in the intermediate grammar `B`. -/
abbrev V61EpsilonRules (N : Type v) := N → Prop

/-- Unit rules in the intermediate grammar `B`. -/
abbrev V61UnitRules (N : Type v) := N → N → Prop

/-- Concrete derivation tree for the intermediate nullable/unit/binary grammar. -/
inductive V61NullableDerivationTree
    {N : Type v} {Sigma : Type u}
    (epsilon : V61EpsilonRules N)
    (terminal : V60TerminalRules N Sigma)
    (unit : V61UnitRules N)
    (binary : V60BinaryRules N) : N → Type (max u v) where
  | epsilon (A : N) (hrule : epsilon A) :
      V61NullableDerivationTree epsilon terminal unit binary A
  | terminal (A : N) (a : Sigma) (hrule : terminal A a) :
      V61NullableDerivationTree epsilon terminal unit binary A
  | unit (A B : N) (hrule : unit A B)
      (sub : V61NullableDerivationTree epsilon terminal unit binary B) :
      V61NullableDerivationTree epsilon terminal unit binary A
  | binary (A B C : N) (hrule : binary A B C)
      (left : V61NullableDerivationTree epsilon terminal unit binary B)
      (right : V61NullableDerivationTree epsilon terminal unit binary C) :
      V61NullableDerivationTree epsilon terminal unit binary A

namespace V61NullableDerivationTree

variable {N : Type v} {Sigma : Type u}
variable {epsilon : V61EpsilonRules N}
variable {terminal : V60TerminalRules N Sigma}
variable {unit : V61UnitRules N}
variable {binary : V60BinaryRules N}

/-- Terminal frontier; epsilon leaves contribute nothing and unit rules add no terminals. -/
def yield {A : N} :
    V61NullableDerivationTree epsilon terminal unit binary A → Word Sigma
  | .epsilon _ _ => []
  | .terminal _ a _ => [a]
  | .unit _ _ _ sub => yield sub
  | .binary _ _ _ _ left right => yield left ++ yield right

/-- Number of terminal leaves, ignoring epsilon leaves and unit edges. -/
def terminalLeafCount {A : N} :
    V61NullableDerivationTree epsilon terminal unit binary A → Nat
  | .epsilon _ _ => 0
  | .terminal _ _ _ => 1
  | .unit _ _ _ sub => terminalLeafCount sub
  | .binary _ _ _ _ left right =>
      terminalLeafCount left + terminalLeafCount right

/-- Frontier length is exactly terminal-leaf count. -/
theorem yield_length_eq_terminalLeafCount {A : N}
    (t : V61NullableDerivationTree epsilon terminal unit binary A) :
    (yield t).length = terminalLeafCount t := by
  induction t with
  | epsilon A hrule => simp [yield, terminalLeafCount]
  | terminal A a hrule => simp [yield, terminalLeafCount]
  | unit A B hrule sub ih => simpa [yield, terminalLeafCount] using ih
  | binary A B C hrule left right ihLeft ihRight =>
      simp [yield, terminalLeafCount, ihLeft, ihRight]

/-- A nonempty frontier contains at least one terminal leaf. -/
theorem terminalLeafCount_pos_of_yield_ne_nil {A : N}
    (t : V61NullableDerivationTree epsilon terminal unit binary A)
    (h : yield t ≠ []) :
    0 < terminalLeafCount t := by
  have hlen_ne : (yield t).length ≠ 0 := by
    simpa using h
  have hlen : 0 < (yield t).length := Nat.pos_of_ne_zero hlen_ne
  rw [yield_length_eq_terminalLeafCount] at hlen
  exact hlen

end V61NullableDerivationTree

/-- One-hole context for nullable/unit/binary derivation trees. -/
inductive V61NullableDerivationContext
    {N : Type v} {Sigma : Type u}
    (epsilon : V61EpsilonRules N)
    (terminal : V60TerminalRules N Sigma)
    (unit : V61UnitRules N)
    (binary : V60BinaryRules N) : N → N → Type (max u v) where
  | hole (A : N) :
      V61NullableDerivationContext epsilon terminal unit binary A A
  | unit (A B H : N) (hrule : unit A B)
      (ctx : V61NullableDerivationContext epsilon terminal unit binary B H) :
      V61NullableDerivationContext epsilon terminal unit binary A H
  | left (A B C H : N) (hrule : binary A B C)
      (ctx : V61NullableDerivationContext epsilon terminal unit binary B H)
      (rightTree : V61NullableDerivationTree epsilon terminal unit binary C) :
      V61NullableDerivationContext epsilon terminal unit binary A H
  | right (A B C H : N) (hrule : binary A B C)
      (leftTree : V61NullableDerivationTree epsilon terminal unit binary B)
      (ctx : V61NullableDerivationContext epsilon terminal unit binary C H) :
      V61NullableDerivationContext epsilon terminal unit binary A H

namespace V61NullableDerivationContext

variable {N : Type v} {Sigma : Type u}
variable {epsilon : V61EpsilonRules N}
variable {terminal : V60TerminalRules N Sigma}
variable {unit : V61UnitRules N}
variable {binary : V60BinaryRules N}

/-- Plug a derivation tree into the unique hole. -/
def plug {A H : N}
    (ctx : V61NullableDerivationContext epsilon terminal unit binary A H)
    (t : V61NullableDerivationTree epsilon terminal unit binary H) :
    V61NullableDerivationTree epsilon terminal unit binary A :=
  match ctx with
  | .hole _ => t
  | .unit A B H hrule sub =>
      .unit A B hrule (plug sub t)
  | .left A B C H hrule sub rightTree =>
      .binary A B C hrule (plug sub t) rightTree
  | .right A B C H hrule leftTree sub =>
      .binary A B C hrule leftTree (plug sub t)

/-- Terminal material strictly to the left of the hole. -/
def leftWord {A H : N} :
    V61NullableDerivationContext epsilon terminal unit binary A H → Word Sigma
  | .hole _ => []
  | .unit _ _ _ _ sub => leftWord sub
  | .left _ _ _ _ _ sub _ => leftWord sub
  | .right _ _ _ _ _ leftTree sub =>
      V61NullableDerivationTree.yield leftTree ++ leftWord sub

/-- Terminal material strictly to the right of the hole. -/
def rightWord {A H : N} :
    V61NullableDerivationContext epsilon terminal unit binary A H → Word Sigma
  | .hole _ => []
  | .unit _ _ _ _ sub => rightWord sub
  | .left _ _ _ _ _ sub rightTree =>
      rightWord sub ++ V61NullableDerivationTree.yield rightTree
  | .right _ _ _ _ _ _ sub => rightWord sub

/-- Plugging decomposes the frontier into left material, hole yield, and right material. -/
theorem yield_plug {A H : N}
    (ctx : V61NullableDerivationContext epsilon terminal unit binary A H)
    (t : V61NullableDerivationTree epsilon terminal unit binary H) :
    V61NullableDerivationTree.yield (plug ctx t) =
      leftWord ctx ++ V61NullableDerivationTree.yield t ++ rightWord ctx := by
  induction ctx with
  | hole A => simp [plug, leftWord, rightWord]
  | unit A B H hrule sub ih =>
      simpa [plug, V61NullableDerivationTree.yield, leftWord, rightWord] using ih
  | left A B C H hrule sub rightTree ih =>
      simp [plug, V61NullableDerivationTree.yield, leftWord, rightWord,
        ih, List.append_assoc]
  | right A B C H hrule leftTree sub ih =>
      simp [plug, V61NullableDerivationTree.yield, leftWord, rightWord,
        ih, List.append_assoc]

/-- Number of grammar edges on the distinguished root-to-hole path. -/
def depth {A H : N} :
    V61NullableDerivationContext epsilon terminal unit binary A H → Nat
  | .hole _ => 0
  | .unit _ _ _ _ sub => depth sub + 1
  | .left _ _ _ _ _ sub _ => depth sub + 1
  | .right _ _ _ _ _ _ sub => depth sub + 1

/--
Any derivation with a nonempty terminal frontier can be decomposed around one
actual terminal leaf.  Unit edges are retained in the one-hole context, which
matches the intermediate grammar `B` used in Appendix A.
-/
theorem exists_terminal_hole_of_yield_ne_nil
    {A : N}
    (t : V61NullableDerivationTree epsilon terminal unit binary A)
    (hNonempty : V61NullableDerivationTree.yield t ≠ []) :
    ∃ (B : N) (a : Sigma) (hrule : terminal B a)
      (ctx : V61NullableDerivationContext epsilon terminal unit binary A B),
      plug ctx (.terminal B a hrule) = t := by
  induction t with
  | epsilon A hrule =>
      exact (hNonempty rfl).elim
  | terminal A a hrule =>
      exact ⟨A, a, hrule, .hole A, rfl⟩
  | unit A B hrule sub ih =>
      obtain ⟨D, a, hterm, ctx, hctx⟩ := ih hNonempty
      refine ⟨D, a, hterm, .unit A B D hrule ctx, ?_⟩
      simp [plug, hctx]
  | binary A B C hrule left right ihLeft ihRight =>
      by_cases hLeft : V61NullableDerivationTree.yield left = []
      · have hRight : V61NullableDerivationTree.yield right ≠ [] := by
          intro hRightNil
          apply hNonempty
          simp [V61NullableDerivationTree.yield, hLeft, hRightNil]
        obtain ⟨D, a, hterm, ctx, hctx⟩ := ihRight hRight
        refine ⟨D, a, hterm,
          .right A B C D hrule left ctx, ?_⟩
        simp [plug, hctx]
      · obtain ⟨D, a, hterm, ctx, hctx⟩ := ihLeft hLeft
        refine ⟨D, a, hterm,
          .left A B C D hrule ctx right, ?_⟩
        simp [plug, hctx]

end V61NullableDerivationContext

end FixedHCFG
end LeanCfgProject
