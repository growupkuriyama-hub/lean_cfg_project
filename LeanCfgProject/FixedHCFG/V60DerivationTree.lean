import LeanCfgProject.FixedHCFG.V60WindowYieldBridge

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Concrete derivation-tree infrastructure for the remaining marked-leaf proof in
Lemma `window-typed-yield`.

Unlike `V60UntypedDerives`, which lives in `Prop`, this indexed tree lives in
`Type`, so subtrees can be replaced explicitly.  The accompanying one-hole
contexts are the exact device needed for the manuscript's repeated-label
shortcut on a unary marked spine.
-/

/-- A concrete SSBNF derivation tree, indexed by its root nonterminal. -/
inductive V60DerivationTree
    {N : Type v} {Sigma : Type u}
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) : N → Type (max u v) where
  | terminal (A : N) (a : Sigma)
      (hrule : terminal A a) :
      V60DerivationTree terminal binary A
  | binary (A B C : N)
      (hrule : binary A B C)
      (left : V60DerivationTree terminal binary B)
      (right : V60DerivationTree terminal binary C) :
      V60DerivationTree terminal binary A

namespace V60DerivationTree

variable {N : Type v} {Sigma : Type u}
variable {terminal : V60TerminalRules N Sigma}
variable {binary : V60BinaryRules N}

/-- Terminal frontier of a concrete SSBNF derivation tree. -/
def yield {A : N} : V60DerivationTree terminal binary A → Word Sigma
  | .terminal _ a _ => [a]
  | .binary _ _ _ _ left right => yield left ++ yield right

/-- Number of terminal leaves.  In SSBNF this equals the terminal-yield length. -/
def leafCount {A : N} : V60DerivationTree terminal binary A → Nat
  | .terminal _ _ _ => 1
  | .binary _ _ _ _ left right => leafCount left + leafCount right

/-- Frontier length and leaf count agree literally. -/
theorem yield_length_eq_leafCount {A : N}
    (t : V60DerivationTree terminal binary A) :
    (yield t).length = leafCount t := by
  induction t with
  | terminal A a hrule => simp [yield, leafCount]
  | binary A B C hrule left right ihLeft ihRight =>
      simp [yield, leafCount, ihLeft, ihRight]

/-- Every concrete non-start derivation tree has at least one leaf. -/
theorem leafCount_pos {A : N}
    (t : V60DerivationTree terminal binary A) :
    0 < leafCount t := by
  induction t with
  | terminal A a hrule => simp [leafCount]
  | binary A B C hrule left right ihLeft ihRight =>
      simp only [leafCount]
      omega

/-- Forgetting the concrete tree recovers the Prop-valued SSBNF derivation. -/
theorem toUntypedDerives {A : N}
    (t : V60DerivationTree terminal binary A) :
    V60UntypedDerives terminal binary A (yield t) := by
  induction t with
  | terminal A a hrule =>
      exact V60UntypedDerives.terminal hrule
  | binary A B C hrule left right ihLeft ihRight =>
      exact V60UntypedDerives.binary hrule ihLeft ihRight

/-- Every Prop-valued SSBNF derivation has a concrete derivation-tree witness. -/
theorem exists_tree_of_untyped_derives
    {A : N} {w : Word Sigma}
    (d : V60UntypedDerives terminal binary A w) :
    ∃ t : V60DerivationTree terminal binary A, yield t = w := by
  induction d with
  | @terminal A a hrule =>
      exact ⟨V60DerivationTree.terminal A a hrule, rfl⟩
  | @binary A B C x y hrule left right ihLeft ihRight =>
      obtain ⟨tl, htl⟩ := ihLeft
      obtain ⟨tr, htr⟩ := ihRight
      refine ⟨V60DerivationTree.binary A B C hrule tl tr, ?_⟩
      simp [yield, htl, htr]

end V60DerivationTree

/--
A one-hole SSBNF derivation-tree context.  `V60DerivationContext A B` is a
valid derivation from root label `A` down to a distinguished subtree whose root
label is `B`.

The labels are explicit constructor arguments on purpose: later cycle-deletion
proofs need to compare the labels occurring on a marked unary chain directly.
-/
inductive V60DerivationContext
    {N : Type v} {Sigma : Type u}
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) : N → N → Type (max u v) where
  | hole (A : N) : V60DerivationContext terminal binary A A
  | left (A B C H : N)
      (hrule : binary A B C)
      (ctx : V60DerivationContext terminal binary B H)
      (rightTree : V60DerivationTree terminal binary C) :
      V60DerivationContext terminal binary A H
  | right (A B C H : N)
      (hrule : binary A B C)
      (leftTree : V60DerivationTree terminal binary B)
      (ctx : V60DerivationContext terminal binary C H) :
      V60DerivationContext terminal binary A H

namespace V60DerivationContext

variable {N : Type v} {Sigma : Type u}
variable {terminal : V60TerminalRules N Sigma}
variable {binary : V60BinaryRules N}

/-- Plug a derivation tree into the unique hole. -/
def plug {A H : N}
    (ctx : V60DerivationContext terminal binary A H)
    (t : V60DerivationTree terminal binary H) :
    V60DerivationTree terminal binary A :=
  match ctx with
  | .hole _ => t
  | .left A B C H hrule sub rightTree =>
      V60DerivationTree.binary A B C hrule (plug sub t) rightTree
  | .right A B C H hrule leftTree sub =>
      V60DerivationTree.binary A B C hrule leftTree (plug sub t)

/-- Terminal material strictly to the left of the hole. -/
def leftWord {A H : N} :
    V60DerivationContext terminal binary A H → Word Sigma
  | .hole _ => []
  | .left _ _ _ _ _ sub _ => leftWord sub
  | .right _ _ _ _ _ leftTree sub =>
      V60DerivationTree.yield leftTree ++ leftWord sub

/-- Terminal material strictly to the right of the hole. -/
def rightWord {A H : N} :
    V60DerivationContext terminal binary A H → Word Sigma
  | .hole _ => []
  | .left _ _ _ _ _ sub rightTree =>
      rightWord sub ++ V60DerivationTree.yield rightTree
  | .right _ _ _ _ _ _ sub => rightWord sub

/-- Plugging decomposes the frontier as left context, hole frontier, right context. -/
theorem yield_plug {A H : N}
    (ctx : V60DerivationContext terminal binary A H)
    (t : V60DerivationTree terminal binary H) :
    V60DerivationTree.yield (plug ctx t) =
      leftWord ctx ++ V60DerivationTree.yield t ++ rightWord ctx := by
  induction ctx with
  | hole A => rfl
  | left A B C H hrule sub rightTree ih =>
      simp [plug, V60DerivationTree.yield, leftWord, rightWord, ih,
        List.append_assoc]
  | right A B C H hrule leftTree sub ih =>
      simp [plug, V60DerivationTree.yield, leftWord, rightWord, ih,
        List.append_assoc]

/-- Number of binary edges on the root-to-hole path. -/
def depth {A H : N} :
    V60DerivationContext terminal binary A H → Nat
  | .hole _ => 0
  | .left _ _ _ _ _ sub _ => depth sub + 1
  | .right _ _ _ _ _ _ sub => depth sub + 1

end V60DerivationContext

end FixedHCFG
end LeanCfgProject
