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

inductive V60DerivationTree
    {N : Type v} {Sigma : Type u}
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) : N → Type (max u v) where
  | terminal {A : N} (a : Sigma)
      (hrule : terminal A a) :
      V60DerivationTree terminal binary A
  | binary {A B C : N}
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
  | .terminal a _ => [a]
  | .binary _ left right => yield left ++ yield right

/-- Number of terminal leaves.  In SSBNF this equals the terminal-yield length. -/
def leafCount {A : N} : V60DerivationTree terminal binary A → Nat
  | .terminal _ _ => 1
  | .binary _ left right => leafCount left + leafCount right

@[simp] theorem yield_terminal_length
    {A : N} {a : Sigma} (hrule : terminal A a) :
    (yield (V60DerivationTree.terminal a hrule)).length = 1 := by
  simp [yield]

/-- Frontier length and leaf count agree literally. -/
theorem yield_length_eq_leafCount {A : N}
    (t : V60DerivationTree terminal binary A) :
    (yield t).length = leafCount t := by
  induction t with
  | terminal a hrule => simp [yield, leafCount]
  | binary hrule left right ihLeft ihRight =>
      simp [yield, leafCount, ihLeft, ihRight]

/-- Every concrete non-start derivation tree has at least one leaf. -/
theorem leafCount_pos {A : N}
    (t : V60DerivationTree terminal binary A) :
    0 < leafCount t := by
  induction t with
  | terminal a hrule => simp [leafCount]
  | binary hrule left right ihLeft ihRight =>
      simp only [leafCount]
      omega

/-- Forgetting the concrete tree recovers the Prop-valued SSBNF derivation. -/
theorem toUntypedDerives {A : N}
    (t : V60DerivationTree terminal binary A) :
    V60UntypedDerives terminal binary A (yield t) := by
  induction t with
  | terminal a hrule =>
      exact V60UntypedDerives.terminal hrule
  | binary hrule left right ihLeft ihRight =>
      exact V60UntypedDerives.binary hrule ihLeft ihRight

/-- Every Prop-valued SSBNF derivation has a concrete derivation-tree witness. -/
theorem exists_tree_of_untyped_derives
    {A : N} {w : Word Sigma}
    (d : V60UntypedDerives terminal binary A w) :
    ∃ t : V60DerivationTree terminal binary A, yield t = w := by
  induction d with
  | terminal hrule =>
      exact ⟨V60DerivationTree.terminal _ hrule, rfl⟩
  | @binary A B C x y hrule left right ihLeft ihRight =>
      obtain ⟨tl, htl⟩ := ihLeft
      obtain ⟨tr, htr⟩ := ihRight
      refine ⟨V60DerivationTree.binary hrule tl tr, ?_⟩
      simp [yield, htl, htr]

end V60DerivationTree

/--
A one-hole SSBNF derivation-tree context.  `V60DerivationContext A B` is a
valid derivation from root label `A` down to a distinguished subtree whose root
label is `B`.
-/
inductive V60DerivationContext
    {N : Type v} {Sigma : Type u}
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) : N → N → Type (max u v) where
  | hole {A : N} : V60DerivationContext terminal binary A A
  | left {A B C H : N}
      (hrule : binary A B C)
      (ctx : V60DerivationContext terminal binary B H)
      (right : V60DerivationTree terminal binary C) :
      V60DerivationContext terminal binary A H
  | right {A B C H : N}
      (hrule : binary A B C)
      (left : V60DerivationTree terminal binary B)
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
  | .hole => t
  | .left hrule sub right =>
      V60DerivationTree.binary hrule (plug sub t) right
  | .right hrule left sub =>
      V60DerivationTree.binary hrule left (plug sub t)

/-- Terminal material strictly to the left of the hole. -/
def leftWord {A H : N} :
    V60DerivationContext terminal binary A H → Word Sigma
  | .hole => []
  | .left _ sub _ => leftWord sub
  | .right _ left sub => V60DerivationTree.yield left ++ leftWord sub

/-- Terminal material strictly to the right of the hole. -/
def rightWord {A H : N} :
    V60DerivationContext terminal binary A H → Word Sigma
  | .hole => []
  | .left _ sub right => rightWord sub ++ V60DerivationTree.yield right
  | .right _ _ sub => rightWord sub

/-- Plugging decomposes the frontier as left context, hole frontier, right context. -/
theorem yield_plug {A H : N}
    (ctx : V60DerivationContext terminal binary A H)
    (t : V60DerivationTree terminal binary H) :
    V60DerivationTree.yield (plug ctx t) =
      leftWord ctx ++ V60DerivationTree.yield t ++ rightWord ctx := by
  induction ctx with
  | hole => simp [plug, leftWord, rightWord]
  | left hrule sub right ih =>
      simp [plug, V60DerivationTree.yield, leftWord, rightWord, ih,
        List.append_assoc]
  | right hrule left sub ih =>
      simp [plug, V60DerivationTree.yield, leftWord, rightWord, ih,
        List.append_assoc]

/-- Number of binary edges on the root-to-hole path. -/
def depth {A H : N} :
    V60DerivationContext terminal binary A H → Nat
  | .hole => 0
  | .left _ sub _ => depth sub + 1
  | .right _ _ sub => depth sub + 1

end V60DerivationContext

end FixedHCFG
end LeanCfgProject
