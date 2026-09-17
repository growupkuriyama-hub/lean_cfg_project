import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60AlignedMarkedSupport
import LeanCfgProject.FixedHCFG.V60MarkedWordReplacement
import LeanCfgProject.FixedHCFG.V60SiblingShortening

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Marked-frontier semantics for one-hole derivation contexts.

This layer proves the part of the boundary-preservation argument corresponding
to thickness shortening of off-path siblings.  Every terminal in such a sibling
is unprotected, so the sibling may be replaced by an arbitrary same-root tree.
Protected symbols inside the distinguished hole are carried through literally
by `V60MarkedWordReplacement`.
-/

/--
A zero-mark aligned subtree may be replaced by any same-root derivation tree.
All of its source terminals are unprotected.
-/
theorem v60_zero_mark_subtree_replacement
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    {A : N}
    (marks : List Bool)
    (oldTree newTree : V60DerivationTree terminal binary A)
    (hAlign : marks.length = V60DerivationTree.leafCount oldTree)
    (hZero : v60MarkCount marks = 0) :
    V60MarkedWordReplacement marks
      (V60DerivationTree.yield oldTree)
      (V60DerivationTree.yield newTree) := by
  have hFalse :=
    V60MarkedWordReplacement.eq_replicate_false_of_markCount_zero marks hZero
  have hLen :
      (V60DerivationTree.yield oldTree).length = marks.length := by
    rw [V60DerivationTree.yield_length_eq_leafCount]
    exact hAlign.symm
  have hPos : 0 < marks.length := by
    rw [hAlign]
    exact V60DerivationTree.leafCount_pos oldTree
  rw [hFalse]
  exact V60MarkedWordReplacement.replicate_false_to_any_of_pos
    marks.length hLen hPos

/--
Boolean frontier annotation induced by a one-hole context.  Every off-path
sibling is unprotected; only the hole carries an externally supplied marking.
-/
def V60MarkedContextFrontier
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    {A H : N}
    (ctx : V60DerivationContext terminal binary A H)
    (holeMarks : List Bool) : List Bool :=
  match ctx with
  | .hole _ => holeMarks
  | .left _ _ _ _ _ sub rightTree =>
      V60MarkedContextFrontier sub holeMarks ++
        List.replicate (V60DerivationTree.leafCount rightTree) false
  | .right _ _ _ _ _ leftTree sub =>
      List.replicate (V60DerivationTree.leafCount leftTree) false ++
        V60MarkedContextFrontier sub holeMarks

namespace V60DerivationContext

/--
Replacing every off-path sibling by an arbitrary same-root tree preserves the
marked frontier of the distinguished hole.
-/
theorem shortenSiblings_markedReplacement
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (shorten : ∀ {A : N},
      V60DerivationTree terminal binary A →
        V60DerivationTree terminal binary A)
    {A H : N}
    (ctx : V60DerivationContext terminal binary A H)
    {holeMarks : List Bool}
    {oldCore newCore : V60DerivationTree terminal binary H}
    (hCore : V60MarkedWordReplacement holeMarks
      (V60DerivationTree.yield oldCore)
      (V60DerivationTree.yield newCore)) :
    V60MarkedWordReplacement
      (V60MarkedContextFrontier ctx holeMarks)
      (V60DerivationTree.yield (plug ctx oldCore))
      (V60DerivationTree.yield
        (plug (shortenSiblings shorten ctx) newCore)) := by
  induction ctx with
  | hole A =>
      simpa [V60MarkedContextFrontier, plug, shortenSiblings] using hCore
  | left A B C H hrule sub rightTree ih =>
      have hRight :
          V60MarkedWordReplacement
            (List.replicate (V60DerivationTree.leafCount rightTree) false)
            (V60DerivationTree.yield rightTree)
            (V60DerivationTree.yield (shorten rightTree)) := by
        apply v60_zero_mark_subtree_replacement
          (List.replicate (V60DerivationTree.leafCount rightTree) false)
          rightTree (shorten rightTree)
        · simp
        · simp
      have hApp := V60MarkedWordReplacement.append (ih hCore) hRight
      simpa [V60MarkedContextFrontier, plug, shortenSiblings,
        V60DerivationTree.yield] using hApp
  | right A B C H hrule leftTree sub ih =>
      have hLeft :
          V60MarkedWordReplacement
            (List.replicate (V60DerivationTree.leafCount leftTree) false)
            (V60DerivationTree.yield leftTree)
            (V60DerivationTree.yield (shorten leftTree)) := by
        apply v60_zero_mark_subtree_replacement
          (List.replicate (V60DerivationTree.leafCount leftTree) false)
          leftTree (shorten leftTree)
        · simp
        · simp
      have hApp := V60MarkedWordReplacement.append hLeft (ih hCore)
      simpa [V60MarkedContextFrontier, plug, shortenSiblings,
        V60DerivationTree.yield] using hApp

/--
The manuscript's thickness replacement is therefore marked-frontier safe.
-/
theorem shortenSiblingsByThickness_markedReplacement
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (tau : Nat)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {A H : N}
    (ctx : V60DerivationContext terminal binary A H)
    {holeMarks : List Bool}
    {oldCore newCore : V60DerivationTree terminal binary H}
    (hCore : V60MarkedWordReplacement holeMarks
      (V60DerivationTree.yield oldCore)
      (V60DerivationTree.yield newCore)) :
    V60MarkedWordReplacement
      (V60MarkedContextFrontier ctx holeMarks)
      (V60DerivationTree.yield (plug ctx oldCore))
      (V60DerivationTree.yield
        (plug (shortenSiblingsByThickness tau hThickness ctx) newCore)) := by
  exact shortenSiblings_markedReplacement
    (fun {A} t =>
      v60ThicknessShortTree
        (terminal := terminal) (binary := binary) tau hThickness t)
    ctx hCore

end V60DerivationContext

end FixedHCFG
end LeanCfgProject
