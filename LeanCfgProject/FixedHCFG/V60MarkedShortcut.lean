import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60MarkedContext

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Marked-word semantics for deleting a repeated-label derivation-context segment.

This file captures the manuscript sentence that replacing an upper occurrence
of a repeated nonterminal by the lower subtree removes only sibling material
with no protected leaf.  The result is stated directly as a marked-word
replacement, so first-`k`/last-`l` preservation follows later from the boundary
mark semantics.
-/

/-- Every aligned annotation acts as the identity replacement on its word. -/
theorem v60_marked_replacement_refl_of_aligned
    {Sigma : Type u}
    (marks : List Bool) (w : Word Sigma)
    (hAlign : marks.length = w.length) :
    V60MarkedWordReplacement marks w w := by
  induction marks generalizing w with
  | nil =>
      cases w with
      | nil => exact V60MarkedWordReplacement.nil
      | cons a w => simp at hAlign
  | cons b marks ih =>
      cases w with
      | nil => simp at hAlign
      | cons a w =>
          have hTail : marks.length = w.length := by
            simpa using hAlign
          have hIH := ih w hTail
          cases b with
          | false =>
              have hStep := V60MarkedWordReplacement.replace [a] hIH
              simpa using hStep
          | true =>
              exact V60MarkedWordReplacement.keep hIH

/-- Mark annotations of composed one-hole contexts compose literally. -/
theorem v60MarkedContextFrontier_comp
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    {A B C : N}
    (outer : V60DerivationContext terminal binary A B)
    (inner : V60DerivationContext terminal binary B C)
    (holeMarks : List Bool) :
    V60MarkedContextFrontier
      (V60DerivationContext.comp outer inner) holeMarks =
    V60MarkedContextFrontier outer
      (V60MarkedContextFrontier inner holeMarks) := by
  induction outer with
  | hole A => rfl
  | left A B D H hrule sub rightTree ih =>
      simp [V60DerivationContext.comp, V60MarkedContextFrontier, ih]
  | right A B D H hrule leftTree sub ih =>
      simp [V60DerivationContext.comp, V60MarkedContextFrontier, ih]

namespace V60DerivationContext

/-- A marked replacement inside the hole lifts through an unchanged context. -/
theorem plug_markedReplacement
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
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
      (V60DerivationTree.yield (plug ctx newCore)) := by
  induction ctx with
  | hole A =>
      simpa [V60MarkedContextFrontier, plug] using hCore
  | left A B C H hrule sub rightTree ih =>
      have hRight :
          V60MarkedWordReplacement
            (List.replicate (V60DerivationTree.leafCount rightTree) false)
            (V60DerivationTree.yield rightTree)
            (V60DerivationTree.yield rightTree) := by
        apply v60_zero_mark_subtree_replacement
          (List.replicate (V60DerivationTree.leafCount rightTree) false)
          rightTree rightTree
        · simp
        · simp
      have hApp := V60MarkedWordReplacement.append (ih hCore) hRight
      simpa [V60MarkedContextFrontier, plug, V60DerivationTree.yield] using hApp
  | right A B C H hrule leftTree sub ih =>
      have hLeft :
          V60MarkedWordReplacement
            (List.replicate (V60DerivationTree.leafCount leftTree) false)
            (V60DerivationTree.yield leftTree)
            (V60DerivationTree.yield leftTree) := by
        apply v60_zero_mark_subtree_replacement
          (List.replicate (V60DerivationTree.leafCount leftTree) false)
          leftTree leftTree
        · simp
        · simp
      have hApp := V60MarkedWordReplacement.append hLeft (ih hCore)
      simpa [V60MarkedContextFrontier, plug, V60DerivationTree.yield] using hApp

/--
Deleting a whole one-hole context removes only its off-path sibling material.
The hole's protected symbols remain unchanged and in the same order.
-/
theorem delete_markedReplacement
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    {A H : N}
    (ctx : V60DerivationContext terminal binary A H)
    (holeMarks : List Bool)
    (core : V60DerivationTree terminal binary H)
    (hAlign : holeMarks.length = V60DerivationTree.leafCount core) :
    V60MarkedWordReplacement
      (V60MarkedContextFrontier ctx holeMarks)
      (V60DerivationTree.yield (plug ctx core))
      (V60DerivationTree.yield core) := by
  induction ctx with
  | hole A =>
      apply v60_marked_replacement_refl_of_aligned
      rw [V60DerivationTree.yield_length_eq_leafCount]
      exact hAlign
  | left A B C H hrule sub rightTree ih =>
      have hSub := ih hAlign
      have hRightLen :
          (V60DerivationTree.yield rightTree).length =
            V60DerivationTree.leafCount rightTree :=
        V60DerivationTree.yield_length_eq_leafCount rightTree
      have hRight :=
        V60MarkedWordReplacement.replicate_false_to_nil
          (V60DerivationTree.leafCount rightTree) hRightLen
      have hApp := V60MarkedWordReplacement.append hSub hRight
      simpa [V60MarkedContextFrontier, plug, V60DerivationTree.yield] using hApp
  | right A B C H hrule leftTree sub ih =>
      have hSub := ih hAlign
      have hLeftLen :
          (V60DerivationTree.yield leftTree).length =
            V60DerivationTree.leafCount leftTree :=
        V60DerivationTree.yield_length_eq_leafCount leftTree
      have hLeft :=
        V60MarkedWordReplacement.replicate_false_to_nil
          (V60DerivationTree.leafCount leftTree) hLeftLen
      have hApp := V60MarkedWordReplacement.append hLeft hSub
      simpa [V60MarkedContextFrontier, plug, V60DerivationTree.yield] using hApp

/--
Deleting a repeated-label cycle is a marked-word replacement from the original
root yield to the shortcut yield.  This is the formal local step used by the
manuscript's repeated-label pruning procedure.
-/
theorem repeated_label_shortcut_markedReplacement
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    {R X : N}
    (outer : V60DerivationContext terminal binary R X)
    (cycle : V60DerivationContext terminal binary X X)
    (core : V60DerivationTree terminal binary X)
    (holeMarks : List Bool)
    (hAlign : holeMarks.length = V60DerivationTree.leafCount core) :
    V60MarkedWordReplacement
      (V60MarkedContextFrontier
        (V60DerivationContext.comp outer cycle) holeMarks)
      (V60DerivationTree.yield
        (V60DerivationContext.plug
          (V60DerivationContext.comp outer cycle) core))
      (V60DerivationTree.yield
        (V60DerivationContext.shortcut outer core)) := by
  have hCycle := delete_markedReplacement cycle holeMarks core hAlign
  have hLift := plug_markedReplacement outer hCycle
  rw [v60MarkedContextFrontier_comp]
  simpa [V60DerivationContext.shortcut,
    V60DerivationContext.plug_comp] using hLift

end V60DerivationContext

end FixedHCFG
end LeanCfgProject
