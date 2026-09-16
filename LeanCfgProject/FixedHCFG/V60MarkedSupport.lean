import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60BoundaryDecomposition

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Concrete support of the first-`k`/last-`l` leaf marking.

Before shortening repeated nonterminal labels, the union of root-to-marked-leaf
paths is a tree with three kinds of vertices: a marked terminal leaf, a unary
vertex where only one child contains a mark, or a genuine branch where both
children contain marks.  Suppressing the unary vertices leaves a full binary
shape.  This file constructs that support directly from an SSBNF derivation
tree and a Boolean frontier annotation, and proves the exact `2r-1` block
count for `r` marked leaves.
-/

/-- Shape of the root-to-marked-leaf support before unary chains are suppressed. -/
inductive V60MarkedSupportShape : Type where
  | leaf : V60MarkedSupportShape
  | unary (child : V60MarkedSupportShape) : V60MarkedSupportShape
  | branch (left right : V60MarkedSupportShape) : V60MarkedSupportShape

namespace V60MarkedSupportShape

/-- Number of marked terminal leaves represented by a support shape. -/
def markedLeaves : V60MarkedSupportShape → Nat
  | .leaf => 1
  | .unary child => markedLeaves child
  | .branch left right => markedLeaves left + markedLeaves right

/-- Number of vertices after maximal unary chains are suppressed. -/
def suppressedBlockCount : V60MarkedSupportShape → Nat
  | .leaf => 1
  | .unary child => suppressedBlockCount child
  | .branch left right =>
      1 + suppressedBlockCount left + suppressedBlockCount right

/-- Every nonempty marked support contains at least one marked terminal. -/
theorem markedLeaves_pos (s : V60MarkedSupportShape) :
    0 < markedLeaves s := by
  induction s with
  | leaf => simp [markedLeaves]
  | unary child ih => simpa [markedLeaves] using ih
  | branch left right ihLeft ihRight =>
      simp only [markedLeaves]
      omega

/-- Suppressing unary paths leaves exactly `2r-1` binary-skeleton blocks. -/
theorem suppressedBlockCount_eq_two_mul_markedLeaves_sub_one
    (s : V60MarkedSupportShape) :
    suppressedBlockCount s = 2 * markedLeaves s - 1 := by
  induction s with
  | leaf => simp [suppressedBlockCount, markedLeaves]
  | unary child ih =>
      simpa [suppressedBlockCount, markedLeaves] using ih
  | branch left right ihLeft ihRight =>
      simp only [suppressedBlockCount, markedLeaves]
      rw [ihLeft, ihRight]
      have hl := markedLeaves_pos left
      have hr := markedLeaves_pos right
      omega

end V60MarkedSupportShape

/--
A proof that `shape` is exactly the support of the `true` leaves in `marks`.
The annotation is split at every binary node according to the left subtree's
leaf count.  Zero-mark children disappear; positive-mark children remain.
-/
inductive V60MarkedSupport
    {N : Type v} {Sigma : Type u}
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) :
    {A : N} → V60DerivationTree terminal binary A →
      List Bool → V60MarkedSupportShape → Prop where
  | terminal (A : N) (a : Sigma) (hrule : terminal A a) :
      V60MarkedSupport terminal binary
        (V60DerivationTree.terminal A a hrule) [true]
        V60MarkedSupportShape.leaf
  | unaryLeft {A B C : N}
      (hrule : binary A B C)
      (left : V60DerivationTree terminal binary B)
      (right : V60DerivationTree terminal binary C)
      {marksLeft marksRight : List Bool}
      {shapeLeft : V60MarkedSupportShape}
      (hLeft : V60MarkedSupport terminal binary left marksLeft shapeLeft)
      (hRightZero : v60MarkCount marksRight = 0) :
      V60MarkedSupport terminal binary
        (V60DerivationTree.binary A B C hrule left right)
        (marksLeft ++ marksRight)
        (.unary shapeLeft)
  | unaryRight {A B C : N}
      (hrule : binary A B C)
      (left : V60DerivationTree terminal binary B)
      (right : V60DerivationTree terminal binary C)
      {marksLeft marksRight : List Bool}
      {shapeRight : V60MarkedSupportShape}
      (hLeftZero : v60MarkCount marksLeft = 0)
      (hRight : V60MarkedSupport terminal binary right marksRight shapeRight) :
      V60MarkedSupport terminal binary
        (V60DerivationTree.binary A B C hrule left right)
        (marksLeft ++ marksRight)
        (.unary shapeRight)
  | branch {A B C : N}
      (hrule : binary A B C)
      (left : V60DerivationTree terminal binary B)
      (right : V60DerivationTree terminal binary C)
      {marksLeft marksRight : List Bool}
      {shapeLeft shapeRight : V60MarkedSupportShape}
      (hLeft : V60MarkedSupport terminal binary left marksLeft shapeLeft)
      (hRight : V60MarkedSupport terminal binary right marksRight shapeRight) :
      V60MarkedSupport terminal binary
        (V60DerivationTree.binary A B C hrule left right)
        (marksLeft ++ marksRight)
        (.branch shapeLeft shapeRight)

namespace V60MarkedSupport

variable {N : Type v} {Sigma : Type u}
variable {terminal : V60TerminalRules N Sigma}
variable {binary : V60BinaryRules N}

/-- The support shape counts exactly the true entries of its frontier annotation. -/
theorem markedLeaves_eq_markCount
    {A : N} {t : V60DerivationTree terminal binary A}
    {marks : List Bool} {shape : V60MarkedSupportShape}
    (h : V60MarkedSupport terminal binary t marks shape) :
    V60MarkedSupportShape.markedLeaves shape = v60MarkCount marks := by
  induction h with
  | terminal A a hrule => simp [V60MarkedSupportShape.markedLeaves]
  | unaryLeft hrule left right hLeft hRightZero ih =>
      simp [V60MarkedSupportShape.markedLeaves, ih, hRightZero]
  | unaryRight hrule left right hLeftZero hRight ih =>
      simp [V60MarkedSupportShape.markedLeaves, ih, hLeftZero]
  | branch hrule left right hLeft hRight ihLeft ihRight =>
      simp [V60MarkedSupportShape.markedLeaves, ihLeft, ihRight]

/--
Every aligned annotation containing at least one mark has a concrete marked
support.  This is the recursive root-to-marked-leaf union from the manuscript.
-/
theorem exists_of_aligned_pos
    {A : N}
    (t : V60DerivationTree terminal binary A)
    (marks : List Bool)
    (hAlign : marks.length = V60DerivationTree.leafCount t)
    (hPos : 0 < v60MarkCount marks) :
    ∃ shape : V60MarkedSupportShape,
      V60MarkedSupport terminal binary t marks shape := by
  induction t generalizing marks with
  | terminal A a hrule =>
      cases marks with
      | nil =>
          simp [V60DerivationTree.leafCount] at hAlign
      | cons b xs =>
          have hxsLen : xs.length = 0 := by
            simpa [V60DerivationTree.leafCount] using hAlign
          have hxs : xs = [] := List.length_eq_zero.mp hxsLen
          subst xs
          cases b with
          | false => simp [v60MarkCount] at hPos
          | true =>
              exact ⟨.leaf, V60MarkedSupport.terminal A a hrule⟩
  | binary A B C hrule left right ihLeft ihRight =>
      let nLeft := V60DerivationTree.leafCount left
      let marksLeft := marks.take nLeft
      let marksRight := marks.drop nLeft
      have hLeftLe : nLeft ≤ marks.length := by
        rw [hAlign]
        simp only [V60DerivationTree.leafCount]
        omega
      have hAlignLeft :
          marksLeft.length = V60DerivationTree.leafCount left := by
        simp [marksLeft, nLeft, List.length_take, Nat.min_eq_left hLeftLe]
      have hAlignRight :
          marksRight.length = V60DerivationTree.leafCount right := by
        simp [marksRight, nLeft, List.length_drop, hAlign,
          V60DerivationTree.leafCount]
      have hSplit : marksLeft ++ marksRight = marks := by
        simpa [marksLeft, marksRight, nLeft] using
          (List.take_append_drop nLeft marks)
      have hCount :
          v60MarkCount marksLeft + v60MarkCount marksRight =
            v60MarkCount marks := by
        simpa [marksLeft, marksRight, nLeft] using
          (v60MarkCount_take_add_drop marks nLeft)
      by_cases hLeftZero : v60MarkCount marksLeft = 0
      · have hRightPos : 0 < v60MarkCount marksRight := by omega
        obtain ⟨shapeRight, hRight⟩ :=
          ihRight marksRight hAlignRight hRightPos
        refine ⟨.unary shapeRight, ?_⟩
        rw [← hSplit]
        exact V60MarkedSupport.unaryRight
          hrule left right hLeftZero hRight
      · have hLeftPos : 0 < v60MarkCount marksLeft := Nat.pos_of_ne_zero hLeftZero
        obtain ⟨shapeLeft, hLeft⟩ :=
          ihLeft marksLeft hAlignLeft hLeftPos
        by_cases hRightZero : v60MarkCount marksRight = 0
        · refine ⟨.unary shapeLeft, ?_⟩
          rw [← hSplit]
          exact V60MarkedSupport.unaryLeft
            hrule left right hLeft hRightZero
        · have hRightPos : 0 < v60MarkCount marksRight :=
            Nat.pos_of_ne_zero hRightZero
          obtain ⟨shapeRight, hRight⟩ :=
            ihRight marksRight hAlignRight hRightPos
          refine ⟨.branch shapeLeft shapeRight, ?_⟩
          rw [← hSplit]
          exact V60MarkedSupport.branch
            hrule left right hLeft hRight

/--
For the actual first-`k`/last-`l` annotation, the concrete support has exactly
`k+l` marked leaves.
-/
theorem exists_boundary_support
    (k l : Nat) {A : N}
    (t : V60DerivationTree terminal binary A)
    (hLong : k + l ≤ V60DerivationTree.leafCount t)
    (hr : k + l ≠ 0) :
    ∃ shape : V60MarkedSupportShape,
      V60MarkedSupport terminal binary t
        (V60BoundaryMarks k l (V60DerivationTree.leafCount t)) shape ∧
      V60MarkedSupportShape.markedLeaves shape = k + l := by
  let marks := V60BoundaryMarks k l (V60DerivationTree.leafCount t)
  have hAlign : marks.length = V60DerivationTree.leafCount t := by
    exact v60BoundaryMarks_length k l _ hLong
  have hPos : 0 < v60MarkCount marks := by
    exact v60BoundaryMarks_count_pos k l _ hr
  obtain ⟨shape, hSupport⟩ := exists_of_aligned_pos t marks hAlign hPos
  refine ⟨shape, hSupport, ?_⟩
  rw [markedLeaves_eq_markCount hSupport]
  exact v60BoundaryMarks_count k l _

/--
Thus the support of exactly the protected boundary leaves has precisely
`2(k+l)-1` suppressed chain blocks, before any per-chain label shortening.
-/
theorem boundary_support_block_count
    (k l : Nat) {A : N}
    (t : V60DerivationTree terminal binary A)
    (hLong : k + l ≤ V60DerivationTree.leafCount t)
    (hr : k + l ≠ 0) :
    ∃ shape : V60MarkedSupportShape,
      V60MarkedSupport terminal binary t
        (V60BoundaryMarks k l (V60DerivationTree.leafCount t)) shape ∧
      V60MarkedSupportShape.suppressedBlockCount shape =
        2 * (k + l) - 1 := by
  obtain ⟨shape, hSupport, hLeaves⟩ :=
    exists_boundary_support k l t hLong hr
  refine ⟨shape, hSupport, ?_⟩
  rw [V60MarkedSupportShape.suppressedBlockCount_eq_two_mul_markedLeaves_sub_one,
    hLeaves]

end V60MarkedSupport

end FixedHCFG
end LeanCfgProject
