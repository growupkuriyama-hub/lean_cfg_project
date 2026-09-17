import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60MarkedSupport

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Alignment-strengthened marked support for the remaining boundary-preservation
part of manuscript Lemma `window-typed-yield`.

`V60MarkedSupport` was intentionally minimal: zero-mark sibling annotations are
only required to have mark count zero.  That is enough for the skeleton count,
but the boundary-preservation proof also needs those annotations to be aligned
with the terminal leaves of the sibling subtree.  The relation below records
that missing local invariant without changing the already verified quantitative
support layer.
-/

inductive V60AlignedMarkedSupport
    {N : Type v} {Sigma : Type u}
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) :
    {A : N} → V60DerivationTree terminal binary A →
      List Bool → V60MarkedSupportShape → Prop where
  | terminal (A : N) (a : Sigma) (hrule : terminal A a) :
      V60AlignedMarkedSupport terminal binary
        (V60DerivationTree.terminal A a hrule) [true]
        V60MarkedSupportShape.leaf
  | unaryLeft {A B C : N}
      (hrule : binary A B C)
      (left : V60DerivationTree terminal binary B)
      (right : V60DerivationTree terminal binary C)
      {marksLeft marksRight : List Bool}
      {shapeLeft : V60MarkedSupportShape}
      (hLeft : V60AlignedMarkedSupport terminal binary left marksLeft shapeLeft)
      (hRightAlign : marksRight.length = V60DerivationTree.leafCount right)
      (hRightZero : v60MarkCount marksRight = 0) :
      V60AlignedMarkedSupport terminal binary
        (V60DerivationTree.binary A B C hrule left right)
        (marksLeft ++ marksRight)
        (.unary shapeLeft)
  | unaryRight {A B C : N}
      (hrule : binary A B C)
      (left : V60DerivationTree terminal binary B)
      (right : V60DerivationTree terminal binary C)
      {marksLeft marksRight : List Bool}
      {shapeRight : V60MarkedSupportShape}
      (hLeftAlign : marksLeft.length = V60DerivationTree.leafCount left)
      (hLeftZero : v60MarkCount marksLeft = 0)
      (hRight : V60AlignedMarkedSupport terminal binary right marksRight shapeRight) :
      V60AlignedMarkedSupport terminal binary
        (V60DerivationTree.binary A B C hrule left right)
        (marksLeft ++ marksRight)
        (.unary shapeRight)
  | branch {A B C : N}
      (hrule : binary A B C)
      (left : V60DerivationTree terminal binary B)
      (right : V60DerivationTree terminal binary C)
      {marksLeft marksRight : List Bool}
      {shapeLeft shapeRight : V60MarkedSupportShape}
      (hLeft : V60AlignedMarkedSupport terminal binary left marksLeft shapeLeft)
      (hRight : V60AlignedMarkedSupport terminal binary right marksRight shapeRight) :
      V60AlignedMarkedSupport terminal binary
        (V60DerivationTree.binary A B C hrule left right)
        (marksLeft ++ marksRight)
        (.branch shapeLeft shapeRight)

namespace V60AlignedMarkedSupport

variable {N : Type v} {Sigma : Type u}
variable {terminal : V60TerminalRules N Sigma}
variable {binary : V60BinaryRules N}

/-- Forget alignment bookkeeping and recover the already verified support. -/
theorem toMarkedSupport
    {A : N} {t : V60DerivationTree terminal binary A}
    {marks : List Bool} {shape : V60MarkedSupportShape}
    (h : V60AlignedMarkedSupport terminal binary t marks shape) :
    V60MarkedSupport terminal binary t marks shape := by
  induction h with
  | terminal A a hrule =>
      exact V60MarkedSupport.terminal A a hrule
  | unaryLeft hrule left right hLeft hRightAlign hRightZero ih =>
      exact V60MarkedSupport.unaryLeft hrule left right ih hRightZero
  | unaryRight hrule left right hLeftAlign hLeftZero hRight ih =>
      exact V60MarkedSupport.unaryRight hrule left right hLeftZero ih
  | branch hrule left right hLeft hRight ihLeft ihRight =>
      exact V60MarkedSupport.branch hrule left right ihLeft ihRight

/-- Every aligned support annotation has exactly one Boolean per terminal leaf. -/
theorem marks_length_eq_leafCount
    {A : N} {t : V60DerivationTree terminal binary A}
    {marks : List Bool} {shape : V60MarkedSupportShape}
    (h : V60AlignedMarkedSupport terminal binary t marks shape) :
    marks.length = V60DerivationTree.leafCount t := by
  induction h with
  | terminal A a hrule =>
      simp [V60DerivationTree.leafCount]
  | unaryLeft hrule left right hLeft hRightAlign hRightZero ih =>
      simp [V60DerivationTree.leafCount, ih, hRightAlign]
  | unaryRight hrule left right hLeftAlign hLeftZero hRight ih =>
      simp [V60DerivationTree.leafCount, hLeftAlign, ih]
  | branch hrule left right hLeft hRight ihLeft ihRight =>
      simp [V60DerivationTree.leafCount, ihLeft, ihRight]

/-- The old exact marked-leaf count transfers unchanged. -/
theorem markedLeaves_eq_markCount
    {A : N} {t : V60DerivationTree terminal binary A}
    {marks : List Bool} {shape : V60MarkedSupportShape}
    (h : V60AlignedMarkedSupport terminal binary t marks shape) :
    V60MarkedSupportShape.markedLeaves shape = v60MarkCount marks := by
  exact V60MarkedSupport.markedLeaves_eq_markCount (toMarkedSupport h)

/--
Every aligned annotation with at least one mark admits an aligned support.
This is the same construction as `V60MarkedSupport.exists_of_aligned_pos`, but
it retains alignment of the zero-mark sibling at every unary support node.
-/
theorem exists_of_aligned_pos
    {A : N}
    (t : V60DerivationTree terminal binary A)
    (marks : List Bool)
    (hAlign : marks.length = V60DerivationTree.leafCount t)
    (hPos : 0 < v60MarkCount marks) :
    ∃ shape : V60MarkedSupportShape,
      V60AlignedMarkedSupport terminal binary t marks shape := by
  induction t generalizing marks with
  | terminal A a hrule =>
      cases marks with
      | nil =>
          simp [V60DerivationTree.leafCount] at hAlign
      | cons b xs =>
          have hxsLen : xs.length = 0 := by
            simpa [V60DerivationTree.leafCount] using hAlign
          have hxs : xs = [] := by
            cases xs with
            | nil => rfl
            | cons x xs => simp at hxsLen
          subst xs
          cases b with
          | false => simp [v60MarkCount] at hPos
          | true =>
              exact ⟨.leaf, V60AlignedMarkedSupport.terminal A a hrule⟩
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
        exact V60AlignedMarkedSupport.unaryRight
          hrule left right hAlignLeft hLeftZero hRight
      · have hLeftPos : 0 < v60MarkCount marksLeft := Nat.pos_of_ne_zero hLeftZero
        obtain ⟨shapeLeft, hLeft⟩ :=
          ihLeft marksLeft hAlignLeft hLeftPos
        by_cases hRightZero : v60MarkCount marksRight = 0
        · refine ⟨.unary shapeLeft, ?_⟩
          rw [← hSplit]
          exact V60AlignedMarkedSupport.unaryLeft
            hrule left right hLeft hAlignRight hRightZero
        · have hRightPos : 0 < v60MarkCount marksRight :=
            Nat.pos_of_ne_zero hRightZero
          obtain ⟨shapeRight, hRight⟩ :=
            ihRight marksRight hAlignRight hRightPos
          refine ⟨.branch shapeLeft shapeRight, ?_⟩
          rw [← hSplit]
          exact V60AlignedMarkedSupport.branch
            hrule left right hLeft hRight

/-- Boundary marks therefore admit an aligned concrete support. -/
theorem exists_boundary_support
    (k l : Nat) {A : N}
    (t : V60DerivationTree terminal binary A)
    (hLong : k + l ≤ V60DerivationTree.leafCount t)
    (hr : k + l ≠ 0) :
    ∃ shape : V60MarkedSupportShape,
      V60AlignedMarkedSupport terminal binary t
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

/-- The aligned support has the same exact `2(k+l)-1` suppressed block count. -/
theorem boundary_support_block_count
    (k l : Nat) {A : N}
    (t : V60DerivationTree terminal binary A)
    (hLong : k + l ≤ V60DerivationTree.leafCount t)
    (hr : k + l ≠ 0) :
    ∃ shape : V60MarkedSupportShape,
      V60AlignedMarkedSupport terminal binary t
        (V60BoundaryMarks k l (V60DerivationTree.leafCount t)) shape ∧
      V60MarkedSupportShape.suppressedBlockCount shape =
        2 * (k + l) - 1 := by
  obtain ⟨shape, hSupport, hLeaves⟩ :=
    exists_boundary_support k l t hLong hr
  refine ⟨shape, hSupport, ?_⟩
  rw [V60MarkedSupportShape.suppressedBlockCount_eq_two_mul_markedLeaves_sub_one,
    hLeaves]

end V60AlignedMarkedSupport

end FixedHCFG
end LeanCfgProject
