import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60DerivationSpine

namespace LeanCfgProject
namespace FixedHCFG

universe u

/-!
Boolean leaf marks for the fixed-window derivation-tree argument.

For a word/tree with `n` terminal leaves and `k+l ≤ n`, the manuscript marks
exactly the first `k` and last `l` leaves.  `V60BoundaryMarks k l n` is that
marking written as a list aligned with the terminal frontier.  Keeping this
layer independent of grammar labels makes the later recursive pruning proof
considerably cleaner: at a binary node the mark list is simply split at the
left child's leaf count.
-/

/-- Number of marked (`true`) positions in a Boolean frontier annotation. -/
def v60MarkCount : List Bool → Nat
  | [] => 0
  | true :: xs => v60MarkCount xs + 1
  | false :: xs => v60MarkCount xs

@[simp] theorem v60MarkCount_nil : v60MarkCount [] = 0 := rfl

@[simp] theorem v60MarkCount_cons_true (xs : List Bool) :
    v60MarkCount (true :: xs) = v60MarkCount xs + 1 := rfl

@[simp] theorem v60MarkCount_cons_false (xs : List Bool) :
    v60MarkCount (false :: xs) = v60MarkCount xs := rfl

@[simp] theorem v60MarkCount_append (xs ys : List Bool) :
    v60MarkCount (xs ++ ys) = v60MarkCount xs + v60MarkCount ys := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
      cases b <;> simp [v60MarkCount, ih, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

@[simp] theorem v60MarkCount_replicate_true (n : Nat) :
    v60MarkCount (List.replicate n true) = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, v60MarkCount, ih]

@[simp] theorem v60MarkCount_replicate_false (n : Nat) :
    v60MarkCount (List.replicate n false) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, v60MarkCount, ih]

/-- First-`k`/last-`l` marking of a frontier with nominal length `n`. -/
def V60BoundaryMarks (k l n : Nat) : List Bool :=
  List.replicate k true ++
    List.replicate (n - (k + l)) false ++
      List.replicate l true

/-- For a long enough frontier the annotation has exactly the frontier length. -/
theorem v60BoundaryMarks_length
    (k l n : Nat) (hLong : k + l ≤ n) :
    (V60BoundaryMarks k l n).length = n := by
  simp [V60BoundaryMarks]
  omega

/-- Exactly `k+l` terminal positions are marked. -/
theorem v60BoundaryMarks_count (k l n : Nat) :
    v60MarkCount (V60BoundaryMarks k l n) = k + l := by
  simp [V60BoundaryMarks, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- The left window is literally the initial block of marked positions. -/
theorem v60BoundaryMarks_take_left (k l n : Nat) :
    (V60BoundaryMarks k l n).take k = List.replicate k true := by
  simp [V60BoundaryMarks]

/-- The right window is literally the final block of marked positions. -/
theorem v60BoundaryMarks_suffix_right (k l n : Nat) :
    v60WindowSuffix l (V60BoundaryMarks k l n) = List.replicate l true := by
  let a := List.replicate k true ++ List.replicate (n - (k + l)) false
  have h := v60WindowSuffix_append_of_le
    l a (List.replicate l true) (by simp)
  simpa [V60BoundaryMarks, a, v60WindowSuffix] using h

/-- Mark counts split additively at every cut of a frontier annotation. -/
theorem v60MarkCount_take_add_drop
    (marks : List Bool) (i : Nat) :
    v60MarkCount (marks.take i) + v60MarkCount (marks.drop i) =
      v60MarkCount marks := by
  rw [← v60MarkCount_append]
  exact congrArg v60MarkCount (List.take_append_drop i marks)

/--
Splitting boundary marks at an arbitrary tree cut does not lose or duplicate a
marked leaf.
-/
theorem v60BoundaryMarks_split_count
    (k l n i : Nat) :
    v60MarkCount ((V60BoundaryMarks k l n).take i) +
      v60MarkCount ((V60BoundaryMarks k l n).drop i) = k + l := by
  rw [v60MarkCount_take_add_drop]
  exact v60BoundaryMarks_count k l n

/-- Positive window size gives a genuinely marked frontier. -/
theorem v60BoundaryMarks_count_pos
    (k l n : Nat) (hr : k + l ≠ 0) :
    0 < v60MarkCount (V60BoundaryMarks k l n) := by
  rw [v60BoundaryMarks_count]
  omega

/--
Alignment predicate used by the recursive pruning construction: one Boolean
annotation entry per terminal leaf of the concrete SSBNF derivation tree.
-/
def V60MarksAlignTree
    {N : Type*} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    {A : N}
    (t : V60DerivationTree terminal binary A)
    (marks : List Bool) : Prop :=
  marks.length = V60DerivationTree.leafCount t

/-- Boundary marks align with every long enough derivation frontier. -/
theorem v60BoundaryMarks_align_tree
    {N : Type*} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (k l : Nat) {A : N}
    (t : V60DerivationTree terminal binary A)
    (hLong : k + l ≤ V60DerivationTree.leafCount t) :
    V60MarksAlignTree t
      (V60BoundaryMarks k l (V60DerivationTree.leafCount t)) := by
  exact v60BoundaryMarks_length k l _ hLong

end FixedHCFG
end LeanCfgProject
