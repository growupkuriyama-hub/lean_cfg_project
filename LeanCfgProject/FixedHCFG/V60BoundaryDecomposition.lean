import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60BoundaryMarks

namespace LeanCfgProject
namespace FixedHCFG

universe u

/-!
Exact list decomposition behind the marked-leaf pruning argument.

Once the first `k` and last `l` terminal leaves are protected, all remaining
changes take place in a single middle factor.  The lemmas below package that
observation in the exact `V60WindowBoundaryEq` vocabulary used by the v60
fixed-window proof.
-/

/-- The factor strictly between the first `k` and last `l` positions. -/
def v60WindowMiddle {Sigma : Type u}
    (k l : Nat) (w : Word Sigma) : Word Sigma :=
  let rest := w.drop k
  rest.take (rest.length - l)

/-- A long word splits into its left window, middle factor, and right window. -/
theorem v60_word_eq_left_middle_right
    {Sigma : Type u}
    (k l : Nat) (w : Word Sigma)
    (hLong : k + l ≤ w.length) :
    w = w.take k ++ v60WindowMiddle k l w ++ v60WindowSuffix l w := by
  let rest : Word Sigma := w.drop k
  have hsplit :
      rest.take (rest.length - l) ++ rest.drop (rest.length - l) = rest :=
    List.take_append_drop (rest.length - l) rest
  have hk : k ≤ w.length := by omega
  have hrestlen : rest.length = w.length - k := by
    simp [rest]
  have hdropIndex : k + (rest.length - l) = w.length - l := by
    rw [hrestlen]
    omega
  have hsuffix :
      rest.drop (rest.length - l) = v60WindowSuffix l w := by
    unfold rest v60WindowSuffix
    rw [List.drop_drop, hdropIndex]
  calc
    w = w.take k ++ w.drop k := (List.take_append_drop k w).symm
    _ = w.take k ++ rest := by rfl
    _ = w.take k ++
        (rest.take (rest.length - l) ++ rest.drop (rest.length - l)) := by
          rw [hsplit]
    _ = w.take k ++ v60WindowMiddle k l w ++ v60WindowSuffix l w := by
          simp [v60WindowMiddle, rest, hsuffix, List.append_assoc]

/--
Replacing only the middle factor preserves both fixed windows, provided the
left and right protected pieces already have the requested lengths.
-/
theorem v60_window_boundary_eq_of_same_ends
    {Sigma : Type u}
    (k l : Nat)
    (left oldMiddle newMiddle right : Word Sigma)
    (hLeft : left.length = k)
    (hRight : right.length = l) :
    V60WindowBoundaryEq k l
      (left ++ oldMiddle ++ right)
      (left ++ newMiddle ++ right) := by
  constructor
  · have hk : k ≤ left.length := by omega
    have hold := List.take_append_of_le_length
      (l₁ := left) (l₂ := oldMiddle ++ right) hk
    have hnew := List.take_append_of_le_length
      (l₁ := left) (l₂ := newMiddle ++ right) hk
    simpa [List.append_assoc] using hold.trans hnew.symm
  · have hl : l ≤ right.length := by omega
    have hold := v60WindowSuffix_append_of_le
      l (left ++ oldMiddle) right hl
    have hnew := v60WindowSuffix_append_of_le
      l (left ++ newMiddle) right hl
    simpa [List.append_assoc] using hold.trans hnew.symm

/-- The protected left window has exactly `k` symbols on every long word. -/
theorem v60_take_left_length
    {Sigma : Type u}
    (k l : Nat) (w : Word Sigma)
    (hLong : k + l ≤ w.length) :
    (w.take k).length = k := by
  simp [List.length_take]
  omega

/-- The protected right window has exactly `l` symbols on every long word. -/
theorem v60_suffix_right_length
    {Sigma : Type u}
    (k l : Nat) (w : Word Sigma)
    (hLong : k + l ≤ w.length) :
    (v60WindowSuffix l w).length = l := by
  unfold v60WindowSuffix
  simp [List.length_drop]
  omega

/--
Main replacement form: for a long word, *any* new middle factor preserves the
first `k` and last `l` symbols when the two boundary factors are copied
verbatim.
-/
theorem v60_window_boundary_eq_replace_middle
    {Sigma : Type u}
    (k l : Nat) (w newMiddle : Word Sigma)
    (hLong : k + l ≤ w.length) :
    V60WindowBoundaryEq k l w
      (w.take k ++ newMiddle ++ v60WindowSuffix l w) := by
  rw [v60_word_eq_left_middle_right k l w hLong]
  exact v60_window_boundary_eq_of_same_ends
    k l (w.take k) (v60WindowMiddle k l w) newMiddle
      (v60WindowSuffix l w)
      (v60_take_left_length k l w hLong)
      (v60_suffix_right_length k l w hLong)

/-- Length of a word obtained by replacing only the unprotected middle. -/
theorem v60_replace_middle_length
    {Sigma : Type u}
    (k l : Nat) (w newMiddle : Word Sigma)
    (hLong : k + l ≤ w.length) :
    (w.take k ++ newMiddle ++ v60WindowSuffix l w).length =
      k + newMiddle.length + l := by
  simp [List.length_append,
    v60_take_left_length k l w hLong,
    v60_suffix_right_length k l w hLong]

end FixedHCFG
end LeanCfgProject
