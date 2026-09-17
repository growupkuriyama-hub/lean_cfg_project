import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60BoundaryDecomposition

namespace LeanCfgProject
namespace FixedHCFG

universe u

/-!
Word-level semantics for the remaining boundary-preservation argument.

A `true` position is protected and must survive literally.  A `false` source
position may contribute an arbitrary replacement chunk, possibly empty.  Thus
an all-false interval may be deleted, shortened, or replaced freely, while a
run of protected positions is copied symbol-for-symbol.
-/

inductive V60MarkedWordReplacement {Sigma : Type u} :
    List Bool → Word Sigma → Word Sigma → Prop where
  | nil : V60MarkedWordReplacement [] [] []
  | keep {a : Sigma} {marks : List Bool} {src dst : Word Sigma}
      (h : V60MarkedWordReplacement marks src dst) :
      V60MarkedWordReplacement (true :: marks) (a :: src) (a :: dst)
  | replace {a : Sigma} {marks : List Bool} {src dst : Word Sigma}
      (chunk : Word Sigma)
      (h : V60MarkedWordReplacement marks src dst) :
      V60MarkedWordReplacement (false :: marks) (a :: src) (chunk ++ dst)

namespace V60MarkedWordReplacement

/-- The source has exactly one symbol for every annotation entry. -/
theorem source_length_eq_marks_length
    {Sigma : Type u} {marks : List Bool} {src dst : Word Sigma}
    (h : V60MarkedWordReplacement marks src dst) :
    src.length = marks.length := by
  induction h with
  | nil => rfl
  | keep h ih => simp [ih]
  | replace chunk h ih => simp [ih]

/-- Every protected source symbol contributes one literal target symbol. -/
theorem markCount_le_target_length
    {Sigma : Type u} {marks : List Bool} {src dst : Word Sigma}
    (h : V60MarkedWordReplacement marks src dst) :
    v60MarkCount marks ≤ dst.length := by
  induction h with
  | nil => simp
  | keep h ih =>
      simp only [v60MarkCount_cons_true, List.length_cons]
      omega
  | replace chunk h ih =>
      simp only [v60MarkCount_cons_false, List.length_append]
      omega

/-- Mark count zero means that every annotation entry is literally `false`. -/
theorem eq_replicate_false_of_markCount_zero
    (marks : List Bool)
    (hZero : v60MarkCount marks = 0) :
    marks = List.replicate marks.length false := by
  induction marks with
  | nil => simp
  | cons b xs ih =>
      cases b with
      | false =>
          simp only [v60MarkCount_cons_false] at hZero
          have hxs := ih hZero
          simp [hxs, List.replicate_succ]
      | true =>
          simp only [v60MarkCount_cons_true] at hZero
          omega

/-- Marked replacements compose horizontally along concatenation. -/
theorem append
    {Sigma : Type u}
    {marksLeft marksRight : List Bool}
    {srcLeft srcRight dstLeft dstRight : Word Sigma}
    (hLeft : V60MarkedWordReplacement marksLeft srcLeft dstLeft)
    (hRight : V60MarkedWordReplacement marksRight srcRight dstRight) :
    V60MarkedWordReplacement
      (marksLeft ++ marksRight)
      (srcLeft ++ srcRight)
      (dstLeft ++ dstRight) := by
  induction hLeft with
  | nil =>
      simpa using hRight
  | keep h ih =>
      simpa [List.append_assoc] using V60MarkedWordReplacement.keep ih
  | replace chunk h ih =>
      simpa [List.append_assoc] using
        V60MarkedWordReplacement.replace chunk ih

/-- Any all-false annotated source can be deleted completely. -/
theorem replicate_false_to_nil
    {Sigma : Type u}
    (n : Nat) {src : Word Sigma}
    (hLen : src.length = n) :
    V60MarkedWordReplacement (List.replicate n false) src [] := by
  induction n generalizing src with
  | zero =>
      have hSrc : src = [] := List.length_eq_zero.mp hLen
      subst src
      exact V60MarkedWordReplacement.nil
  | succ n ih =>
      cases src with
      | nil => simp at hLen
      | cons a xs =>
          have hTail : xs.length = n := by
            simpa using hLen
          have hNil := ih hTail
          have hStep :
              V60MarkedWordReplacement
                (false :: List.replicate n false) (a :: xs) [] := by
            simpa using V60MarkedWordReplacement.replace [] hNil
          simpa [List.replicate_succ] using hStep

/-- A nonempty all-false source interval can be replaced by an arbitrary chunk. -/
theorem replicate_false_to_any_of_pos
    {Sigma : Type u}
    (n : Nat) {src dst : Word Sigma}
    (hLen : src.length = n)
    (hPos : 0 < n) :
    V60MarkedWordReplacement (List.replicate n false) src dst := by
  cases n with
  | zero => omega
  | succ n =>
      cases src with
      | nil => simp at hLen
      | cons a xs =>
          have hTail : xs.length = n := by
            simpa using hLen
          have hNil := replicate_false_to_nil n hTail
          have hStep :
              V60MarkedWordReplacement
                (false :: List.replicate n false) (a :: xs) dst := by
            simpa using V60MarkedWordReplacement.replace dst hNil
          simpa [List.replicate_succ] using hStep

/-- An all-protected word cannot change. -/
theorem eq_of_replicate_true
    {Sigma : Type u} (n : Nat) {src dst : Word Sigma}
    (h : V60MarkedWordReplacement (List.replicate n true) src dst) :
    src = dst := by
  induction n generalizing src dst with
  | zero =>
      simp only [List.replicate_zero] at h
      cases h
      rfl
  | succ n ih =>
      simp only [List.replicate_succ] at h
      cases h with
      | @keep a marks srcTail dstTail hTail =>
          have hEq : srcTail = dstTail := ih hTail
          simpa [hEq]

/-- A protected initial block gives identical first `k` symbols. -/
theorem take_eq_of_true_prefix
    {Sigma : Type u} (k : Nat) (tailMarks : List Bool)
    {src dst : Word Sigma}
    (h : V60MarkedWordReplacement
      (List.replicate k true ++ tailMarks) src dst) :
    src.take k = dst.take k := by
  induction k generalizing src dst with
  | zero => simp
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append] at h
      cases h with
      | @keep a marks srcTail dstTail hTail =>
          simp [ih hTail]

/-- A protected final block gives identical last `l` symbols. -/
theorem suffix_eq_of_true_suffix
    {Sigma : Type u} (l : Nat) (preMarks : List Bool)
    {src dst : Word Sigma}
    (h : V60MarkedWordReplacement
      (preMarks ++ List.replicate l true) src dst) :
    v60WindowSuffix l src = v60WindowSuffix l dst := by
  induction preMarks generalizing src dst with
  | nil =>
      have hEq : src = dst := by
        apply eq_of_replicate_true l
        simpa using h
      simpa [hEq]
  | cons b rest ih =>
      cases b with
      | false =>
          simp only [List.cons_append] at h
          cases h with
          | @replace a marks srcTail dstTail chunk hTail =>
              have hSrcEq :
                  srcTail.length = (rest ++ List.replicate l true).length :=
                source_length_eq_marks_length hTail
              have hSrcLen : l ≤ srcTail.length := by
                rw [hSrcEq]
                simp
              have hDstBound :
                  v60MarkCount (rest ++ List.replicate l true) ≤ dstTail.length :=
                markCount_le_target_length hTail
              have hDstLen : l ≤ dstTail.length := by
                simp only [v60MarkCount_append,
                  v60MarkCount_replicate_true] at hDstBound
                omega
              have hSrcDrop :=
                v60WindowSuffix_append_of_le l [a] srcTail hSrcLen
              have hDstDrop :=
                v60WindowSuffix_append_of_le l chunk dstTail hDstLen
              calc
                v60WindowSuffix l (a :: srcTail) =
                    v60WindowSuffix l srcTail := by
                      simpa using hSrcDrop
                _ = v60WindowSuffix l dstTail := ih hTail
                _ = v60WindowSuffix l (chunk ++ dstTail) := hDstDrop.symm
      | true =>
          simp only [List.cons_append] at h
          cases h with
          | @keep a marks srcTail dstTail hTail =>
              have hSrcEq :
                  srcTail.length = (rest ++ List.replicate l true).length :=
                source_length_eq_marks_length hTail
              have hSrcLen : l ≤ srcTail.length := by
                rw [hSrcEq]
                simp
              have hDstBound :
                  v60MarkCount (rest ++ List.replicate l true) ≤ dstTail.length :=
                markCount_le_target_length hTail
              have hDstLen : l ≤ dstTail.length := by
                simp only [v60MarkCount_append,
                  v60MarkCount_replicate_true] at hDstBound
                omega
              have hSrcDrop :=
                v60WindowSuffix_append_of_le l [a] srcTail hSrcLen
              have hDstDrop :=
                v60WindowSuffix_append_of_le l [a] dstTail hDstLen
              calc
                v60WindowSuffix l (a :: srcTail) =
                    v60WindowSuffix l srcTail := by
                      simpa using hSrcDrop
                _ = v60WindowSuffix l dstTail := ih hTail
                _ = v60WindowSuffix l (a :: dstTail) := by
                      simpa using hDstDrop.symm

/-- Boundary-mark replacement implies the exact fixed-window equality. -/
theorem boundary_eq_of_boundary_marks
    {Sigma : Type u} (k l n : Nat) {src dst : Word Sigma}
    (h : V60MarkedWordReplacement (V60BoundaryMarks k l n) src dst) :
    V60WindowBoundaryEq k l src dst := by
  constructor
  · have hPrefix : V60MarkedWordReplacement
        (List.replicate k true ++
          (List.replicate (n - (k + l)) false ++ List.replicate l true))
        src dst := by
      simpa [V60BoundaryMarks, List.append_assoc] using h
    exact take_eq_of_true_prefix k
      (List.replicate (n - (k + l)) false ++ List.replicate l true)
      hPrefix
  · have hSuffix : V60MarkedWordReplacement
        ((List.replicate k true ++ List.replicate (n - (k + l)) false) ++
          List.replicate l true) src dst := by
      simpa [V60BoundaryMarks, List.append_assoc] using h
    exact suffix_eq_of_true_suffix l
      (List.replicate k true ++ List.replicate (n - (k + l)) false)
      hSuffix

/-- Boundary-mark replacement leaves at least the protected `k+l` symbols. -/
theorem boundary_target_length
    {Sigma : Type u} (k l n : Nat) {src dst : Word Sigma}
    (h : V60MarkedWordReplacement (V60BoundaryMarks k l n) src dst) :
    k + l ≤ dst.length := by
  have hBound := markCount_le_target_length h
  rw [v60BoundaryMarks_count] at hBound
  exact hBound

end V60MarkedWordReplacement

end FixedHCFG
end LeanCfgProject
