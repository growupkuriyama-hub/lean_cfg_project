import LeanCfgProject.TCS1.MarkedBoundarySelection

/-!
# TCS #1 v68: first-k / last-l boundary marking

This module instantiates the generic marked-leaf pruning construction with the
actual marking used in Lemma 7.1: mark the first k terminal leaves and the last
l terminal leaves of a successful derivation.

A Boolean mask of length n is

  true^k ++ false^(n-k-l) ++ true^l

when k+l <= n.  Applying the mask to the left-to-right terminal leaves and
then pruning gives a MarkedBoundaryKernel with:

* exactly k+l marked leaves;
* marked word equal to the length-k prefix followed by the length-l suffix;
* original full yield unchanged.

This closes the boundary-selection part of the long-word tree surgery.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section FixedWindowBoundaryMarking

variable {N : Type u}
variable {α : Type v}

/-- Select letters whose aligned Boolean mask entry is true. -/
def selectByMask : List Bool → Word α → Word α
  | true :: bs, a :: w =>
      a :: selectByMask bs w
  | false :: bs, _ :: w =>
      selectByMask bs w
  | _, _ => []

/--
Aligned concatenations may be selected independently on the two sides.
-/
theorem selectByMask_append_aligned
    (m₁ m₂ : List Bool)
    (u v : Word α)
    (hlen : m₁.length = u.length) :
    selectByMask (m₁ ++ m₂) (u ++ v) =
      selectByMask m₁ u ++ selectByMask m₂ v := by
  induction u generalizing m₁ with
  | nil =>
      have hm : m₁ = [] :=
        List.length_eq_zero.mp (by simpa using hlen)
      subst m₁
      simp [selectByMask]
  | cons a u ih =>
      cases m₁ with
      | nil =>
          simp at hlen
      | cons b bs =>
          have htail : bs.length = u.length := by
            simpa using Nat.succ.inj hlen
          cases b <;>
            simp [selectByMask, ih bs htail]

@[simp] theorem selectByMask_replicate_true
    (w : Word α) :
    selectByMask (List.replicate w.length true) w = w := by
  induction w with
  | nil =>
      simp [selectByMask]
  | cons a w ih =>
      simp [selectByMask, ih]

@[simp] theorem selectByMask_replicate_false
    (w : Word α) :
    selectByMask (List.replicate w.length false) w = [] := by
  induction w with
  | nil =>
      simp [selectByMask]
  | cons a w ih =>
      simp [selectByMask, ih]

/--
Mark the leaves of an explicit derivation tree by a Boolean list.  Extra mask
bits are ignored and a missing bit defaults to false; the main theorem below
uses an exactly aligned mask.
-/
def markWithMask
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    BinaryDerivationTree terminalRule binaryRule A →
    List Bool →
    LeafMarkedTree terminalRule binaryRule A
  | _, BinaryDerivationTree.terminal a hterm, mask =>
      LeafMarkedTree.terminal a hterm (mask.headD false)
  | _, BinaryDerivationTree.binary hbin left right, mask =>
      LeafMarkedTree.binary hbin
        (markWithMask left
          (mask.take (BinaryDerivationTree.leafCount left)))
        (markWithMask right
          (mask.drop (BinaryDerivationTree.leafCount left)))

/-- Marking does not change the underlying terminal yield. -/
theorem markWithMask_yield
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (T : BinaryDerivationTree terminalRule binaryRule A)
    (mask : List Bool) :
    LeafMarkedTree.yield (markWithMask T mask) =
      BinaryDerivationTree.yield T := by
  induction T generalizing mask with
  | terminal a hterm =>
      simp [markWithMask, LeafMarkedTree.yield,
        BinaryDerivationTree.yield]
  | binary hbin left right ihL ihR =>
      simp [markWithMask, LeafMarkedTree.yield,
        BinaryDerivationTree.yield, ihL, ihR]

/--
For an exactly aligned mask, the marked terminal word is exactly the
mask-selected terminal yield.
-/
theorem markWithMask_markedWord
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (T : BinaryDerivationTree terminalRule binaryRule A)
    (mask : List Bool)
    (hlen :
      mask.length =
        BinaryDerivationTree.leafCount T) :
    LeafMarkedTree.markedWord (markWithMask T mask) =
      selectByMask mask (BinaryDerivationTree.yield T) := by
  induction T generalizing mask with
  | terminal a hterm =>
      cases mask with
      | nil =>
          simp [BinaryDerivationTree.leafCount] at hlen
      | cons b bs =>
          have hbs : bs = [] := by
            apply List.length_eq_zero.mp
            simpa [BinaryDerivationTree.leafCount] using
              Nat.succ.inj hlen
          subst bs
          cases b <;>
            simp [markWithMask, LeafMarkedTree.markedWord,
              selectByMask]
  | binary hbin left right ihL ihR =>
      have hleft :
          (mask.take
              (BinaryDerivationTree.leafCount left)).length =
            BinaryDerivationTree.leafCount left := by
        have hle :
            BinaryDerivationTree.leafCount left ≤ mask.length := by
          simp only [BinaryDerivationTree.leafCount] at hlen
          omega
        simp [List.length_take, hle]
      have hright :
          (mask.drop
              (BinaryDerivationTree.leafCount left)).length =
            BinaryDerivationTree.leafCount right := by
        simp only [BinaryDerivationTree.leafCount] at hlen
        simp [List.length_drop, hlen]
      simp only [markWithMask, LeafMarkedTree.markedWord]
      rw [ihL _ hleft, ihR _ hright]
      have hyieldLeft :
          (BinaryDerivationTree.yield left).length =
            BinaryDerivationTree.leafCount left :=
        BinaryDerivationTree.yield_length
          terminalRule binaryRule left
      rw [BinaryDerivationTree.yield]
      symm
      apply selectByMask_append_aligned
      rw [List.length_take]
      rw [hyieldLeft]
      have hle :
          BinaryDerivationTree.leafCount left ≤ mask.length := by
        simp only [BinaryDerivationTree.leafCount] at hlen
        omega
      simp [hle]

/-- Boolean mask marking the first k and last l leaves among n leaves. -/
def boundaryMask (k l n : Nat) : List Bool :=
  List.replicate k true ++
    List.replicate (n - k - l) false ++
    List.replicate l true

/-- The boundary mask has the expected total length when k+l <= n. -/
theorem boundaryMask_length
    {k l n : Nat}
    (hfit : k + l ≤ n) :
    (boundaryMask k l n).length = n := by
  simp [boundaryMask]
  omega

/--
Selecting by the boundary mask gives exactly the length-k prefix followed by
the length-l suffix.
-/
theorem selectByMask_boundaryMask
    (w : Word α)
    (k l : Nat)
    (hfit : k + l ≤ w.length) :
    selectByMask
        (boundaryMask k l w.length) w
      =
    w.take k ++ w.drop (w.length - l) := by
  let n := w.length
  let m := n - k - l
  let u := w.take k
  let rest := w.drop k
  let mid := rest.take m
  let q := rest.drop m

  have hk : k ≤ n := by
    dsimp [n]
    omega
  have hu : u.length = k := by
    dsimp [u]
    simp [List.length_take, hk]

  have hrestLen : rest.length = n - k := by
    dsimp [rest, n]
    simp [List.length_drop]

  have hmle : m ≤ rest.length := by
    dsimp [m]
    rw [hrestLen]
    omega
  have hmid : mid.length = m := by
    dsimp [mid]
    simp [List.length_take, hmle]

  have hqLen : q.length = l := by
    dsimp [q]
    rw [List.length_drop, hrestLen]
    dsimp [m]
    omega

  have hw :
      w = u ++ mid ++ q := by
    have h₁ : w = u ++ rest := by
      dsimp [u, rest]
      exact (List.take_append_drop k w).symm
    have h₂ : rest = mid ++ q := by
      dsimp [mid, q]
      exact (List.take_append_drop m rest).symm
    rw [h₁, h₂, List.append_assoc]

  have hmask :
      boundaryMask k l n =
        List.replicate k true ++
          (List.replicate m false ++
            List.replicate l true) := by
    dsimp [boundaryMask, m]
    simp [List.append_assoc]

  rw [show w = u ++ (mid ++ q) by
        rw [hw, List.append_assoc]]
  rw [show boundaryMask k l w.length =
      List.replicate k true ++
        (List.replicate m false ++
          List.replicate l true) by
        simpa [n] using hmask]
  rw [selectByMask_append_aligned
      (List.replicate k true)
      (List.replicate m false ++
        List.replicate l true)
      u (mid ++ q) (by simp [hu])]
  rw [selectByMask_replicate_true]
  rw [selectByMask_append_aligned
      (List.replicate m false)
      (List.replicate l true)
      mid q (by simp [hmid])]
  rw [selectByMask_replicate_false,
      selectByMask_replicate_true]
  simp only [List.nil_append]

  have hdrop :
      q = w.drop (w.length - l) := by
    dsimp [q, rest, m, n]
    rw [List.drop_drop]
    congr 1
    omega
  rw [hdrop]

/--
The selected boundary word has exactly k+l letters.
-/
theorem boundary_selected_length
    (w : Word α)
    (k l : Nat)
    (hfit : k + l ≤ w.length) :
    (w.take k ++ w.drop (w.length - l)).length =
      k + l := by
  have hk : k ≤ w.length := by omega
  simp only [List.length_append]
  rw [List.length_take, Nat.min_eq_left hk]
  rw [List.length_drop]
  omega

/--
Tree-surgery input for Lemma 7.1.

From any successful derivation whose yield has at least k+l terminals, with
k+l>0, we obtain the pruned union of root paths to exactly the first k and
last l terminal leaves.
-/
theorem exists_fixedWindow_boundary_kernel
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {w : Word α}
    (d : UntypedDerives terminalRule binaryRule A w)
    (k l : Nat)
    (hr : 0 < k + l)
    (hfit : k + l ≤ w.length) :
    ∃ K : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.originalYield K = w
      ∧
      MarkedBoundaryKernel.markedWord K =
        w.take k ++ w.drop (w.length - l)
      ∧
      MarkedBoundaryKernel.markedLeafCount K = k + l := by
  obtain ⟨T, hT⟩ :=
    BinaryDerivationTree.exists_of_derivation
      terminalRule binaryRule d
  let mask := boundaryMask k l w.length
  let MT := markWithMask T mask

  have hleaf :
      BinaryDerivationTree.leafCount T = w.length := by
    rw [← BinaryDerivationTree.yield_length
      terminalRule binaryRule T, hT]

  have hmaskLen :
      mask.length =
        BinaryDerivationTree.leafCount T := by
    dsimp [mask]
    rw [boundaryMask_length hfit, hleaf]

  have hmarkedWord :
      LeafMarkedTree.markedWord MT =
        w.take k ++ w.drop (w.length - l) := by
    dsimp [MT]
    rw [markWithMask_markedWord
      terminalRule binaryRule T mask hmaskLen]
    rw [hT]
    exact selectByMask_boundaryMask w k l hfit

  have hmarkedCount :
      LeafMarkedTree.markedCount MT = k + l := by
    have hlen :=
      LeafMarkedTree.markedWord_length
        terminalRule binaryRule MT
    rw [hmarkedWord,
      boundary_selected_length w k l hfit] at hlen
    exact hlen.symm

  have hpos :
      0 < LeafMarkedTree.markedCount MT := by
    rw [hmarkedCount]
    exact hr

  obtain ⟨K, hYield, hWord, hCount⟩ :=
    LeafMarkedTree.exists_pruned_kernel
      terminalRule binaryRule MT hpos

  refine ⟨K, ?_, ?_, ?_⟩
  · rw [hYield]
    dsimp [MT]
    rw [markWithMask_yield
      terminalRule binaryRule T mask, hT]
  · rw [hWord, hmarkedWord]
  · rw [hCount, hmarkedCount]

end FixedWindowBoundaryMarking

end TCS1
end LeanCfgProject
