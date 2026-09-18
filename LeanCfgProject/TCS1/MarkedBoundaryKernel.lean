import LeanCfgProject.TCS1.YieldTypedRefinementCore
import LeanCfgProject.TCS1.FixedWindowTreeCombinatorics

/-!
# TCS #1 v68: marked-boundary derivation kernel

This module formalizes the tree object used in the long-word branch of
Lemma 7.1.

Starting from an SSBNF derivation, mark selected terminal leaves and retain the
union of their root paths.  A retained binary node has either:

* one retained child and one omitted sibling subtree; or
* two retained children.

`MarkedBoundaryKernel` records exactly that pruned derivation tree.  It keeps
the omitted sibling derivations only to remember their root nonterminals; a
later reconstruction may replace each omitted sibling by any other terminal
yield of the same root.

The key combinatorics are now internal to Lean:

* the marked leaves form a full binary branching skeleton after unary chains
  are contracted;
* `segmentLengths` records the lengths of all maximal unary chains;
* the number of such segments is exactly `2r-1` for `r` marked leaves;
* their sum is exactly the number of omitted sibling subtrees;
* if every segment has length at most `N`, then the number of omitted
  siblings is at most `(2r-1)N`;
* replacing omitted siblings by yields of length at most `tau` gives a
  genuine derivation of length at most
  `r + (2r-1) N tau`.

Thus the remaining Lemma 7.1 obligation is reduced to the cycle-shortening
step establishing the uniform segment bound and to the boundary-position fact
for the first k / last l marked leaves.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section MarkedBoundaryKernel

variable {N : Type u}
variable {α : Type v}

/--
A derivation tree pruned to the union of root-to-marked-leaf paths.

Unary constructors retain exactly one marked child and remember the omitted
sibling derivation.  The branch constructor retains both marked children.
-/
inductive MarkedBoundaryKernel
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop) :
    N → Type (max u v)
  | marked
      {A : N}
      (a : α)
      (hterm : terminalRule A a) :
      MarkedBoundaryKernel terminalRule binaryRule A
  | unaryLeft
      {A B C : N}
      (hbin : binaryRule A B C)
      (child :
        MarkedBoundaryKernel terminalRule binaryRule B)
      (siblingWord : Word α)
      (sibling :
        UntypedDerives terminalRule binaryRule C siblingWord) :
      MarkedBoundaryKernel terminalRule binaryRule A
  | unaryRight
      {A B C : N}
      (hbin : binaryRule A B C)
      (siblingWord : Word α)
      (sibling :
        UntypedDerives terminalRule binaryRule B siblingWord)
      (child :
        MarkedBoundaryKernel terminalRule binaryRule C) :
      MarkedBoundaryKernel terminalRule binaryRule A
  | branch
      {A B C : N}
      (hbin : binaryRule A B C)
      (left :
        MarkedBoundaryKernel terminalRule binaryRule B)
      (right :
        MarkedBoundaryKernel terminalRule binaryRule C) :
      MarkedBoundaryKernel terminalRule binaryRule A

namespace MarkedBoundaryKernel

/-- Original full yield represented by the pruned kernel. -/
def originalYield
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    MarkedBoundaryKernel terminalRule binaryRule A →
    Word α
  | _, marked a _ => [a]
  | _, unaryLeft _ child siblingWord _ =>
      originalYield child ++ siblingWord
  | _, unaryRight _ siblingWord _ child =>
      siblingWord ++ originalYield child
  | _, branch _ left right =>
      originalYield left ++ originalYield right

/-- Terminal labels of the marked leaves, in left-to-right order. -/
def markedWord
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    MarkedBoundaryKernel terminalRule binaryRule A →
    Word α
  | _, marked a _ => [a]
  | _, unaryLeft _ child _ _ =>
      markedWord child
  | _, unaryRight _ _ _ child =>
      markedWord child
  | _, branch _ left right =>
      markedWord left ++ markedWord right

/-- Number of marked terminal leaves. -/
def markedLeafCount
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    MarkedBoundaryKernel terminalRule binaryRule A →
    Nat
  | _, marked _ _ => 1
  | _, unaryLeft _ child _ _ =>
      markedLeafCount child
  | _, unaryRight _ _ _ child =>
      markedLeafCount child
  | _, branch _ left right =>
      markedLeafCount left + markedLeafCount right

/-- Number of omitted sibling subtrees. -/
def omittedCount
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    MarkedBoundaryKernel terminalRule binaryRule A →
    Nat
  | _, marked _ _ => 0
  | _, unaryLeft _ child _ _ =>
      1 + omittedCount child
  | _, unaryRight _ _ _ child =>
      1 + omittedCount child
  | _, branch _ left right =>
      omittedCount left + omittedCount right

/--
Lengths of maximal one-child chains.

The accumulator is the length of the chain entering the current kernel.
At a branch the current segment ends and fresh zero-length segments begin in
both children.  At a marked leaf the current segment ends.
-/
def segmentLengthsAux
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop}
    (entering : Nat) :
    {A : N} →
    MarkedBoundaryKernel terminalRule binaryRule A →
    List Nat
  | _, marked _ _ => [entering]
  | _, unaryLeft _ child _ _ =>
      segmentLengthsAux (entering + 1) child
  | _, unaryRight _ _ _ child =>
      segmentLengthsAux (entering + 1) child
  | _, branch _ left right =>
      entering ::
        (segmentLengthsAux 0 left ++
          segmentLengthsAux 0 right)

/-- Maximal one-child-chain lengths of the whole kernel. -/
def segmentLengths
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop}
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    List Nat :=
  segmentLengthsAux 0 K

/-- The kernel still represents a genuine derivation of its original yield. -/
theorem originalYield_derives
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    UntypedDerives terminalRule binaryRule
      A (originalYield K) := by
  induction K with
  | marked a hterm =>
      exact UntypedDerives.terminal hterm
  | unaryLeft hbin child siblingWord sibling ih =>
      exact UntypedDerives.binary hbin ih sibling
  | unaryRight hbin siblingWord sibling child ih =>
      exact UntypedDerives.binary hbin sibling ih
  | branch hbin left right ihL ihR =>
      exact UntypedDerives.binary hbin ihL ihR

/-- The marked word has exactly one symbol per marked leaf. -/
theorem markedWord_length
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    (markedWord K).length = markedLeafCount K := by
  induction K with
  | marked a hterm =>
      simp [markedWord, markedLeafCount]
  | unaryLeft hbin child siblingWord sibling ih =>
      simpa [markedWord, markedLeafCount] using ih
  | unaryRight hbin siblingWord sibling child ih =>
      simpa [markedWord, markedLeafCount] using ih
  | branch hbin left right ihL ihR =>
      simp [markedWord, markedLeafCount, ihL, ihR]

/-- There is always at least one marked leaf. -/
theorem markedLeafCount_pos
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    0 < markedLeafCount K := by
  induction K with
  | marked =>
      simp [markedLeafCount]
  | unaryLeft hbin child siblingWord sibling ih =>
      simpa [markedLeafCount] using ih
  | unaryRight hbin siblingWord sibling child ih =>
      simpa [markedLeafCount] using ih
  | branch hbin left right ihL ihR =>
      simp only [markedLeafCount]
      omega

/--
The segment list has exactly 2r-1 entries when there are r marked leaves.
This is the full-binary-skeleton identity with unary chains contracted.
-/
theorem segmentLengthsAux_length
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (entering : Nat)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    (segmentLengthsAux entering K).length =
      2 * markedLeafCount K - 1 := by
  induction K generalizing entering with
  | marked =>
      simp [segmentLengthsAux, markedLeafCount]
  | unaryLeft hbin child siblingWord sibling ih =>
      simpa [segmentLengthsAux, markedLeafCount] using
        ih (entering + 1)
  | unaryRight hbin siblingWord sibling child ih =>
      simpa [segmentLengthsAux, markedLeafCount] using
        ih (entering + 1)
  | branch hbin left right ihL ihR =>
      have hpL :=
        markedLeafCount_pos terminalRule binaryRule left
      have hpR :=
        markedLeafCount_pos terminalRule binaryRule right
      simp only [segmentLengthsAux, List.length_cons,
        List.length_append, markedLeafCount]
      rw [ihL 0, ihR 0]
      omega

@[simp] theorem segmentLengths_length
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    (segmentLengths K).length =
      2 * markedLeafCount K - 1 := by
  exact segmentLengthsAux_length
    terminalRule binaryRule 0 K

/--
The sum of segment lengths is exactly the number of omitted sibling subtrees,
up to the entering-chain accumulator.
-/
theorem segmentLengthsAux_sum
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (entering : Nat)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    (segmentLengthsAux entering K).sum =
      entering + omittedCount K := by
  induction K generalizing entering with
  | marked =>
      simp [segmentLengthsAux, omittedCount]
  | unaryLeft hbin child siblingWord sibling ih =>
      rw [segmentLengthsAux]
      rw [ih (entering + 1)]
      simp only [omittedCount]
      omega
  | unaryRight hbin siblingWord sibling child ih =>
      rw [segmentLengthsAux]
      rw [ih (entering + 1)]
      simp only [omittedCount]
      omega
  | branch hbin left right ihL ihR =>
      simp only [segmentLengthsAux, List.sum_cons,
        List.sum_append, omittedCount]
      rw [ihL 0, ihR 0]
      omega

@[simp] theorem segmentLengths_sum
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    (segmentLengths K).sum = omittedCount K := by
  simpa [segmentLengths] using
    segmentLengthsAux_sum
      terminalRule binaryRule 0 K

/--
If every maximal one-child chain has length at most Nbound, the number of
omitted sibling subtrees is at most (2r-1)Nbound.
-/
theorem omittedCount_le_of_segment_bound
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A)
    (Nbound : Nat)
    (hseg :
      ∀ c ∈ segmentLengths K, c ≤ Nbound) :
    omittedCount K ≤
      (2 * markedLeafCount K - 1) * Nbound := by
  have hsum :
      (segmentLengths K).sum ≤
        (2 * markedLeafCount K - 1) * Nbound := by
    apply
      chainExpansion_sum_le
        (segmentLengths K)
        (2 * markedLeafCount K - 1)
        Nbound
    · exact le_of_eq
        (segmentLengths_length
          terminalRule binaryRule K)
    · exact hseg
  simpa using hsum

/--
Rebuild the kernel after choosing one replacement terminal word for every
possible omitted sibling root.
-/
def rebuildWord
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop}
    (shortWord : N → Word α) :
    {A : N} →
    MarkedBoundaryKernel terminalRule binaryRule A →
    Word α
  | _, marked a _ => [a]
  | _, @unaryLeft _ _ _ _ B C _ child _ _ =>
      rebuildWord shortWord child ++ shortWord C
  | _, @unaryRight _ _ _ _ B _ _ _ child =>
      shortWord B ++ rebuildWord shortWord child
  | _, branch _ left right =>
      rebuildWord shortWord left ++ rebuildWord shortWord right

/-- Replacing omitted siblings by any same-root terminal derivations is valid. -/
theorem rebuildWord_derives
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (shortWord : N → Word α)
    (hshort :
      ∀ X : N,
        UntypedDerives terminalRule binaryRule
          X (shortWord X))
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    UntypedDerives terminalRule binaryRule
      A (rebuildWord shortWord K) := by
  induction K with
  | marked a hterm =>
      exact UntypedDerives.terminal hterm
  | @unaryLeft A B C hbin child siblingWord sibling ih =>
      exact UntypedDerives.binary hbin ih (hshort C)
  | @unaryRight A B C hbin siblingWord sibling child ih =>
      exact UntypedDerives.binary hbin (hshort B) ih
  | branch hbin left right ihL ihR =>
      exact UntypedDerives.binary hbin ihL ihR

/--
Length of a rebuilt yield: one terminal per marked leaf plus at most tau for
every omitted sibling subtree.
-/
theorem rebuildWord_length_le
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (shortWord : N → Word α)
    (τ : Nat)
    (hshortLen : ∀ X : N, (shortWord X).length ≤ τ)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    (rebuildWord shortWord K).length ≤
      markedLeafCount K + omittedCount K * τ := by
  induction K with
  | marked a hterm =>
      simp [rebuildWord, markedLeafCount, omittedCount]
  | @unaryLeft A B C hbin child siblingWord sibling ih =>
      have hC := hshortLen C
      simp only [rebuildWord, List.length_append,
        markedLeafCount, omittedCount]
      calc
        (rebuildWord shortWord child).length +
            (shortWord C).length
          ≤
        (markedLeafCount child +
            omittedCount child * τ) + τ :=
          Nat.add_le_add ih hC
        _ =
        markedLeafCount child +
          (1 + omittedCount child) * τ := by
            ring
  | @unaryRight A B C hbin siblingWord sibling child ih =>
      have hB := hshortLen B
      simp only [rebuildWord, List.length_append,
        markedLeafCount, omittedCount]
      calc
        (shortWord B).length +
            (rebuildWord shortWord child).length
          ≤
        τ + (markedLeafCount child +
            omittedCount child * τ) :=
          Nat.add_le_add hB ih
        _ =
        markedLeafCount child +
          (1 + omittedCount child) * τ := by
            ring
  | branch hbin left right ihL ihR =>
      simp only [rebuildWord, List.length_append,
        markedLeafCount, omittedCount]
      calc
        (rebuildWord shortWord left).length +
            (rebuildWord shortWord right).length
          ≤
        (markedLeafCount left + omittedCount left * τ) +
          (markedLeafCount right + omittedCount right * τ) :=
            Nat.add_le_add ihL ihR
        _ =
        markedLeafCount left + markedLeafCount right +
          (omittedCount left + omittedCount right) * τ := by
            ring

/--
Paper-facing long-case length theorem.

Once cycle shortening establishes that every unary segment has length at most
Nbound, replacing each omitted sibling by a tau-short terminal yield gives the
exact Lemma 7.1 numerical envelope.
-/
theorem rebuildWord_fixedWindow_length_le
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (shortWord : N → Word α)
    (τ Nbound r : Nat)
    (hshortLen : ∀ X : N, (shortWord X).length ≤ τ)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A)
    (hr : markedLeafCount K = r)
    (hseg :
      ∀ c ∈ segmentLengths K, c ≤ Nbound) :
    (rebuildWord shortWord K).length ≤
      r + (2 * r - 1) * Nbound * τ := by
  have hbase :=
    rebuildWord_length_le
      terminalRule binaryRule shortWord τ hshortLen K
  have homit :
      omittedCount K ≤
        (2 * markedLeafCount K - 1) * Nbound :=
    omittedCount_le_of_segment_bound
      terminalRule binaryRule K Nbound hseg
  have hmul :
      omittedCount K * τ ≤
        ((2 * markedLeafCount K - 1) * Nbound) * τ :=
    Nat.mul_le_mul_right τ homit
  rw [hr] at hbase hmul
  exact le_trans hbase
    (Nat.add_le_add_left hmul r)

end MarkedBoundaryKernel

end MarkedBoundaryKernel

end TCS1
end LeanCfgProject
