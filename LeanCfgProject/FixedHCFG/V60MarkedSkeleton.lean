import LeanCfgProject.FixedHCFG.V60DerivationTree

namespace LeanCfgProject
namespace FixedHCFG

universe v

/-!
Pure combinatorics of the manuscript's marked-leaf skeleton.

After maximal one-child chains are suppressed conceptually, the union of paths
from the root to the marked leaves is a full binary skeleton.  Every skeleton
vertex carries one maximal one-child chain of base nonterminal labels.  Once
repeated labels on such a chain have been shortcut, the chain is simple.

This file isolates the exact counting statement used in Lemma
`window-typed-yield`: a skeleton with `r` marked leaves and `N` available base
nonterminal labels retains at most `(2*r-1)*N` nonterminal vertices.
-/

/-- A maximal one-child chain after repeated base labels have been shortcut. -/
structure V60SimpleChain (N : Type v) where
  labels : List N
  nodup : labels.Nodup
  nonempty : labels ≠ []

/-- Binary skeleton obtained after suppressing interiors of one-child chains. -/
inductive V60MarkedSkeleton (N : Type v) : Type v where
  | leaf (chain : V60SimpleChain N) : V60MarkedSkeleton N
  | branch (chain : V60SimpleChain N)
      (left right : V60MarkedSkeleton N) : V60MarkedSkeleton N

namespace V60MarkedSkeleton

variable {N : Type v}

/-- Number of marked terminal leaves represented by the skeleton. -/
def markedLeaves : V60MarkedSkeleton N → Nat
  | .leaf _ => 1
  | .branch _ left right => markedLeaves left + markedLeaves right

/-- Number of chain blocks, i.e. vertices of the suppressed binary skeleton. -/
def blockCount : V60MarkedSkeleton N → Nat
  | .leaf _ => 1
  | .branch _ left right => 1 + blockCount left + blockCount right

/-- Number of original nonterminal vertices retained on all simple chains. -/
def nodeCount : V60MarkedSkeleton N → Nat
  | .leaf chain => chain.labels.length
  | .branch chain left right =>
      chain.labels.length + nodeCount left + nodeCount right

/-- Every marked skeleton contains at least one marked leaf. -/
theorem markedLeaves_pos (s : V60MarkedSkeleton N) :
    0 < markedLeaves s := by
  induction s with
  | leaf chain => simp [markedLeaves]
  | branch chain left right ihLeft ihRight =>
      simp only [markedLeaves]
      omega

/-- A full binary skeleton with `r` leaves has exactly `2*r-1` chain blocks. -/
theorem blockCount_eq_two_mul_markedLeaves_sub_one
    (s : V60MarkedSkeleton N) :
    blockCount s = 2 * markedLeaves s - 1 := by
  induction s with
  | leaf chain => simp [blockCount, markedLeaves]
  | branch chain left right ihLeft ihRight =>
      simp only [blockCount, markedLeaves]
      rw [ihLeft, ihRight]
      have hLeft := markedLeaves_pos left
      have hRight := markedLeaves_pos right
      omega

/-- Every simple chain uses at most all available base nonterminal labels. -/
theorem chain_length_le_card [Fintype N] (chain : V60SimpleChain N) :
    chain.labels.length ≤ Fintype.card N := by
  exact chain.nodup.length_le_card

/-- Retained nonterminal nodes are bounded by chain blocks times `N`. -/
theorem nodeCount_le_blockCount_mul_card
    [Fintype N] (s : V60MarkedSkeleton N) :
    nodeCount s ≤ blockCount s * Fintype.card N := by
  induction s with
  | leaf chain =>
      simpa [nodeCount, blockCount] using chain_length_le_card chain
  | branch chain left right ihLeft ihRight =>
      have hChain := chain_length_le_card chain
      simp only [nodeCount, blockCount]
      calc
        chain.labels.length + nodeCount left + nodeCount right
            ≤ Fintype.card N +
                blockCount left * Fintype.card N +
                blockCount right * Fintype.card N := by
              exact Nat.add_le_add (Nat.add_le_add hChain ihLeft) ihRight
        _ = (1 + blockCount left + blockCount right) * Fintype.card N := by
              simp [Nat.add_mul, Nat.add_assoc]

/-- Exact manuscript count `(2r-1)N` after repeated-label shortcutting. -/
theorem nodeCount_le_manuscript_bound
    [Fintype N] (s : V60MarkedSkeleton N) :
    nodeCount s ≤
      (2 * markedLeaves s - 1) * Fintype.card N := by
  calc
    nodeCount s ≤ blockCount s * Fintype.card N :=
      nodeCount_le_blockCount_mul_card s
    _ = (2 * markedLeaves s - 1) * Fintype.card N := by
      rw [blockCount_eq_two_mul_markedLeaves_sub_one]

end V60MarkedSkeleton

end FixedHCFG
end LeanCfgProject
