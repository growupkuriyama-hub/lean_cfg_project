import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60MarkedSupport

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Quantitative core of the concrete marked-leaf pruning argument.

The proof follows the manuscript literally at the level of maximal unary
chains.  While the marked support has only one live child, we accumulate a
one-hole derivation context.  At the next marked branch (or marked terminal)
we shorten that whole context at once:

* repeated base-nonterminal labels are deleted by `V60DerivationSpine`;
* every off-path sibling is replaced by a thickness-bounded same-root tree.

Thus each suppressed support block costs at most `|N| * tau` terminals.  The
marked terminal leaves themselves each cost exactly one terminal.  Recursing at
genuine marked branches gives the bound

  markedLeaves + suppressedBlockCount * |N| * tau.

Boundary-symbol preservation is deliberately separated into the next layer;
this file discharges the hard quantitative tree construction.
-/

/--
Shorten one accumulated root-to-current-node context and plug an arbitrary
already-pruned core tree into it.  The surrounding terminal material costs at
most one thickness charge for each of at most `|N|` retained chain vertices.
-/
theorem v60_compress_prefix_around_core
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (tau : Nat)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {R A : N}
    (ctxPrefix : V60DerivationContext terminal binary R A)
    (core : V60DerivationTree terminal binary A) :
    ∃ ctx' : V60DerivationContext terminal binary R A,
      (V60DerivationTree.yield
        (V60DerivationContext.plug ctx' core)).length ≤
        (V60DerivationTree.yield core).length + Fintype.card N * tau := by
  obtain ⟨ctxSimple, hDepth⟩ :=
    V60DerivationSpine.exists_context_with_depth_succ_le_card ctxPrefix
  let ctx' :=
    V60DerivationContext.shortenSiblingsByThickness
      tau hThickness ctxSimple
  have hMaterial :
      V60DerivationContext.terminalMaterialLength ctx' ≤
        V60DerivationContext.depth ctxSimple * tau := by
    dsimp [ctx']
    exact V60DerivationContext.terminalMaterialLength_shortenSiblingsByThickness_le
      tau hThickness ctxSimple
  have hDepthLe : V60DerivationContext.depth ctxSimple ≤ Fintype.card N := by
    omega
  have hScaled :
      V60DerivationContext.depth ctxSimple * tau ≤ Fintype.card N * tau :=
    Nat.mul_le_mul_right tau hDepthLe
  have hMaterialBound :
      V60DerivationContext.terminalMaterialLength ctx' ≤
        Fintype.card N * tau := le_trans hMaterial hScaled
  refine ⟨ctx', ?_⟩
  rw [V60DerivationContext.yield_plug]
  simp only [List.length_append]
  unfold V60DerivationContext.terminalMaterialLength at hMaterialBound
  omega

namespace V60MarkedSupport

variable {N : Type v} {Sigma : Type u}
variable {terminal : V60TerminalRules N Sigma}
variable {binary : V60BinaryRules N}

/--
Recursive marked-tree pruning with an accumulated unary-chain context.

The context begins at some outer root `R` and ends at the root of the current
marked support.  Unary support nodes merely extend it.  At a marked branch or
leaf, the whole context is cycle-shortened and sibling-shortened in one shot.
-/
theorem prune_with_prefix_length_bound
    [Fintype N]
    (tau : Nat)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {A : N} {t : V60DerivationTree terminal binary A}
    {marks : List Bool} {shape : V60MarkedSupportShape}
    (h : V60MarkedSupport terminal binary t marks shape) :
    ∀ {R : N} (ctxPrefix : V60DerivationContext terminal binary R A),
      ∃ t' : V60DerivationTree terminal binary R,
        (V60DerivationTree.yield t').length ≤
          V60MarkedSupportShape.markedLeaves shape +
            V60MarkedSupportShape.suppressedBlockCount shape *
              Fintype.card N * tau := by
  induction h with
  | terminal A a hrule =>
      intro R ctxPrefix
      let core := V60DerivationTree.terminal A a hrule
      obtain ⟨ctx', hBound⟩ :=
        v60_compress_prefix_around_core tau hThickness ctxPrefix core
      refine ⟨V60DerivationContext.plug ctx' core, ?_⟩
      simpa [core, V60DerivationTree.yield,
        V60MarkedSupportShape.markedLeaves,
        V60MarkedSupportShape.suppressedBlockCount,
        Nat.mul_assoc] using hBound
  | @unaryLeft A B C hrule left right marksLeft marksRight shapeLeft
      hLeft hRightZero ih =>
      intro R ctxPrefix
      let step : V60DerivationContext terminal binary A B :=
        V60DerivationContext.left A B C B hrule
          (V60DerivationContext.hole B) right
      let ctxNext : V60DerivationContext terminal binary R B :=
        V60DerivationContext.comp ctxPrefix step
      obtain ⟨t', hBound⟩ := ih ctxNext
      refine ⟨t', ?_⟩
      simpa [V60MarkedSupportShape.markedLeaves,
        V60MarkedSupportShape.suppressedBlockCount] using hBound
  | @unaryRight A B C hrule left right marksLeft marksRight shapeRight
      hLeftZero hRight ih =>
      intro R ctxPrefix
      let step : V60DerivationContext terminal binary A C :=
        V60DerivationContext.right A B C C hrule left
          (V60DerivationContext.hole C)
      let ctxNext : V60DerivationContext terminal binary R C :=
        V60DerivationContext.comp ctxPrefix step
      obtain ⟨t', hBound⟩ := ih ctxNext
      refine ⟨t', ?_⟩
      simpa [V60MarkedSupportShape.markedLeaves,
        V60MarkedSupportShape.suppressedBlockCount] using hBound
  | @branch A B C hrule left right marksLeft marksRight shapeLeft shapeRight
      hLeft hRight ihLeft ihRight =>
      intro R ctxPrefix
      obtain ⟨left', hLeftBound⟩ :=
        ihLeft (V60DerivationContext.hole B)
      obtain ⟨right', hRightBound⟩ :=
        ihRight (V60DerivationContext.hole C)
      let core : V60DerivationTree terminal binary A :=
        V60DerivationTree.binary A B C hrule left' right'
      obtain ⟨ctx', hPrefixBound⟩ :=
        v60_compress_prefix_around_core tau hThickness ctxPrefix core
      refine ⟨V60DerivationContext.plug ctx' core, ?_⟩
      calc
        (V60DerivationTree.yield
            (V60DerivationContext.plug ctx' core)).length
            ≤ (V60DerivationTree.yield core).length +
                Fintype.card N * tau := hPrefixBound
        _ = (V60DerivationTree.yield left').length +
              (V60DerivationTree.yield right').length +
                Fintype.card N * tau := by
              simp [core, V60DerivationTree.yield, List.length_append]
        _ ≤ (V60MarkedSupportShape.markedLeaves shapeLeft +
                V60MarkedSupportShape.suppressedBlockCount shapeLeft *
                  Fintype.card N * tau) +
              (V60MarkedSupportShape.markedLeaves shapeRight +
                V60MarkedSupportShape.suppressedBlockCount shapeRight *
                  Fintype.card N * tau) +
              Fintype.card N * tau := by
              exact Nat.add_le_add_right
                (Nat.add_le_add hLeftBound hRightBound)
                (Fintype.card N * tau)
        _ = V60MarkedSupportShape.markedLeaves
              (.branch shapeLeft shapeRight) +
            V60MarkedSupportShape.suppressedBlockCount
              (.branch shapeLeft shapeRight) * Fintype.card N * tau := by
              simp [V60MarkedSupportShape.markedLeaves,
                V60MarkedSupportShape.suppressedBlockCount,
                Nat.add_mul, Nat.mul_assoc, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm]

/--
Closed quantitative pruning theorem: start with the trivial root context.  Every
concrete marked support therefore has a same-root SSBNF derivation whose length
is bounded by one marked terminal per protected leaf plus `|N|*tau` per
suppressed support block.
-/
theorem prune_length_bound
    [Fintype N]
    (tau : Nat)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {A : N} {t : V60DerivationTree terminal binary A}
    {marks : List Bool} {shape : V60MarkedSupportShape}
    (h : V60MarkedSupport terminal binary t marks shape) :
    ∃ t' : V60DerivationTree terminal binary A,
      (V60DerivationTree.yield t').length ≤
        V60MarkedSupportShape.markedLeaves shape +
          V60MarkedSupportShape.suppressedBlockCount shape *
            Fintype.card N * tau := by
  exact prune_with_prefix_length_bound tau hThickness h
    (V60DerivationContext.hole A)

/--
For the actual first-`k`/last-`l` support, the quantitative construction already
reaches the manuscript's displayed positive-window length bound.  What remains
for the full compression certificate is to attach the boundary-equality proof
to this same recursively constructed tree.
-/
theorem exists_boundary_pruned_tree_length_bound
    [Fintype N]
    (tau : Nat)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    (k l : Nat) {A : N}
    (t : V60DerivationTree terminal binary A)
    (hLong : k + l ≤ V60DerivationTree.leafCount t)
    (hr : k + l ≠ 0) :
    ∃ t' : V60DerivationTree terminal binary A,
      (V60DerivationTree.yield t').length ≤
        k + l + (2 * (k + l) - 1) * Fintype.card N * tau := by
  obtain ⟨shape, hSupport, hBlocks⟩ :=
    boundary_support_block_count k l t hLong hr
  have hLeaves : V60MarkedSupportShape.markedLeaves shape = k + l := by
    rw [markedLeaves_eq_markCount hSupport]
    exact v60BoundaryMarks_count k l _
  obtain ⟨t', hBound⟩ := prune_length_bound tau hThickness hSupport
  refine ⟨t', ?_⟩
  simpa [hLeaves, hBlocks] using hBound

end V60MarkedSupport

end FixedHCFG
end LeanCfgProject
