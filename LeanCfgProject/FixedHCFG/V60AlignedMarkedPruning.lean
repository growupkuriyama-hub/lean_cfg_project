import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60AlignedMarkedSupport
import LeanCfgProject.FixedHCFG.V60MarkedContextShortening

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Boundary-preserving recursive pruning of an aligned marked support.

The quantitative `V60MarkedPruningLength` construction already compresses each
maximal unary support block and proves the manuscript length bound.  The aligned
support relation retains the missing frontier information on every zero-mark
sibling.  Combining it with `marked_compress_prefix_around_core` lets the same
recursive construction carry a `V60MarkedWordReplacement` proof all the way
from the original derivation tree to the pruned tree.
-/

namespace V60AlignedMarkedSupport

variable {N : Type v} {Sigma : Type u}
variable {terminal : V60TerminalRules N Sigma}
variable {binary : V60BinaryRules N}

/--
Recursive marked-support pruning with both semantics and the quantitative
suppressed-block bound.  The accumulated context is compressed only when the
support reaches a marked leaf or a genuine marked branch, exactly as in the
manuscript proof.
-/
theorem prune_with_prefix_marked_bound
    [Fintype N]
    (tau : Nat)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {A : N} {t : V60DerivationTree terminal binary A}
    {marks : List Bool} {shape : V60MarkedSupportShape}
    (h : V60AlignedMarkedSupport terminal binary t marks shape) :
    ∀ {R : N} (ctxPrefix : V60DerivationContext terminal binary R A),
      ∃ t' : V60DerivationTree terminal binary R,
        V60MarkedWordReplacement
          (V60MarkedContextFrontier ctxPrefix marks)
          (V60DerivationTree.yield
            (V60DerivationContext.plug ctxPrefix t))
          (V60DerivationTree.yield t') ∧
        (V60DerivationTree.yield t').length ≤
          V60MarkedSupportShape.markedLeaves shape +
            V60MarkedSupportShape.suppressedBlockCount shape *
              Fintype.card N * tau := by
  induction h with
  | terminal A a hrule =>
      intro R ctxPrefix
      let core : V60DerivationTree terminal binary A :=
        V60DerivationTree.terminal A a hrule
      have hCore :
          V60MarkedWordReplacement [true]
            (V60DerivationTree.yield core)
            (V60DerivationTree.yield core) := by
        apply v60_marked_replacement_refl_of_aligned
        simp [core, V60DerivationTree.yield]
      obtain ⟨t', hMarked, hBound⟩ :=
        V60DerivationContext.marked_compress_prefix_around_core
          tau hThickness ctxPrefix hCore
      refine ⟨t', ?_, ?_⟩
      · simpa [core] using hMarked
      · simpa [core, V60DerivationTree.yield,
          V60MarkedSupportShape.markedLeaves,
          V60MarkedSupportShape.suppressedBlockCount,
          Nat.mul_assoc] using hBound
  | @unaryLeft A B C hrule left right marksLeft marksRight shapeLeft
      hLeft hRightAlign hRightZero ih =>
      intro R ctxPrefix
      have hRightMarks :
          marksRight =
            List.replicate (V60DerivationTree.leafCount right) false := by
        have hFalse :=
          V60MarkedWordReplacement.eq_replicate_false_of_markCount_zero
            marksRight hRightZero
        simpa [hRightAlign] using hFalse
      let step : V60DerivationContext terminal binary A B :=
        V60DerivationContext.left A B C B hrule
          (V60DerivationContext.hole B) right
      let ctxNext : V60DerivationContext terminal binary R B :=
        V60DerivationContext.comp ctxPrefix step
      obtain ⟨t', hMarked, hBound⟩ := ih ctxNext
      have hFrontier :
          V60MarkedContextFrontier ctxNext marksLeft =
            V60MarkedContextFrontier ctxPrefix (marksLeft ++ marksRight) := by
        dsimp [ctxNext]
        rw [v60MarkedContextFrontier_comp]
        simp [step, V60MarkedContextFrontier, hRightMarks]
      have hPlug :
          V60DerivationContext.plug ctxNext left =
            V60DerivationContext.plug ctxPrefix
              (V60DerivationTree.binary A B C hrule left right) := by
        dsimp [ctxNext]
        rw [V60DerivationContext.plug_comp]
        simp [step, V60DerivationContext.plug]
      refine ⟨t', ?_, ?_⟩
      · rw [hFrontier, hPlug] at hMarked
        exact hMarked
      · simpa [V60MarkedSupportShape.markedLeaves,
          V60MarkedSupportShape.suppressedBlockCount] using hBound
  | @unaryRight A B C hrule left right marksLeft marksRight shapeRight
      hLeftAlign hLeftZero hRight ih =>
      intro R ctxPrefix
      have hLeftMarks :
          marksLeft =
            List.replicate (V60DerivationTree.leafCount left) false := by
        have hFalse :=
          V60MarkedWordReplacement.eq_replicate_false_of_markCount_zero
            marksLeft hLeftZero
        simpa [hLeftAlign] using hFalse
      let step : V60DerivationContext terminal binary A C :=
        V60DerivationContext.right A B C C hrule left
          (V60DerivationContext.hole C)
      let ctxNext : V60DerivationContext terminal binary R C :=
        V60DerivationContext.comp ctxPrefix step
      obtain ⟨t', hMarked, hBound⟩ := ih ctxNext
      have hFrontier :
          V60MarkedContextFrontier ctxNext marksRight =
            V60MarkedContextFrontier ctxPrefix (marksLeft ++ marksRight) := by
        dsimp [ctxNext]
        rw [v60MarkedContextFrontier_comp]
        simp [step, V60MarkedContextFrontier, hLeftMarks]
      have hPlug :
          V60DerivationContext.plug ctxNext right =
            V60DerivationContext.plug ctxPrefix
              (V60DerivationTree.binary A B C hrule left right) := by
        dsimp [ctxNext]
        rw [V60DerivationContext.plug_comp]
        simp [step, V60DerivationContext.plug]
      refine ⟨t', ?_, ?_⟩
      · rw [hFrontier, hPlug] at hMarked
        exact hMarked
      · simpa [V60MarkedSupportShape.markedLeaves,
          V60MarkedSupportShape.suppressedBlockCount] using hBound
  | @branch A B C hrule left right marksLeft marksRight shapeLeft shapeRight
      hLeft hRight ihLeft ihRight =>
      intro R ctxPrefix
      obtain ⟨left', hLeftMarked, hLeftBound⟩ :=
        ihLeft (V60DerivationContext.hole B)
      obtain ⟨right', hRightMarked, hRightBound⟩ :=
        ihRight (V60DerivationContext.hole C)
      have hLeftCore :
          V60MarkedWordReplacement marksLeft
            (V60DerivationTree.yield left)
            (V60DerivationTree.yield left') := by
        simpa [V60MarkedContextFrontier,
          V60DerivationContext.plug] using hLeftMarked
      have hRightCore :
          V60MarkedWordReplacement marksRight
            (V60DerivationTree.yield right)
            (V60DerivationTree.yield right') := by
        simpa [V60MarkedContextFrontier,
          V60DerivationContext.plug] using hRightMarked
      let oldCore : V60DerivationTree terminal binary A :=
        V60DerivationTree.binary A B C hrule left right
      let newCore : V60DerivationTree terminal binary A :=
        V60DerivationTree.binary A B C hrule left' right'
      have hCore :
          V60MarkedWordReplacement (marksLeft ++ marksRight)
            (V60DerivationTree.yield oldCore)
            (V60DerivationTree.yield newCore) := by
        have hApp := V60MarkedWordReplacement.append hLeftCore hRightCore
        simpa [oldCore, newCore, V60DerivationTree.yield] using hApp
      obtain ⟨t', hMarked, hPrefixBound⟩ :=
        V60DerivationContext.marked_compress_prefix_around_core
          tau hThickness ctxPrefix hCore
      refine ⟨t', ?_, ?_⟩
      · simpa [oldCore] using hMarked
      · calc
          (V60DerivationTree.yield t').length
              ≤ (V60DerivationTree.yield newCore).length +
                  Fintype.card N * tau := hPrefixBound
          _ = (V60DerivationTree.yield left').length +
                (V60DerivationTree.yield right').length +
                  Fintype.card N * tau := by
                simp [newCore, V60DerivationTree.yield,
                  List.length_append]
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

/-- Closed semantic-and-quantitative pruning from the trivial root context. -/
theorem prune_marked_bound
    [Fintype N]
    (tau : Nat)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {A : N} {t : V60DerivationTree terminal binary A}
    {marks : List Bool} {shape : V60MarkedSupportShape}
    (h : V60AlignedMarkedSupport terminal binary t marks shape) :
    ∃ t' : V60DerivationTree terminal binary A,
      V60MarkedWordReplacement marks
        (V60DerivationTree.yield t)
        (V60DerivationTree.yield t') ∧
      (V60DerivationTree.yield t').length ≤
        V60MarkedSupportShape.markedLeaves shape +
          V60MarkedSupportShape.suppressedBlockCount shape *
            Fintype.card N * tau := by
  simpa [V60MarkedContextFrontier, V60DerivationContext.plug] using
    (prune_with_prefix_marked_bound tau hThickness h
      (V60DerivationContext.hole A))

end V60AlignedMarkedSupport

end FixedHCFG
end LeanCfgProject
