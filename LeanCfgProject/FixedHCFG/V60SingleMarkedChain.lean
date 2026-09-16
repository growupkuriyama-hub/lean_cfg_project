import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60MarkedSupport

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
The one-mark base case of the concrete marked-tree pruning construction.

If the marked support contains exactly one terminal leaf, it cannot branch: it
is a single root-to-leaf chain.  We expose that chain as a derivation context,
remove repeated base-nonterminal labels using `V60DerivationSpine`, and then
replace all off-path siblings by thickness-bounded same-root trees.  The marked
terminal itself is kept literally unchanged.
-/

namespace V60MarkedSupport

variable {N : Type v} {Sigma : Type u}
variable {terminal : V60TerminalRules N Sigma}
variable {binary : V60BinaryRules N}

/--
A support with one marked leaf is represented by a one-hole derivation context
ending at the very same terminal rule as in the original tree.
-/
theorem exists_terminal_context_of_one_mark
    {A : N} {t : V60DerivationTree terminal binary A}
    {marks : List Bool} {shape : V60MarkedSupportShape}
    (h : V60MarkedSupport terminal binary t marks shape)
    (hOne : V60MarkedSupportShape.markedLeaves shape = 1) :
    ∃ (H : N) (a : Sigma) (hrule : terminal H a)
      (ctx : V60DerivationContext terminal binary A H),
      t = V60DerivationContext.plug ctx
        (V60DerivationTree.terminal H a hrule) := by
  induction h with
  | terminal A a hrule =>
      exact ⟨A, a, hrule, V60DerivationContext.hole A, rfl⟩
  | @unaryLeft A B C hrule left right marksLeft marksRight shapeLeft
      hLeft hRightZero ih =>
      have hChildOne : V60MarkedSupportShape.markedLeaves shapeLeft = 1 := by
        simpa [V60MarkedSupportShape.markedLeaves] using hOne
      obtain ⟨H, a, hterm, ctx, htree⟩ := ih hChildOne
      refine ⟨H, a, hterm,
        V60DerivationContext.left A B C H hrule ctx right, ?_⟩
      simp [V60DerivationContext.plug, htree]
  | @unaryRight A B C hrule left right marksLeft marksRight shapeRight
      hLeftZero hRight ih =>
      have hChildOne : V60MarkedSupportShape.markedLeaves shapeRight = 1 := by
        simpa [V60MarkedSupportShape.markedLeaves] using hOne
      obtain ⟨H, a, hterm, ctx, htree⟩ := ih hChildOne
      refine ⟨H, a, hterm,
        V60DerivationContext.right A B C H hrule left ctx, ?_⟩
      simp [V60DerivationContext.plug, htree]
  | @branch A B C hrule left right marksLeft marksRight shapeLeft shapeRight
      hLeft hRight ihLeft ihRight =>
      have hLeftPos := V60MarkedSupportShape.markedLeaves_pos shapeLeft
      have hRightPos := V60MarkedSupportShape.markedLeaves_pos shapeRight
      simp only [V60MarkedSupportShape.markedLeaves] at hOne
      omega

/--
Concrete one-block pruning theorem.  The resulting derivation keeps the marked
terminal rule itself, while the total terminal yield is bounded by one marked
terminal plus one thickness charge for each of at most `|N|` retained chain
vertices.
-/
theorem compress_one_mark_chain
    [Fintype N]
    (tau : Nat)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {A : N} {t : V60DerivationTree terminal binary A}
    {marks : List Bool} {shape : V60MarkedSupportShape}
    (h : V60MarkedSupport terminal binary t marks shape)
    (hOne : V60MarkedSupportShape.markedLeaves shape = 1) :
    ∃ (H : N) (a : Sigma) (hrule : terminal H a)
      (ctx' : V60DerivationContext terminal binary A H),
      V60UntypedDerives terminal binary A
        (V60DerivationTree.yield
          (V60DerivationContext.plug ctx'
            (V60DerivationTree.terminal H a hrule))) ∧
      V60DerivationTree.yield
          (V60DerivationContext.plug ctx'
            (V60DerivationTree.terminal H a hrule)) =
        V60DerivationContext.leftWord ctx' ++ [a] ++
          V60DerivationContext.rightWord ctx' ∧
      (V60DerivationTree.yield
          (V60DerivationContext.plug ctx'
            (V60DerivationTree.terminal H a hrule))).length ≤
        1 + Fintype.card N * tau := by
  obtain ⟨H, a, hterm, ctx, htree⟩ :=
    exists_terminal_context_of_one_mark h hOne
  obtain ⟨ctxSimple, hDepth⟩ :=
    V60DerivationSpine.exists_context_with_depth_succ_le_card ctx
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
  refine ⟨H, a, hterm, ctx', ?_, ?_, ?_⟩
  · exact V60DerivationTree.toUntypedDerives
      (V60DerivationContext.plug ctx'
        (V60DerivationTree.terminal H a hterm))
  · simpa [V60DerivationTree.yield] using
      (V60DerivationContext.yield_plug ctx'
        (V60DerivationTree.terminal H a hterm))
  · rw [V60DerivationContext.yield_plug]
    simp only [V60DerivationTree.yield, List.length_append,
      List.length_singleton]
    unfold V60DerivationContext.terminalMaterialLength at hMaterialBound
    omega

end V60MarkedSupport

end FixedHCFG
end LeanCfgProject
