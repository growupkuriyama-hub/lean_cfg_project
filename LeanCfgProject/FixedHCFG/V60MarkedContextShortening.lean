import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60MarkedContextPruning

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Marked normalization with simultaneous sibling replacement.

A marked-word replacement is deliberately oriented by the original source
marks, so a separately normalized intermediate word cannot in general be used
as the source of a second replacement.  The theorem below therefore performs
repeated-label deletion and off-path sibling replacement in one recursive
construction.  This is the form needed by the fixed-window proof.
-/

namespace V60DerivationContext

variable {N : Type v} {Sigma : Type u}
variable {terminal : V60TerminalRules N Sigma}
variable {binary : V60BinaryRules N}

/--
Normalize a root-to-hole chain to a duplicate-free chain while simultaneously
replacing every retained off-path sibling by `shorten`.  Protected symbols in
the hole survive literally, and retained chain labels all come from the
original context.
-/
theorem normalize_marked_context_with_sibling_replacement
    (shorten : ∀ {X : N},
      V60DerivationTree terminal binary X →
        V60DerivationTree terminal binary X)
    {A H : N}
    (ctx : V60DerivationContext terminal binary A H)
    {holeMarks : List Bool}
    {oldCore newCore : V60DerivationTree terminal binary H}
    (hCore : V60MarkedWordReplacement holeMarks
      (V60DerivationTree.yield oldCore)
      (V60DerivationTree.yield newCore)) :
    ∃ normCtx : V60DerivationContext terminal binary A H,
      (A :: targetLabels normCtx).Nodup ∧
      V60MarkedWordReplacement
        (V60MarkedContextFrontier ctx holeMarks)
        (V60DerivationTree.yield (plug ctx oldCore))
        (V60DerivationTree.yield
          (plug (shortenSiblings shorten normCtx) newCore)) ∧
      ∀ Z, Z ∈ targetLabels normCtx → Z ∈ targetLabels ctx := by
  classical
  by_cases hRepeat : A ∈ targetLabels ctx
  · obtain ⟨preCtx, suffix, hSplit, hPrePos⟩ :=
      split_at_target_mem ctx hRepeat
    have hSuffixLt : depth suffix < depth ctx := by
      rw [hSplit, depth_comp]
      omega
    obtain ⟨normSuffix, hNodup, hRec, hSubset⟩ :=
      normalize_marked_context_with_sibling_replacement shorten suffix hCore
    refine ⟨normSuffix, hNodup, ?_, ?_⟩
    · have hDelete := delete_markedReplacement_of_core preCtx hRec
      rw [hSplit, v60MarkedContextFrontier_comp]
      simpa [plug_comp] using hDelete
    · intro Z hZ
      rw [hSplit, targetLabels_comp]
      exact List.mem_append.mpr (Or.inr (hSubset Z hZ))
  · cases ctx with
    | hole A =>
        refine ⟨.hole A, ?_, ?_, ?_⟩
        · simpa [targetLabels] using List.nodup_singleton A
        · simpa [V60MarkedContextFrontier, plug, shortenSiblings] using hCore
        · intro Z hZ
          simp [targetLabels] at hZ
    | left A B C H hrule sub rightTree =>
        obtain ⟨normSub, hNodupSub, hRec, hSubset⟩ :=
          normalize_marked_context_with_sibling_replacement shorten sub hCore
        let normCtx : V60DerivationContext terminal binary A H :=
          .left A B C H hrule normSub rightTree
        have hNo : A ≠ B ∧ A ∉ targetLabels sub := by
          simpa [targetLabels] using hRepeat
        have hANotNorm : A ∉ targetLabels normSub := by
          intro hA
          exact hNo.2 (hSubset A hA)
        have hANotTail : A ∉ B :: targetLabels normSub := by
          simp [hNo.1, hANotNorm]
        refine ⟨normCtx, ?_, ?_, ?_⟩
        · change (A :: B :: targetLabels normSub).Nodup
          exact List.nodup_cons.mpr ⟨hANotTail, hNodupSub⟩
        · have hRight :
              V60MarkedWordReplacement
                (List.replicate
                  (V60DerivationTree.leafCount rightTree) false)
                (V60DerivationTree.yield rightTree)
                (V60DerivationTree.yield (shorten rightTree)) := by
            apply v60_zero_mark_subtree_replacement
              (List.replicate
                (V60DerivationTree.leafCount rightTree) false)
              rightTree (shorten rightTree)
            · simp
            · simp
          have hApp := V60MarkedWordReplacement.append hRec hRight
          simpa [normCtx, V60MarkedContextFrontier, plug, shortenSiblings,
            V60DerivationTree.yield] using hApp
        · intro Z hZ
          simp only [normCtx, targetLabels, List.mem_cons] at hZ ⊢
          rcases hZ with hEq | hMem
          · exact Or.inl hEq
          · exact Or.inr (hSubset Z hMem)
    | right A B C H hrule leftTree sub =>
        obtain ⟨normSub, hNodupSub, hRec, hSubset⟩ :=
          normalize_marked_context_with_sibling_replacement shorten sub hCore
        let normCtx : V60DerivationContext terminal binary A H :=
          .right A B C H hrule leftTree normSub
        have hNo : A ≠ C ∧ A ∉ targetLabels sub := by
          simpa [targetLabels] using hRepeat
        have hANotNorm : A ∉ targetLabels normSub := by
          intro hA
          exact hNo.2 (hSubset A hA)
        have hANotTail : A ∉ C :: targetLabels normSub := by
          simp [hNo.1, hANotNorm]
        refine ⟨normCtx, ?_, ?_, ?_⟩
        · change (A :: C :: targetLabels normSub).Nodup
          exact List.nodup_cons.mpr ⟨hANotTail, hNodupSub⟩
        · have hLeft :
              V60MarkedWordReplacement
                (List.replicate
                  (V60DerivationTree.leafCount leftTree) false)
                (V60DerivationTree.yield leftTree)
                (V60DerivationTree.yield (shorten leftTree)) := by
            apply v60_zero_mark_subtree_replacement
              (List.replicate
                (V60DerivationTree.leafCount leftTree) false)
              leftTree (shorten leftTree)
            · simp
            · simp
          have hApp := V60MarkedWordReplacement.append hLeft hRec
          simpa [normCtx, V60MarkedContextFrontier, plug, shortenSiblings,
            V60DerivationTree.yield] using hApp
        · intro Z hZ
          simp only [normCtx, targetLabels, List.mem_cons] at hZ ⊢
          rcases hZ with hEq | hMem
          · exact Or.inl hEq
          · exact Or.inr (hSubset Z hMem)
termination_by depth ctx
decreasing_by
  all_goals simp_all [depth, depth_comp] <;> omega

/--
Specialization of the simultaneous construction to the manuscript thickness
replacement.  The target context is label-simple and all of its retained
siblings have yield length at most `tau`.
-/
theorem normalize_marked_context_by_thickness
    (tau : Nat)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {A H : N}
    (ctx : V60DerivationContext terminal binary A H)
    {holeMarks : List Bool}
    {oldCore newCore : V60DerivationTree terminal binary H}
    (hCore : V60MarkedWordReplacement holeMarks
      (V60DerivationTree.yield oldCore)
      (V60DerivationTree.yield newCore)) :
    ∃ normCtx : V60DerivationContext terminal binary A H,
      (A :: targetLabels normCtx).Nodup ∧
      V60MarkedWordReplacement
        (V60MarkedContextFrontier ctx holeMarks)
        (V60DerivationTree.yield (plug ctx oldCore))
        (V60DerivationTree.yield
          (plug (shortenSiblingsByThickness tau hThickness normCtx) newCore)) ∧
      ∀ Z, Z ∈ targetLabels normCtx → Z ∈ targetLabels ctx := by
  simpa [shortenSiblingsByThickness] using
    (normalize_marked_context_with_sibling_replacement
      (terminal := terminal) (binary := binary)
      (fun {X} t =>
        v60ThicknessShortTree
          (terminal := terminal) (binary := binary) tau hThickness t)
      ctx hCore)

/--
One accumulated marked chain can therefore be compressed semantically and
quantitatively in a single step.  The result preserves the original marked
frontier and costs at most `|N| * tau` terminal material around the transformed
core.
-/
theorem marked_compress_prefix_around_core
    [Fintype N]
    (tau : Nat)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {R A : N}
    (ctxPrefix : V60DerivationContext terminal binary R A)
    {holeMarks : List Bool}
    {oldCore newCore : V60DerivationTree terminal binary A}
    (hCore : V60MarkedWordReplacement holeMarks
      (V60DerivationTree.yield oldCore)
      (V60DerivationTree.yield newCore)) :
    ∃ t' : V60DerivationTree terminal binary R,
      V60MarkedWordReplacement
        (V60MarkedContextFrontier ctxPrefix holeMarks)
        (V60DerivationTree.yield (plug ctxPrefix oldCore))
        (V60DerivationTree.yield t') ∧
      (V60DerivationTree.yield t').length ≤
        (V60DerivationTree.yield newCore).length + Fintype.card N * tau := by
  obtain ⟨normCtx, hNodup, hMarked, hSubset⟩ :=
    normalize_marked_context_by_thickness tau hThickness ctxPrefix hCore
  let shortCtx := shortenSiblingsByThickness tau hThickness normCtx
  let t' : V60DerivationTree terminal binary R := plug shortCtx newCore
  refine ⟨t', ?_, ?_⟩
  · simpa [t', shortCtx] using hMarked
  · have hDepthSucc : depth normCtx + 1 ≤ Fintype.card N :=
      depth_succ_le_card_of_nodup_targetLabels normCtx hNodup
    have hDepth : depth normCtx ≤ Fintype.card N := by omega
    have hMaterial : terminalMaterialLength shortCtx ≤ depth normCtx * tau := by
      dsimp [shortCtx]
      exact terminalMaterialLength_shortenSiblingsByThickness_le
        tau hThickness normCtx
    have hScaled : depth normCtx * tau ≤ Fintype.card N * tau :=
      Nat.mul_le_mul_right tau hDepth
    have hMaterialBound : terminalMaterialLength shortCtx ≤
        Fintype.card N * tau := le_trans hMaterial hScaled
    rw [show t' = plug shortCtx newCore by rfl]
    rw [yield_plug]
    simp only [List.length_append]
    unfold terminalMaterialLength at hMaterialBound
    omega

end V60DerivationContext

end FixedHCFG
end LeanCfgProject
