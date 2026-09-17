import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60MarkedShortcut

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Root-oriented infrastructure for iterating the marked repeated-label shortcut.

The quantitative pruning layer already bounds every cycle-free unary block.
To connect that construction to the marked-word boundary semantics, we expose
exactly the list of labels visited after the root of a one-hole context.  A
repeated root label can then be split off as a positive-depth cycle and removed
by the marked shortcut lemmas.
-/

namespace V60DerivationContext

variable {N : Type v} {Sigma : Type u}
variable {terminal : V60TerminalRules N Sigma}
variable {binary : V60BinaryRules N}

/-- Labels visited strictly after the root on the path to the hole. -/
def targetLabels {A H : N} :
    V60DerivationContext terminal binary A H → List N
  | .hole _ => []
  | .left _ B _ _ _ sub _ => B :: targetLabels sub
  | .right _ _ C _ _ _ sub => C :: targetLabels sub

/-- The number of post-root labels is exactly the context depth. -/
theorem targetLabels_length {A H : N}
    (ctx : V60DerivationContext terminal binary A H) :
    (targetLabels ctx).length = depth ctx := by
  induction ctx with
  | hole A => rfl
  | left A B C H hrule sub rightTree ih =>
      simp [targetLabels, depth, ih]
  | right A B C H hrule leftTree sub ih =>
      simp [targetLabels, depth, ih]

/-- Target-label lists concatenate literally under context composition. -/
theorem targetLabels_comp {A B C : N}
    (outer : V60DerivationContext terminal binary A B)
    (inner : V60DerivationContext terminal binary B C) :
    targetLabels (comp outer inner) =
      targetLabels outer ++ targetLabels inner := by
  induction outer with
  | hole A => rfl
  | left A B D H hrule sub rightTree ih =>
      simp [comp, targetLabels, ih]
  | right A B D H hrule leftTree sub ih =>
      simp [comp, targetLabels, ih]

/-- Context composition is associative. -/
theorem comp_assoc {A B C D : N}
    (outer : V60DerivationContext terminal binary A B)
    (middle : V60DerivationContext terminal binary B C)
    (inner : V60DerivationContext terminal binary C D) :
    comp (comp outer middle) inner =
      comp outer (comp middle inner) := by
  induction outer with
  | hole A => rfl
  | left A B E H hrule sub rightTree ih =>
      simp [comp, ih]
  | right A B E H hrule leftTree sub ih =>
      simp [comp, ih]

/--
Every label appearing after the root determines a positive-depth initial segment
ending at that label and a suffix continuing to the original hole.
-/
theorem split_at_target_mem
    {A H Z : N}
    (ctx : V60DerivationContext terminal binary A H)
    (hZ : Z ∈ targetLabels ctx) :
    ∃ (preCtx : V60DerivationContext terminal binary A Z)
      (suffix : V60DerivationContext terminal binary Z H),
      ctx = comp preCtx suffix ∧ 0 < depth preCtx := by
  induction ctx with
  | hole A =>
      simp [targetLabels] at hZ
  | left A B C H hrule sub rightTree ih =>
      simp only [targetLabels, List.mem_cons] at hZ
      rcases hZ with hEq | hMem
      · subst Z
        let preCtx : V60DerivationContext terminal binary A B :=
          .left A B C B hrule (.hole B) rightTree
        refine ⟨preCtx, sub, ?_, ?_⟩
        · simp [preCtx, comp]
        · simp [preCtx, depth]
      · obtain ⟨pre, suf, hSplit, hPos⟩ := ih hMem
        let preCtx : V60DerivationContext terminal binary A Z :=
          .left A B C Z hrule pre rightTree
        refine ⟨preCtx, suf, ?_, ?_⟩
        · simp [preCtx, comp, hSplit]
        · simp [preCtx, depth]
  | right A B C H hrule leftTree sub ih =>
      simp only [targetLabels, List.mem_cons] at hZ
      rcases hZ with hEq | hMem
      · subst Z
        let preCtx : V60DerivationContext terminal binary A C :=
          .right A B C C hrule leftTree (.hole C)
        refine ⟨preCtx, sub, ?_, ?_⟩
        · simp [preCtx, comp]
        · simp [preCtx, depth]
      · obtain ⟨pre, suf, hSplit, hPos⟩ := ih hMem
        let preCtx : V60DerivationContext terminal binary A Z :=
          .right A B C Z hrule leftTree pre
        refine ⟨preCtx, suf, ?_, ?_⟩
        · simp [preCtx, comp, hSplit]
        · simp [preCtx, depth]

/-- Sibling shortening distributes over context composition. -/
theorem shortenSiblings_comp
    (shorten : ∀ {A : N},
      V60DerivationTree terminal binary A →
        V60DerivationTree terminal binary A)
    {A B C : N}
    (outer : V60DerivationContext terminal binary A B)
    (inner : V60DerivationContext terminal binary B C) :
    shortenSiblings shorten (comp outer inner) =
      comp (shortenSiblings shorten outer)
        (shortenSiblings shorten inner) := by
  induction outer with
  | hole A => rfl
  | left A B D H hrule sub rightTree ih =>
      simp [comp, shortenSiblings, ih]
  | right A B D H hrule leftTree sub ih =>
      simp [comp, shortenSiblings, ih]

/-- A duplicate-free root-to-hole label list has at most `|N|` vertices. -/
theorem depth_succ_le_card_of_nodup_targetLabels
    [Fintype N]
    {A H : N}
    (ctx : V60DerivationContext terminal binary A H)
    (hNodup : (A :: targetLabels ctx).Nodup) :
    depth ctx + 1 ≤ Fintype.card N := by
  have hLen := hNodup.length_le_card
  rw [List.length_cons, targetLabels_length] at hLen
  omega

/--
One repeated occurrence of the root label can be deleted even when the hole
core has already been transformed.  The surviving suffix is strictly shallower,
its path labels came from the original context, and the entire operation is one
marked-word replacement rather than a transitive composition of replacements.
-/
theorem delete_repeated_root_prefix_markedReplacement
    {R H : N}
    (ctx : V60DerivationContext terminal binary R H)
    (hRepeat : R ∈ targetLabels ctx)
    {holeMarks : List Bool}
    {oldCore newCore : V60DerivationTree terminal binary H}
    (hCore : V60MarkedWordReplacement holeMarks
      (V60DerivationTree.yield oldCore)
      (V60DerivationTree.yield newCore)) :
    ∃ suffix : V60DerivationContext terminal binary R H,
      depth suffix < depth ctx ∧
      V60MarkedWordReplacement
        (V60MarkedContextFrontier ctx holeMarks)
        (V60DerivationTree.yield (plug ctx oldCore))
        (V60DerivationTree.yield (plug suffix newCore)) ∧
      ∀ Z, Z ∈ targetLabels suffix → Z ∈ targetLabels ctx := by
  obtain ⟨preCtx, suffix, hSplit, hPrePos⟩ :=
    split_at_target_mem ctx hRepeat
  refine ⟨suffix, ?_, ?_, ?_⟩
  · rw [hSplit, depth_comp]
    omega
  · have hSuffix := plug_markedReplacement suffix hCore
    have hDelete := delete_markedReplacement_of_core preCtx hSuffix
    rw [hSplit, v60MarkedContextFrontier_comp]
    simpa [plug_comp] using hDelete
  · intro Z hZ
    rw [hSplit, targetLabels_comp]
    exact List.mem_append.mpr (Or.inr hZ)

/--
Iterating the repeated-label deletion yields a same-endpoint context whose full
root-to-hole label list is duplicate-free.  At the same time, every protected
hole symbol is preserved literally, and every label retained by the new chain
already occurred on the original chain.
-/
theorem normalize_marked_context
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
        (V60DerivationTree.yield (plug normCtx newCore)) ∧
      ∀ Z, Z ∈ targetLabels normCtx → Z ∈ targetLabels ctx := by
  classical
  by_cases hRepeat : A ∈ targetLabels ctx
  · obtain ⟨preCtx, suffix, hSplit, hPrePos⟩ :=
      split_at_target_mem ctx hRepeat
    have hSuffixLt : depth suffix < depth ctx := by
      rw [hSplit, depth_comp]
      omega
    obtain ⟨normSuffix, hNodup, hRec, hSubset⟩ :=
      normalize_marked_context suffix hCore
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
        · simpa [V60MarkedContextFrontier, plug] using hCore
        · intro Z hZ
          simp [targetLabels] at hZ
    | left A B C H hrule sub rightTree =>
        obtain ⟨normSub, hNodupSub, hRec, hSubset⟩ :=
          normalize_marked_context sub hCore
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
                (V60DerivationTree.yield rightTree) := by
            apply v60_zero_mark_subtree_replacement
              (List.replicate
                (V60DerivationTree.leafCount rightTree) false)
              rightTree rightTree
            · simp
            · simp
          have hApp := V60MarkedWordReplacement.append hRec hRight
          simpa [normCtx, V60MarkedContextFrontier, plug,
            V60DerivationTree.yield] using hApp
        · intro Z hZ
          simp only [normCtx, targetLabels, List.mem_cons] at hZ ⊢
          rcases hZ with hEq | hMem
          · exact Or.inl hEq
          · exact Or.inr (hSubset Z hMem)
    | right A B C H hrule leftTree sub =>
        obtain ⟨normSub, hNodupSub, hRec, hSubset⟩ :=
          normalize_marked_context sub hCore
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
                (V60DerivationTree.yield leftTree) := by
            apply v60_zero_mark_subtree_replacement
              (List.replicate
                (V60DerivationTree.leafCount leftTree) false)
              leftTree leftTree
            · simp
            · simp
          have hApp := V60MarkedWordReplacement.append hLeft hRec
          simpa [normCtx, V60MarkedContextFrontier, plug,
            V60DerivationTree.yield] using hApp
        · intro Z hZ
          simp only [normCtx, targetLabels, List.mem_cons] at hZ ⊢
          rcases hZ with hEq | hMem
          · exact Or.inl hEq
          · exact Or.inr (hSubset Z hMem)
termination_by depth ctx
decreasing_by
  all_goals simp_all [depth, depth_comp] <;> omega

end V60DerivationContext

end FixedHCFG
end LeanCfgProject
