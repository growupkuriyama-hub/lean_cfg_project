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
Every label appearing after the root determines a positive-depth prefix ending
at that label and a suffix continuing to the original hole.
-/
theorem split_at_target_mem
    {A H Z : N}
    (ctx : V60DerivationContext terminal binary A H)
    (hZ : Z ∈ targetLabels ctx) :
    ∃ (prefix : V60DerivationContext terminal binary A Z)
      (suffix : V60DerivationContext terminal binary Z H),
      ctx = comp prefix suffix ∧ 0 < depth prefix := by
  induction ctx with
  | hole A =>
      simp [targetLabels] at hZ
  | left A B C H hrule sub rightTree ih =>
      simp only [targetLabels, List.mem_cons] at hZ
      rcases hZ with hEq | hMem
      · subst Z
        let prefix : V60DerivationContext terminal binary A B :=
          .left A B C B hrule (.hole B) rightTree
        refine ⟨prefix, sub, ?_, ?_⟩
        · simp [prefix, comp]
        · simp [prefix, depth]
      · obtain ⟨pre, suf, hSplit, hPos⟩ := ih hMem
        let prefix : V60DerivationContext terminal binary A Z :=
          .left A B C Z hrule pre rightTree
        refine ⟨prefix, suf, ?_, ?_⟩
        · simp [prefix, comp, hSplit]
        · simp [prefix, depth]
  | right A B C H hrule leftTree sub ih =>
      simp only [targetLabels, List.mem_cons] at hZ
      rcases hZ with hEq | hMem
      · subst Z
        let prefix : V60DerivationContext terminal binary A C :=
          .right A B C C hrule leftTree (.hole C)
        refine ⟨prefix, sub, ?_, ?_⟩
        · simp [prefix, comp]
        · simp [prefix, depth]
      · obtain ⟨pre, suf, hSplit, hPos⟩ := ih hMem
        let prefix : V60DerivationContext terminal binary A Z :=
          .right A B C Z hrule leftTree pre
        refine ⟨prefix, suf, ?_, ?_⟩
        · simp [prefix, comp, hSplit]
        · simp [prefix, depth]

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

end V60DerivationContext

end FixedHCFG
end LeanCfgProject
