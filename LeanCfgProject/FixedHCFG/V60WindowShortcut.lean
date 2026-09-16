import LeanCfgProject.FixedHCFG.V60DerivationTree

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Boundary preservation for the repeated-label shortcut used in manuscript Lemma
`window-typed-yield`.

The derivation-context algebra in `V60DerivationTree` exposes a repeated-label
segment as terminal material immediately to the left and right of the retained
subtree.  The lemmas below state precisely when deleting that material leaves
the first `k` and last `l` terminals unchanged.  This is the local structural
step needed before iterating cycle deletion along the marked-leaf skeleton.
-/

/-- Appending material on the left does not change the last `l` symbols once
    the common suffix itself already contains at least `l` symbols. -/
theorem v60WindowSuffix_append_of_le
    {Sigma : Type u} (l : Nat) (a b : Word Sigma)
    (h : l ≤ b.length) :
    v60WindowSuffix l (a ++ b) = v60WindowSuffix l b := by
  unfold v60WindowSuffix
  rw [List.length_append]
  have hidx :
      a.length + b.length - l = a.length + (b.length - l) := by
    omega
  rw [hidx, List.drop_append]
  have hdrop : a.drop (a.length + (b.length - l)) = [] :=
    List.drop_eq_nil_of_le (by omega)
  rw [hdrop]
  simp

/--
Delete terminal material `dl` and `dr` around a retained middle word `m`.
The first window is safe either because it lies completely in the outer prefix
`p`, or because no left material is deleted and it lies in `p ++ m`.  The last
window has the exact dual condition.

This formulation covers interior marked chains as well as the two boundary
chains meeting the first `k` or last `l` marked terminals.
-/
theorem v60_window_boundary_eq_of_middle_deletion
    {Sigma : Type u}
    (k l : Nat) (p dl m dr s : Word Sigma)
    (hPrefix : k ≤ p.length ∨ (dl = [] ∧ k ≤ (p ++ m).length))
    (hSuffix : l ≤ s.length ∨ (dr = [] ∧ l ≤ (m ++ s).length)) :
    V60WindowBoundaryEq k l
      (p ++ dl ++ m ++ dr ++ s)
      (p ++ m ++ s) := by
  constructor
  · rcases hPrefix with hk | ⟨hdl, hk⟩
    · have hold := List.take_append_of_le_length
        (l₁ := p) (l₂ := dl ++ m ++ dr ++ s) hk
      have hnew := List.take_append_of_le_length
        (l₁ := p) (l₂ := m ++ s) hk
      exact hold.trans hnew.symm
    · have hold := List.take_append_of_le_length
        (l₁ := p ++ m) (l₂ := dr ++ s) hk
      have hnew := List.take_append_of_le_length
        (l₁ := p ++ m) (l₂ := s) hk
      simpa [hdl, List.append_assoc] using hold.trans hnew.symm
  · rcases hSuffix with hl | ⟨hdr, hl⟩
    · have hold := v60WindowSuffix_append_of_le
        l (p ++ dl ++ m ++ dr) s hl
      have hnew := v60WindowSuffix_append_of_le
        l (p ++ m) s hl
      simpa [List.append_assoc] using hold.trans hnew.symm
    · have hold := v60WindowSuffix_append_of_le
        l (p ++ dl) (m ++ s) hl
      have hnew := v60WindowSuffix_append_of_le
        l p (m ++ s) hl
      simpa [hdr, List.append_assoc] using hold.trans hnew.symm

/--
A repeated-label derivation-context cycle can therefore be removed while
preserving the fixed windows whenever the deleted left/right material satisfies
the corresponding protection conditions.
-/
theorem v60_repeated_label_shortcut_preserves_window
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (k l : Nat) {R X : N}
    (outer : V60DerivationContext terminal binary R X)
    (cycle : V60DerivationContext terminal binary X X)
    (t : V60DerivationTree terminal binary X)
    (hPrefix :
      k ≤ (V60DerivationContext.leftWord outer).length ∨
        (V60DerivationContext.leftWord cycle = [] ∧
          k ≤ (V60DerivationContext.leftWord outer ++
            V60DerivationTree.yield t).length))
    (hSuffix :
      l ≤ (V60DerivationContext.rightWord outer).length ∨
        (V60DerivationContext.rightWord cycle = [] ∧
          l ≤ (V60DerivationTree.yield t ++
            V60DerivationContext.rightWord outer).length)) :
    V60WindowBoundaryEq k l
      (V60DerivationTree.yield
        (V60DerivationContext.plug
          (V60DerivationContext.comp outer cycle) t))
      (V60DerivationTree.yield
        (V60DerivationContext.shortcut outer t)) := by
  rw [V60DerivationContext.yield_plug_comp_cycle]
  rw [V60DerivationContext.yield_shortcut]
  exact v60_window_boundary_eq_of_middle_deletion
    k l
    (V60DerivationContext.leftWord outer)
    (V60DerivationContext.leftWord cycle)
    (V60DerivationTree.yield t)
    (V60DerivationContext.rightWord cycle)
    (V60DerivationContext.rightWord outer)
    hPrefix hSuffix

/--
Interior protected-cycle form used most often in the marked skeleton: if the
whole first window is already outside the cycle on the left and the whole last
window is already outside it on the right, shortcutting preserves both windows,
keeps a valid derivation from the same root, keeps length at least `k+l`, and
strictly decreases the marked-spine depth.
-/
theorem v60_protected_repeated_label_shortcut
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (k l : Nat) {R X : N}
    (outer : V60DerivationContext terminal binary R X)
    (cycle : V60DerivationContext terminal binary X X)
    (t : V60DerivationTree terminal binary X)
    (hcycle : 0 < V60DerivationContext.depth cycle)
    (hk : k ≤ (V60DerivationContext.leftWord outer).length)
    (hl : l ≤ (V60DerivationContext.rightWord outer).length) :
    ∃ z : Word Sigma,
      V60UntypedDerives terminal binary R z ∧
      k + l ≤ z.length ∧
      V60WindowBoundaryEq k l
        (V60DerivationTree.yield
          (V60DerivationContext.plug
            (V60DerivationContext.comp outer cycle) t)) z ∧
      V60DerivationContext.depth outer <
        V60DerivationContext.depth
          (V60DerivationContext.comp outer cycle) := by
  let z := V60DerivationTree.yield
    (V60DerivationContext.shortcut outer t)
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · exact V60DerivationContext.shortcut_toUntypedDerives outer t
  · dsimp [z]
    rw [V60DerivationContext.yield_shortcut]
    simp only [List.length_append]
    omega
  · dsimp [z]
    exact v60_repeated_label_shortcut_preserves_window
      k l outer cycle t (Or.inl hk) (Or.inl hl)
  · exact V60DerivationContext.shortcut_depth_lt_of_cycle
      outer cycle hcycle

end FixedHCFG
end LeanCfgProject
