import LeanCfgProject.FixedHCFG.V61NullableShortening

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Epsilon elimination for the intermediate grammar in Appendix A of TCS v61.
The source grammar may have epsilon, terminal, unit, and binary rules.  The
post-elimination grammar retains terminal and binary rules and adds the usual
unit variants of binary rules whose opposite child is nullable.  The theorem
below proves equality of every nonterminal's nonempty terminal language.
-/

def V61Nullable
    {N : Type v} {Sigma : Type u}
    (epsilon : V61EpsilonRules N)
    (terminal : V60TerminalRules N Sigma)
    (unit : V61UnitRules N)
    (binary : V60BinaryRules N)
    (A : N) : Prop :=
  ∃ t : V61NullableDerivationTree epsilon terminal unit binary A,
    V61NullableDerivationTree.yield t = []

/-- Unit rules after deleting non-start epsilon rules. -/
def V61EpsElimUnit
    {N : Type v} {Sigma : Type u}
    (epsilon : V61EpsilonRules N)
    (terminal : V60TerminalRules N Sigma)
    (unit : V61UnitRules N)
    (binary : V60BinaryRules N) : V61UnitRules N :=
  fun A B =>
    unit A B ∨
      (∃ C : N, binary A B C ∧
        V61Nullable epsilon terminal unit binary C) ∨
      (∃ C : N, binary A C B ∧
        V61Nullable epsilon terminal unit binary C)

/-- Epsilon-free tree type produced by the standard nullable-child expansion. -/
abbrev V61EpsFreeTree
    {N : Type v} {Sigma : Type u}
    (epsilon : V61EpsilonRules N)
    (terminal : V60TerminalRules N Sigma)
    (unit : V61UnitRules N)
    (binary : V60BinaryRules N)
    (A : N) :=
  V61NullableDerivationTree (fun _ : N => False) terminal
    (V61EpsElimUnit epsilon terminal unit binary) binary A

/-- A post-elimination tree cannot have empty terminal frontier. -/
theorem v61_eps_free_yield_ne_nil
    {N : Type v} {Sigma : Type u}
    {epsilon : V61EpsilonRules N}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    {A : N}
    (t : V61EpsFreeTree epsilon terminal unit binary A) :
    V61NullableDerivationTree.yield t ≠ [] := by
  induction t with
  | epsilon A hfalse => exact hfalse.elim
  | terminal A a hrule => simp [V61NullableDerivationTree.yield]
  | unit A B hrule sub ih => simpa [V61NullableDerivationTree.yield] using ih
  | binary A B C hrule left right ihLeft ihRight =>
      intro hnil
      have hlen :
          (V61NullableDerivationTree.yield left).length +
            (V61NullableDerivationTree.yield right).length = 0 := by
        simpa [V61NullableDerivationTree.yield, List.length_append] using
          congrArg List.length hnil
      have hleft0 : (V61NullableDerivationTree.yield left).length = 0 := by omega
      apply ihLeft
      simpa using hleft0

/-- Forward simulation: every nonempty source derivation survives epsilon elimination. -/
theorem v61_epsilon_elim_forward
    {N : Type v} {Sigma : Type u}
    {epsilon : V61EpsilonRules N}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    {A : N}
    (t : V61NullableDerivationTree epsilon terminal unit binary A)
    (hNonempty : V61NullableDerivationTree.yield t ≠ []) :
    ∃ t' : V61EpsFreeTree epsilon terminal unit binary A,
      V61NullableDerivationTree.yield t' =
        V61NullableDerivationTree.yield t := by
  induction t with
  | epsilon A hrule => exact (hNonempty rfl).elim
  | terminal A a hrule =>
      exact ⟨.terminal A a hrule, rfl⟩
  | unit A B hrule sub ih =>
      obtain ⟨sub', hsub⟩ := ih hNonempty
      refine ⟨.unit A B (Or.inl hrule) sub', ?_⟩
      simpa [V61NullableDerivationTree.yield] using hsub
  | binary A B C hrule left right ihLeft ihRight =>
      by_cases hLeft : V61NullableDerivationTree.yield left = []
      · by_cases hRight : V61NullableDerivationTree.yield right = []
        · apply False.elim
          apply hNonempty
          simp [V61NullableDerivationTree.yield, hLeft, hRight]
        · obtain ⟨right', hright⟩ := ihRight hRight
          have hNullableLeft : V61Nullable epsilon terminal unit binary B :=
            ⟨left, hLeft⟩
          have hUnit : V61EpsElimUnit epsilon terminal unit binary A C :=
            Or.inr (Or.inr ⟨B, hrule, hNullableLeft⟩)
          refine ⟨.unit A C hUnit right', ?_⟩
          simp [V61NullableDerivationTree.yield, hLeft, hright]
      · by_cases hRight : V61NullableDerivationTree.yield right = []
        · obtain ⟨left', hleft⟩ := ihLeft hLeft
          have hNullableRight : V61Nullable epsilon terminal unit binary C :=
            ⟨right, hRight⟩
          have hUnit : V61EpsElimUnit epsilon terminal unit binary A B :=
            Or.inr (Or.inl ⟨C, hrule, hNullableRight⟩)
          refine ⟨.unit A B hUnit left', ?_⟩
          simp [V61NullableDerivationTree.yield, hRight, hleft]
        · obtain ⟨left', hleft⟩ := ihLeft hLeft
          obtain ⟨right', hright⟩ := ihRight hRight
          refine ⟨.binary A B C hrule left' right', ?_⟩
          simp [V61NullableDerivationTree.yield, hleft, hright]

/-- Reverse simulation: every epsilon-eliminated derivation is a source derivation. -/
theorem v61_epsilon_elim_reverse
    {N : Type v} {Sigma : Type u}
    {epsilon : V61EpsilonRules N}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    {A : N}
    (t : V61EpsFreeTree epsilon terminal unit binary A) :
    ∃ t' : V61NullableDerivationTree epsilon terminal unit binary A,
      V61NullableDerivationTree.yield t' =
        V61NullableDerivationTree.yield t := by
  induction t with
  | epsilon A hfalse => exact hfalse.elim
  | terminal A a hrule =>
      exact ⟨.terminal A a hrule, rfl⟩
  | unit A B hrule sub ih =>
      obtain ⟨sub', hsub⟩ := ih
      rcases hrule with horig | hderived
      · refine ⟨.unit A B horig sub', ?_⟩
        simpa [V61NullableDerivationTree.yield] using hsub
      · rcases hderived with hRightNullable | hLeftNullable
        · obtain ⟨C, hbin, hnullable⟩ := hRightNullable
          obtain ⟨right, hright⟩ := hnullable
          refine ⟨.binary A B C hbin sub' right, ?_⟩
          simp [V61NullableDerivationTree.yield, hsub, hright]
        · obtain ⟨C, hbin, hnullable⟩ := hLeftNullable
          obtain ⟨left, hleft⟩ := hnullable
          refine ⟨.binary A C B hbin left sub', ?_⟩
          simp [V61NullableDerivationTree.yield, hsub, hleft]
  | binary A B C hrule left right ihLeft ihRight =>
      obtain ⟨left', hleft⟩ := ihLeft
      obtain ⟨right', hright⟩ := ihRight
      refine ⟨.binary A B C hrule left' right', ?_⟩
      simp [V61NullableDerivationTree.yield, hleft, hright]

/-- Exact preservation of each nonterminal's nonempty terminal language. -/
theorem v61_epsilon_elim_nonempty_language_iff
    {N : Type v} {Sigma : Type u}
    {epsilon : V61EpsilonRules N}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    {A : N} {w : Word Sigma}
    (hw : w ≠ []) :
    (∃ t : V61NullableDerivationTree epsilon terminal unit binary A,
        V61NullableDerivationTree.yield t = w) ↔
      (∃ t : V61EpsFreeTree epsilon terminal unit binary A,
        V61NullableDerivationTree.yield t = w) := by
  constructor
  · rintro ⟨t, ht⟩
    have hNonempty : V61NullableDerivationTree.yield t ≠ [] := by
      rw [ht]
      exact hw
    obtain ⟨t', ht'⟩ := v61_epsilon_elim_forward t hNonempty
    exact ⟨t', ht'.trans ht⟩
  · rintro ⟨t, ht⟩
    obtain ⟨t', ht'⟩ := v61_epsilon_elim_reverse t
    exact ⟨t', ht'.trans ht⟩

/--
The short-nonempty-yield bound from the nullable grammar transfers unchanged
across epsilon elimination.  This is the quantitative sentence used in the
v61 normalization proof before unit closure is computed.
-/
theorem v61_epsilon_elim_short_nonempty_bound
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    {epsilon : V61EpsilonRules N}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    (tau : Nat)
    (hThickness : V61NullableThicknessBound epsilon terminal unit binary tau)
    {A : N}
    (t : V61EpsFreeTree epsilon terminal unit binary A) :
    ∃ t' : V61EpsFreeTree epsilon terminal unit binary A,
      (V61NullableDerivationTree.yield t').length ≤
        1 + Fintype.card N * tau := by
  have hTargetNonempty := v61_eps_free_yield_ne_nil t
  obtain ⟨source, hsource⟩ := v61_epsilon_elim_reverse t
  have hSourceNonempty : V61NullableDerivationTree.yield source ≠ [] := by
    rw [hsource]
    exact hTargetNonempty
  obtain ⟨shortSource, hShortNonempty, hShortBound⟩ :=
    v61_exists_short_nonempty_tree tau hThickness source hSourceNonempty
  obtain ⟨shortTarget, hsame⟩ :=
    v61_epsilon_elim_forward shortSource hShortNonempty
  refine ⟨shortTarget, ?_⟩
  rw [hsame]
  exact hShortBound

end FixedHCFG
end LeanCfgProject
