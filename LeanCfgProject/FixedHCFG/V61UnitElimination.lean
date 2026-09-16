import LeanCfgProject.FixedHCFG.V61EpsilonElimination

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Unit-closure elimination for Appendix A of TCS revision v61.

After non-start epsilon elimination, the manuscript computes unit closure and
copies every unit-reachable non-unit production to its source.  This file
formalizes that construction at derivation-tree level and proves that every
nonterminal language, hence the quantitative shortest-yield bound, is
preserved.
-/

/-- Reflexive-transitive closure of unit productions. -/
inductive V61UnitClosure {N : Type v}
    (unit : V61UnitRules N) : N → N → Prop where
  | refl (A : N) : V61UnitClosure unit A A
  | step {A B C : N} (hrule : unit A B)
      (rest : V61UnitClosure unit B C) :
      V61UnitClosure unit A C

namespace V61UnitClosure

variable {N : Type v} {unit : V61UnitRules N}

/-- Unit closure is transitive. -/
theorem trans {A B C : N}
    (hAB : V61UnitClosure unit A B)
    (hBC : V61UnitClosure unit B C) :
    V61UnitClosure unit A C := by
  induction hAB with
  | refl A => exact hBC
  | step hrule rest ih => exact .step hrule (ih hBC)

end V61UnitClosure

/-- Terminal rules copied through unit closure. -/
def V61UnitFreeTerminal
    {N : Type v} {Sigma : Type u}
    (terminal : V60TerminalRules N Sigma)
    (unit : V61UnitRules N) : V60TerminalRules N Sigma :=
  fun A a => ∃ B : N, V61UnitClosure unit A B ∧ terminal B a

/-- Binary rules copied through unit closure. -/
def V61UnitFreeBinary
    {N : Type v}
    (unit : V61UnitRules N)
    (binary : V60BinaryRules N) : V60BinaryRules N :=
  fun A B C => ∃ D : N, V61UnitClosure unit A D ∧ binary D B C

/-- Epsilon-free source grammar before unit elimination. -/
abbrev V61UnitSourceTree
    {N : Type v} {Sigma : Type u}
    (terminal : V60TerminalRules N Sigma)
    (unit : V61UnitRules N)
    (binary : V60BinaryRules N)
    (A : N) :=
  V61NullableDerivationTree (fun _ : N => False) terminal unit binary A

/-- Unit-free grammar obtained by copying unit-reachable terminal/binary rules. -/
abbrev V61UnitFreeTree
    {N : Type v} {Sigma : Type u}
    (terminal : V60TerminalRules N Sigma)
    (unit : V61UnitRules N)
    (binary : V60BinaryRules N)
    (A : N) :=
  V61NullableDerivationTree (fun _ : N => False)
    (V61UnitFreeTerminal terminal unit) (fun _ _ : N => False)
    (V61UnitFreeBinary unit binary) A

/-- Wrap a source derivation by a unit-closure path. -/
theorem v61_unit_wrap_source
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    {A B : N}
    (hAB : V61UnitClosure unit A B)
    (t : V61UnitSourceTree terminal unit binary B) :
    ∃ t' : V61UnitSourceTree terminal unit binary A,
      V61NullableDerivationTree.yield t' =
        V61NullableDerivationTree.yield t := by
  induction hAB with
  | refl A => exact ⟨t, rfl⟩
  | @step A B C hrule rest ih =>
      obtain ⟨tB, htB⟩ := ih t
      refine ⟨.unit A B hrule tB, ?_⟩
      simpa [V61NullableDerivationTree.yield] using htB

/--
Prepending one source unit edge to a unit-free target derivation is absorbed
into the copied root production.
-/
theorem v61_unit_prepend_target
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    {A B : N}
    (hAB : unit A B)
    (t : V61UnitFreeTree terminal unit binary B) :
    ∃ t' : V61UnitFreeTree terminal unit binary A,
      V61NullableDerivationTree.yield t' =
        V61NullableDerivationTree.yield t := by
  cases t with
  | epsilon B hfalse => exact hfalse.elim
  | terminal B a hcopy =>
      obtain ⟨D, hBD, hterm⟩ := hcopy
      have hAD : V61UnitClosure unit A D :=
        .step hAB hBD
      exact ⟨.terminal A a ⟨D, hAD, hterm⟩, rfl⟩
  | unit B C hfalse sub => exact hfalse.elim
  | binary B C D hcopy left right =>
      obtain ⟨E, hBE, hbin⟩ := hcopy
      have hAE : V61UnitClosure unit A E :=
        .step hAB hBE
      exact ⟨.binary A C D ⟨E, hAE, hbin⟩ left right, rfl⟩

/-- Forward simulation of unit elimination. -/
theorem v61_unit_elim_forward
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    {A : N}
    (t : V61UnitSourceTree terminal unit binary A) :
    ∃ t' : V61UnitFreeTree terminal unit binary A,
      V61NullableDerivationTree.yield t' =
        V61NullableDerivationTree.yield t := by
  induction t with
  | epsilon A hfalse => exact hfalse.elim
  | terminal A a hrule =>
      exact ⟨.terminal A a ⟨A, .refl A, hrule⟩, rfl⟩
  | unit A B hrule sub ih =>
      obtain ⟨sub', hsub⟩ := ih
      obtain ⟨t', ht'⟩ := v61_unit_prepend_target hrule sub'
      refine ⟨t', ?_⟩
      rw [ht', hsub]
      rfl
  | binary A B C hrule left right ihLeft ihRight =>
      obtain ⟨left', hleft⟩ := ihLeft
      obtain ⟨right', hright⟩ := ihRight
      refine ⟨.binary A B C ⟨A, .refl A, hrule⟩ left' right', ?_⟩
      simp [V61NullableDerivationTree.yield, hleft, hright]

/-- Reverse simulation of unit elimination. -/
theorem v61_unit_elim_reverse
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    {A : N}
    (t : V61UnitFreeTree terminal unit binary A) :
    ∃ t' : V61UnitSourceTree terminal unit binary A,
      V61NullableDerivationTree.yield t' =
        V61NullableDerivationTree.yield t := by
  induction t with
  | epsilon A hfalse => exact hfalse.elim
  | terminal A a hcopy =>
      obtain ⟨B, hAB, hterm⟩ := hcopy
      let leaf : V61UnitSourceTree terminal unit binary B :=
        .terminal B a hterm
      obtain ⟨t', ht'⟩ := v61_unit_wrap_source hAB leaf
      refine ⟨t', ?_⟩
      simpa [leaf, V61NullableDerivationTree.yield] using ht'
  | unit A B hfalse sub => exact hfalse.elim
  | binary A B C hcopy left right ihLeft ihRight =>
      obtain ⟨D, hAD, hbin⟩ := hcopy
      obtain ⟨left', hleft⟩ := ihLeft
      obtain ⟨right', hright⟩ := ihRight
      let root : V61UnitSourceTree terminal unit binary D :=
        .binary D B C hbin left' right'
      obtain ⟨t', ht'⟩ := v61_unit_wrap_source hAD root
      refine ⟨t', ?_⟩
      rw [ht']
      simp [root, V61NullableDerivationTree.yield, hleft, hright]

/-- Unit elimination preserves every nonterminal terminal language exactly. -/
theorem v61_unit_elim_language_iff
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    {A : N} {w : Word Sigma} :
    (∃ t : V61UnitSourceTree terminal unit binary A,
        V61NullableDerivationTree.yield t = w) ↔
      (∃ t : V61UnitFreeTree terminal unit binary A,
        V61NullableDerivationTree.yield t = w) := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨t', ht'⟩ := v61_unit_elim_forward t
    exact ⟨t', ht'.trans ht⟩
  · rintro ⟨t, ht⟩
    obtain ⟨t', ht'⟩ := v61_unit_elim_reverse t
    exact ⟨t', ht'.trans ht⟩

/--
Quantitative Appendix A consequence: after epsilon elimination followed by
unit-closure elimination, every productive nonterminal still has a terminal
yield of length at most `1 + |N| * tau`.
-/
theorem v61_unit_elim_short_bound_after_epsilon
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    {epsilon : V61EpsilonRules N}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    (tau : Nat)
    (hThickness : V61NullableThicknessBound epsilon terminal unit binary tau)
    {A : N}
    (t : V61UnitFreeTree terminal
      (V61EpsElimUnit epsilon terminal unit binary) binary A) :
    ∃ t' : V61UnitFreeTree terminal
        (V61EpsElimUnit epsilon terminal unit binary) binary A,
      (V61NullableDerivationTree.yield t').length ≤
        1 + Fintype.card N * tau := by
  obtain ⟨epsTree, heps⟩ := v61_unit_elim_reverse t
  obtain ⟨shortEps, hShort⟩ :=
    v61_epsilon_elim_short_nonempty_bound tau hThickness epsTree
  obtain ⟨shortUnitFree, hsame⟩ := v61_unit_elim_forward shortEps
  refine ⟨shortUnitFree, ?_⟩
  rw [hsame]
  exact hShort

end FixedHCFG
end LeanCfgProject
