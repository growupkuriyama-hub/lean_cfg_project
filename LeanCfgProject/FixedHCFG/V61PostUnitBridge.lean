import LeanCfgProject.FixedHCFG.V61UnitElimination
import LeanCfgProject.FixedHCFG.V60DerivationTree

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Bridge from the v61 normalization pipeline back to the exact SSBNF derivation
model used by the fixed-window development.

After epsilon and unit elimination, the remaining non-start productions are
exactly terminal and binary productions.  Hence the unit-free v61 trees are
literally equivalent to `V60DerivationTree` over the copied rule relations.
This file packages that equivalence and transports the Appendix A thickness
bound into `V60BaseThicknessBound`.
-/

/-- Forget the impossible epsilon/unit constructors of a unit-free v61 tree. -/
def v61UnitFreeToV60
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    {A : N} :
    V61UnitFreeTree terminal unit binary A →
      V60DerivationTree (V61UnitFreeTerminal terminal unit)
        (V61UnitFreeBinary unit binary) A
  | .epsilon _ hfalse => hfalse.elim
  | .terminal A a hrule => .terminal A a hrule
  | .unit _ _ hfalse _ => hfalse.elim
  | .binary A B C hrule left right =>
      .binary A B C hrule (v61UnitFreeToV60 left) (v61UnitFreeToV60 right)

/-- Re-embed an exact terminal/binary tree as a unit-free v61 tree. -/
def v60ToV61UnitFree
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    {A : N} :
    V60DerivationTree (V61UnitFreeTerminal terminal unit)
        (V61UnitFreeBinary unit binary) A →
      V61UnitFreeTree terminal unit binary A
  | .terminal A a hrule => .terminal A a hrule
  | .binary A B C hrule left right =>
      .binary A B C hrule (v60ToV61UnitFree left) (v60ToV61UnitFree right)

/-- The forward bridge preserves the terminal frontier. -/
theorem v61UnitFreeToV60_yield
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    {A : N}
    (t : V61UnitFreeTree terminal unit binary A) :
    V60DerivationTree.yield (v61UnitFreeToV60 t) =
      V61NullableDerivationTree.yield t := by
  induction t with
  | epsilon A hfalse => exact hfalse.elim
  | terminal A a hrule => rfl
  | unit A B hfalse sub => exact hfalse.elim
  | binary A B C hrule left right ihLeft ihRight =>
      simp [v61UnitFreeToV60, V60DerivationTree.yield,
        V61NullableDerivationTree.yield, ihLeft, ihRight]

/-- The reverse bridge preserves the terminal frontier. -/
theorem v60ToV61UnitFree_yield
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    {A : N}
    (t : V60DerivationTree (V61UnitFreeTerminal terminal unit)
        (V61UnitFreeBinary unit binary) A) :
    V61NullableDerivationTree.yield (v60ToV61UnitFree t) =
      V60DerivationTree.yield t := by
  induction t with
  | terminal A a hrule => rfl
  | binary A B C hrule left right ihLeft ihRight =>
      simp [v60ToV61UnitFree, V60DerivationTree.yield,
        V61NullableDerivationTree.yield, ihLeft, ihRight]

/--
The quantitative result of epsilon plus unit elimination, expressed in the
exact base-thickness interface already consumed by the fixed-window proof.
-/
theorem v61_post_unit_base_thickness_bound
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    {epsilon : V61EpsilonRules N}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    (tau : Nat)
    (hThickness : V61NullableThicknessBound epsilon terminal unit binary tau) :
    V60BaseThicknessBound
      (V61UnitFreeTerminal terminal
        (V61EpsElimUnit epsilon terminal unit binary))
      (V61UnitFreeBinary
        (V61EpsElimUnit epsilon terminal unit binary) binary)
      (1 + Fintype.card N * tau) := by
  intro A hProductive
  obtain ⟨w, dw⟩ := hProductive
  obtain ⟨tree, htree⟩ := V60DerivationTree.exists_tree_of_untyped_derives dw
  let unitTree : V61UnitFreeTree terminal
      (V61EpsElimUnit epsilon terminal unit binary) binary A :=
    v60ToV61UnitFree tree
  obtain ⟨shortUnitTree, hShort⟩ :=
    v61_unit_elim_short_bound_after_epsilon tau hThickness unitTree
  let shortTree := v61UnitFreeToV60 shortUnitTree
  refine ⟨V60DerivationTree.yield shortTree,
    V60DerivationTree.toUntypedDerives shortTree, ?_⟩
  rw [v61UnitFreeToV60_yield]
  exact hShort

/-- Arithmetic form of the polynomial Appendix A thickness envelope. -/
theorem v61_normalization_thickness_arithmetic
    (Ncard tau n tauR cN cTau : Nat)
    (hCard : Ncard ≤ cN * n)
    (hTau : tau ≤ cTau * n * (tauR + 1)) :
    1 + Ncard * tau ≤
      1 + (cN * cTau) * n * n * (tauR + 1) := by
  calc
    1 + Ncard * tau ≤
        1 + (cN * n) * (cTau * n * (tauR + 1)) :=
      Nat.add_le_add_left (Nat.mul_le_mul hCard hTau) 1
    _ = 1 + (cN * cTau) * n * n * (tauR + 1) := by ring

/--
If terminal isolation/binarization supply the manuscript's linear state and
thickness bounds, the post-unit SSBNF core has the advertised polynomial
thickness bound.
-/
theorem v61_post_unit_polynomial_base_thickness
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    {epsilon : V61EpsilonRules N}
    {terminal : V60TerminalRules N Sigma}
    {unit : V61UnitRules N}
    {binary : V60BinaryRules N}
    (tau n tauR cN cTau : Nat)
    (hThickness : V61NullableThicknessBound epsilon terminal unit binary tau)
    (hCard : Fintype.card N ≤ cN * n)
    (hTau : tau ≤ cTau * n * (tauR + 1)) :
    V60BaseThicknessBound
      (V61UnitFreeTerminal terminal
        (V61EpsElimUnit epsilon terminal unit binary))
      (V61UnitFreeBinary
        (V61EpsElimUnit epsilon terminal unit binary) binary)
      (1 + (cN * cTau) * n * n * (tauR + 1)) := by
  have hBase := v61_post_unit_base_thickness_bound tau hThickness
  have hBound := v61_normalization_thickness_arithmetic
    (Fintype.card N) tau n tauR cN cTau hCard hTau
  intro A hProductive
  obtain ⟨z, dz, hz⟩ := hBase A hProductive
  exact ⟨z, dz, le_trans hz hBound⟩

end FixedHCFG
end LeanCfgProject
