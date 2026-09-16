import Mathlib.Data.List.Nodup
import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V61NullableDerivation

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Cycle-free root-to-terminal spines for the v61 thickness-preserving
normalization proof.

The intermediate binary grammar of Appendix A may still contain epsilon rules,
so this file mirrors the exact structural argument of the earlier SSBNF spine
layer using `V61NullableDerivationTree`.  No positivity assumption is imposed
on off-path siblings: they may derive the empty word, exactly as required by
the v61 proof.
-/

inductive V61NullableDerivationSpine
    {N : Type v} {Sigma : Type u}
    (epsilon : V61EpsilonRules N)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N)
    (R : N) : N → List N → Type (max u v) where
  | root :
      V61NullableDerivationSpine epsilon terminal binary R R [R]
  | left {A B C : N} {sp : List N}
      (parent : V61NullableDerivationSpine epsilon terminal binary R A sp)
      (hrule : binary A B C)
      (rightTree : V61NullableDerivationTree epsilon terminal binary C) :
      V61NullableDerivationSpine epsilon terminal binary R B (sp.concat B)
  | right {A B C : N} {sp : List N}
      (parent : V61NullableDerivationSpine epsilon terminal binary R A sp)
      (hrule : binary A B C)
      (leftTree : V61NullableDerivationTree epsilon terminal binary B) :
      V61NullableDerivationSpine epsilon terminal binary R C (sp.concat C)

namespace V61NullableDerivationSpine

variable {N : Type v} {Sigma : Type u}
variable {epsilon : V61EpsilonRules N}
variable {terminal : V60TerminalRules N Sigma}
variable {binary : V60BinaryRules N}

/-- One binary edge selecting the left child. -/
def leftStep {A B C : N}
    (hrule : binary A B C)
    (rightTree : V61NullableDerivationTree epsilon terminal binary C) :
    V61NullableDerivationContext epsilon terminal binary A B :=
  .left A B C B hrule (.hole B) rightTree

/-- One binary edge selecting the right child. -/
def rightStep {A B C : N}
    (hrule : binary A B C)
    (leftTree : V61NullableDerivationTree epsilon terminal binary B) :
    V61NullableDerivationContext epsilon terminal binary A C :=
  .right A B C C hrule leftTree (.hole C)

/-- Composition of nullable one-hole contexts. -/
def comp {A B C : N}
    (outer : V61NullableDerivationContext epsilon terminal binary A B)
    (inner : V61NullableDerivationContext epsilon terminal binary B C) :
    V61NullableDerivationContext epsilon terminal binary A C :=
  match outer with
  | .hole _ => inner
  | .left A B D H hrule sub rightTree =>
      .left A B D C hrule (comp sub inner) rightTree
  | .right A B D H hrule leftTree sub =>
      .right A B D C hrule leftTree (comp sub inner)

/-- Nullable-context depths add under composition. -/
theorem depth_comp {A B C : N}
    (outer : V61NullableDerivationContext epsilon terminal binary A B)
    (inner : V61NullableDerivationContext epsilon terminal binary B C) :
    V61NullableDerivationContext.depth (comp outer inner) =
      V61NullableDerivationContext.depth outer +
        V61NullableDerivationContext.depth inner := by
  induction outer with
  | hole A => simp [comp, V61NullableDerivationContext.depth]
  | left A B D H hrule sub rightTree ih =>
      simp [comp, V61NullableDerivationContext.depth, ih,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | right A B D H hrule leftTree sub ih =>
      simp [comp, V61NullableDerivationContext.depth, ih,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Forget the remembered label list and recover the nullable one-hole context. -/
def toContext {R H : N} {sp : List N} :
    V61NullableDerivationSpine epsilon terminal binary R H sp →
      V61NullableDerivationContext epsilon terminal binary R H
  | .root => .hole R
  | .left parent hrule rightTree =>
      comp (toContext parent) (leftStep hrule rightTree)
  | .right parent hrule leftTree =>
      comp (toContext parent) (rightStep hrule leftTree)

/-- The label list contains one vertex more than the number of path edges. -/
theorem spine_length_eq_depth_add_one
    {R H : N} {sp : List N}
    (d : V61NullableDerivationSpine epsilon terminal binary R H sp) :
    sp.length = V61NullableDerivationContext.depth (toContext d) + 1 := by
  induction d with
  | root => simp [toContext, V61NullableDerivationContext.depth]
  | left parent hrule rightTree ih =>
      simp [toContext, leftStep, depth_comp,
        V61NullableDerivationContext.depth, ih, Nat.add_comm]
  | right parent hrule leftTree ih =>
      simp [toContext, rightStep, depth_comp,
        V61NullableDerivationContext.depth, ih, Nat.add_comm]

/-- Extend a forward spine through an ordinary nullable derivation context. -/
def appendContext
    {R A H : N} {sp : List N}
    (pre : V61NullableDerivationSpine epsilon terminal binary R A sp) :
    (ctx : V61NullableDerivationContext epsilon terminal binary A H) →
      Σ sp' : List N,
        V61NullableDerivationSpine epsilon terminal binary R H sp'
  | .hole _ => ⟨sp, pre⟩
  | .left A B C H hrule sub rightTree =>
      appendContext (.left pre hrule rightTree) sub
  | .right A B C H hrule leftTree sub =>
      appendContext (.right pre hrule leftTree) sub

/-- Every nullable derivation context has a forward-spine presentation. -/
def ofContext {A H : N}
    (ctx : V61NullableDerivationContext epsilon terminal binary A H) :
    Σ sp : List N,
      V61NullableDerivationSpine epsilon terminal binary A H sp :=
  appendContext (.root) ctx

/-- Any earlier label on a spine is reached by a prefix spine. -/
theorem prefix_of_mem_spine
    {R X Z : N} {sp : List N}
    (d : V61NullableDerivationSpine epsilon terminal binary R X sp)
    (hZ : Z ∈ sp) :
    ∃ sp' : List N,
      Nonempty (V61NullableDerivationSpine epsilon terminal binary R Z sp') ∧
        sp'.length ≤ sp.length := by
  induction d with
  | root =>
      simp only [List.mem_singleton] at hZ
      subst Z
      exact ⟨[R], ⟨V61NullableDerivationSpine.root⟩, le_rfl⟩
  | @left A B C sp parent hrule rightTree ih =>
      rw [List.concat_eq_append] at hZ
      rcases List.mem_append.mp hZ with hZ | hZB
      · obtain ⟨sp', ⟨hpre⟩, hlen⟩ := ih hZ
        refine ⟨sp', ⟨hpre⟩, ?_⟩
        simp only [List.length_concat]
        omega
      · have hEq : Z = B := List.mem_singleton.mp hZB
        subst Z
        exact ⟨sp.concat B,
          ⟨V61NullableDerivationSpine.left parent hrule rightTree⟩, le_rfl⟩
  | @right A B C sp parent hrule leftTree ih =>
      rw [List.concat_eq_append] at hZ
      rcases List.mem_append.mp hZ with hZ | hZC
      · obtain ⟨sp', ⟨hpre⟩, hlen⟩ := ih hZ
        refine ⟨sp', ⟨hpre⟩, ?_⟩
        simp only [List.length_concat]
        omega
      · have hEq : Z = C := List.mem_singleton.mp hZC
        subst Z
        exact ⟨sp.concat C,
          ⟨V61NullableDerivationSpine.right parent hrule leftTree⟩, le_rfl⟩

/-- A repeated base-nonterminal label can be deleted from a nullable spine. -/
theorem exists_shorter_spine_of_not_nodup
    {R X : N} {sp : List N}
    (d : V61NullableDerivationSpine epsilon terminal binary R X sp)
    (hdup : ¬ sp.Nodup) :
    ∃ sp' : List N,
      Nonempty (V61NullableDerivationSpine epsilon terminal binary R X sp') ∧
        sp'.length < sp.length := by
  induction d with
  | root =>
      exact (hdup (List.nodup_singleton R)).elim
  | @left A B C sp parent hrule rightTree ih =>
      by_cases hmem : B ∈ sp
      · obtain ⟨sp', ⟨hpre⟩, hlen⟩ := prefix_of_mem_spine parent hmem
        refine ⟨sp', ⟨hpre⟩, ?_⟩
        simp only [List.length_concat]
        omega
      · have hParentDup : ¬ sp.Nodup := by
          intro hnd
          exact hdup ((List.nodup_concat _ _).mpr ⟨hmem, hnd⟩)
        obtain ⟨sp', ⟨hshort⟩, hlen⟩ := ih hParentDup
        refine ⟨sp'.concat B,
          ⟨V61NullableDerivationSpine.left hshort hrule rightTree⟩, ?_⟩
        simp only [List.length_concat]
        omega
  | @right A B C sp parent hrule leftTree ih =>
      by_cases hmem : C ∈ sp
      · obtain ⟨sp', ⟨hpre⟩, hlen⟩ := prefix_of_mem_spine parent hmem
        refine ⟨sp', ⟨hpre⟩, ?_⟩
        simp only [List.length_concat]
        omega
      · have hParentDup : ¬ sp.Nodup := by
          intro hnd
          exact hdup ((List.nodup_concat _ _).mpr ⟨hmem, hnd⟩)
        obtain ⟨sp', ⟨hshort⟩, hlen⟩ := ih hParentDup
        refine ⟨sp'.concat C,
          ⟨V61NullableDerivationSpine.right hshort hrule leftTree⟩, ?_⟩
        simp only [List.length_concat]
        omega

/-- Every nullable forward spine has a cycle-free same-endpoint spine. -/
theorem exists_nodup_spine
    {R X : N} {sp : List N}
    (d : V61NullableDerivationSpine epsilon terminal binary R X sp) :
    ∃ sp' : List N,
      Nonempty (V61NullableDerivationSpine epsilon terminal binary R X sp') ∧
        sp'.Nodup := by
  classical
  let P : Nat → Prop := fun n =>
    ∃ sp' : List N,
      Nonempty (V61NullableDerivationSpine epsilon terminal binary R X sp') ∧
        sp'.length = n
  have hP : ∃ n, P n := ⟨sp.length, sp, ⟨d⟩, rfl⟩
  obtain ⟨sp0, hd0, hlen0⟩ := Nat.find_spec hP
  rcases hd0 with ⟨d0⟩
  refine ⟨sp0, ⟨d0⟩, ?_⟩
  by_contra hdup
  obtain ⟨sp1, hd1, hshort⟩ :=
    exists_shorter_spine_of_not_nodup d0 hdup
  have hP1 : P sp1.length := ⟨sp1, hd1, rfl⟩
  have hmin : Nat.find hP ≤ sp1.length := Nat.find_min' hP hP1
  rw [hlen0] at hshort
  omega

/-- Every nullable context admits a same-root/same-hole simple spine. -/
theorem exists_nodup_spine_of_context
    {A H : N}
    (ctx : V61NullableDerivationContext epsilon terminal binary A H) :
    ∃ sp : List N,
      Nonempty (V61NullableDerivationSpine epsilon terminal binary A H sp) ∧
        sp.Nodup := by
  classical
  rcases ofContext ctx with ⟨sp, d⟩
  exact exists_nodup_spine d

/--
Finite-state path bound needed in Appendix A: after deleting cycles, a
root-to-terminal path uses at most one occurrence of each base nonterminal.
-/
theorem exists_context_with_depth_succ_le_card
    [Fintype N]
    {A H : N}
    (ctx : V61NullableDerivationContext epsilon terminal binary A H) :
    ∃ ctx' : V61NullableDerivationContext epsilon terminal binary A H,
      V61NullableDerivationContext.depth ctx' + 1 ≤ Fintype.card N := by
  obtain ⟨sp, ⟨d⟩, hnd⟩ := exists_nodup_spine_of_context ctx
  refine ⟨toContext d, ?_⟩
  have hlen : sp.length ≤ Fintype.card N := hnd.length_le_card
  rw [spine_length_eq_depth_add_one d] at hlen
  exact hlen

end V61NullableDerivationSpine

end FixedHCFG
end LeanCfgProject
