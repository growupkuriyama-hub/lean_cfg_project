import Mathlib.Data.List.Nodup
import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60SiblingShortening

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Forward derivation spines for the chain-shortening part of manuscript Lemma
`window-typed-yield`.

`V60DerivationContext` is convenient for plugging trees, but it is oriented
from the root toward a pre-existing hole.  For cycle deletion it is more useful
to build the distinguished path one edge at a time and remember its sequence of
base nonterminal labels.  The type below is exactly that forward presentation.

The main result of this file is structural: every derivation context admits a
same-endpoint context whose root-to-hole label list is duplicate-free.  Hence,
for a finite base nonterminal set, every maximal unary chain can be represented
using at most `|N|` nonterminal vertices.  Boundary preservation is handled
separately by `V60WindowShortcut`.
-/

inductive V60DerivationSpine
    {N : Type v} {Sigma : Type u}
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N)
    (R : N) : N → List N → Type (max u v) where
  | root : V60DerivationSpine terminal binary R R [R]
  | left {A B C : N} {sp : List N}
      (parent : V60DerivationSpine terminal binary R A sp)
      (hrule : binary A B C)
      (rightTree : V60DerivationTree terminal binary C) :
      V60DerivationSpine terminal binary R B (sp.concat B)
  | right {A B C : N} {sp : List N}
      (parent : V60DerivationSpine terminal binary R A sp)
      (hrule : binary A B C)
      (leftTree : V60DerivationTree terminal binary B) :
      V60DerivationSpine terminal binary R C (sp.concat C)

namespace V60DerivationSpine

variable {N : Type v} {Sigma : Type u}
variable {terminal : V60TerminalRules N Sigma}
variable {binary : V60BinaryRules N}

/-- The one-edge context selecting the left child of a binary rule. -/
def leftStep {A B C : N}
    (hrule : binary A B C)
    (rightTree : V60DerivationTree terminal binary C) :
    V60DerivationContext terminal binary A B :=
  .left A B C B hrule (.hole B) rightTree

/-- The one-edge context selecting the right child of a binary rule. -/
def rightStep {A B C : N}
    (hrule : binary A B C)
    (leftTree : V60DerivationTree terminal binary B) :
    V60DerivationContext terminal binary A C :=
  .right A B C C hrule leftTree (.hole C)

/-- Forget the remembered label list and recover the ordinary one-hole context. -/
def toContext {R H : N} {sp : List N} :
    V60DerivationSpine terminal binary R H sp →
      V60DerivationContext terminal binary R H
  | .root => .hole R
  | .left parent hrule rightTree =>
      V60DerivationContext.comp (toContext parent)
        (leftStep hrule rightTree)
  | .right parent hrule leftTree =>
      V60DerivationContext.comp (toContext parent)
        (rightStep hrule leftTree)

/-- The remembered label list has one vertex more than the number of edges. -/
theorem spine_length_eq_depth_add_one
    {R H : N} {sp : List N}
    (d : V60DerivationSpine terminal binary R H sp) :
    sp.length = V60DerivationContext.depth (toContext d) + 1 := by
  induction d with
  | root => simp [toContext, V60DerivationContext.depth]
  | left parent hrule rightTree ih =>
      simp [toContext, leftStep, V60DerivationContext.depth_comp,
        V60DerivationContext.depth, List.length_concat, ih,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | right parent hrule leftTree ih =>
      simp [toContext, rightStep, V60DerivationContext.depth_comp,
        V60DerivationContext.depth, List.length_concat, ih,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/--
Continue an already-built forward spine through an ordinary derivation context.
This gives a constructive equivalence in the direction needed below.
-/
def appendContext
    {R A H : N} {sp : List N}
    (prefix : V60DerivationSpine terminal binary R A sp) :
    (ctx : V60DerivationContext terminal binary A H) →
      Σ sp' : List N, V60DerivationSpine terminal binary R H sp'
  | .hole _ => ⟨sp, prefix⟩
  | .left A B C H hrule sub rightTree =>
      appendContext (.left prefix hrule rightTree) sub
  | .right A B C H hrule leftTree sub =>
      appendContext (.right prefix hrule leftTree) sub

/-- Every ordinary derivation context has a forward-spine presentation. -/
def ofContext {A H : N}
    (ctx : V60DerivationContext terminal binary A H) :
    Σ sp : List N, V60DerivationSpine terminal binary A H sp :=
  appendContext (.root) ctx

/-- Any label occurring earlier on a spine is itself reached by a prefix spine. -/
theorem prefix_of_mem_spine
    {R X Z : N} {sp : List N}
    (d : V60DerivationSpine terminal binary R X sp)
    (hZ : Z ∈ sp) :
    ∃ sp' : List N,
      V60DerivationSpine terminal binary R Z sp' ∧
        sp'.length ≤ sp.length := by
  induction d with
  | @root R =>
      simp only [List.mem_singleton] at hZ
      subst Z
      exact ⟨[R], V60DerivationSpine.root, le_rfl⟩
  | @left A B C sp parent hrule rightTree ih =>
      rw [List.concat_eq_append] at hZ
      rcases List.mem_append.mp hZ with hZ | hZB
      · obtain ⟨sp', hpre, hlen⟩ := ih hZ
        refine ⟨sp', hpre, ?_⟩
        simp only [List.length_concat]
        omega
      · have hEq : Z = B := List.mem_singleton.mp hZB
        subst Z
        exact ⟨sp.concat B,
          V60DerivationSpine.left parent hrule rightTree, le_rfl⟩
  | @right A B C sp parent hrule leftTree ih =>
      rw [List.concat_eq_append] at hZ
      rcases List.mem_append.mp hZ with hZ | hZC
      · obtain ⟨sp', hpre, hlen⟩ := ih hZ
        refine ⟨sp', hpre, ?_⟩
        simp only [List.length_concat]
        omega
      · have hEq : Z = C := List.mem_singleton.mp hZC
        subst Z
        exact ⟨sp.concat C,
          V60DerivationSpine.right parent hrule leftTree, le_rfl⟩

/-- A repeated base-nonterminal label can be deleted from a forward spine. -/
theorem exists_shorter_spine_of_not_nodup
    {R X : N} {sp : List N}
    (d : V60DerivationSpine terminal binary R X sp)
    (hdup : ¬ sp.Nodup) :
    ∃ sp' : List N,
      V60DerivationSpine terminal binary R X sp' ∧
        sp'.length < sp.length := by
  induction d with
  | @root R =>
      exact (hdup (List.nodup_singleton R)).elim
  | @left A B C sp parent hrule rightTree ih =>
      by_cases hmem : B ∈ sp
      · obtain ⟨sp', hpre, hlen⟩ := prefix_of_mem_spine parent hmem
        refine ⟨sp', hpre, ?_⟩
        simp only [List.length_concat]
        omega
      · have hParentDup : ¬ sp.Nodup := by
          intro hnd
          exact hdup ((List.nodup_concat _ _).mpr ⟨hmem, hnd⟩)
        obtain ⟨sp', hshort, hlen⟩ := ih hParentDup
        refine ⟨sp'.concat B,
          V60DerivationSpine.left hshort hrule rightTree, ?_⟩
        simp only [List.length_concat]
        omega
  | @right A B C sp parent hrule leftTree ih =>
      by_cases hmem : C ∈ sp
      · obtain ⟨sp', hpre, hlen⟩ := prefix_of_mem_spine parent hmem
        refine ⟨sp', hpre, ?_⟩
        simp only [List.length_concat]
        omega
      · have hParentDup : ¬ sp.Nodup := by
          intro hnd
          exact hdup ((List.nodup_concat _ _).mpr ⟨hmem, hnd⟩)
        obtain ⟨sp', hshort, hlen⟩ := ih hParentDup
        refine ⟨sp'.concat C,
          V60DerivationSpine.right hshort hrule leftTree, ?_⟩
        simp only [List.length_concat]
        omega

/-- Every forward spine has a cycle-free same-endpoint spine. -/
theorem exists_nodup_spine
    {R X : N} {sp : List N}
    (d : V60DerivationSpine terminal binary R X sp) :
    ∃ sp' : List N,
      V60DerivationSpine terminal binary R X sp' ∧ sp'.Nodup := by
  classical
  let P : Nat → Prop := fun n =>
    ∃ sp' : List N,
      V60DerivationSpine terminal binary R X sp' ∧ sp'.length = n
  have hP : ∃ n, P n := ⟨sp.length, sp, d, rfl⟩
  obtain ⟨sp0, d0, hlen0⟩ := Nat.find_spec hP
  refine ⟨sp0, d0, ?_⟩
  by_contra hdup
  obtain ⟨sp1, d1, hshort⟩ :=
    exists_shorter_spine_of_not_nodup d0 hdup
  have hP1 : P sp1.length := ⟨sp1, d1, rfl⟩
  have hmin : Nat.find hP ≤ sp1.length := Nat.find_min' hP hP1
  rw [hlen0] at hshort
  omega

/--
Every derivation context therefore admits a same-root/same-hole context whose
root-to-hole chain is simple.
-/
theorem exists_nodup_spine_of_context
    {A H : N}
    (ctx : V60DerivationContext terminal binary A H) :
    ∃ sp : List N,
      V60DerivationSpine terminal binary A H sp ∧ sp.Nodup := by
  classical
  rcases ofContext ctx with ⟨sp, d⟩
  exact exists_nodup_spine d

/--
Finite-state chain bound used by every block of the marked skeleton: a simple
root-to-hole chain contains at most `|N|` nonterminal vertices.
-/
theorem exists_context_with_depth_succ_le_card
    [Fintype N]
    {A H : N}
    (ctx : V60DerivationContext terminal binary A H) :
    ∃ ctx' : V60DerivationContext terminal binary A H,
      V60DerivationContext.depth ctx' + 1 ≤ Fintype.card N := by
  obtain ⟨sp, d, hnd⟩ := exists_nodup_spine_of_context ctx
  refine ⟨toContext d, ?_⟩
  have hlen : sp.length ≤ Fintype.card N := hnd.length_le_card
  rw [spine_length_eq_depth_add_one d] at hlen
  exact hlen

end V60DerivationSpine

end FixedHCFG
end LeanCfgProject
