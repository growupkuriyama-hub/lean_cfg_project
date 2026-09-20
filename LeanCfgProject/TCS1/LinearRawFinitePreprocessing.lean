import LeanCfgProject.TCS1.LinearRawEpsilonUnitSemantics
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# TCS #1: finite prepared grammar after linear epsilon/unit elimination

The semantic preprocessing file proves that epsilon and unit elimination
preserve every nonempty word of a raw linear grammar. This module makes the
resulting unit-free rule family finite and indexed.

For each source production we need at most two non-unit rule variants:

* the original prepared nonempty/non-unit RHS;
* when the unique core of u B v is nullable, the dropped-core terminal rule
  u v.

Unit elimination then copies either variant to every unit-reachable source.
Hence a generous finite index universe is a subtype of

  N x (P x Bool),

so the number of resulting prepared rules is at most 2 |N| |P|.

The output is an actual PreparedLinearIndexedCFG, ready for the already
verified linear-spine normalization.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section LinearRawFinitePreprocessing

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}

/--
Terminal-only prepared RHS produced by deleting the nullable core of
u B v. The non-unit condition guarantees that u v is nonempty.
-/
def droppedCorePreparedRhs
    (left right : List α)
    (hnonunit : left ≠ [] ∨ right ≠ []) :
    PreparedLinearRhs N α :=
  match left, right with
  | [], [] =>
      False.elim
        (hnonunit.elim
          (fun h => h rfl)
          (fun h => h rfl))
  | [], b :: rest =>
      PreparedLinearRhs.terminals b rest
  | a :: rest, right =>
      PreparedLinearRhs.terminals a (rest ++ right)

/-- The dropped-core prepared RHS spells exactly u v. -/
theorem droppedCorePreparedRhs_toMixed
    (left right : List α)
    (hnonunit : left ≠ [] ∨ right ≠ []) :
    (droppedCorePreparedRhs
      (N := N) left right hnonunit).toMixedRhs
      =
    (left ++ right).map Sum.inr := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exfalso
          exact
            hnonunit.elim
              (fun h => h rfl)
              (fun h => h rfl)
      | cons b rest =>
          rfl
  | cons a rest =>
      simp [droppedCorePreparedRhs,
        PreparedLinearRhs.toMixedRhs,
        List.map_append]

/-- Its source length is exactly the number of surviving terminals. -/
theorem droppedCorePreparedRhs_sourceLength
    (left right : List α)
    (hnonunit : left ≠ [] ∨ right ≠ []) :
    (droppedCorePreparedRhs
      (N := N) left right hnonunit).sourceLength
      =
    left.length + right.length := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exfalso
          exact
            hnonunit.elim
              (fun h => h rfl)
              (fun h => h rfl)
      | cons b rest =>
          simp [droppedCorePreparedRhs,
            PreparedLinearRhs.sourceLength]
  | cons a rest =>
      simp [droppedCorePreparedRhs,
        PreparedLinearRhs.sourceLength]
      omega

/--
Validity of one of the two possible epsilon-free non-unit variants attached
to source production p.
-/
def RawLinearCoreVariantValid
    (G : RawLinearIndexedCFG N α P)
    (q : P × Bool) : Prop :=
  match q.2 with
  | false =>
      ∃ rhs : PreparedLinearRhs N α,
        G.rhs q.1 = RawLinearRhs.prepared rhs
  | true =>
      ∃ left : List α,
      ∃ core : N,
      ∃ right : List α,
      ∃ hnonunit : left ≠ [] ∨ right ≠ [],
        G.rhs q.1 =
          RawLinearRhs.prepared
            (PreparedLinearRhs.around
              left core right hnonunit)
        ∧
        RawLinearNullable G core

/-- Finite index of non-unit epsilon-free core-rule variants. -/
abbrev RawLinearCoreRuleIndex
    (G : RawLinearIndexedCFG N α P) :=
  {q : P × Bool // RawLinearCoreVariantValid G q}

noncomputable instance rawLinearCoreRuleIndexFintype
    [Fintype P]
    (G : RawLinearIndexedCFG N α P) :
    Fintype (RawLinearCoreRuleIndex G) :=
  Fintype.ofFinite _

/-- Source production underlying one core-rule variant. -/
def rawLinearCoreRuleSource
    (G : RawLinearIndexedCFG N α P)
    (q : RawLinearCoreRuleIndex G) : P :=
  q.1.1

/-- Prepared RHS represented by one valid core-rule variant. -/
noncomputable def rawLinearCorePreparedRhs
    (G : RawLinearIndexedCFG N α P)
    (q : RawLinearCoreRuleIndex G) :
    PreparedLinearRhs N α := by
  rcases q with ⟨⟨p, variant⟩, hvalid⟩
  cases variant with
  | false =>
      rcases hvalid with ⟨rhs, hrhs⟩
      exact rhs
  | true =>
      rcases hvalid with
        ⟨left, core, right, hnonunit, hrhs, hnullable⟩
      exact
        droppedCorePreparedRhs
          (N := N) left right hnonunit

/--
Original variants decode to the unique prepared RHS already stored in the raw
source production.
-/
theorem rawLinearCorePreparedRhs_false
    (G : RawLinearIndexedCFG N α P)
    (p : P)
    (hvalid :
      RawLinearCoreVariantValid G (p, false)) :
    let q : RawLinearCoreRuleIndex G :=
      ⟨(p, false), hvalid⟩
    G.rhs p =
      RawLinearRhs.prepared
        (rawLinearCorePreparedRhs G q) := by
  rcases hvalid with ⟨rhs, hrhs⟩
  simpa [rawLinearCorePreparedRhs] using hrhs

/--
Dropped-core variants decode to the terminal-only prepared RHS obtained from
their nullable-core source rule.
-/
theorem rawLinearCorePreparedRhs_true
    (G : RawLinearIndexedCFG N α P)
    (p : P)
    (hvalid :
      RawLinearCoreVariantValid G (p, true)) :
    ∃ left : List α,
    ∃ core : N,
    ∃ right : List α,
    ∃ hnonunit : left ≠ [] ∨ right ≠ [],
      G.rhs p =
        RawLinearRhs.prepared
          (PreparedLinearRhs.around
            left core right hnonunit)
      ∧
      RawLinearNullable G core
      ∧
      rawLinearCorePreparedRhs G
        (⟨(p, true), hvalid⟩ :
          RawLinearCoreRuleIndex G)
        =
      droppedCorePreparedRhs
        (N := N) left right hnonunit := by
  rcases hvalid with
    ⟨left, core, right, hnonunit, hrhs, hnullable⟩
  refine
    ⟨left, core, right, hnonunit,
      hrhs, hnullable, ?_⟩
  rfl

/--
After unit elimination, a prepared rule is indexed by its copied root A and
one core-rule variant whose original lhs is unit-reachable from A.
-/
abbrev RawLinearPreparedRuleIndex
    [Fintype N] [Fintype P]
    (G : RawLinearIndexedCFG N α P) :=
  {q : N × RawLinearCoreRuleIndex G //
    RawLinearUnitReach G
      q.1 (G.lhs (rawLinearCoreRuleSource G q.2))}

noncomputable instance rawLinearPreparedRuleIndexFintype
    [Fintype N] [Fintype P]
    (G : RawLinearIndexedCFG N α P) :
    Fintype (RawLinearPreparedRuleIndex G) :=
  Fintype.ofFinite _

/-- Concrete finite prepared grammar after epsilon and unit elimination. -/
noncomputable def rawLinearPreparedGrammar
    [Fintype N] [Fintype P]
    (G : RawLinearIndexedCFG N α P) :
    PreparedLinearIndexedCFG
      N α (RawLinearPreparedRuleIndex G) where
  lhs q := q.1.1
  rhs q := rawLinearCorePreparedRhs G q.1.2

/-- There are at most two core variants per source production. -/
theorem rawLinearCoreRuleIndex_card_le
    [Fintype P]
    (G : RawLinearIndexedCFG N α P) :
    Fintype.card (RawLinearCoreRuleIndex G)
      ≤
    2 * Fintype.card P := by
  calc
    Fintype.card (RawLinearCoreRuleIndex G)
        ≤ Fintype.card (P × Bool) :=
      Fintype.card_subtype_le _
    _ = Fintype.card P * 2 := by
      simp
    _ = 2 * Fintype.card P := by
      omega

/-- The copied unit-free prepared rule set is finite and quadratically bounded. -/
theorem rawLinearPreparedRuleIndex_card_le
    [Fintype N] [Fintype P]
    (G : RawLinearIndexedCFG N α P) :
    Fintype.card (RawLinearPreparedRuleIndex G)
      ≤
    2 * Fintype.card N * Fintype.card P := by
  have hsub :
      Fintype.card (RawLinearPreparedRuleIndex G)
        ≤
      Fintype.card
        (N × RawLinearCoreRuleIndex G) :=
    Fintype.card_subtype_le _
  have hcore :=
    rawLinearCoreRuleIndex_card_le G
  calc
    Fintype.card (RawLinearPreparedRuleIndex G)
        ≤
      Fintype.card N *
        Fintype.card (RawLinearCoreRuleIndex G) := by
          simpa using hsub
    _ ≤
      Fintype.card N *
        (2 * Fintype.card P) :=
      Nat.mul_le_mul_left _ hcore
    _ = 2 * Fintype.card N * Fintype.card P := by
      ring

end LinearRawFinitePreprocessing

end TCS1
end LeanCfgProject
