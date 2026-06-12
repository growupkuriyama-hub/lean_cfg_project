import LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCore

/-!
# Dedekind lower-bound core

This file proves the combinatorial core behind the paper's Dedekind-number
lower-bound discussion.

The point is deliberately separated from heavy finite-cardinality arithmetic:
for any preorder-like carrier with a relation `≤`, consider the formal context
whose attributes are all lower sets and whose incidence is membership.  Its
closure operator sends a set to the intersection of all lower sets containing it.
Lean checks that the closed extents are exactly the lower sets.

For the Boolean cube `Fin n -> Bool`, lower sets are precisely the monotone
families / Dedekind objects.  Thus this file supplies the theorem-body core
needed for the statement that a concept-object family can have Dedekind-number
size even when the generating carrier has only Boolean-cube size.

This is intended as the safe Lean-checked combinatorial lower-bound layer below
the full ORC-specific realization theorem.
-/

open Set

universe u

namespace ObservedResidualConcept

/-- A lower set in a type equipped with a relation `≤`. -/
def IsORCLowerSet (α : Type u) [LE α] (D : Set α) : Prop :=
  ∀ {x y : α}, y ∈ D → x ≤ y → x ∈ D

/-- Lower sets, packaged as a subtype. -/
def ORCLowerSet (α : Type u) [LE α] : Type u :=
  {D : Set α // IsORCLowerSet α D}

/-- Closure by all lower sets containing `U`.

Equivalently: the intersection of all lower sets that contain `U`. -/
def lowerSetClosure {α : Type u} [LE α] (U : Set α) : Set α :=
  {x | ∀ D : ORCLowerSet α, U ⊆ D.1 → x ∈ D.1}

/-- Closed extents for the lower-set context. -/
def LowerContextClosedExtent (α : Type u) [LE α] : Type u :=
  {U : Set α // lowerSetClosure U = U}

variable {α : Type u} [LE α]

/-- The lower-set closure is extensive. -/
theorem subset_lowerSetClosure (U : Set α) :
    U ⊆ lowerSetClosure U := by
  intro x hx
  intro D hUD
  exact hUD hx

/-- The lower-set closure is monotone. -/
theorem lowerSetClosure_mono {U V : Set α} (hUV : U ⊆ V) :
    lowerSetClosure U ⊆ lowerSetClosure V := by
  intro x hx
  intro D hVD
  exact hx D (fun u hu => hVD (hUV hu))

/-- The closure by lower sets is itself a lower set. -/
theorem lowerSetClosure_isLowerSet (U : Set α) :
    IsORCLowerSet α (lowerSetClosure U) := by
  intro x y hy hxy
  intro D hUD
  exact D.2 (hy D hUD) hxy

/-- A packaged version of `lowerSetClosure_isLowerSet`. -/
def lowerSetClosure_asLowerSet (U : Set α) : ORCLowerSet α :=
  ⟨lowerSetClosure U, lowerSetClosure_isLowerSet U⟩

/-- Lower sets are fixed points of lower-set closure. -/
theorem lowerSetClosure_eq_of_lowerSet (D : ORCLowerSet α) :
    lowerSetClosure D.1 = D.1 := by
  ext x
  constructor
  · intro hx
    exact hx D (by intro y hy; exact hy)
  · intro hx
    exact subset_lowerSetClosure D.1 hx

/-- Fixed points of lower-set closure are exactly lower sets. -/
theorem lowerSetClosed_iff_isLowerSet (U : Set α) :
    lowerSetClosure U = U ↔ IsORCLowerSet α U := by
  constructor
  · intro h
    rw [← h]
    exact lowerSetClosure_isLowerSet U
  · intro h
    exact lowerSetClosure_eq_of_lowerSet ⟨U, h⟩

/-- Send a lower set to the corresponding closed extent. -/
def ORCLowerSet.toClosed (D : ORCLowerSet α) :
    LowerContextClosedExtent α :=
  ⟨D.1, lowerSetClosure_eq_of_lowerSet D⟩

/-- Send a closed extent to the corresponding lower set. -/
def LowerContextClosedExtent.toLowerSet (C : LowerContextClosedExtent α) :
    ORCLowerSet α :=
  ⟨C.1, (lowerSetClosed_iff_isLowerSet C.1).mp C.2⟩

/-- Closed extents of the lower-set context are equivalent to lower sets. -/
def lowerSet_closedExtent_equiv :
    ORCLowerSet α ≃ LowerContextClosedExtent α where
  toFun := ORCLowerSet.toClosed
  invFun := LowerContextClosedExtent.toLowerSet
  left_inv := by
    intro D
    apply Subtype.ext
    rfl
  right_inv := by
    intro C
    apply Subtype.ext
    rfl

/-- In particular, the map from lower sets to closed extents is injective. -/
theorem lowerSet_toClosed_injective :
    Function.Injective (ORCLowerSet.toClosed (α := α)) := by
  intro D E h
  have hval := congrArg Subtype.val h
  apply Subtype.ext
  exact hval

/-- Finite-cardinality lower bound: there are at least as many closed extents as
lower sets. -/
theorem card_lowerSets_le_card_closedExtents
    [Fintype (ORCLowerSet α)] [Fintype (LowerContextClosedExtent α)] :
    Fintype.card (ORCLowerSet α) ≤ Fintype.card (LowerContextClosedExtent α) := by
  exact Fintype.card_le_of_injective
    (ORCLowerSet.toClosed (α := α))
    (lowerSet_toClosed_injective (α := α))

/-- Boolean cube used for the Dedekind-number family. -/
abbrev BoolCube (n : Nat) : Type :=
  Fin n → Bool

/-- The closed extents of the Boolean lower-set context are exactly the lower
sets of the Boolean cube. -/
def boolean_dedekind_closedExtent_equiv (n : Nat) :
    ORCLowerSet (BoolCube n) ≃ LowerContextClosedExtent (BoolCube n) :=
  lowerSet_closedExtent_equiv (α := BoolCube n)

/-- Paper-facing Dedekind lower-bound core package.

For the Boolean cube, lower sets inject into the corresponding closed extents.
The number of lower sets of the Boolean cube is the Dedekind-number side of the
paper's lower-bound discussion.
-/
theorem boolean_dedekind_lower_bound_core (n : Nat) :
    Function.Injective
      (ORCLowerSet.toClosed (α := BoolCube n)) := by
  exact lowerSet_toClosed_injective (α := BoolCube n)

/-- Finite-cardinality Boolean version. -/
theorem boolean_card_lowerSets_le_card_closedExtents (n : Nat)
    [Fintype (ORCLowerSet (BoolCube n))]
    [Fintype (LowerContextClosedExtent (BoolCube n))] :
    Fintype.card (ORCLowerSet (BoolCube n))
      ≤ Fintype.card (LowerContextClosedExtent (BoolCube n)) := by
  exact card_lowerSets_le_card_closedExtents (α := BoolCube n)

end ObservedResidualConcept
