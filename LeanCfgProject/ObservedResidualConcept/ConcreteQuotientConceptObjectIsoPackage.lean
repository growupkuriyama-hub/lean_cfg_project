import LeanCfgProject.ObservedSyntacticConcreteQuotientConceptIsoSummary

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u

/-
ConcreteQuotientConceptObjectIsoPackage.lean

Theorem-body experiment.

Purpose:
  package the concrete observed syntactic quotient concept-object
  correspondence as a bundled order / closure / product isomorphism core.

After CI #225, the set-level round-trip layer is checked.  This file bundles
that layer into a single structure containing:

  - to/from maps between original and quotient-side concept extents;
  - closedness preservation in both directions;
  - round-trip laws on closed extents;
  - order reflection/equivalence on closed extents;
  - closure preservation;
  - ConceptProduct preservation.

This is intentionally a paper-facing bundle rather than an attempt to introduce
a global Quantale typeclass.
-/

variable {Q : Type u} [Monoid Q]

/-- The observed subset on the concrete observed syntactic quotient. -/
abbrev concreteObservedQuotientObservedSet
    (S : Set Q) :
    Set (ObservedSyntacticQuotient (Q := Q) S) :=
  Set.image (observedSyntacticQuotientMap (Q := Q) S) S

/-- The image map on concept extents. -/
def concreteQuotientConceptTo
    (S : Set Q) (U : Set Q) :
    Set (ObservedSyntacticQuotient (Q := Q) S) :=
  Set.image (observedSyntacticQuotientMap (Q := Q) S) U

/-- The preimage map on concept extents. -/
def concreteQuotientConceptFrom
    (S : Set Q)
    (Ubar : Set (ObservedSyntacticQuotient (Q := Q) S)) :
    Set Q :=
  { x : Q | observedSyntacticQuotientMap (Q := Q) S x ∈ Ubar }

/-- Image is monotone. -/
theorem concreteQuotientConceptTo_mono
    (S : Set Q) {U V : Set Q}
    (hUV : U ⊆ V) :
    concreteQuotientConceptTo (Q := Q) S U
      ⊆
    concreteQuotientConceptTo (Q := Q) S V := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, hUV hx, rfl⟩

/-- Preimage is monotone. -/
theorem concreteQuotientConceptFrom_mono
    (S : Set Q)
    {Ubar Vbar : Set (ObservedSyntacticQuotient (Q := Q) S)}
    (hUV : Ubar ⊆ Vbar) :
    concreteQuotientConceptFrom (Q := Q) S Ubar
      ⊆
    concreteQuotientConceptFrom (Q := Q) S Vbar := by
  intro x hx
  exact hUV hx

/--
For closed original extents, image reflects and preserves inclusion.
-/
theorem concreteQuotientConceptTo_subset_iff_closed
    (S : Set Q) {U V : Set Q}
    (hU : IsConceptExtent S U)
    (hV : IsConceptExtent S V) :
    concreteQuotientConceptTo (Q := Q) S U
      ⊆
    concreteQuotientConceptTo (Q := Q) S V
      ↔
    U ⊆ V := by
  constructor
  · intro h x hx
    have hxpre :
        x ∈ concreteQuotientConceptFrom (Q := Q) S
          (concreteQuotientConceptTo (Q := Q) S V) := by
      exact h ⟨x, hx, rfl⟩
    change
      x ∈
        { z : Q |
          observedSyntacticQuotientMap (Q := Q) S z
            ∈
          Set.image (observedSyntacticQuotientMap (Q := Q) S) V } at hxpre
    have hround :=
      concreteObservedSyntacticQuotient_preimage_image_closedExtent_eq
        (Q := Q) S V hV
    rw [hround] at hxpre
    exact hxpre
  · intro h
    exact concreteQuotientConceptTo_mono (Q := Q) S h

/--
For closed quotient extents, preimage reflects and preserves inclusion.
-/
theorem concreteQuotientConceptFrom_subset_iff_closed
    (S : Set Q)
    {Ubar Vbar : Set (ObservedSyntacticQuotient (Q := Q) S)}
    (hUbar : IsConceptExtent (concreteObservedQuotientObservedSet (Q := Q) S) Ubar)
    (hVbar : IsConceptExtent (concreteObservedQuotientObservedSet (Q := Q) S) Vbar) :
    concreteQuotientConceptFrom (Q := Q) S Ubar
      ⊆
    concreteQuotientConceptFrom (Q := Q) S Vbar
      ↔
    Ubar ⊆ Vbar := by
  constructor
  · intro h y hy
    rcases observedSyntacticQuotientMap_surjective (Q := Q) S y with ⟨x, hx⟩
    have hxU : x ∈ concreteQuotientConceptFrom (Q := Q) S Ubar := by
      change observedSyntacticQuotientMap (Q := Q) S x ∈ Ubar
      rw [hx]
      exact hy
    have hxV := h hxU
    change observedSyntacticQuotientMap (Q := Q) S x ∈ Vbar at hxV
    rw [hx] at hxV
    exact hxV
  · intro h
    exact concreteQuotientConceptFrom_mono (Q := Q) S h

/--
Bundled order / closure / product isomorphism core for the concrete observed
syntactic quotient concept object.
-/
structure ConcreteQuotientConceptObjectIsoPackage
    (S : Set Q) where
  toSet :
    Set Q → Set (ObservedSyntacticQuotient (Q := Q) S)
  fromSet :
    Set (ObservedSyntacticQuotient (Q := Q) S) → Set Q

  to_closed :
    ∀ U : Set Q,
      IsConceptExtent S U →
      IsConceptExtent (concreteObservedQuotientObservedSet (Q := Q) S) (toSet U)

  from_closed :
    ∀ Ubar : Set (ObservedSyntacticQuotient (Q := Q) S),
      IsConceptExtent (concreteObservedQuotientObservedSet (Q := Q) S) Ubar →
      IsConceptExtent S (fromSet Ubar)

  from_to_closed :
    ∀ U : Set Q,
      IsConceptExtent S U →
      fromSet (toSet U) = U

  to_from_closed :
    ∀ Ubar : Set (ObservedSyntacticQuotient (Q := Q) S),
      IsConceptExtent (concreteObservedQuotientObservedSet (Q := Q) S) Ubar →
      toSet (fromSet Ubar) = Ubar

  to_subset_iff_closed :
    ∀ U V : Set Q,
      IsConceptExtent S U →
      IsConceptExtent S V →
      (toSet U ⊆ toSet V ↔ U ⊆ V)

  from_subset_iff_closed :
    ∀ Ubar Vbar : Set (ObservedSyntacticQuotient (Q := Q) S),
      IsConceptExtent (concreteObservedQuotientObservedSet (Q := Q) S) Ubar →
      IsConceptExtent (concreteObservedQuotientObservedSet (Q := Q) S) Vbar →
      (fromSet Ubar ⊆ fromSet Vbar ↔ Ubar ⊆ Vbar)

  closure_preserved :
    ∀ U : Set Q,
      toSet (ConceptClosure S U)
        =
      ConceptClosure (concreteObservedQuotientObservedSet (Q := Q) S) (toSet U)

  quotient_closure_roundtrip :
    ∀ Ubar : Set (ObservedSyntacticQuotient (Q := Q) S),
      toSet (ConceptClosure S (fromSet Ubar))
        =
      ConceptClosure (concreteObservedQuotientObservedSet (Q := Q) S) Ubar

  product_preserved :
    ∀ A B : Set Q,
      toSet (ConceptProduct S A B)
        =
      ConceptProduct
        (concreteObservedQuotientObservedSet (Q := Q) S)
        (toSet A)
        (toSet B)

/--
The concrete observed syntactic quotient carries the bundled concept-object
order/closure/product isomorphism core.
-/
def concreteObservedSyntacticQuotient_conceptObjectIsoPackage
    (S : Set Q) :
    ConcreteQuotientConceptObjectIsoPackage (Q := Q) S where
  toSet := concreteQuotientConceptTo (Q := Q) S
  fromSet := concreteQuotientConceptFrom (Q := Q) S

  to_closed := by
    intro U hU
    exact concreteObservedSyntacticQuotient_image_closedExtent
      (Q := Q) S U hU

  from_closed := by
    intro Ubar hUbar
    exact concreteObservedSyntacticQuotient_pullback_closedExtent
      (Q := Q) S Ubar hUbar

  from_to_closed := by
    intro U hU
    exact concreteObservedSyntacticQuotient_preimage_image_closedExtent_eq
      (Q := Q) S U hU

  to_from_closed := by
    intro Ubar hUbar
    exact concreteObservedSyntacticQuotient_image_preimage_closedExtent_eq
      (Q := Q) S Ubar hUbar

  to_subset_iff_closed := by
    intro U V hU hV
    exact concreteQuotientConceptTo_subset_iff_closed
      (Q := Q) S hU hV

  from_subset_iff_closed := by
    intro Ubar Vbar hUbar hVbar
    exact concreteQuotientConceptFrom_subset_iff_closed
      (Q := Q) S hUbar hVbar

  closure_preserved := by
    intro U
    exact concreteObservedSyntacticQuotient_conceptClosure_image_eq
      (Q := Q) S U

  quotient_closure_roundtrip := by
    intro Ubar
    exact concreteObservedSyntacticQuotient_image_conceptClosure_preimage_eq
      (Q := Q) S Ubar

  product_preserved := by
    intro A B
    exact concreteObservedSyntacticQuotient_conceptProduct_image_eq
      (Q := Q) S A B

end LeanCfgProject
