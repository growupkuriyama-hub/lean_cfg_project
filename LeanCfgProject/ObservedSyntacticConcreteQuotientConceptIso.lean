import LeanCfgProject.ObservedSyntacticConcreteQuotientPaperSummary

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u

/-
ObservedSyntacticConcreteQuotientConceptIso.lean

Theorem-body experiment.

Purpose:
  move the paper target "Concrete quotient concept-object isomorphism" closer
  to a checked theorem-body result.

After #221, the concrete quotient type, quotient monoid, projection map, exact
kernel, and preservation theorems are available.  This file proves the
set-level round-trip facts for concept extents:

  - image-preimage is exact on the quotient side by surjectivity;
  - preimage-image is exact on concept closures on the original side because
    concept closures are saturated under SameObservedSyntactic;
  - therefore closed extents round-trip through the concrete quotient map;
  - concept closure on the quotient side is computed by image of the pulled-back
    concept closure.

This is still a set-level theorem-body package, not a bundled order/quantale
isomorphism structure.
-/

variable {Q : Type u} [Monoid Q]

/--
Concept closures are saturated under the observed syntactic congruence.

This direct lemma is intentionally local to the concrete quotient experiment,
so that the round-trip proof below does not rely on a possibly changing
paper-facing wrapper name.
-/
theorem conceptClosure_mem_of_sameObservedSyntactic
    (S : Set Q) (U : Set Q)
    {x y : Q}
    (hxy : SameObservedSyntactic S x y)
    (hx : x ∈ ConceptClosure S U) :
    y ∈ ConceptClosure S U := by
  intro ab hab
  exact (hxy ab.1 ab.2).mp (hx ab hab)

/--
Image-preimage round trip for the concrete observed quotient projection.

This is the quotient-side round-trip and uses only surjectivity.
-/
theorem concreteObservedSyntacticQuotient_image_preimage_eq
    (S : Set Q)
    (Ubar : Set (ObservedSyntacticQuotient (Q := Q) S)) :
    Set.image (observedSyntacticQuotientMap (Q := Q) S)
      { x : Q | observedSyntacticQuotientMap (Q := Q) S x ∈ Ubar }
      =
    Ubar := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    rcases observedSyntacticQuotientMap_surjective (Q := Q) S y with ⟨x, hx⟩
    refine ⟨x, ?_, hx⟩
    rw [hx]
    exact hy

/--
Preimage-image round trip for concept closures.

This is the original-side round-trip.  The nontrivial point is that
`ConceptClosure S U` is saturated under `SameObservedSyntactic S`, and the
kernel of the concrete projection is exactly that relation.
-/
theorem concreteObservedSyntacticQuotient_preimage_image_conceptClosure_eq
    (S : Set Q) (U : Set Q) :
    { x : Q |
        observedSyntacticQuotientMap (Q := Q) S x
          ∈
        Set.image (observedSyntacticQuotientMap (Q := Q) S)
          (ConceptClosure S U) }
      =
    ConceptClosure S U := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, hxy_map⟩
    have hyx : SameObservedSyntactic S y x :=
      (observedSyntacticQuotientMap_kernel (Q := Q) S y x).mp hxy_map
    exact conceptClosure_mem_of_sameObservedSyntactic (Q := Q) S U hyx hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/--
Preimage-image round trip for an arbitrary closed extent.
-/
theorem concreteObservedSyntacticQuotient_preimage_image_closedExtent_eq
    (S : Set Q) (U : Set Q)
    (hU : IsConceptExtent S U) :
    { x : Q |
        observedSyntacticQuotientMap (Q := Q) S x
          ∈
        Set.image (observedSyntacticQuotientMap (Q := Q) S) U }
      =
    U := by
  calc
    { x : Q |
        observedSyntacticQuotientMap (Q := Q) S x
          ∈
        Set.image (observedSyntacticQuotientMap (Q := Q) S) U }
        =
      { x : Q |
        observedSyntacticQuotientMap (Q := Q) S x
          ∈
        Set.image (observedSyntacticQuotientMap (Q := Q) S)
          (ConceptClosure S U) } := by
          rw [hU]
    _ = ConceptClosure S U := by
          exact concreteObservedSyntacticQuotient_preimage_image_conceptClosure_eq
            (Q := Q) S U
    _ = U := hU

/--
Quotient-side closure after pulling back and pushing forward.

This is the quotient-side concept-object round-trip in closure form.
-/
theorem concreteObservedSyntacticQuotient_image_conceptClosure_preimage_eq
    (S : Set Q)
    (Ubar : Set (ObservedSyntacticQuotient (Q := Q) S)) :
    Set.image (observedSyntacticQuotientMap (Q := Q) S)
      (ConceptClosure S
        { x : Q | observedSyntacticQuotientMap (Q := Q) S x ∈ Ubar })
      =
    ConceptClosure
      (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
      Ubar := by
  calc
    Set.image (observedSyntacticQuotientMap (Q := Q) S)
      (ConceptClosure S
        { x : Q | observedSyntacticQuotientMap (Q := Q) S x ∈ Ubar })
        =
      ConceptClosure
        (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
        (Set.image (observedSyntacticQuotientMap (Q := Q) S)
          { x : Q | observedSyntacticQuotientMap (Q := Q) S x ∈ Ubar }) := by
          exact concreteObservedSyntacticQuotient_conceptClosure_image_eq
            (Q := Q) S
            { x : Q | observedSyntacticQuotientMap (Q := Q) S x ∈ Ubar }
    _ =
      ConceptClosure
        (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
        Ubar := by
          rw [concreteObservedSyntacticQuotient_image_preimage_eq (Q := Q) S Ubar]

/--
Closed quotient extents round-trip through pullback and image.

The closedness hypothesis is not needed for the raw image-preimage equality, but
is included here because this is the concept-object statement.
-/
theorem concreteObservedSyntacticQuotient_image_preimage_closedExtent_eq
    (S : Set Q)
    (Ubar : Set (ObservedSyntacticQuotient (Q := Q) S))
    (hUbar :
      IsConceptExtent
        (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
        Ubar) :
    Set.image (observedSyntacticQuotientMap (Q := Q) S)
      { x : Q | observedSyntacticQuotientMap (Q := Q) S x ∈ Ubar }
      =
    Ubar := by
  exact concreteObservedSyntacticQuotient_image_preimage_eq
    (Q := Q) S Ubar

/--
Pullback of a closed quotient extent is a closed original extent.

This reuses the concrete quotient preservation layer checked by #221.
-/
theorem concreteObservedSyntacticQuotient_pullback_closedExtent
    (S : Set Q)
    (Ubar : Set (ObservedSyntacticQuotient (Q := Q) S))
    (hUbar :
      IsConceptExtent
        (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
        Ubar) :
    IsConceptExtent S
      { x : Q | observedSyntacticQuotientMap (Q := Q) S x ∈ Ubar } := by
  exact concreteObservedSyntacticQuotient_preimage_isConceptExtent
    (Q := Q) S Ubar hUbar

/--
Image of a closed original extent is closed on the quotient side, in the
closure-form sense sufficient for the paper-level quotient concept object.

This theorem states the closedness by giving the defining closure equality.
-/
theorem concreteObservedSyntacticQuotient_image_closedExtent_closure_eq
    (S : Set Q) (U : Set Q)
    (hU : IsConceptExtent S U) :
    ConceptClosure
      (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
      (Set.image (observedSyntacticQuotientMap (Q := Q) S) U)
      =
    Set.image (observedSyntacticQuotientMap (Q := Q) S) U := by
  calc
    ConceptClosure
      (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
      (Set.image (observedSyntacticQuotientMap (Q := Q) S) U)
      =
    Set.image (observedSyntacticQuotientMap (Q := Q) S)
      (ConceptClosure S U) := by
        symm
        exact concreteObservedSyntacticQuotient_conceptClosure_image_eq
          (Q := Q) S U
    _ =
    Set.image (observedSyntacticQuotientMap (Q := Q) S) U := by
      rw [hU]

/--
Image of a closed original extent is a closed quotient extent.
-/
theorem concreteObservedSyntacticQuotient_image_closedExtent
    (S : Set Q) (U : Set Q)
    (hU : IsConceptExtent S U) :
    IsConceptExtent
      (Set.image (observedSyntacticQuotientMap (Q := Q) S) S)
      (Set.image (observedSyntacticQuotientMap (Q := Q) S) U) := by
  exact concreteObservedSyntacticQuotient_image_closedExtent_closure_eq
    (Q := Q) S U hU

end LeanCfgProject
