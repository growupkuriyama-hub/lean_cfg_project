import LeanCfgProject.ObservedResidualConcept.CanonicalResidualClosureSystem
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
ObservedSyntacticResidualCorollaries.lean

Small corollary layer after CI #149.

This file repackages the canonical residual-closure-system results under names
that are convenient for the paper appendix.  It adds no new assumptions and is
intended to be a stable CI target for the v25.2 canonical-object layer.
-/

variable {Q : Type u} [Mul Q]

/--
Residual intersections are closed concept extents.
-/
theorem residualIntersection_is_closed_concept
    (S : Set Q) (K : Set (Q × Q)) :
    ConceptClosure S (ResidualIntersection S K) =
      ResidualIntersection S K :=
  residualIntersection_closed S K

/--
Every concept closure is the residual intersection of the common contexts of
the original set.
-/
theorem conceptClosure_as_common_residual_intersection
    (S U : Set Q) :
    ConceptClosure S U =
      ResidualIntersection S (CommonContexts S U) :=
  conceptClosure_eq_residualIntersection_commonContexts S U

/--
Closed concept extents are exactly residual intersections.
-/
theorem closed_concepts_iff_residual_intersections
    (S U : Set Q) :
    ConceptClosure S U = U ↔
      ∃ K : Set (Q × Q), U = ResidualIntersection S K :=
  isConceptExtent_iff_exists_residualIntersection S U

/--
Every two-sided frame residual is already a closed concept extent.
-/
theorem frame_residual_is_closed_concept
    (S : Set Q) (a b : Q) :
    ConceptClosure S (TwoSidedResidual S a b) =
      TwoSidedResidual S a b :=
  conceptClosure_twoSidedResidual_eq S a b

/--
Every two-sided frame residual is a singleton-indexed residual intersection.
-/
theorem frame_residual_as_singleton_intersection
    (S : Set Q) (a b : Q) :
    TwoSidedResidual S a b =
      ResidualIntersection S ({(a, b)} : Set (Q × Q)) :=
  (residualIntersection_singleton S a b).symm

/--
The full carrier is the empty residual intersection.
-/
theorem univ_as_empty_residual_intersection
    (S : Set Q) :
    (Set.univ : Set Q) =
      ResidualIntersection S (∅ : Set (Q × Q)) :=
  (residualIntersection_empty S).symm

/--
A compact paper-facing package for the canonical residual closure system.
-/
theorem observedResidualClosureSystem_package
    (S U : Set Q) :
    (ConceptClosure S U =
      ResidualIntersection S (CommonContexts S U))
    ∧
    (ConceptClosure S U = U ↔
      ∃ K : Set (Q × Q), U = ResidualIntersection S K) := by
  exact ⟨conceptClosure_as_common_residual_intersection S U,
         closed_concepts_iff_residual_intersections S U⟩

end LeanCfgProject
