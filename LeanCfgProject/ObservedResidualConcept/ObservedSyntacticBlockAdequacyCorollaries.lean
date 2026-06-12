import LeanCfgProject.ObservedResidualConcept.ObservedSyntacticConcept
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
ObservedSyntacticBlockAdequacyCorollaries.lean

Small corollary layer after CI #149.

This file gives paper-facing names for the syntactic-block adequacy theorem.
It stays at the abstract `(Q,S)` level and does not mention CFG presentations.
-/

variable {Q : Type u} [Mul Q]

/--
If a nonempty sound state image `U` lies inside a frame residual and the
residual is contained in one observed syntactic block, then `U` generates the
whole residual by concept closure.
-/
theorem nonempty_state_image_generates_single_block_residual
    (S U : Set Q) (a b : Q)
    (hU : U ⊆ TwoSidedResidual S a b)
    (hne : ∃ u0 : Q, u0 ∈ U)
    (hblock :
      ∀ x y : Q,
        x ∈ TwoSidedResidual S a b →
        y ∈ TwoSidedResidual S a b →
          SameObservedSyntactic S x y) :
    ConceptClosure S U = TwoSidedResidual S a b :=
  syntacticBlockAdequacy S U a b hU hne hblock

/--
Coverage form of the same criterion: the residual is contained in the closure
of the state image.
-/
theorem single_block_residual_covered_by_state_concept
    (S U : Set Q) (a b : Q)
    (hU : U ⊆ TwoSidedResidual S a b)
    (hne : ∃ u0 : Q, u0 ∈ U)
    (hblock :
      ∀ x y : Q,
        x ∈ TwoSidedResidual S a b →
        y ∈ TwoSidedResidual S a b →
          SameObservedSyntactic S x y) :
    TwoSidedResidual S a b ⊆ ConceptClosure S U :=
  residual_subset_conceptClosure_of_nonempty_subset_pairwiseBlock
    S U a b hU hne hblock

/--
Pointed form: if the whole residual lies in the observed syntactic block of a
witness `u0 ∈ U`, then `U` generates the residual.
-/
theorem pointed_single_block_adequacy
    (S U : Set Q) (a b u0 : Q)
    (hU : U ⊆ TwoSidedResidual S a b)
    (hu0 : u0 ∈ U)
    (hblock :
      ∀ rho : Q,
        rho ∈ TwoSidedResidual S a b →
          SameObservedSyntactic S rho u0) :
    ConceptClosure S U = TwoSidedResidual S a b :=
  conceptClosure_eq_residual_of_subset_singleBlock
    S U a b u0 hU hu0 hblock

/--
The closure of a state image inside a single-block residual is itself closed
and equal to that residual.
-/
theorem single_block_state_concept_is_closed_residual
    (S U : Set Q) (a b : Q)
    (hU : U ⊆ TwoSidedResidual S a b)
    (hne : ∃ u0 : Q, u0 ∈ U)
    (hblock :
      ∀ x y : Q,
        x ∈ TwoSidedResidual S a b →
        y ∈ TwoSidedResidual S a b →
          SameObservedSyntactic S x y) :
    ConceptClosure S (ConceptClosure S U) =
      TwoSidedResidual S a b := by
  rw [conceptClosure_idempotent S U]
  exact syntacticBlockAdequacy S U a b hU hne hblock

/--
A compact paper-facing package for abstract syntactic-block adequacy.
-/
theorem syntacticBlockAdequacy_package
    (S U : Set Q) (a b : Q)
    (hU : U ⊆ TwoSidedResidual S a b)
    (hne : ∃ u0 : Q, u0 ∈ U)
    (hblock :
      ∀ x y : Q,
        x ∈ TwoSidedResidual S a b →
        y ∈ TwoSidedResidual S a b →
          SameObservedSyntactic S x y) :
    (ConceptClosure S U = TwoSidedResidual S a b)
    ∧ (TwoSidedResidual S a b ⊆ ConceptClosure S U) := by
  exact ⟨syntacticBlockAdequacy S U a b hU hne hblock,
         residual_subset_conceptClosure_of_nonempty_subset_pairwiseBlock
          S U a b hU hne hblock⟩

end LeanCfgProject
