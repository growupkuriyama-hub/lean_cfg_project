import LeanCfgProject.ObservedSyntacticResidualCorollaries
import LeanCfgProject.ObservedSyntacticBlockAdequacyCorollaries
import LeanCfgProject.ObservedSyntacticCongruence

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
ObservedSyntacticPaperCorollaries.lean

Paper-facing corollary layer for the v25.2 observed-syntactic object.

This file collects three independent components:
  * maximal observed syntactic congruence;
  * canonical residual closure system;
  * syntactic-block adequacy.
-/

variable {Q : Type u}

/--
For monoids, the observed syntactic relation is the largest two-sided stable
relation preserving the observed subset.
-/
theorem paper_observedSyntactic_maximal_package
    [Monoid Q] (S : Set Q) :
    TwoSidedStableRel (SameObservedSyntactic S)
      ∧ PreservesSubset S (SameObservedSyntactic S)
      ∧
      (∀ R : Q → Q → Prop,
        TwoSidedStableRel R →
        PreservesSubset S R →
        ∀ x y : Q, R x y → SameObservedSyntactic S x y) :=
  observedSyntacticCongruence_summary (S := S)

/--
The canonical residual closure system package.
-/
theorem paper_canonicalResidualClosure_package
    [Mul Q] (S U : Set Q) :
    (ConceptClosure S U =
      ResidualIntersection S (CommonContexts S U))
    ∧
    (ConceptClosure S U = U ↔
      ∃ K : Set (Q × Q), U = ResidualIntersection S K) :=
  observedResidualClosureSystem_package S U

/--
The syntactic-block adequacy package.
-/
theorem paper_syntacticBlockAdequacy_package
    [Mul Q] (S U : Set Q) (a b : Q)
    (hU : U ⊆ TwoSidedResidual S a b)
    (hne : ∃ u0 : Q, u0 ∈ U)
    (hblock :
      ∀ x y : Q,
        x ∈ TwoSidedResidual S a b →
        y ∈ TwoSidedResidual S a b →
          SameObservedSyntactic S x y) :
    (ConceptClosure S U = TwoSidedResidual S a b)
    ∧ (TwoSidedResidual S a b ⊆ ConceptClosure S U) :=
  syntacticBlockAdequacy_package S U a b hU hne hblock

/--
A compact abstract paper package: canonical closure plus syntactic-block
adequacy for one frame residual.
-/
theorem paper_observedSyntacticCanonicalAdequacy_package
    [Mul Q] (S U : Set Q) (a b : Q)
    (hU : U ⊆ TwoSidedResidual S a b)
    (hne : ∃ u0 : Q, u0 ∈ U)
    (hblock :
      ∀ x y : Q,
        x ∈ TwoSidedResidual S a b →
        y ∈ TwoSidedResidual S a b →
          SameObservedSyntactic S x y) :
    (ConceptClosure S U =
      ResidualIntersection S (CommonContexts S U))
    ∧
    (ConceptClosure S U = TwoSidedResidual S a b) := by
  exact ⟨conceptClosure_as_common_residual_intersection S U,
         syntacticBlockAdequacy S U a b hU hne hblock⟩

end LeanCfgProject
