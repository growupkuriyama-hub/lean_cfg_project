import LeanCfgProject.ObservedResidualConcept.ObservedSyntacticConcept
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u

/-
PointwiseAdequacy.lean

Planned theorem item 2:
  for R = Res_S(a,b) and U ⊆ R,

    cl_S(U) = R  ↔  U^▷ = R^▷  ↔  R ⊆ cl_S(U).

In the existing Lean vocabulary, `U^▷` is `CommonContexts S U`.
This file proves the core intent-closure identity
`CommonContexts S (ConceptClosure S U) = CommonContexts S U`
and then specializes it to two-sided residuals.

This is not a release/summary/package/certificate module.
-/

variable {Q : Type u} [Mul Q]

/--
Taking concept closure does not change the intent/common-context side.

Paper notation:
  (cl_S U)^▷ = U^▷.
-/
theorem commonContexts_conceptClosure_eq
    (S U : Set Q) :
    CommonContexts S (ConceptClosure S U) =
      CommonContexts S U := by
  apply Set.ext
  intro ab
  constructor
  · intro h gamma hgamma
    exact h gamma (subset_conceptClosure S U hgamma)
  · intro h gamma hgamma
    exact hgamma ab h

/--
If two sets have the same residual concept closure, then they have the same
common contexts.
-/
theorem commonContexts_eq_of_conceptClosure_eq
    (S U V : Set Q)
    (hcl : ConceptClosure S U = ConceptClosure S V) :
    CommonContexts S U = CommonContexts S V := by
  calc
    CommonContexts S U
        = CommonContexts S (ConceptClosure S U) :=
          (commonContexts_conceptClosure_eq S U).symm
    _ = CommonContexts S (ConceptClosure S V) := by
          rw [hcl]
    _ = CommonContexts S V :=
          commonContexts_conceptClosure_eq S V

/--
If two sets have the same common contexts, then they have the same residual
concept closure.
-/
theorem conceptClosure_eq_of_commonContexts_eq
    (S U V : Set Q)
    (hctx : CommonContexts S U = CommonContexts S V) :
    ConceptClosure S U = ConceptClosure S V := by
  apply Set.ext
  intro gamma
  constructor
  · intro hgamma ab habV
    have habU : ab ∈ CommonContexts S U := by
      rw [hctx]
      exact habV
    exact hgamma ab habU
  · intro hgamma ab habU
    have habV : ab ∈ CommonContexts S V := by
      rw [← hctx]
      exact habU
    exact hgamma ab habV

/--
Pointwise adequacy is equivalent to equality of accepting observed frames.

Here `R = TwoSidedResidual S a b`, so the statement is:

  cl_S(U) = R  ↔  U^▷ = R^▷.
-/
theorem pointwiseAdequacy_iff_commonContexts_eq
    (S U : Set Q) (a b : Q) :
    ConceptClosure S U = TwoSidedResidual S a b
      ↔
    CommonContexts S U =
      CommonContexts S (TwoSidedResidual S a b) := by
  constructor
  · intro hAdeq
    have hcl :
        ConceptClosure S U =
          ConceptClosure S (TwoSidedResidual S a b) := by
      rw [conceptClosure_twoSidedResidual_eq S a b]
      exact hAdeq
    exact commonContexts_eq_of_conceptClosure_eq S U
      (TwoSidedResidual S a b) hcl
  · intro hctx
    have hcl :
        ConceptClosure S U =
          ConceptClosure S (TwoSidedResidual S a b) :=
      conceptClosure_eq_of_commonContexts_eq S U
        (TwoSidedResidual S a b) hctx
    rw [conceptClosure_twoSidedResidual_eq S a b] at hcl
    exact hcl

/--
For a sound state image `U ⊆ R`, pointwise adequacy is equivalent to coverage.

Here `R = TwoSidedResidual S a b`, so the statement is:

  cl_S(U) = R  ↔  R ⊆ cl_S(U).
-/
theorem pointwiseAdequacy_iff_residual_subset_closure
    (S U : Set Q) (a b : Q)
    (hU : U ⊆ TwoSidedResidual S a b) :
    ConceptClosure S U = TwoSidedResidual S a b
      ↔
    TwoSidedResidual S a b ⊆ ConceptClosure S U := by
  constructor
  · intro hAdeq
    intro rho hrho
    rw [hAdeq]
    exact hrho
  · intro hcover
    apply Set.Subset.antisymm
    · have hmono :
          ConceptClosure S U
            ⊆
          ConceptClosure S (TwoSidedResidual S a b) :=
        conceptClosure_mono S hU
      rw [conceptClosure_twoSidedResidual_eq S a b] at hmono
      exact hmono
    · exact hcover

/--
Equality of accepting observed frames is equivalent to residual coverage,
under the usual soundness hypothesis `U ⊆ R`.

This is the Lean form of:

  U^▷ = R^▷  ↔  R ⊆ cl_S(U).
-/
theorem commonContexts_eq_iff_residual_subset_closure
    (S U : Set Q) (a b : Q)
    (hU : U ⊆ TwoSidedResidual S a b) :
    CommonContexts S U =
        CommonContexts S (TwoSidedResidual S a b)
      ↔
    TwoSidedResidual S a b ⊆ ConceptClosure S U :=
  (pointwiseAdequacy_iff_commonContexts_eq S U a b).symm.trans
    (pointwiseAdequacy_iff_residual_subset_closure S U a b hU)

/--
Triple packaging of the pointwise adequacy equivalences.

This is a theorem with content, not a release package: it records both
directions from the common central proposition.
-/
theorem pointwiseAdequacy_equivalences
    (S U : Set Q) (a b : Q)
    (hU : U ⊆ TwoSidedResidual S a b) :
    (ConceptClosure S U = TwoSidedResidual S a b
      ↔
     CommonContexts S U =
        CommonContexts S (TwoSidedResidual S a b))
    ∧
    (ConceptClosure S U = TwoSidedResidual S a b
      ↔
     TwoSidedResidual S a b ⊆ ConceptClosure S U)
    ∧
    (CommonContexts S U =
        CommonContexts S (TwoSidedResidual S a b)
      ↔
     TwoSidedResidual S a b ⊆ ConceptClosure S U) := by
  exact ⟨pointwiseAdequacy_iff_commonContexts_eq S U a b,
    pointwiseAdequacy_iff_residual_subset_closure S U a b hU,
    commonContexts_eq_iff_residual_subset_closure S U a b hU⟩

end LeanCfgProject
