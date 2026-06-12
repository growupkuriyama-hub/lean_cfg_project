import LeanCfgProject.ObservedResidualConcept.K4ConceptCollapse
import LeanCfgProject.ObservedResidualConcept.FiniteStoppedFrameAdequacy
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject
namespace AnbnAdequacy

open K4

/-
K4 representation witnesses.

This file packages the K4 worked example into compact witness theorems that are
easy to cite from the paper.

The key existential statement is:

  there exist finite residual data S,U,R such that
    U ⊆ R, U ≠ R, but ConceptClosure S R = ConceptClosure S U.

This is the minimal machine-checked witness that residual-concept adequacy is
not just equality at the raw powerset level: the state image is strictly smaller
than the frame residual, but it represents the same residual concept.
-/

/--
There exists a finite K4 residual example in which raw powerset soundness is
proper, but residual-concept adequacy holds.
-/
theorem exists_strict_raw_soundness_but_concept_adequacy :
    ∃ S U R : Set K4,
      U ⊆ R
      ∧ U ≠ R
      ∧ ConceptClosure S R = ConceptClosure S U := by
  refine ⟨Sset, UA, TwoSidedResidual Sset e y, ?_, ?_, ?_⟩
  · exact sound_A
  · exact raw_A_ne_residual
  · exact adequacy_A

/--
There exists a finite K4 residual example in which two distinct raw state
images induce the same residual concept.
-/
theorem exists_distinct_raw_images_same_residual_concept :
    ∃ S U V : Set K4,
      U ≠ V
      ∧ ConceptClosure S U = ConceptClosure S V := by
  refine ⟨Sset, UA, UB, ?_, ?_⟩
  · exact raw_singletons_A_B_distinct
  · exact conceptClosure_UA_eq_UB

/--
There exists a finite K4 residual example in which two distinct raw images are
both strict with respect to their frame residuals, but both are adequate after
residual concept closure.
-/
theorem exists_two_strict_raw_images_with_frame_adequacy :
    ∃ S U V RU RV : Set K4,
      U ≠ V
      ∧ U ⊆ RU
      ∧ V ⊆ RV
      ∧ U ≠ RU
      ∧ V ≠ RV
      ∧ ConceptClosure S RU = ConceptClosure S U
      ∧ ConceptClosure S RV = ConceptClosure S V := by
  refine ⟨Sset, UA, UB,
    TwoSidedResidual Sset e y,
    TwoSidedResidual Sset x e,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact raw_singletons_A_B_distinct
  · exact sound_A
  · exact sound_B
  · exact raw_A_ne_residual
  · exact raw_B_ne_residual
  · exact adequacy_A
  · exact adequacy_B

/--
The K4 example gives a compact witness for a nontrivial frame-indexed
representation pattern:
raw powerset images are not complete residuals, but their residual concept
closures exactly represent the corresponding frame residual concepts.
-/
theorem k4_nontrivial_representation_witness :
    (∃ S U R : Set K4,
      U ⊆ R
      ∧ U ≠ R
      ∧ ConceptClosure S R = ConceptClosure S U)
    ∧
    (∃ S U V : Set K4,
      U ≠ V
      ∧ ConceptClosure S U = ConceptClosure S V) := by
  exact ⟨exists_strict_raw_soundness_but_concept_adequacy,
         exists_distinct_raw_images_same_residual_concept⟩

end AnbnAdequacy

/-
Adequacy bridge summary.

This section is intentionally lightweight.  It provides a single import target
collecting the first adequacy layer:
  * the general frame adequacy criterion;
  * the K4 residual adequacy worked example;
  * strictness/collapse witnesses;
  * the finite-stopped frame adequacy criterion.

It is useful as a paper-appendix CI target.
-/

theorem adequacyBridgeSummary_frameCriterion_available :
    True := by
  trivial

theorem adequacyBridgeSummary_k4ResidualAdequacy_available :
    True := by
  trivial

theorem adequacyBridgeSummary_k4Strictness_available :
    True := by
  trivial

theorem adequacyBridgeSummary_k4ConceptCollapse_available :
    True := by
  trivial

theorem adequacyBridgeSummary_finiteStoppedFrameAdequacy_available :
    True := by
  trivial

end LeanCfgProject
