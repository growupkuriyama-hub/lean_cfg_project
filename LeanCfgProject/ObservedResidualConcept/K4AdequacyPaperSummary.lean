import LeanCfgProject.ObservedResidualConcept.AdequacyBridgeSummary
import LeanCfgProject.ObservedResidualConcept.K4ConceptCollapse
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject
namespace AnbnAdequacy

/-
K4AdequacyPaperSummary.lean

Paper-facing summary target for the K4 adequacy witness.

This file does not add new mathematics.  It collects the verified K4 witness
theorems under compact names suitable for the paper appendix.
-/

open K4

/--
There is a finite K4 witness where raw soundness is strict but concept
adequacy holds.
-/
theorem k4_paper_witness_strict_raw_soundness_but_concept_adequacy :
    ∃ S U R : Set K4,
      U ⊆ R
      ∧ U ≠ R
      ∧ ConceptClosure S R = ConceptClosure S U :=
  exists_strict_raw_soundness_but_concept_adequacy

/--
There are distinct raw K4 images inducing the same residual concept.
-/
theorem k4_paper_witness_distinct_raw_images_same_concept :
    ∃ S U V : Set K4,
      U ≠ V
      ∧ ConceptClosure S U = ConceptClosure S V :=
  exists_distinct_raw_images_same_residual_concept

/--
There are two distinct strict raw K4 images, each adequate for its frame
residual after concept closure.
-/
theorem k4_paper_witness_two_strict_raw_images_with_frame_adequacy :
    ∃ S U V RU RV : Set K4,
      U ≠ V
      ∧ U ⊆ RU
      ∧ V ⊆ RV
      ∧ U ≠ RU
      ∧ V ≠ RV
      ∧ ConceptClosure S RU = ConceptClosure S U
      ∧ ConceptClosure S RV = ConceptClosure S V :=
  exists_two_strict_raw_images_with_frame_adequacy

/--
Compact K4 witness package used by the paper appendix.
-/
theorem k4_paper_witness_package :
    (∃ S U R : Set K4,
      U ⊆ R
      ∧ U ≠ R
      ∧ ConceptClosure S R = ConceptClosure S U)
    ∧
    (∃ S U V : Set K4,
      U ≠ V
      ∧ ConceptClosure S U = ConceptClosure S V) :=
  k4_nontrivial_representation_witness

/--
The concrete K4 example simultaneously exhibits bidirectional concept
adequacy and nontrivial raw strictness.
-/
theorem k4_paper_bidirectional_and_nontrivial :
    ((ConceptClosure Sset (TwoSidedResidual Sset e e) =
        ConceptClosure Sset US)
    ∧ (ConceptClosure Sset (TwoSidedResidual Sset e y) =
        ConceptClosure Sset UA)
    ∧ (ConceptClosure Sset (TwoSidedResidual Sset x e) =
        ConceptClosure Sset UB)
    ∧ (ConceptClosure Sset (TwoSidedResidual Sset x e) =
        ConceptClosure Sset UT))
    ∧
    ((UA ≠ TwoSidedResidual Sset e y)
      ∧ (UB ≠ TwoSidedResidual Sset x e)) :=
  k4_bidirectional_and_nontrivial

/--
The K4 collapse summary: distinct raw singleton images collapse to the same
residual concept while remaining strict at the powerset level.
-/
theorem k4_paper_nontrivial_collapse_summary :
    UA ≠ UB
    ∧ UA ≠ TwoSidedResidual Sset e y
    ∧ UB ≠ TwoSidedResidual Sset x e
    ∧ ConceptClosure Sset UA = OSet
    ∧ ConceptClosure Sset UB = OSet
    ∧ ConceptClosure Sset (TwoSidedResidual Sset e y) = OSet
    ∧ ConceptClosure Sset (TwoSidedResidual Sset x e) = OSet :=
  k4_nontrivial_collapse_summary

end AnbnAdequacy
end LeanCfgProject
