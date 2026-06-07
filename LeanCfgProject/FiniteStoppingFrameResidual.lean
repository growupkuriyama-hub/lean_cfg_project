import LeanCfgProject.FiniteSaturationMeasure
import LeanCfgProject.ClosedStageFrameBridge
import LeanCfgProject.ClosedStageFrameIntentStability

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedFintypeInType false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u

/-
Finite stopping frame consequences.

This file combines the unconditional finite-stopping theorem from
`FiniteSaturationMeasure` with the two-sided frame/residual/intent bridge.

For the standard observation `h`, if the carrier state type is finite, then
there exists a bounded finite saturation stage whose residual concept
semantics both computes the carrier concept semantics and retains the typed
two-sided frame as residual/intent information.
-/

/--
For the standard observation `h`, there exists a bounded closed finite
saturation stage at which the typed frame belongs to the intent side of the
closed-stage concept semantics.
-/
theorem exists_le_carrierStage_frame_intent_h_of_fintype
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u} [Fintype W]
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    ∃ N ≤ Fintype.card W * Fintype.card M,
      ((profile X).lt, (profile X).rt) ∈
        CommonContexts
          (CarrierStartImage H.h H profile R S0)
          (CarrierClosedStageConceptSemantics
            (CarrierStartImage H.h H profile R S0)
            H.h H profile R N X) := by
  obtain ⟨N, hNB, hClosed⟩ :=
    exists_le_carrierIsSaturationClosed_stage_h_of_fintype
      H profile R
  refine ⟨N, hNB, ?_⟩
  exact carrier_frame_mem_commonContexts_closedStageConcept_h
    H profile R S0 hStartFrame N hClosed hctx

/--
For the standard observation `h`, there exists a bounded closed finite
saturation stage whose closed-stage concept semantics is bounded by the
residual closure determined by the typed frame.
-/
theorem exists_le_carrierStage_frame_residual_bound_h_of_fintype
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u} [Fintype W]
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    ∃ N ≤ Fintype.card W * Fintype.card M,
      CarrierClosedStageConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R N X ⊆
        ConceptClosure
          (CarrierStartImage H.h H profile R S0)
          (TwoSidedResidual
            (CarrierStartImage H.h H profile R S0)
            (profile X).lt
            (profile X).rt) := by
  obtain ⟨N, hNB, hClosed⟩ :=
    exists_le_carrierIsSaturationClosed_stage_h_of_fintype
      H profile R
  refine ⟨N, hNB, ?_⟩
  exact carrierClosedStageConceptSemantics_subset_frame_residual_closure_h
    H profile R S0 hStartFrame N hClosed hctx

/--
Combined bounded finite-stopping frame theorem: for the standard observation
`h`, there exists a bounded closed finite saturation stage whose closed-stage
concept semantics both has the typed frame on its intent side and is bounded by
the corresponding frame residual closure.
-/
theorem exists_le_carrierStage_frame_intent_and_residual_h_of_fintype
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u} [Fintype W]
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    ∃ N ≤ Fintype.card W * Fintype.card M,
      (((profile X).lt, (profile X).rt) ∈
        CommonContexts
          (CarrierStartImage H.h H profile R S0)
          (CarrierClosedStageConceptSemantics
            (CarrierStartImage H.h H profile R S0)
            H.h H profile R N X))
      ∧
      (CarrierClosedStageConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R N X ⊆
        ConceptClosure
          (CarrierStartImage H.h H profile R S0)
          (TwoSidedResidual
            (CarrierStartImage H.h H profile R S0)
            (profile X).lt
            (profile X).rt)) := by
  obtain ⟨N, hNB, hClosed⟩ :=
    exists_le_carrierIsSaturationClosed_stage_h_of_fintype
      H profile R
  refine ⟨N, hNB, ?_⟩
  constructor
  · exact carrier_frame_mem_commonContexts_closedStageConcept_h
      H profile R S0 hStartFrame N hClosed hctx
  · exact carrierClosedStageConceptSemantics_subset_frame_residual_closure_h
      H profile R S0 hStartFrame N hClosed hctx

/--
For the standard observation `h`, there exists a bounded finite stage that
computes carrier concept semantics for all states and simultaneously carries
the frame-intent and frame-residual information for the chosen contextual
occurrence.
-/
theorem exists_le_carrierStage_computes_concept_and_frame_h_of_fintype
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u} [Fintype W]
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    ∃ N ≤ Fintype.card W * Fintype.card M,
      (∀ Y : W,
        CarrierClosedStageConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R N Y =
          CarrierConceptSemantics
            (CarrierStartImage H.h H profile R S0)
            H.h H profile R Y)
      ∧
      (((profile X).lt, (profile X).rt) ∈
        CommonContexts
          (CarrierStartImage H.h H profile R S0)
          (CarrierClosedStageConceptSemantics
            (CarrierStartImage H.h H profile R S0)
            H.h H profile R N X))
      ∧
      (CarrierClosedStageConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R N X ⊆
        ConceptClosure
          (CarrierStartImage H.h H profile R S0)
          (TwoSidedResidual
            (CarrierStartImage H.h H profile R S0)
            (profile X).lt
            (profile X).rt)) := by
  obtain ⟨N, hNB, hClosed⟩ :=
    exists_le_carrierIsSaturationClosed_stage_h_of_fintype
      H profile R
  refine ⟨N, hNB, ?_⟩
  constructor
  · intro Y
    exact carrierClosedStageConceptSemantics_eq_carrierConceptSemantics_h
      (CarrierStartImage H.h H profile R S0)
      H profile R N hClosed Y
  · constructor
    · exact carrier_frame_mem_commonContexts_closedStageConcept_h
        H profile R S0 hStartFrame N hClosed hctx
    · exact carrierClosedStageConceptSemantics_subset_frame_residual_closure_h
        H profile R S0 hStartFrame N hClosed hctx

end LeanCfgProject
