import LeanCfgProject.FrameAdequacyCriterion
import LeanCfgProject.FiniteStoppingFrameResidual
import LeanCfgProject.LocalStoppingFrameResidual

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedFintypeInType false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u

/-
Finite stopped frame adequacy.

This file merges the finite-stopping layer with the frame adequacy criterion.

The guiding form is:

  if a finite stopped/closed-stage concept semantics covers the frame residual,
  then the frame residual concept equals the stopped-stage state concept.

Thus, after the finite saturation theorem, adequacy at a finite stage is reduced
to a concrete finite coverage check.

This is the bridge between:
  * effectiveness / finite stopping, and
  * frame-indexed adequacy / representation.
-/

/--
Closed-stage frame adequacy criterion for the standard observation `h`.

If stage `N` is closed and the frame residual is covered by the closed-stage
concept semantics of `X`, then the frame residual concept equals that
closed-stage concept semantics.
-/
theorem carrier_closedStage_frame_adequacy_of_coverage_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    (N : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage H.h H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        N))
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r)
    (hcover :
      TwoSidedResidual
          (CarrierStartImage H.h H profile R S0)
          (profile X).lt
          (profile X).rt
        ⊆
      CarrierClosedStageConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R N X) :
    ConceptClosure
        (CarrierStartImage H.h H profile R S0)
        (TwoSidedResidual
          (CarrierStartImage H.h H profile R S0)
          (profile X).lt
          (profile X).rt)
      =
      CarrierClosedStageConceptSemantics
        (CarrierStartImage H.h H profile R S0)
        H.h H profile R N X := by
  have hsound :
      SaturationIter
          (CarrierTerminalImage H.h H profile R)
          (CarrierBinaryRel H profile R)
          N X
        ⊆
      TwoSidedResidual
        (CarrierStartImage H.h H profile R S0)
        (profile X).lt
        (profile X).rt := by
    have hSemEq :
        SaturationIter
            (CarrierTerminalImage H.h H profile R)
            (CarrierBinaryRel H profile R)
            N X =
          CarrierStateSemantics H.h H profile R X :=
      closedStage_computes_carrierStateSemantics
        H.h H.map_append H profile R N hClosed X
    rw [hSemEq]
    exact carrier_state_semantics_subset_frame_residual_h
      H profile R S0 hStartFrame hctx
  unfold CarrierClosedStageConceptSemantics
  exact adequacy_of_residual_coverage
    (CarrierStartImage H.h H profile R S0)
    (SaturationIter
      (CarrierTerminalImage H.h H profile R)
      (CarrierBinaryRel H profile R)
      N X)
    (TwoSidedResidual
      (CarrierStartImage H.h H profile R S0)
      (profile X).lt
      (profile X).rt)
    hsound hcover

/--
Local-stopping version of closed-stage frame adequacy.

If the checkable equality `U_(N+1)=U_N` holds and the frame residual is covered
by the stopped-stage concept semantics, then the frame residual concept equals
the stopped-stage concept.
-/
theorem carrier_localStopped_frame_adequacy_of_coverage_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    (N : Nat)
    (hStop : ∀ X : W,
      SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        N X)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r)
    (hcover :
      TwoSidedResidual
          (CarrierStartImage H.h H profile R S0)
          (profile X).lt
          (profile X).rt
        ⊆
      CarrierClosedStageConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R N X) :
    ConceptClosure
        (CarrierStartImage H.h H profile R S0)
        (TwoSidedResidual
          (CarrierStartImage H.h H profile R S0)
          (profile X).lt
          (profile X).rt)
      =
      CarrierClosedStageConceptSemantics
        (CarrierStartImage H.h H profile R S0)
        H.h H profile R N X := by
  have hClosed :=
    carrierSaturationStage_closed_of_succ_eq
      H.h H profile R N hStop
  exact carrier_closedStage_frame_adequacy_of_coverage_h
    H profile R S0 hStartFrame N hClosed hctx hcover

/--
Finite-stopping existence version.

For finite carrier state type `W`, there exists a bounded closed stage `N`.
If, at that stage, the concrete coverage condition holds for a contextual
occurrence, then the frame residual concept equals the finite stopped-stage
concept semantics.
-/
theorem exists_le_finiteStopped_frame_adequacy_of_coverage_h
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
    (hctx : ContextFamily H profile R S0 X ell r)
    (hcoverAtClosed :
      ∀ N : Nat,
        IsSaturationClosed
          (CarrierTerminalImage H.h H profile R)
          (CarrierBinaryRel H profile R)
          (SaturationIter
            (CarrierTerminalImage H.h H profile R)
            (CarrierBinaryRel H profile R)
            N) →
        TwoSidedResidual
            (CarrierStartImage H.h H profile R S0)
            (profile X).lt
            (profile X).rt
          ⊆
        CarrierClosedStageConceptSemantics
            (CarrierStartImage H.h H profile R S0)
            H.h H profile R N X) :
    ∃ N ≤ Fintype.card W * Fintype.card M,
      ConceptClosure
          (CarrierStartImage H.h H profile R S0)
          (TwoSidedResidual
            (CarrierStartImage H.h H profile R S0)
            (profile X).lt
            (profile X).rt)
        =
        CarrierClosedStageConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R N X := by
  obtain ⟨N, hNB, hClosed⟩ :=
    exists_le_carrierIsSaturationClosed_stage_h_of_fintype
      H profile R
  refine ⟨N, hNB, ?_⟩
  exact carrier_closedStage_frame_adequacy_of_coverage_h
    H profile R S0 hStartFrame N hClosed hctx
    (hcoverAtClosed N hClosed)

/--
Finite-stopping concept version.

Under the same coverage-at-closed-stage condition, there exists a bounded stage
whose finite stopped-stage concept semantics is both equal to the frame residual
concept and equal to the carrier concept semantics.
-/
theorem exists_le_finiteStopped_frame_adequacy_and_carrierConcept_h
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
    (hctx : ContextFamily H profile R S0 X ell r)
    (hcoverAtClosed :
      ∀ N : Nat,
        IsSaturationClosed
          (CarrierTerminalImage H.h H profile R)
          (CarrierBinaryRel H profile R)
          (SaturationIter
            (CarrierTerminalImage H.h H profile R)
            (CarrierBinaryRel H profile R)
            N) →
        TwoSidedResidual
            (CarrierStartImage H.h H profile R S0)
            (profile X).lt
            (profile X).rt
          ⊆
        CarrierClosedStageConceptSemantics
            (CarrierStartImage H.h H profile R S0)
            H.h H profile R N X) :
    ∃ N ≤ Fintype.card W * Fintype.card M,
      (ConceptClosure
          (CarrierStartImage H.h H profile R S0)
          (TwoSidedResidual
            (CarrierStartImage H.h H profile R S0)
            (profile X).lt
            (profile X).rt)
        =
        CarrierClosedStageConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R N X)
      ∧
      (CarrierClosedStageConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R N X =
        CarrierConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R X) := by
  obtain ⟨N, hNB, hClosed⟩ :=
    exists_le_carrierIsSaturationClosed_stage_h_of_fintype
      H profile R
  refine ⟨N, hNB, ?_⟩
  constructor
  · exact carrier_closedStage_frame_adequacy_of_coverage_h
      H profile R S0 hStartFrame N hClosed hctx
      (hcoverAtClosed N hClosed)
  · exact carrierClosedStageConceptSemantics_eq_carrierConceptSemantics_h
      (CarrierStartImage H.h H profile R S0)
      H profile R N hClosed X

end LeanCfgProject
