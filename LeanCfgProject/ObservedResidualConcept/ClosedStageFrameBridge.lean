import LeanCfgProject.ObservedResidualConcept.ClosedStageConceptBridge
import LeanCfgProject.ObservedResidualConcept.FrameIntentClosureBridge
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u

/-
Closed-stage frame bridge.

This file connects the closed-stage saturation semantics with the two-sided
frame/residual results.  The point is that, once a finite `h`-saturation stage
is closed, the concept closure of that *finite stage* already has the same
frame-residual and frame-intent properties as the full carrier concept
semantics.
-/

/--
If a finite `h`-saturation stage is closed, then the concept semantics obtained
from that closed stage is contained in the residual closure determined by the
typed two-sided frame.
-/
theorem carrierClosedStageConceptSemantics_subset_frame_residual_closure_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    (n : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage H.h H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        n))
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    CarrierClosedStageConceptSemantics
        (CarrierStartImage H.h H profile R S0)
        H.h H profile R n X ⊆
      ConceptClosure
        (CarrierStartImage H.h H profile R S0)
        (TwoSidedResidual
          (CarrierStartImage H.h H profile R S0)
          (profile X).lt
          (profile X).rt) := by
  rw [carrierClosedStageConceptSemantics_eq_carrierConceptSemantics_h
    (CarrierStartImage H.h H profile R S0) H profile R n hClosed X]
  exact carrierConceptSemantics_subset_frame_residual_closure_via_saturation_h
    H profile R S0 hStartFrame hctx

/--
If a finite `h`-saturation stage is closed, then the typed frame belongs to the
intent side of the closed-stage concept semantics.
-/
theorem carrier_frame_mem_commonContexts_closedStageConcept_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    (n : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage H.h H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        n))
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    ((profile X).lt, (profile X).rt) ∈
      CommonContexts
        (CarrierStartImage H.h H profile R S0)
        (CarrierClosedStageConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R n X) := by
  rw [carrierClosedStageConceptSemantics_eq_carrierConceptSemantics_h
    (CarrierStartImage H.h H profile R S0) H profile R n hClosed X]
  exact carrier_frame_mem_commonContexts_carrierConcept_h
    H profile R S0 hStartFrame hctx

/--
Closed-stage version of the frame-intent statement, expressed through
saturation-concept semantics.  This is useful when the paper wants to describe
the finite algorithm as: iterate saturation until closed, then close the finite
stage in the residual concept lattice.
-/
theorem carrier_frame_mem_commonContexts_closedStage_as_saturationConcept_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    (n : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage H.h H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        n))
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    ((profile X).lt, (profile X).rt) ∈
      CommonContexts
        (CarrierStartImage H.h H profile R S0)
        (CarrierSaturationConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R X) := by
  exact carrier_frame_mem_commonContexts_saturationConcept_h
    H profile R S0 hStartFrame hctx

end LeanCfgProject
