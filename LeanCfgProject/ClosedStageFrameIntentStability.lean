import LeanCfgProject.ClosedStageConceptStability
import LeanCfgProject.ClosedStageFrameBridge

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u

/-
Closed-stage frame-intent stability.

This is an "attack" layer after `ClosedStageConceptStability`.
It combines concept-level stability after a closed saturation stage with the
two-sided frame residual/intent bridge.

Mathematically: once an `h`-saturation stage is closed, all later closed-stage
concept semantics still remember the two-sided typed frame as an intent-side
common context, and remain bounded by the corresponding frame residual closure.
-/

/--
After a closed `h`-saturation stage, every later closed-stage concept semantics
still has the typed frame in its intent side.
-/
theorem carrier_frame_mem_commonContexts_laterClosedStageConcept_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    (N k : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage H.h H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        N))
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    ((profile X).lt, (profile X).rt) ∈
      CommonContexts
        (CarrierStartImage H.h H profile R S0)
        (CarrierClosedStageConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R (N + k) X) := by
  rw [carrierClosedStageConceptSemantics_later_eq_carrierConceptSemantics_h
    (CarrierStartImage H.h H profile R S0)
    H profile R N k hClosed X]
  exact carrier_frame_mem_commonContexts_carrierConcept_h
    H profile R S0 hStartFrame hctx

/--
After a closed `h`-saturation stage, every later closed-stage concept semantics
is contained in the frame residual closure determined by the typed frame.
-/
theorem carrier_laterClosedStageConcept_subset_frame_residual_closure_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    (N k : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage H.h H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        N))
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    CarrierClosedStageConceptSemantics
        (CarrierStartImage H.h H profile R S0)
        H.h H profile R (N + k) X ⊆
      ConceptClosure
        (CarrierStartImage H.h H profile R S0)
        (TwoSidedResidual
          (CarrierStartImage H.h H profile R S0)
          (profile X).lt
          (profile X).rt) := by
  rw [carrierClosedStageConceptSemantics_later_eq_carrierConceptSemantics_h
    (CarrierStartImage H.h H profile R S0)
    H profile R N k hClosed X]
  exact carrierConceptSemantics_subset_frame_residual_closure_via_saturation_h
    H profile R S0 hStartFrame hctx

/--
Finite-coverage version: if stage `N` covers the full saturation image, then
every later closed-stage concept semantics has the typed frame in its intent
side.
-/
theorem carrier_frame_mem_commonContexts_laterClosedStageConcept_h_of_covers
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    (N k : Nat)
    (hCover : ∀ X : W,
      CarrierSaturationImage H.h H profile R X ⊆
        SaturationIter
          (CarrierTerminalImage H.h H profile R)
          (CarrierBinaryRel H profile R)
          N X)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    ((profile X).lt, (profile X).rt) ∈
      CommonContexts
        (CarrierStartImage H.h H profile R S0)
        (CarrierClosedStageConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R (N + k) X) := by
  have hClosed :=
    carrierSaturationStage_closed_of_covers_saturationImage
      H.h H profile R N hCover
  exact carrier_frame_mem_commonContexts_laterClosedStageConcept_h
    H profile R S0 hStartFrame N k hClosed hctx

/--
Finite-coverage version: if stage `N` covers the full saturation image, then
every later closed-stage concept semantics is bounded by the frame residual
closure.
-/
theorem carrier_laterClosedStageConcept_subset_frame_residual_closure_h_of_covers
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    (N k : Nat)
    (hCover : ∀ X : W,
      CarrierSaturationImage H.h H profile R X ⊆
        SaturationIter
          (CarrierTerminalImage H.h H profile R)
          (CarrierBinaryRel H profile R)
          N X)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    CarrierClosedStageConceptSemantics
        (CarrierStartImage H.h H profile R S0)
        H.h H profile R (N + k) X ⊆
      ConceptClosure
        (CarrierStartImage H.h H profile R S0)
        (TwoSidedResidual
          (CarrierStartImage H.h H profile R S0)
          (profile X).lt
          (profile X).rt) := by
  have hClosed :=
    carrierSaturationStage_closed_of_covers_saturationImage
      H.h H profile R N hCover
  exact carrier_laterClosedStageConcept_subset_frame_residual_closure_h
    H profile R S0 hStartFrame N k hClosed hctx

end LeanCfgProject
