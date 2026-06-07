import LeanCfgProject.LocalStoppingCorrectness
import LeanCfgProject.ClosedStageFrameIntentStability

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u

/-
Local stopping frame/residual consequences.

This file packages the two-sided frame consequences of the checkable local
stopping condition

  SaturationIter (N+1) = SaturationIter N

for the standard observation `h`.

After local stopping is detected, the stopped stage and all later closed-stage
concept semantics still remember the typed two-sided frame as an intent-side
common context and remain bounded by the corresponding frame residual closure.
-/

/--
If local stopping is detected for the standard observation `h`, then the
stopped-stage concept semantics is bounded by the residual closure determined
by the typed frame.
-/
theorem carrier_stoppedStageConcept_subset_frame_residual_closure_h
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
    (hctx : ContextFamily H profile R S0 X ell r) :
    CarrierClosedStageConceptSemantics
        (CarrierStartImage H.h H profile R S0)
        H.h H profile R N X ⊆
      ConceptClosure
        (CarrierStartImage H.h H profile R S0)
        (TwoSidedResidual
          (CarrierStartImage H.h H profile R S0)
          (profile X).lt
          (profile X).rt) := by
  have hClosed :=
    carrierSaturationStage_closed_of_succ_eq
      H.h H profile R N hStop
  exact carrierClosedStageConceptSemantics_subset_frame_residual_closure_h
    H profile R S0 hStartFrame N hClosed hctx

/--
If local stopping is detected for the standard observation `h`, then every
later closed-stage concept semantics is bounded by the residual closure
determined by the typed frame.
-/
theorem carrier_laterStoppedStageConcept_subset_frame_residual_closure_h
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
    carrierSaturationStage_closed_of_succ_eq
      H.h H profile R N hStop
  exact carrier_laterClosedStageConcept_subset_frame_residual_closure_h
    H profile R S0 hStartFrame N k hClosed hctx

/--
If local stopping is detected, the typed frame remains in the intent side of
the stopped-stage concept semantics.
This is a residual/intent paired version of local stopping.
-/
theorem carrier_frame_mem_commonContexts_stoppedStageConcept_h_of_succ_eq
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
    (hctx : ContextFamily H profile R S0 X ell r) :
    ((profile X).lt, (profile X).rt) ∈
      CommonContexts
        (CarrierStartImage H.h H profile R S0)
        (CarrierClosedStageConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R N X) := by
  exact carrier_frame_mem_commonContexts_localStoppedClosedStage_h
    H profile R S0 hStartFrame N hStop hctx

/--
If local stopping is detected, the typed frame remains in the intent side of
every later closed-stage concept semantics.
-/
theorem carrier_frame_mem_commonContexts_laterStoppedStageConcept_h_of_succ_eq
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
    (hctx : ContextFamily H profile R S0 X ell r) :
    ((profile X).lt, (profile X).rt) ∈
      CommonContexts
        (CarrierStartImage H.h H profile R S0)
        (CarrierClosedStageConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R (N + k) X) := by
  exact carrier_frame_mem_commonContexts_localStoppedLaterClosedStage_h
    H profile R S0 hStartFrame N k hStop hctx

/--
Combined local-stopping frame theorem: after local stopping, the stopped-stage
concept semantics has both the intent-side frame membership and the residual
closure bound.
-/
theorem carrier_localStopped_frame_intent_and_residual_h
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
    (hctx : ContextFamily H profile R S0 X ell r) :
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
  constructor
  · exact carrier_frame_mem_commonContexts_stoppedStageConcept_h_of_succ_eq
      H profile R S0 hStartFrame N hStop hctx
  · exact carrier_stoppedStageConcept_subset_frame_residual_closure_h
      H profile R S0 hStartFrame N hStop hctx

end LeanCfgProject
