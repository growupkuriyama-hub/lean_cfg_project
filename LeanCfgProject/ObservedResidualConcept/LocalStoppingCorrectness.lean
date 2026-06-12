import LeanCfgProject.ObservedResidualConcept.LaterClosedStageClosure
import LeanCfgProject.ObservedResidualConcept.ClosedStageFrameIntentStability
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/-
Local stopping correctness.

This is an "attack" layer for the algorithmic reading of finite saturation.

Previous modules phrase correctness using `IsSaturationClosed`.  This file
packages the same results in the form an implementation would actually test:

  if stage `N+1` is equal to stage `N`, then stage `N` is closed,
  computes the carrier saturation image, computes carrier state semantics,
  and its residual concept closure computes carrier concept semantics.

For the standard observation `h`, the same local stopping condition also
preserves the two-sided frame as residual/intent data.
-/

/--
A local stopping equality `N+1 = N` implies closedness of stage `N`.
-/
theorem carrierSaturationStage_closed_of_succ_eq
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat)
    (hStop : ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X) :
    IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N) := by
  exact (carrierSaturationStage_closed_iff_succ_eq
    q H profile R N).mpr hStop

/--
If the local stopping equality holds, then stage `N` is exactly the full
carrier saturation image.
-/
theorem carrierSaturationStage_eq_saturationImage_of_succ_eq
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat)
    (hStop : ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X)
    (X : W) :
    SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X =
      CarrierSaturationImage q H profile R X := by
  have hClosed :=
    carrierSaturationStage_closed_of_succ_eq
      q H profile R N hStop
  exact (carrierSaturationStage_closed_iff_eq_saturationImage
    q H profile R N).mp hClosed X

/--
If the local stopping equality holds, then stage `N` computes carrier state
semantics.
-/
theorem carrierSaturationStage_eq_stateSemantics_of_succ_eq
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat)
    (hStop : ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X)
    (X : W) :
    SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X =
      CarrierStateSemantics q H profile R X := by
  have hClosed :=
    carrierSaturationStage_closed_of_succ_eq
      q H profile R N hStop
  exact closedStage_computes_carrierStateSemantics
    q q_mul H profile R N hClosed X

/--
If the local stopping equality holds, then the closed-stage concept semantics at
stage `N` is the usual carrier concept semantics.
-/
theorem carrierClosedStageConcept_eq_carrierConcept_of_succ_eq
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat)
    (hStop : ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X)
    (X : W) :
    CarrierClosedStageConceptSemantics S q H profile R N X =
      CarrierConceptSemantics S q H profile R X := by
  have hClosed :=
    carrierSaturationStage_closed_of_succ_eq
      q H profile R N hStop
  exact closedStage_computes_carrierConceptSemantics
    S q q_mul H profile R N hClosed X

/--
If the local stopping equality holds, then every later saturation stage computes
carrier state semantics.
-/
theorem carrierSaturationIter_eq_stateSemantics_of_succ_eq_later
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N k : Nat)
    (hStop : ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X)
    (X : W) :
    SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + k) X =
      CarrierStateSemantics q H profile R X := by
  have hClosed :=
    carrierSaturationStage_closed_of_succ_eq
      q H profile R N hStop
  exact carrierSaturationIter_eq_stateSemantics_of_closed_later
    q q_mul H profile R N k hClosed X

/--
If the local stopping equality holds, then every later closed-stage concept
semantics computes carrier concept semantics.
-/
theorem carrierClosedStageConcept_later_eq_carrierConcept_of_succ_eq
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N k : Nat)
    (hStop : ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X)
    (X : W) :
    CarrierClosedStageConceptSemantics S q H profile R (N + k) X =
      CarrierConceptSemantics S q H profile R X := by
  have hClosed :=
    carrierSaturationStage_closed_of_succ_eq
      q H profile R N hStop
  exact carrierClosedStageConceptSemantics_later_eq_carrierConceptSemantics
    S q q_mul H profile R N k hClosed X

/--
Standard-observation version: local stopping for `h` computes carrier state
semantics.
-/
theorem carrierSaturationStage_eq_stateSemantics_h_of_succ_eq
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
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
    (X : W) :
    SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        N X =
      CarrierStateSemantics H.h H profile R X := by
  exact carrierSaturationStage_eq_stateSemantics_of_succ_eq
    H.h H.map_append H profile R N hStop X

/--
Standard-observation version: local stopping for `h` computes carrier concept
semantics.
-/
theorem carrierClosedStageConcept_eq_carrierConcept_h_of_succ_eq
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (S : Set M)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
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
    (X : W) :
    CarrierClosedStageConceptSemantics S H.h H profile R N X =
      CarrierConceptSemantics S H.h H profile R X := by
  exact carrierClosedStageConcept_eq_carrierConcept_of_succ_eq
    S H.h H.map_append H profile R N hStop X

/--
For the standard observation `h`, local stopping also preserves the typed frame
on the intent side of the closed-stage concept semantics.
-/
theorem carrier_frame_mem_commonContexts_localStoppedClosedStage_h
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
  have hClosed :=
    carrierSaturationStage_closed_of_succ_eq
      H.h H profile R N hStop
  exact carrier_frame_mem_commonContexts_closedStageConcept_h
    H profile R S0 hStartFrame N hClosed hctx

/--
For the standard observation `h`, local stopping also gives the frame-intent
property at every later closed-stage concept semantics.
-/
theorem carrier_frame_mem_commonContexts_localStoppedLaterClosedStage_h
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
  have hClosed :=
    carrierSaturationStage_closed_of_succ_eq
      H.h H profile R N hStop
  exact carrier_frame_mem_commonContexts_laterClosedStageConcept_h
    H profile R S0 hStartFrame N k hClosed hctx

end LeanCfgProject
