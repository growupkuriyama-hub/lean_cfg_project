import LeanCfgProject.ClosedStageEquivalences

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/-
Closed-stage concept stability.

This is an "attack" layer after `ClosedStageEquivalences`.
It upgrades closed-stage stability from raw saturation stages to residual
concept semantics.

Mathematically: once a finite saturation stage is closed, not only the raw
saturation stages but also the residual concept semantics obtained from all
later stages are stable and equal to the carrier concept semantics.
-/

/--
If stage `N` is closed, then the closed-stage concept semantics at stage
`N + k` is equal to the closed-stage concept semantics at stage `N`.
-/
theorem carrierClosedStageConceptSemantics_eq_of_closed_later
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N k : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N))
    (X : W) :
    CarrierClosedStageConceptSemantics S q H profile R (N + k) X =
      CarrierClosedStageConceptSemantics S q H profile R N X := by
  unfold CarrierClosedStageConceptSemantics
  rw [carrierSaturationIter_eq_closed_stage_add
    q H profile R N k hClosed X]

/--
If stage `N` is closed, then every later closed-stage concept semantics computes
the usual carrier concept semantics.
-/
theorem carrierClosedStageConceptSemantics_later_eq_carrierConceptSemantics
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
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N))
    (X : W) :
    CarrierClosedStageConceptSemantics S q H profile R (N + k) X =
      CarrierConceptSemantics S q H profile R X := by
  calc
    CarrierClosedStageConceptSemantics S q H profile R (N + k) X =
        CarrierClosedStageConceptSemantics S q H profile R N X := by
          exact carrierClosedStageConceptSemantics_eq_of_closed_later
            S q H profile R N k hClosed X
    _ =
        CarrierConceptSemantics S q H profile R X := by
          exact carrierClosedStageConceptSemantics_eq_carrierConceptSemantics
            S q q_mul H profile R N hClosed X

/--
Standard-observation version of later concept stability.
-/
theorem carrierClosedStageConceptSemantics_later_eq_carrierConceptSemantics_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (S : Set M)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N k : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage H.h H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        N))
    (X : W) :
    CarrierClosedStageConceptSemantics S H.h H profile R (N + k) X =
      CarrierConceptSemantics S H.h H profile R X := by
  exact carrierClosedStageConceptSemantics_later_eq_carrierConceptSemantics
    S H.h H.map_append H profile R N k hClosed X

/--
If stage `N` is closed, then all later closed-stage concept semantics are equal
to each other.
-/
theorem carrierClosedStageConceptSemantics_eq_of_closed_two_later
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N k l : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N))
    (X : W) :
    CarrierClosedStageConceptSemantics S q H profile R (N + k) X =
      CarrierClosedStageConceptSemantics S q H profile R (N + l) X := by
  calc
    CarrierClosedStageConceptSemantics S q H profile R (N + k) X =
        CarrierClosedStageConceptSemantics S q H profile R N X := by
          exact carrierClosedStageConceptSemantics_eq_of_closed_later
            S q H profile R N k hClosed X
    _ =
        CarrierClosedStageConceptSemantics S q H profile R (N + l) X := by
          symm
          exact carrierClosedStageConceptSemantics_eq_of_closed_later
            S q H profile R N l hClosed X

/--
If a stage covers the full carrier saturation image, then every later
closed-stage concept semantics computes the usual carrier concept semantics.
This is the finite-coverage version of later concept stability.
-/
theorem carrierClosedStageConceptSemantics_later_eq_carrierConcept_of_covers
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
    (hCover : ∀ X : W,
      CarrierSaturationImage q H profile R X ⊆
        SaturationIter
          (CarrierTerminalImage q H profile R)
          (CarrierBinaryRel H profile R)
          N X)
    (X : W) :
    CarrierClosedStageConceptSemantics S q H profile R (N + k) X =
      CarrierConceptSemantics S q H profile R X := by
  have hClosed :=
    carrierSaturationStage_closed_of_covers_saturationImage
      q H profile R N hCover
  exact carrierClosedStageConceptSemantics_later_eq_carrierConceptSemantics
    S q q_mul H profile R N k hClosed X

/--
Standard-observation finite-coverage version of later concept stability.
-/
theorem carrierClosedStageConceptSemantics_later_eq_carrierConcept_h_of_covers
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (S : Set M)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N k : Nat)
    (hCover : ∀ X : W,
      CarrierSaturationImage H.h H profile R X ⊆
        SaturationIter
          (CarrierTerminalImage H.h H profile R)
          (CarrierBinaryRel H profile R)
          N X)
    (X : W) :
    CarrierClosedStageConceptSemantics S H.h H profile R (N + k) X =
      CarrierConceptSemantics S H.h H profile R X := by
  exact carrierClosedStageConceptSemantics_later_eq_carrierConcept_of_covers
    S H.h H.map_append H profile R N k hCover X

/--
If stage `N` is closed, then binary rule soundness holds at every later
closed-stage concept level.
-/
theorem carrier_binaryRule_sound_as_laterClosedStageConceptSemantics
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N k : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N))
    (br : CarrierBinaryRule profile)
    (hmem : List.Mem (CarrierTypedRule.binary br) R) :
    ConceptProduct S
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + k) br.Y)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + k) br.Z)
      ⊆
    CarrierClosedStageConceptSemantics S q H profile R (N + k) br.X := by
  have hLaterClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + k)) := by
    intro X a ha
    have hEqStage :=
      carrierSaturationIter_eq_closed_stage_add
        q H profile R N k hClosed X
    have hClosedN := hClosed X
    -- rewrite the goal and assumption back to stage N
    rw [hEqStage] at ha
    have hRes := hClosedN ha
    simpa [hEqStage] using hRes
  exact carrier_binaryRule_sound_as_closedStageConceptSemantics
    S q H profile R (N + k) hLaterClosed br hmem

end LeanCfgProject
