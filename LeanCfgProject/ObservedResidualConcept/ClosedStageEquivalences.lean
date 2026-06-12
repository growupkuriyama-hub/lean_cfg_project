import LeanCfgProject.ObservedResidualConcept.FiniteCoverageStopping
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/-
Closed-stage equivalences.

This is an "attack" layer toward finite stopping and executable saturation
criteria.  It turns the closed-stage results into usable equivalences:

* a stage is closed iff the next stage is equal to it;
* for carrier saturation, a stage is closed iff it covers the full saturation
  image;
* equivalently, a closed carrier stage is exactly the full saturation image;
* with a multiplicative observation, a closed carrier stage is exactly the
  carrier state semantics.

These statements are useful for the paper's effectiveness story because they
identify several interchangeable ways of recognizing that saturation has
already computed the desired semantics.
-/

/--
A saturation stage is closed iff the next saturation stage is equal to it.
This is the local stopping criterion.
-/
theorem saturationStage_closed_iff_succ_eq
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (N : Nat) :
    IsSaturationClosed Terminal Binary
      (SaturationIter Terminal Binary N)
    ↔
    ∀ X : State,
      SaturationIter Terminal Binary (N + 1) X =
        SaturationIter Terminal Binary N X := by
  constructor
  · intro hClosed X
    exact saturationIter_succ_eq_of_closed Terminal Binary N hClosed X
  · intro hEq
    intro X a ha
    change a ∈ SaturationIter Terminal Binary (N + 1) X at ha
    simpa [hEq X] using ha

/--
Carrier version of the local stopping criterion.
-/
theorem carrierSaturationStage_closed_iff_succ_eq
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat) :
    IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N)
    ↔
    ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X := by
  exact saturationStage_closed_iff_succ_eq
    (CarrierTerminalImage q H profile R)
    (CarrierBinaryRel H profile R)
    N

/--
For carrier saturation, a finite stage is closed iff it contains the full
carrier saturation image.  The forward direction says that a closed stage
already captures all finite insertions; the reverse direction says that a stage
covering the full image is automatically closed.
-/
theorem carrierSaturationStage_closed_iff_covers_saturationImage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat) :
    IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N)
    ↔
    ∀ X : W,
      CarrierSaturationImage q H profile R X ⊆
        SaturationIter
          (CarrierTerminalImage q H profile R)
          (CarrierBinaryRel H profile R)
          N X := by
  constructor
  · intro hClosed X a ha
    have hEq :=
      carrierSaturationImage_eq_of_closed_stage q H profile R N hClosed X
    simpa [hEq] using ha
  · intro hCover
    exact carrierSaturationStage_closed_of_covers_saturationImage
      q H profile R N hCover

/--
A carrier saturation stage is closed iff it is exactly the full carrier
saturation image.
-/
theorem carrierSaturationStage_closed_iff_eq_saturationImage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat) :
    IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N)
    ↔
    ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X =
      CarrierSaturationImage q H profile R X := by
  constructor
  · intro hClosed X
    symm
    exact carrierSaturationImage_eq_of_closed_stage
      q H profile R N hClosed X
  · intro hEq
    apply carrierSaturationStage_closed_of_covers_saturationImage
      q H profile R N
    intro X a ha
    simpa [(hEq X).symm] using ha

/--
With a multiplicative observation, a carrier saturation stage is closed iff it
is exactly the carrier state semantics.
-/
theorem carrierSaturationStage_closed_iff_eq_stateSemantics
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat) :
    IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N)
    ↔
    ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X =
      CarrierStateSemantics q H profile R X := by
  constructor
  · intro hClosed X
    exact closedStage_computes_carrierStateSemantics
      q q_mul H profile R N hClosed X
  · intro hEq
    apply carrierSaturationStage_closed_of_covers_saturationImage
      q H profile R N
    intro X a ha
    have hSatState :
        a ∈ CarrierStateSemantics q H profile R X := by
      have hImg :=
        carrier_saturationImage_eq_stateSemantics q q_mul H profile R X
      simpa [hImg] using ha
    simpa [(hEq X).symm] using hSatState

/--
Standard-observation version: a finite `h`-saturation stage is closed iff it
is exactly the carrier state semantics for `h`.
-/
theorem carrierSaturationStage_closed_iff_eq_stateSemantics_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat) :
    IsSaturationClosed
      (CarrierTerminalImage H.h H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        N)
    ↔
    ∀ X : W,
      SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        N X =
      CarrierStateSemantics H.h H profile R X := by
  exact carrierSaturationStage_closed_iff_eq_stateSemantics
    H.h H.map_append H profile R N

/--
A stopped carrier saturation stage remains equal to carrier state semantics at
all later stages.
-/
theorem carrierSaturationIter_eq_stateSemantics_of_closed_later
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
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N))
    (X : W) :
    SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + k) X =
      CarrierStateSemantics q H profile R X := by
  calc
    SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + k) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X := by
          exact carrierSaturationIter_eq_closed_stage_add
            q H profile R N k hClosed X
    _ =
      CarrierStateSemantics q H profile R X := by
          exact closedStage_computes_carrierStateSemantics
            q q_mul H profile R N hClosed X

end LeanCfgProject
