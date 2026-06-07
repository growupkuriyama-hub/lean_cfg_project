import LeanCfgProject.ClosedStageRuleSemantics

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/-
Later closed-stage closure.

This "attack" layer strengthens the closed-stage story itself:

  once a saturation stage `N` is closed, every later stage `N+k` is also closed.

Together with the previous modules, this means that after stopping, every later
finite stage is again a rule-closed semantic model, computes the same state
semantics, and yields the same residual concept semantics.
-/

/--
Generic version: once a saturation stage `N` is closed, every later stage
`N + k` is closed.
-/
theorem saturationIter_closed_of_closed_add
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (N k : Nat)
    (hClosed : IsSaturationClosed Terminal Binary
      (SaturationIter Terminal Binary N)) :
    IsSaturationClosed Terminal Binary
      (SaturationIter Terminal Binary (N + k)) := by
  rw [saturationStage_closed_iff_succ_eq]
  intro X
  calc
    SaturationIter Terminal Binary ((N + k) + 1) X =
        SaturationIter Terminal Binary N X := by
          rw [Nat.add_assoc]
          exact saturationIter_eq_closed_stage_add
            Terminal Binary N (k + 1) hClosed X
    _ =
        SaturationIter Terminal Binary (N + k) X := by
          symm
          exact saturationIter_eq_closed_stage_add
            Terminal Binary N k hClosed X

/--
Generic version with an arbitrary later stage `m ≥ N`.
-/
theorem saturationIter_closed_of_closed_le
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    {N m : Nat}
    (hNm : N ≤ m)
    (hClosed : IsSaturationClosed Terminal Binary
      (SaturationIter Terminal Binary N)) :
    IsSaturationClosed Terminal Binary
      (SaturationIter Terminal Binary m) := by
  rw [saturationStage_closed_iff_succ_eq]
  intro X
  calc
    SaturationIter Terminal Binary (m + 1) X =
        SaturationIter Terminal Binary N X := by
          exact saturationIter_eq_of_le_closed_stage
            Terminal Binary (Nat.succ_le_succ hNm) hClosed X
    _ =
        SaturationIter Terminal Binary m X := by
          symm
          exact saturationIter_eq_of_le_closed_stage
            Terminal Binary hNm hClosed X

/--
Carrier version: once carrier saturation stage `N` is closed, every later stage
`N+k` is closed.
-/
theorem carrierSaturationIter_closed_of_closed_add
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
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
        N)) :
    IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + k)) := by
  exact saturationIter_closed_of_closed_add
    (CarrierTerminalImage q H profile R)
    (CarrierBinaryRel H profile R)
    N k hClosed

/--
Carrier version with an arbitrary later stage `m ≥ N`.
-/
theorem carrierSaturationIter_closed_of_closed_le
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    {N m : Nat}
    (hNm : N ≤ m)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N)) :
    IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        m) := by
  exact saturationIter_closed_of_closed_le
    (CarrierTerminalImage q H profile R)
    (CarrierBinaryRel H profile R)
    hNm hClosed

/--
If a stage covers the full carrier saturation image, then every later stage is
closed.
-/
theorem carrierSaturationIter_closed_of_covers_add
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
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
          N X) :
    IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + k)) := by
  have hClosed :=
    carrierSaturationStage_closed_of_covers_saturationImage
      q H profile R N hCover
  exact carrierSaturationIter_closed_of_closed_add
    q H profile R N k hClosed

/--
Standard-observation version: if an `h`-saturation stage is closed, all later
`h`-saturation stages are closed.
-/
theorem carrierSaturationIter_closed_of_closed_add_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
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
        N)) :
    IsSaturationClosed
      (CarrierTerminalImage H.h H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        (N + k)) := by
  exact carrierSaturationIter_closed_of_closed_add
    H.h H profile R N k hClosed

/--
If a stage `N` is closed, then the local stopping criterion holds at every
later stage `N+k`.
-/
theorem carrierSaturationIter_succ_eq_of_closed_later
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
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
    SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        ((N + k) + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + k) X := by
  have hLater :=
    carrierSaturationIter_closed_of_closed_add
      q H profile R N k hClosed
  exact (carrierSaturationStage_closed_iff_succ_eq
    q H profile R (N + k)).mp hLater X

/--
If a stage covers the full saturation image, then the local stopping criterion
holds at every later stage.
-/
theorem carrierSaturationIter_succ_eq_of_covers_later
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
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
    SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        ((N + k) + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + k) X := by
  have hClosed :=
    carrierSaturationStage_closed_of_covers_saturationImage
      q H profile R N hCover
  exact carrierSaturationIter_succ_eq_of_closed_later
    q H profile R N k hClosed X

end LeanCfgProject
