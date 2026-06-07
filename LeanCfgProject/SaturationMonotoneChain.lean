import LeanCfgProject.SaturationStability

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/-
Monotone-chain consequences for saturation.

The basic monotonicity theorem `saturationIter_mono_of_le` already exists in
`CarrierSaturationCorrectness`.  This file packages the consequences needed for
the finite-algorithm story: once a stage is closed, all later stages are equal
to it.
-/

/--
If stage `n` is closed, then every later stage `m ≥ n` is equal to stage `n`.
-/
theorem saturationIter_eq_of_le_closed_stage
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    {n m : Nat}
    (hnm : n ≤ m)
    (hClosed : IsSaturationClosed Terminal Binary
      (SaturationIter Terminal Binary n))
    (X : State) :
    SaturationIter Terminal Binary m X =
      SaturationIter Terminal Binary n X := by
  apply Set.Subset.antisymm
  · exact saturationIter_subset_closed_stage
      Terminal Binary n hClosed m X
  · exact saturationIter_mono_of_le Terminal Binary hnm X

/--
A closed saturation stage is stable under any later finite number of additional
iterations.
-/
theorem saturationIter_eq_closed_stage_add
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (n k : Nat)
    (hClosed : IsSaturationClosed Terminal Binary
      (SaturationIter Terminal Binary n))
    (X : State) :
    SaturationIter Terminal Binary (n + k) X =
      SaturationIter Terminal Binary n X := by
  exact saturationIter_eq_of_le_closed_stage
    Terminal Binary (Nat.le_add_right n k) hClosed X

/--
Carrier version: if carrier saturation stage `n` is closed, all later stages
are equal to it.
-/
theorem carrierSaturationIter_eq_of_le_closed_stage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    {n m : Nat}
    (hnm : n ≤ m)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n))
    (X : W) :
    SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        m X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n X := by
  exact saturationIter_eq_of_le_closed_stage
    (CarrierTerminalImage q H profile R)
    (CarrierBinaryRel H profile R)
    hnm hClosed X

/--
Carrier version with an additive tail: a closed stage remains unchanged after
any number of additional iterations.
-/
theorem carrierSaturationIter_eq_closed_stage_add
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (n k : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n))
    (X : W) :
    SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (n + k) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n X := by
  exact carrierSaturationIter_eq_of_le_closed_stage
    q H profile R (Nat.le_add_right n k) hClosed X

/--
Standard-observation version of eventual stability after a closed stage.
-/
theorem carrierSaturationIter_eq_closed_stage_add_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (n k : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage H.h H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        n))
    (X : W) :
    SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        (n + k) X =
      SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        n X := by
  exact carrierSaturationIter_eq_closed_stage_add
    H.h H profile R n k hClosed X

end LeanCfgProject
