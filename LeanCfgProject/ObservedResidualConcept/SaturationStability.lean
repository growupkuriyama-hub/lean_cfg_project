import LeanCfgProject.ObservedResidualConcept.CarrierSaturationLeast
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/--
If a saturation stage is already closed under the one-step saturation
operator, then the next stage is equal to it.

This is the local fixed-point criterion for `SaturationIter`.
-/
theorem saturationIter_succ_eq_of_closed
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (n : Nat)
    (hClosed : IsSaturationClosed Terminal Binary
      (SaturationIter Terminal Binary n))
    (X : State) :
    SaturationIter Terminal Binary (n + 1) X =
      SaturationIter Terminal Binary n X := by
  apply Set.Subset.antisymm
  · change SaturationStep Terminal Binary
      (SaturationIter Terminal Binary n) X ⊆
      SaturationIter Terminal Binary n X
    exact hClosed X
  · exact saturationIter_subset_succ Terminal Binary n X

/--
If a saturation stage is closed, then every finite saturation stage is included
in that closed stage.  This is the leastness argument specialized to a closed
iteration stage.
-/
theorem saturationIter_subset_closed_stage
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (n : Nat)
    (hClosed : IsSaturationClosed Terminal Binary
      (SaturationIter Terminal Binary n)) :
    ∀ k : Nat, ∀ X : State,
      SaturationIter Terminal Binary k X ⊆
        SaturationIter Terminal Binary n X := by
  apply saturationIter_subset_of_closed Terminal Binary
    (SaturationIter Terminal Binary n)
  · intro X x hx
    exact hClosed X (Or.inr (Or.inl hx))
  · intro X Y Z b c hbin hb hc
    exact hClosed X
      (Or.inr (Or.inr ⟨Y, Z, b, c, hbin, hb, hc, rfl⟩))

/--
Carrier version: if a carrier saturation stage is closed, then the
finite-stage carrier saturation image is exactly that stage.
-/
theorem carrierSaturationImage_eq_of_closed_stage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (n : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n))
    (X : W) :
    CarrierSaturationImage q H profile R X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n X := by
  apply Set.Subset.antisymm
  · intro a ha
    rcases ha with ⟨k, hk⟩
    exact saturationIter_subset_closed_stage
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      n hClosed k X hk
  · intro a ha
    exact ⟨n, ha⟩

/--
If a carrier saturation stage is closed, then carrier state semantics is equal
to that closed stage.  This combines the paper-level equality
`CarrierSaturationImage = CarrierStateSemantics` with the closed-stage
criterion above.
-/
theorem carrierStateSemantics_eq_closed_saturationStage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (n : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n))
    (X : W) :
    CarrierStateSemantics q H profile R X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n X := by
  calc
    CarrierStateSemantics q H profile R X =
        CarrierSaturationImage q H profile R X := by
          symm
          exact carrier_saturationImage_eq_stateSemantics
            q q_mul H profile R X
    _ =
        SaturationIter
          (CarrierTerminalImage q H profile R)
          (CarrierBinaryRel H profile R)
          n X := by
          exact carrierSaturationImage_eq_of_closed_stage
            q H profile R n hClosed X

/--
For the standard observation `h`, a closed carrier saturation stage computes
the carrier state semantics.
-/
theorem carrierStateSemantics_eq_closed_saturationStage_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (n : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage H.h H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        n))
    (X : W) :
    CarrierStateSemantics H.h H profile R X =
      SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        n X := by
  exact carrierStateSemantics_eq_closed_saturationStage
    H.h H.map_append H profile R n hClosed X

end LeanCfgProject
