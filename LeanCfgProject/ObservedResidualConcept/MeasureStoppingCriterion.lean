import LeanCfgProject.ObservedResidualConcept.FiniteStoppingCore
import LeanCfgProject.ObservedResidualConcept.ClosedStageEquivalences
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/-
Measure stopping criterion.

This file is the bridge between the arithmetic core in `FiniteStoppingCore`
and a future concrete cardinality measure such as

  SatMeasure n = ∑ X, ncard (SaturationIter Terminal Binary n X).

It does not yet use `Set.ncard`.  Instead it abstracts the needed property:

  whenever some component of the stage changes from n to n+1, a natural-number
  measure strictly increases.

Together with boundedness, this proves existence of a pointwise stable stage.
The file then specializes this abstract result to generic saturation and to
carrier saturation.
-/

/--
Abstract pointwise stopping criterion from a bounded monotone measure.

If `mu` is monotone and bounded by `B`, and if any pointwise change in the
stage family forces a strict increase of `mu`, then some stage `N ≤ B` is
pointwise stable.
-/
theorem exists_le_pointwise_stable_of_measure
    {State : Type u}
    {Alpha : Type v}
    (Stage : Nat → State → Set Alpha)
    (mu : Nat → Nat)
    (hmu_mono : Monotone mu)
    {B : Nat}
    (hmu_bound : ∀ n : Nat, mu n ≤ B)
    (hstrict_of_change :
      ∀ n : Nat,
        (∃ X : State, Stage (n + 1) X ≠ Stage n X) →
          mu n < mu (n + 1)) :
    ∃ N ≤ B, ∀ X : State, Stage (N + 1) X = Stage N X := by
  classical
  obtain ⟨N, hNB, hmu_eq⟩ :=
    exists_le_eq_succ_of_monotone_bounded hmu_mono hmu_bound
  refine ⟨N, hNB, ?_⟩
  by_contra hnot
  have hchange : ∃ X : State, Stage (N + 1) X ≠ Stage N X := by
    exact not_forall.mp hnot
  have hlt : mu N < mu (N + 1) :=
    hstrict_of_change N hchange
  have hbad : mu N < mu N := by
    simpa [hmu_eq] using hlt
  exact (Nat.lt_irrefl (mu N)) hbad

/--
Bound-free version of the abstract pointwise stopping criterion.
-/
theorem exists_pointwise_stable_of_measure
    {State : Type u}
    {Alpha : Type v}
    (Stage : Nat → State → Set Alpha)
    (mu : Nat → Nat)
    (hmu_mono : Monotone mu)
    {B : Nat}
    (hmu_bound : ∀ n : Nat, mu n ≤ B)
    (hstrict_of_change :
      ∀ n : Nat,
        (∃ X : State, Stage (n + 1) X ≠ Stage n X) →
          mu n < mu (n + 1)) :
    ∃ N : Nat, ∀ X : State, Stage (N + 1) X = Stage N X := by
  obtain ⟨N, _hNB, hstable⟩ :=
    exists_le_pointwise_stable_of_measure
      Stage mu hmu_mono hmu_bound hstrict_of_change
  exact ⟨N, hstable⟩

/--
Generic saturation version: a bounded monotone measure that strictly increases
whenever any saturation component changes yields a pointwise stable saturation
stage.
-/
theorem exists_le_saturationStableStage_of_measure
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (mu : Nat → Nat)
    (hmu_mono : Monotone mu)
    {B : Nat}
    (hmu_bound : ∀ n : Nat, mu n ≤ B)
    (hstrict_of_change :
      ∀ n : Nat,
        (∃ X : State,
          SaturationIter Terminal Binary (n + 1) X ≠
            SaturationIter Terminal Binary n X) →
          mu n < mu (n + 1)) :
    ∃ N ≤ B, ∀ X : State,
      SaturationIter Terminal Binary (N + 1) X =
        SaturationIter Terminal Binary N X := by
  exact exists_le_pointwise_stable_of_measure
    (fun n X => SaturationIter Terminal Binary n X)
    mu hmu_mono hmu_bound hstrict_of_change

/--
Generic saturation version: the same assumptions yield a closed saturation
stage.
-/
theorem exists_le_isSaturationClosed_of_measure
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (mu : Nat → Nat)
    (hmu_mono : Monotone mu)
    {B : Nat}
    (hmu_bound : ∀ n : Nat, mu n ≤ B)
    (hstrict_of_change :
      ∀ n : Nat,
        (∃ X : State,
          SaturationIter Terminal Binary (n + 1) X ≠
            SaturationIter Terminal Binary n X) →
          mu n < mu (n + 1)) :
    ∃ N ≤ B,
      IsSaturationClosed Terminal Binary
        (SaturationIter Terminal Binary N) := by
  obtain ⟨N, hNB, hstable⟩ :=
    exists_le_saturationStableStage_of_measure
      Terminal Binary mu hmu_mono hmu_bound hstrict_of_change
  refine ⟨N, hNB, ?_⟩
  exact (saturationStage_closed_iff_succ_eq Terminal Binary N).mpr hstable

/--
Carrier saturation version: a bounded monotone measure that strictly increases
whenever any carrier saturation component changes yields a pointwise stable
carrier saturation stage.
-/
theorem exists_le_carrierStableStage_of_measure
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (mu : Nat → Nat)
    (hmu_mono : Monotone mu)
    {B : Nat}
    (hmu_bound : ∀ n : Nat, mu n ≤ B)
    (hstrict_of_change :
      ∀ n : Nat,
        (∃ X : W,
          SaturationIter
              (CarrierTerminalImage q H profile R)
              (CarrierBinaryRel H profile R)
              (n + 1) X ≠
            SaturationIter
              (CarrierTerminalImage q H profile R)
              (CarrierBinaryRel H profile R)
              n X) →
          mu n < mu (n + 1)) :
    ∃ N ≤ B, ∀ X : W,
      SaturationIter
          (CarrierTerminalImage q H profile R)
          (CarrierBinaryRel H profile R)
          (N + 1) X =
        SaturationIter
          (CarrierTerminalImage q H profile R)
          (CarrierBinaryRel H profile R)
          N X := by
  exact exists_le_saturationStableStage_of_measure
    (CarrierTerminalImage q H profile R)
    (CarrierBinaryRel H profile R)
    mu hmu_mono hmu_bound hstrict_of_change

/--
Carrier saturation version: the same assumptions yield a closed carrier
saturation stage.
-/
theorem exists_le_carrierIsSaturationClosed_of_measure
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (mu : Nat → Nat)
    (hmu_mono : Monotone mu)
    {B : Nat}
    (hmu_bound : ∀ n : Nat, mu n ≤ B)
    (hstrict_of_change :
      ∀ n : Nat,
        (∃ X : W,
          SaturationIter
              (CarrierTerminalImage q H profile R)
              (CarrierBinaryRel H profile R)
              (n + 1) X ≠
            SaturationIter
              (CarrierTerminalImage q H profile R)
              (CarrierBinaryRel H profile R)
              n X) →
          mu n < mu (n + 1)) :
    ∃ N ≤ B,
      IsSaturationClosed
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (SaturationIter
          (CarrierTerminalImage q H profile R)
          (CarrierBinaryRel H profile R)
          N) := by
  exact exists_le_isSaturationClosed_of_measure
    (CarrierTerminalImage q H profile R)
    (CarrierBinaryRel H profile R)
    mu hmu_mono hmu_bound hstrict_of_change

/--
If the abstract measure criterion holds for carrier saturation, then there is a
bounded stage that computes carrier state semantics.
-/
theorem exists_le_carrierStage_computes_stateSemantics_of_measure
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (mu : Nat → Nat)
    (hmu_mono : Monotone mu)
    {B : Nat}
    (hmu_bound : ∀ n : Nat, mu n ≤ B)
    (hstrict_of_change :
      ∀ n : Nat,
        (∃ X : W,
          SaturationIter
              (CarrierTerminalImage q H profile R)
              (CarrierBinaryRel H profile R)
              (n + 1) X ≠
            SaturationIter
              (CarrierTerminalImage q H profile R)
              (CarrierBinaryRel H profile R)
              n X) →
          mu n < mu (n + 1)) :
    ∃ N ≤ B, ∀ X : W,
      SaturationIter
          (CarrierTerminalImage q H profile R)
          (CarrierBinaryRel H profile R)
          N X =
        CarrierStateSemantics q H profile R X := by
  obtain ⟨N, hNB, hClosed⟩ :=
    exists_le_carrierIsSaturationClosed_of_measure
      q H profile R mu hmu_mono hmu_bound hstrict_of_change
  refine ⟨N, hNB, ?_⟩
  intro X
  exact closedStage_computes_carrierStateSemantics
    q q_mul H profile R N hClosed X

/--
If the abstract measure criterion holds for carrier saturation, then there is a
bounded stage whose residual closure computes carrier concept semantics.
-/
theorem exists_le_carrierStage_computes_conceptSemantics_of_measure
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
    (mu : Nat → Nat)
    (hmu_mono : Monotone mu)
    {B : Nat}
    (hmu_bound : ∀ n : Nat, mu n ≤ B)
    (hstrict_of_change :
      ∀ n : Nat,
        (∃ X : W,
          SaturationIter
              (CarrierTerminalImage q H profile R)
              (CarrierBinaryRel H profile R)
              (n + 1) X ≠
            SaturationIter
              (CarrierTerminalImage q H profile R)
              (CarrierBinaryRel H profile R)
              n X) →
          mu n < mu (n + 1)) :
    ∃ N ≤ B, ∀ X : W,
      CarrierClosedStageConceptSemantics S q H profile R N X =
        CarrierConceptSemantics S q H profile R X := by
  obtain ⟨N, hNB, hClosed⟩ :=
    exists_le_carrierIsSaturationClosed_of_measure
      q H profile R mu hmu_mono hmu_bound hstrict_of_change
  refine ⟨N, hNB, ?_⟩
  intro X
  exact closedStage_computes_carrierConceptSemantics
    S q q_mul H profile R N hClosed X

end LeanCfgProject
