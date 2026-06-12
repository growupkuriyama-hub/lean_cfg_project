import Mathlib.Tactic
import LeanCfgProject.ObservedResidualConcept.MeasureStoppingCriterion
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedFintypeInType false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/-
Finite saturation measure.

This is the concrete finite-measure layer.

We count a subset of a finite type `Q` by summing its characteristic function
over `Finset.univ`.  Since arbitrary set membership is not computably decidable,
the definition is explicitly noncomputable and uses classical decidability.

Main result:
  if `State` and `Q` are finite, then some stage `N ≤ |State| * |Q|`
  is closed under saturation.

Carrier consequences then give an unconditional bounded stage computing
carrier state semantics and carrier concept semantics.
-/

section IndicatorMeasure

variable {Q : Type v} [Fintype Q]

/-- Cardinality of a subset of a finite type, defined by an indicator sum. -/
noncomputable def StageCard (U : Set Q) : Nat := by
  classical
  exact ∑ q : Q, if q ∈ U then 1 else 0

/-- Indicator cardinality is monotone under subset inclusion. -/
theorem stageCard_mono {A B : Set Q} (hsub : A ⊆ B) :
    StageCard A ≤ StageCard B := by
  classical
  unfold StageCard
  apply Finset.sum_le_sum
  intro q _hq
  by_cases hA : q ∈ A
  · have hB : q ∈ B := hsub hA
    simp [hA, hB]
  · by_cases hB : q ∈ B
    · simp [hA, hB]
    · simp [hA, hB]

/-- Indicator cardinality is bounded by the size of the finite ambient type. -/
theorem stageCard_le_card (U : Set Q) :
    StageCard U ≤ Fintype.card Q := by
  classical
  unfold StageCard
  calc
    (∑ q : Q, if q ∈ U then 1 else 0) ≤ ∑ _q : Q, (1 : Nat) := by
      apply Finset.sum_le_sum
      intro q _hq
      by_cases hqU : q ∈ U <;> simp [hqU]
    _ = Fintype.card Q := by
      simp

/--
If `A ⊆ B` but `A ≠ B`, then the indicator cardinality strictly increases.
-/
theorem stageCard_lt_of_subset_ne {A B : Set Q}
    (hsub : A ⊆ B)
    (hne : A ≠ B) :
    StageCard A < StageCard B := by
  classical
  have hproper : ∃ q : Q, q ∈ B ∧ q ∉ A := by
    by_contra hno
    have hBA : B ⊆ A := by
      intro q hqB
      by_contra hqA
      exact hno ⟨q, hqB, hqA⟩
    exact hne (Set.Subset.antisymm hsub hBA)
  rcases hproper with ⟨q0, hq0B, hq0A⟩
  unfold StageCard
  apply Finset.sum_lt_sum
  · intro q _hq
    by_cases hqA : q ∈ A
    · have hqB : q ∈ B := hsub hqA
      simp [hqA, hqB]
    · by_cases hqB : q ∈ B
      · simp [hqA, hqB]
      · simp [hqA, hqB]
  · refine ⟨q0, Finset.mem_univ q0, ?_⟩
    simp [hq0A, hq0B]

end IndicatorMeasure

section GenericSaturationMeasure

variable {State : Type u}
variable {Q : Type v} [Mul Q] [Fintype State] [Fintype Q]
variable (Terminal : State → Set Q)
variable (Binary : State → State → State → Prop)

/--
Concrete saturation measure:
sum, over all states, of the indicator-cardinality of the saturation stage.
-/
noncomputable def SatMeasureIndicator (n : Nat) : Nat :=
  ∑ X : State, StageCard (SaturationIter Terminal Binary n X)

/-- The concrete saturation measure is monotone. -/
theorem satMeasureIndicator_mono :
    Monotone (SatMeasureIndicator Terminal Binary) := by
  classical
  intro a b hab
  unfold SatMeasureIndicator
  apply Finset.sum_le_sum
  intro X _hX
  exact stageCard_mono
    (saturationIter_mono_of_le Terminal Binary hab X)

/-- The concrete saturation measure is bounded by `|State| * |Q|`. -/
theorem satMeasureIndicator_bound (n : Nat) :
    SatMeasureIndicator Terminal Binary n ≤
      Fintype.card State * Fintype.card Q := by
  classical
  unfold SatMeasureIndicator
  calc
    (∑ X : State, StageCard (SaturationIter Terminal Binary n X)) ≤
        ∑ _X : State, Fintype.card Q := by
          apply Finset.sum_le_sum
          intro X _hX
          exact stageCard_le_card
            (SaturationIter Terminal Binary n X)
    _ = Fintype.card State * Fintype.card Q := by
          simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/--
If some component changes between stages `n` and `n+1`, then the concrete
saturation measure strictly increases.
-/
theorem satMeasureIndicator_strict_of_change
    (n : Nat)
    (hchange :
      ∃ X : State,
        SaturationIter Terminal Binary (n + 1) X ≠
          SaturationIter Terminal Binary n X) :
    SatMeasureIndicator Terminal Binary n <
      SatMeasureIndicator Terminal Binary (n + 1) := by
  classical
  rcases hchange with ⟨X0, hX0change⟩
  unfold SatMeasureIndicator
  apply Finset.sum_lt_sum
  · intro X _hX
    exact stageCard_mono
      (saturationIter_subset_succ Terminal Binary n X)
  · refine ⟨X0, Finset.mem_univ X0, ?_⟩
    exact stageCard_lt_of_subset_ne
      (saturationIter_subset_succ Terminal Binary n X0)
      (Ne.symm hX0change)

/--
Unconditional bounded pointwise stabilization for finite saturation.
There exists `N ≤ |State| * |Q|` such that stage `N+1` equals stage `N`
componentwise.
-/
theorem exists_le_stable_stage_of_fintype :
    ∃ N ≤ Fintype.card State * Fintype.card Q,
      ∀ X : State,
        SaturationIter Terminal Binary (N + 1) X =
          SaturationIter Terminal Binary N X := by
  exact exists_le_saturationStableStage_of_measure
    Terminal Binary
    (SatMeasureIndicator Terminal Binary)
    (satMeasureIndicator_mono Terminal Binary)
    (satMeasureIndicator_bound Terminal Binary)
    (satMeasureIndicator_strict_of_change Terminal Binary)

/--
Unconditional bounded closed stage for finite saturation.
-/
theorem exists_le_isSaturationClosed_stage_of_fintype :
    ∃ N ≤ Fintype.card State * Fintype.card Q,
      IsSaturationClosed Terminal Binary
        (SaturationIter Terminal Binary N) := by
  exact exists_le_isSaturationClosed_of_measure
    Terminal Binary
    (SatMeasureIndicator Terminal Binary)
    (satMeasureIndicator_mono Terminal Binary)
    (satMeasureIndicator_bound Terminal Binary)
    (satMeasureIndicator_strict_of_change Terminal Binary)

/--
Unconditional closed stage for finite saturation, without displaying the bound.
-/
theorem exists_isSaturationClosed_stage_of_fintype :
    ∃ N,
      IsSaturationClosed Terminal Binary
        (SaturationIter Terminal Binary N) := by
  obtain ⟨N, _hNB, hClosed⟩ :=
    exists_le_isSaturationClosed_stage_of_fintype Terminal Binary
  exact ⟨N, hClosed⟩

end GenericSaturationMeasure

section CarrierFiniteSaturationMeasure

variable {Sigma : Type u}
variable {M : Type u} [Monoid M] [Fintype M]
variable {Q : Type v} [Monoid Q] [Fintype Q]

/--
Bounded closed stage for carrier saturation, obtained from finite state and
finite observation carrier.
-/
theorem exists_le_carrierIsSaturationClosed_stage_of_fintype
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u} [Fintype W]
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile)) :
    ∃ N ≤ Fintype.card W * Fintype.card Q,
      IsSaturationClosed
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (SaturationIter
          (CarrierTerminalImage q H profile R)
          (CarrierBinaryRel H profile R)
          N) := by
  exact exists_le_isSaturationClosed_stage_of_fintype
    (CarrierTerminalImage q H profile R)
    (CarrierBinaryRel H profile R)

/--
There exists a bounded carrier saturation stage that computes carrier state
semantics.
-/
theorem exists_le_carrierStage_computes_stateSemantics_of_fintype
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u} [Fintype W]
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile)) :
    ∃ N ≤ Fintype.card W * Fintype.card Q,
      ∀ X : W,
        SaturationIter
            (CarrierTerminalImage q H profile R)
            (CarrierBinaryRel H profile R)
            N X =
          CarrierStateSemantics q H profile R X := by
  obtain ⟨N, hNB, hClosed⟩ :=
    exists_le_carrierIsSaturationClosed_stage_of_fintype
      q H profile R
  refine ⟨N, hNB, ?_⟩
  intro X
  exact closedStage_computes_carrierStateSemantics
    q q_mul H profile R N hClosed X

/--
There exists a bounded carrier saturation stage whose residual closure computes
carrier concept semantics.
-/
theorem exists_le_carrierStage_computes_conceptSemantics_of_fintype
    (S : Set Q)
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u} [Fintype W]
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile)) :
    ∃ N ≤ Fintype.card W * Fintype.card Q,
      ∀ X : W,
        CarrierClosedStageConceptSemantics S q H profile R N X =
          CarrierConceptSemantics S q H profile R X := by
  obtain ⟨N, hNB, hClosed⟩ :=
    exists_le_carrierIsSaturationClosed_stage_of_fintype
      q H profile R
  refine ⟨N, hNB, ?_⟩
  intro X
  exact closedStage_computes_carrierConceptSemantics
    S q q_mul H profile R N hClosed X

/--
Standard-observation version of bounded closed-stage existence.
-/
theorem exists_le_carrierIsSaturationClosed_stage_h_of_fintype
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u} [Fintype W]
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile)) :
    ∃ N ≤ Fintype.card W * Fintype.card M,
      IsSaturationClosed
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        (SaturationIter
          (CarrierTerminalImage H.h H profile R)
          (CarrierBinaryRel H profile R)
          N) := by
  exact exists_le_carrierIsSaturationClosed_stage_of_fintype
    (q := H.h) (H := H) (profile := profile) (R := R)

/--
Standard-observation version: a bounded stage computes carrier state semantics.
-/
theorem exists_le_carrierStage_computes_stateSemantics_h_of_fintype
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u} [Fintype W]
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile)) :
    ∃ N ≤ Fintype.card W * Fintype.card M,
      ∀ X : W,
        SaturationIter
            (CarrierTerminalImage H.h H profile R)
            (CarrierBinaryRel H profile R)
            N X =
          CarrierStateSemantics H.h H profile R X := by
  exact exists_le_carrierStage_computes_stateSemantics_of_fintype
    (q := H.h) (q_mul := H.map_append) (H := H)
    (profile := profile) (R := R)

/--
Standard-observation version: a bounded stage computes carrier concept
semantics.
-/
theorem exists_le_carrierStage_computes_conceptSemantics_h_of_fintype
    (S : Set M)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u} [Fintype W]
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile)) :
    ∃ N ≤ Fintype.card W * Fintype.card M,
      ∀ X : W,
        CarrierClosedStageConceptSemantics S H.h H profile R N X =
          CarrierConceptSemantics S H.h H profile R X := by
  exact exists_le_carrierStage_computes_conceptSemantics_of_fintype
    (S := S) (q := H.h) (q_mul := H.map_append) (H := H)
    (profile := profile) (R := R)

end CarrierFiniteSaturationMeasure

end LeanCfgProject
