import LeanCfgProject.ClosedStageAlgorithmCorrectness
import LeanCfgProject.ClosedStageFrameBridge

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/-
Finite coverage stopping criterion.

This is a deliberately "attack" layer toward a full finite stopping theorem.
It does not yet prove that such a covering stage exists from `Fintype` data.
Instead it proves the key correctness implication:

  if a finite stage `N` already contains the whole carrier saturation image,
  then stage `N` is closed, all later stages are stable, and it computes both
  the carrier state semantics and the residual concept semantics.

This is the precise theorem one wants once a future finite-enumeration argument
produces such an `N`.
-/

/--
Every finite saturation stage is contained in the full carrier saturation image.
-/
theorem carrierSaturationIter_subset_saturationImage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (n : Nat)
    (X : W) :
    SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n X ⊆
      CarrierSaturationImage q H profile R X := by
  intro a ha
  exact ⟨n, ha⟩

/--
If a finite stage `N` contains the whole carrier saturation image, then that
stage is closed under the one-step saturation operator.
-/
theorem carrierSaturationStage_closed_of_covers_saturationImage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat)
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
        N) := by
  intro X a ha
  rcases ha with haPrev | haRest
  · exact haPrev
  · rcases haRest with haTerm | haBin
    · apply hCover X
      exact carrier_terminal_mem_saturationImage q H profile R haTerm
    · rcases haBin with ⟨Y, Z, b, c, hbin, hb, hc, haEq⟩
      rw [haEq]
      apply hCover X
      exact carrier_binary_mul_mem_saturationImage q H profile R hbin
        (carrierSaturationIter_subset_saturationImage q H profile R N Y hb)
        (carrierSaturationIter_subset_saturationImage q H profile R N Z hc)

/--
A covering stage is exactly the carrier saturation image.
-/
theorem carrierSaturationStage_eq_saturationImage_of_covers
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat)
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
        N X =
      CarrierSaturationImage q H profile R X := by
  apply Set.Subset.antisymm
  · exact carrierSaturationIter_subset_saturationImage q H profile R N X
  · exact hCover X

/--
If a finite stage covers the full saturation image, then it computes carrier
state semantics.
-/
theorem carrierSaturationStage_eq_stateSemantics_of_covers
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
        N X =
      CarrierStateSemantics q H profile R X := by
  have hClosed :=
    carrierSaturationStage_closed_of_covers_saturationImage
      q H profile R N hCover
  exact closedStage_computes_carrierStateSemantics
    q q_mul H profile R N hClosed X

/--
If a finite stage covers the full saturation image, then its concept closure
computes carrier concept semantics.
-/
theorem carrierClosedStageConcept_eq_carrierConcept_of_covers
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
    (hCover : ∀ X : W,
      CarrierSaturationImage q H profile R X ⊆
        SaturationIter
          (CarrierTerminalImage q H profile R)
          (CarrierBinaryRel H profile R)
          N X)
    (X : W) :
    CarrierClosedStageConceptSemantics S q H profile R N X =
      CarrierConceptSemantics S q H profile R X := by
  have hClosed :=
    carrierSaturationStage_closed_of_covers_saturationImage
      q H profile R N hCover
  exact closedStage_computes_carrierConceptSemantics
    S q q_mul H profile R N hClosed X

/--
A covering stage is stable after any further number of iterations.
-/
theorem carrierSaturationIter_eq_covering_stage_add
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
        (N + k) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X := by
  have hClosed :=
    carrierSaturationStage_closed_of_covers_saturationImage
      q H profile R N hCover
  exact carrierSaturationIter_eq_closed_stage_add
    q H profile R N k hClosed X

/--
Standard-observation version: a covering `h`-saturation stage computes carrier
state semantics.
-/
theorem carrierSaturationStage_eq_stateSemantics_h_of_covers
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat)
    (hCover : ∀ X : W,
      CarrierSaturationImage H.h H profile R X ⊆
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
  exact carrierSaturationStage_eq_stateSemantics_of_covers
    H.h H.map_append H profile R N hCover X

/--
Standard-observation version: a covering `h`-saturation stage computes carrier
concept semantics.
-/
theorem carrierClosedStageConcept_eq_carrierConcept_h_of_covers
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (S : Set M)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat)
    (hCover : ∀ X : W,
      CarrierSaturationImage H.h H profile R X ⊆
        SaturationIter
          (CarrierTerminalImage H.h H profile R)
          (CarrierBinaryRel H profile R)
          N X)
    (X : W) :
    CarrierClosedStageConceptSemantics S H.h H profile R N X =
      CarrierConceptSemantics S H.h H profile R X := by
  exact carrierClosedStageConcept_eq_carrierConcept_of_covers
    S H.h H.map_append H profile R N hCover X

/--
Standard-observation version: a covering `h`-saturation stage has the same
frame-intent property as the full carrier concept semantics.
-/
theorem carrier_frame_mem_commonContexts_coveringClosedStage_h
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
          H.h H profile R N X) := by
  have hClosed :=
    carrierSaturationStage_closed_of_covers_saturationImage
      H.h H profile R N hCover
  exact carrier_frame_mem_commonContexts_closedStageConcept_h
    H profile R S0 hStartFrame N hClosed hctx

end LeanCfgProject
