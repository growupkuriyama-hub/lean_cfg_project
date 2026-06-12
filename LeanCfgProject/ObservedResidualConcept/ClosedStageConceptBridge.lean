import LeanCfgProject.SaturationStability
import LeanCfgProject.CarrierSaturationConceptSoundness

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/--
Concept semantics computed from a particular finite saturation stage.
When that stage is closed, this is the same as the saturation-based carrier
concept semantics, hence also the usual carrier concept semantics.
-/
def CarrierClosedStageConceptSemantics
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (n : Nat)
    (X : W) : Set Q :=
  ConceptClosure S
    (SaturationIter
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      n X)

/--
The closed-stage concept semantics is a concept extent.
-/
theorem carrierClosedStageConceptSemantics_isConceptExtent
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (n : Nat)
    (X : W) :
    IsConceptExtent S
      (CarrierClosedStageConceptSemantics S q H profile R n X) := by
  unfold CarrierClosedStageConceptSemantics
  exact conceptClosure_isConceptExtent S
    (SaturationIter
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      n X)

/--
If the finite saturation stage `n` is closed, then closing that stage gives the
same concept semantics as closing the full saturation image.
-/
theorem carrierClosedStageConceptSemantics_eq_saturationConceptSemantics
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
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
    CarrierClosedStageConceptSemantics S q H profile R n X =
      CarrierSaturationConceptSemantics S q H profile R X := by
  unfold CarrierClosedStageConceptSemantics
  unfold CarrierSaturationConceptSemantics
  rw [carrierSaturationImage_eq_of_closed_stage q H profile R n hClosed X]

/--
If the finite saturation stage `n` is closed, then closing that stage gives the
usual carrier concept semantics.
-/
theorem carrierClosedStageConceptSemantics_eq_carrierConceptSemantics
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
    (n : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n))
    (X : W) :
    CarrierClosedStageConceptSemantics S q H profile R n X =
      CarrierConceptSemantics S q H profile R X := by
  calc
    CarrierClosedStageConceptSemantics S q H profile R n X =
        CarrierSaturationConceptSemantics S q H profile R X := by
          exact carrierClosedStageConceptSemantics_eq_saturationConceptSemantics
            S q H profile R n hClosed X
    _ =
        CarrierConceptSemantics S q H profile R X := by
          exact carrierSaturationConceptSemantics_eq_carrierConceptSemantics
            S q q_mul H profile R X

/--
Standard-observation version: if a finite `h`-saturation stage is closed, then
its concept closure is the usual carrier concept semantics for `h`.
-/
theorem carrierClosedStageConceptSemantics_eq_carrierConceptSemantics_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (S : Set M)
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
    CarrierClosedStageConceptSemantics S H.h H profile R n X =
      CarrierConceptSemantics S H.h H profile R X := by
  exact carrierClosedStageConceptSemantics_eq_carrierConceptSemantics
    S H.h H.map_append H profile R n hClosed X

/--
Binary rule soundness using only a closed finite saturation stage.  This is the
concept-product soundness theorem in a form suitable for an algorithm that
stops once the stage is closed.
-/
theorem carrier_binaryRel_sound_as_closedStageConceptSemantics
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
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
    {X Y Z : W}
    (hbin : CarrierBinaryRel H profile R X Y Z) :
    ConceptProduct S
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n Y)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n Z)
      ⊆
    CarrierClosedStageConceptSemantics S q H profile R n X := by
  have hs :=
    carrier_binaryRel_sound_as_saturationConceptSemantics
      S q H profile R hbin
  have eX := carrierSaturationImage_eq_of_closed_stage
    q H profile R n hClosed X
  have eY := carrierSaturationImage_eq_of_closed_stage
    q H profile R n hClosed Y
  have eZ := carrierSaturationImage_eq_of_closed_stage
    q H profile R n hClosed Z
  unfold CarrierClosedStageConceptSemantics
  unfold CarrierSaturationConceptSemantics at hs
  simpa [eX, eY, eZ] using hs

/--
Listed-rule version of binary rule soundness for a closed finite saturation
stage.
-/
theorem carrier_binaryRule_sound_as_closedStageConceptSemantics
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
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
    (br : CarrierBinaryRule profile)
    (hmem : List.Mem (CarrierTypedRule.binary br) R) :
    ConceptProduct S
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n br.Y)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n br.Z)
      ⊆
    CarrierClosedStageConceptSemantics S q H profile R n br.X := by
  exact carrier_binaryRel_sound_as_closedStageConceptSemantics
    S q H profile R n hClosed ⟨br, hmem, rfl, rfl, rfl⟩

end LeanCfgProject
