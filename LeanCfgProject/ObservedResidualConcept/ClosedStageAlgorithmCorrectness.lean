import LeanCfgProject.ObservedResidualConcept.ClosedStageConceptBridge
import LeanCfgProject.ObservedResidualConcept.ClosedStageFrameBridge
import LeanCfgProject.ObservedResidualConcept.SaturationMonotoneChain
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/-
Algorithmic correctness package for closed finite saturation stages.

This file states the algorithmic reading of the previous modules:
if a finite saturation stage is closed, then that finite stage computes the
state semantics and its residual closure computes the carrier concept
semantics.  In the standard observation `h`, the same closed stage also carries
the two-sided frame residual/intent information.
-/

/--
Closed-stage correctness at the state-semantics level.
-/
theorem closedStage_computes_carrierStateSemantics
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
    SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n X =
      CarrierStateSemantics q H profile R X := by
  symm
  exact carrierStateSemantics_eq_closed_saturationStage
    q q_mul H profile R n hClosed X

/--
Closed-stage correctness at the concept-semantics level.
-/
theorem closedStage_computes_carrierConceptSemantics
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
  exact carrierClosedStageConceptSemantics_eq_carrierConceptSemantics
    S q q_mul H profile R n hClosed X

/--
Standard-observation version of closed-stage state-semantics correctness.
-/
theorem closedStage_computes_carrierStateSemantics_h
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
    SaturationIter
        (CarrierTerminalImage H.h H profile R)
        (CarrierBinaryRel H profile R)
        n X =
      CarrierStateSemantics H.h H profile R X := by
  symm
  exact carrierStateSemantics_eq_closed_saturationStage_h
    H profile R n hClosed X

/--
Standard-observation version of closed-stage concept-semantics correctness.
-/
theorem closedStage_computes_carrierConceptSemantics_h
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
  exact carrierClosedStageConceptSemantics_eq_carrierConceptSemantics_h
    S H profile R n hClosed X

/--
Closed-stage concept semantics is concept-product sound for listed carrier
binary rules.
-/
theorem closedStage_binaryRule_conceptSound
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
  exact carrier_binaryRule_sound_as_closedStageConceptSemantics
    S q H profile R n hClosed br hmem

end LeanCfgProject
