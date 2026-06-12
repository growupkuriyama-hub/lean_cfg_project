import LeanCfgProject.ObservedResidualConcept.CarrierObservedAdequacy
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u

/-
CarrierObservedAdequacyCorollaries.lean

Lightweight paper-facing aliases for the carrier observed-block adequacy layer.

The theorem statements deliberately mirror the already-verified declarations in
`CarrierObservedAdequacy.lean`, but give shorter paper-facing names.
-/

/--
Paper-facing alias for carrier observed-block frame adequacy at the standard
observation `h`.
-/
theorem paper_carrierObservedBlockAdequacy_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (Rrules : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile Rrules S0 X ell r)
    (hne :
      ∃ gamma : M,
        gamma ∈ CarrierStateSemantics H.h H profile Rrules X)
    (hblock :
      ∀ x y : M,
        x ∈ TwoSidedResidual
              (CarrierStartImage H.h H profile Rrules S0)
              (profile X).lt
              (profile X).rt →
        y ∈ TwoSidedResidual
              (CarrierStartImage H.h H profile Rrules S0)
              (profile X).lt
              (profile X).rt →
          SameObservedSyntactic
            (CarrierStartImage H.h H profile Rrules S0) x y) :
    CarrierConceptSemantics
        (CarrierStartImage H.h H profile Rrules S0)
        H.h H profile Rrules X
      =
      TwoSidedResidual
        (CarrierStartImage H.h H profile Rrules S0)
        (profile X).lt
        (profile X).rt :=
  carrierObservedAdequacy_summary_h
    H profile Rrules S0 hStartFrame hctx hne hblock

/--
Paper-facing residual-left version.
-/
theorem paper_frameResidual_eq_carrierConcept_of_observedBlock_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (Rrules : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile Rrules S0 X ell r)
    (hne :
      ∃ gamma : M,
        gamma ∈ CarrierStateSemantics H.h H profile Rrules X)
    (hblock :
      ∀ x y : M,
        x ∈ TwoSidedResidual
              (CarrierStartImage H.h H profile Rrules S0)
              (profile X).lt
              (profile X).rt →
        y ∈ TwoSidedResidual
              (CarrierStartImage H.h H profile Rrules S0)
              (profile X).lt
              (profile X).rt →
          SameObservedSyntactic
            (CarrierStartImage H.h H profile Rrules S0) x y) :
    TwoSidedResidual
        (CarrierStartImage H.h H profile Rrules S0)
        (profile X).lt
        (profile X).rt
      =
      CarrierConceptSemantics
        (CarrierStartImage H.h H profile Rrules S0)
        H.h H profile Rrules X :=
  carrier_frame_residual_eq_conceptSemantics_of_observedSyntacticBlock_h
    H profile Rrules S0 hStartFrame hctx hne hblock

/--
Paper-facing coverage version.
-/
theorem paper_frameResidual_subset_carrierConcept_of_observedBlock_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (Rrules : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile Rrules S0 X ell r)
    (hne :
      ∃ gamma : M,
        gamma ∈ CarrierStateSemantics H.h H profile Rrules X)
    (hblock :
      ∀ x y : M,
        x ∈ TwoSidedResidual
              (CarrierStartImage H.h H profile Rrules S0)
              (profile X).lt
              (profile X).rt →
        y ∈ TwoSidedResidual
              (CarrierStartImage H.h H profile Rrules S0)
              (profile X).lt
              (profile X).rt →
          SameObservedSyntactic
            (CarrierStartImage H.h H profile Rrules S0) x y) :
    TwoSidedResidual
        (CarrierStartImage H.h H profile Rrules S0)
        (profile X).lt
        (profile X).rt
      ⊆
      CarrierConceptSemantics
        (CarrierStartImage H.h H profile Rrules S0)
        H.h H profile Rrules X :=
  carrier_frame_residual_subset_conceptSemantics_of_observedSyntacticBlock_h
    H profile Rrules S0 hStartFrame hctx hne hblock

end LeanCfgProject
