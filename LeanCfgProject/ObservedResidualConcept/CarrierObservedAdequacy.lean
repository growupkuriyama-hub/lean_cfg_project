import LeanCfgProject.ObservedResidualConcept.ObservedSyntacticConcept
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/-
CarrierObservedAdequacy.lean

This file connects the v25.1 observed-syntactic-block adequacy theorem to
carrier state semantics and fixed-h frames.

This v2 removes unsafe local reducibility attributes rejected by Lean 4.31.

The previous file `ObservedSyntacticConcept.lean` proves the abstract monoid
statement:

  U ⊆ Res_S(a,b), U nonempty, and Res_S(a,b) is contained in one observed
  syntactic block
  ----------------------------------------------------------------------
  ConceptClosure S U = Res_S(a,b).

Here we instantiate `U` as a carrier state image and use the already verified
frame soundness theorem to discharge `U ⊆ Res`.

This is the first Lean bridge from the canonical `(Q,S)` adequacy theorem back
to CFG presentation descriptors.
-/

/--
Carrier frame adequacy from observed syntactic block, for the standard
observation `q = h`.

If the carrier state image is nonempty and the frame residual is contained in a
single observed syntactic block, then the carrier concept semantics of the state
is exactly the frame residual.
-/
theorem carrier_frame_adequacy_of_observedSyntacticBlock_h
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
        (profile X).rt := by
  unfold CarrierConceptSemantics
  have hsound :
      CarrierStateSemantics H.h H profile Rrules X ⊆
        TwoSidedResidual
          (CarrierStartImage H.h H profile Rrules S0)
          (profile X).lt
          (profile X).rt := by
    simpa [CarrierStartImage] using
      (carrier_state_semantics_subset_frame_residual_h
        H profile Rrules S0 hStartFrame hctx)
  exact syntacticBlockAdequacy
    (CarrierStartImage H.h H profile Rrules S0)
    (CarrierStateSemantics H.h H profile Rrules X)
    (profile X).lt
    (profile X).rt
    hsound hne hblock

/--
Symmetric form of the previous theorem, with the frame residual concept on the
left.  This is often the way the paper phrases representation.
-/
theorem carrier_frame_residual_eq_conceptSemantics_of_observedSyntacticBlock_h
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
        H.h H profile Rrules X := by
  symm
  exact carrier_frame_adequacy_of_observedSyntacticBlock_h
    H profile Rrules S0 hStartFrame hctx hne hblock

/--
Coverage corollary.

Under the observed-syntactic-block hypotheses, the frame residual is covered by
the carrier concept semantics.  This is the coverage condition needed by the
general adequacy criterion.
-/
theorem carrier_frame_residual_subset_conceptSemantics_of_observedSyntacticBlock_h
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
        H.h H profile Rrules X := by
  rw [carrier_frame_residual_eq_conceptSemantics_of_observedSyntacticBlock_h
    H profile Rrules S0 hStartFrame hctx hne hblock]

/--
Factor-through-`h` version.

Let `q = theta ∘ h`.  If the carrier state image under this observation is
nonempty and the corresponding theta-frame residual lies in one observed
syntactic block, then the carrier concept semantics is exactly that frame
residual.
-/
theorem carrier_frame_adequacy_of_observedSyntacticBlock_factor
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (theta : M →* Q)
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
      ∃ gamma : Q,
        gamma ∈ CarrierStateSemantics
          (fun w : Word Sigma => theta (H.h w))
          H profile Rrules X)
    (hblock :
      ∀ x y : Q,
        x ∈ TwoSidedResidual
              (CarrierStartImage
                (fun w : Word Sigma => theta (H.h w))
                H profile Rrules S0)
              (theta ((profile X).lt))
              (theta ((profile X).rt)) →
        y ∈ TwoSidedResidual
              (CarrierStartImage
                (fun w : Word Sigma => theta (H.h w))
                H profile Rrules S0)
              (theta ((profile X).lt))
              (theta ((profile X).rt)) →
          SameObservedSyntactic
            (CarrierStartImage
              (fun w : Word Sigma => theta (H.h w))
              H profile Rrules S0) x y) :
    CarrierConceptSemantics
        (CarrierStartImage
          (fun w : Word Sigma => theta (H.h w))
          H profile Rrules S0)
        (fun w : Word Sigma => theta (H.h w))
        H profile Rrules X
      =
      TwoSidedResidual
        (CarrierStartImage
          (fun w : Word Sigma => theta (H.h w))
          H profile Rrules S0)
        (theta ((profile X).lt))
        (theta ((profile X).rt)) := by
  unfold CarrierConceptSemantics
  have hsound :
      CarrierStateSemantics
          (fun w : Word Sigma => theta (H.h w))
          H profile Rrules X ⊆
        TwoSidedResidual
          (CarrierStartImage
            (fun w : Word Sigma => theta (H.h w))
            H profile Rrules S0)
          (theta ((profile X).lt))
          (theta ((profile X).rt)) := by
    simpa [CarrierStartImage] using
      (carrier_state_semantics_subset_frame_residual_factor
        theta H profile Rrules S0 hStartFrame hctx)
  exact syntacticBlockAdequacy
    (CarrierStartImage
      (fun w : Word Sigma => theta (H.h w))
      H profile Rrules S0)
    (CarrierStateSemantics
      (fun w : Word Sigma => theta (H.h w))
      H profile Rrules X)
    (theta ((profile X).lt))
    (theta ((profile X).rt))
    hsound hne hblock

/--
Summary theorem for the standard observation `h`.

This packages the statement closest to the paper corollary:
productive witnessed states whose frame residual is a single observed syntactic
block are frame-adequate.
-/
theorem carrierObservedAdequacy_summary_h
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
  carrier_frame_adequacy_of_observedSyntacticBlock_h
    H profile Rrules S0 hStartFrame hctx hne hblock

end LeanCfgProject
