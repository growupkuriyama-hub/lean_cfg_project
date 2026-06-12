import LeanCfgProject.ObservedResidualConcept.FrameSoundness
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/-
Frame adequacy criterion.

This file is the first adequacy layer.

It does not yet prove adequacy for a concrete language.  Instead it isolates
the reusable criterion:

  soundness U ⊆ R
  coverage  R ⊆ ConceptClosure S U
  --------------------------------
  ConceptClosure S R = ConceptClosure S U

Thus the future work for concrete examples or classes is reduced to proving
the coverage condition.  The carrier versions specialize this criterion to
context residuals and to the two-sided frame residuals already proved sound in
`FrameSoundness`.
-/

/--
General adequacy criterion.

If a state image `U` is sound with respect to a residual candidate `R`, and
`R` is covered by the concept closure of `U`, then the residual concept and the
state concept are equal.
-/
theorem adequacy_of_residual_coverage
    {Q : Type u} [Mul Q]
    (S U R : Set Q)
    (hsound : U ⊆ R)
    (hcover : R ⊆ ConceptClosure S U) :
    ConceptClosure S R = ConceptClosure S U := by
  apply Set.Subset.antisymm
  · calc
      ConceptClosure S R
          ⊆ ConceptClosure S (ConceptClosure S U) :=
            conceptClosure_mono S hcover
      _ = ConceptClosure S U :=
            conceptClosure_idempotent S U
  · exact conceptClosure_mono S hsound

/--
For a sound residual candidate `R`, adequacy is equivalent to the coverage
condition `R ⊆ ConceptClosure S U`.
-/
theorem adequacy_iff_residual_coverage
    {Q : Type u} [Mul Q]
    (S U R : Set Q)
    (hsound : U ⊆ R) :
    ConceptClosure S R = ConceptClosure S U ↔
      R ⊆ ConceptClosure S U := by
  constructor
  · intro hAdeq
    intro gamma hgamma
    have hcl : gamma ∈ ConceptClosure S R :=
      subset_conceptClosure S R hgamma
    simpa [hAdeq] using hcl
  · intro hcover
    exact adequacy_of_residual_coverage S U R hsound hcover

/--
Context-level carrier adequacy criterion.

For an arbitrary multiplicative observation `q`, the already verified context
soundness gives the inclusion from the carrier state image into the context
residual.  Therefore adequacy at the context residual is reduced to the single
coverage condition appearing as `hcover`.
-/
theorem carrier_context_adequacy_of_coverage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (Rrules : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    {X : W}
    (ell r : Word Sigma)
    (hctx : ContextFamily H profile Rrules S0 X ell r)
    (hcover :
      TwoSidedResidual
          (CarrierStartImage q H profile Rrules S0)
          (q ell)
          (q r)
        ⊆
      CarrierConceptSemantics
          (CarrierStartImage q H profile Rrules S0)
          q H profile Rrules X) :
    ConceptClosure
        (CarrierStartImage q H profile Rrules S0)
        (TwoSidedResidual
          (CarrierStartImage q H profile Rrules S0)
          (q ell)
          (q r))
      =
      CarrierConceptSemantics
        (CarrierStartImage q H profile Rrules S0)
        q H profile Rrules X := by
  have hsound :
      CarrierStateSemantics q H profile Rrules X ⊆
        TwoSidedResidual
          (CarrierStartImage q H profile Rrules S0)
          (q ell)
          (q r) := by
    simpa [CarrierStartImage] using
      (carrier_state_semantics_subset_residual
        q q_mul H profile Rrules S0 ell r hctx)
  have hcover' :
      TwoSidedResidual
          (CarrierStartImage q H profile Rrules S0)
          (q ell)
          (q r)
        ⊆
      ConceptClosure
        (CarrierStartImage q H profile Rrules S0)
        (CarrierStateSemantics q H profile Rrules X) := by
    simpa [CarrierConceptSemantics] using hcover
  unfold CarrierConceptSemantics
  exact adequacy_of_residual_coverage
    (CarrierStartImage q H profile Rrules S0)
    (CarrierStateSemantics q H profile Rrules X)
    (TwoSidedResidual
      (CarrierStartImage q H profile Rrules S0)
      (q ell)
      (q r))
    hsound hcover'

/--
Frame-level adequacy criterion for the standard observation `q = h`.

The two-sided frame soundness theorem supplies the soundness inclusion
automatically.  Hence adequacy of the frame residual is equivalent to verifying
the coverage condition `hcover`.
-/
theorem carrier_frame_adequacy_of_coverage_h
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
    (hcover :
      TwoSidedResidual
          (CarrierStartImage H.h H profile Rrules S0)
          (profile X).lt
          (profile X).rt
        ⊆
      CarrierConceptSemantics
          (CarrierStartImage H.h H profile Rrules S0)
          H.h H profile Rrules X) :
    ConceptClosure
        (CarrierStartImage H.h H profile Rrules S0)
        (TwoSidedResidual
          (CarrierStartImage H.h H profile Rrules S0)
          (profile X).lt
          (profile X).rt)
      =
      CarrierConceptSemantics
        (CarrierStartImage H.h H profile Rrules S0)
        H.h H profile Rrules X := by
  have hsound :
      CarrierStateSemantics H.h H profile Rrules X ⊆
        TwoSidedResidual
          (CarrierStartImage H.h H profile Rrules S0)
          (profile X).lt
          (profile X).rt := by
    simpa [CarrierStartImage] using
      (carrier_state_semantics_subset_frame_residual_h
        H profile Rrules S0 hStartFrame hctx)
  have hcover' :
      TwoSidedResidual
          (CarrierStartImage H.h H profile Rrules S0)
          (profile X).lt
          (profile X).rt
        ⊆
      ConceptClosure
        (CarrierStartImage H.h H profile Rrules S0)
        (CarrierStateSemantics H.h H profile Rrules X) := by
    simpa [CarrierConceptSemantics] using hcover
  unfold CarrierConceptSemantics
  exact adequacy_of_residual_coverage
    (CarrierStartImage H.h H profile Rrules S0)
    (CarrierStateSemantics H.h H profile Rrules X)
    (TwoSidedResidual
      (CarrierStartImage H.h H profile Rrules S0)
      (profile X).lt
      (profile X).rt)
    hsound hcover'

/--
Frame-level adequacy criterion for observations factoring through `h`.

If `q = theta ∘ h`, then frame soundness again supplies the soundness
inclusion.  The only additional proof obligation for adequacy is the coverage
condition `hcover`.
-/
theorem carrier_frame_adequacy_of_coverage_factor
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
    (hcover :
      TwoSidedResidual
          (CarrierStartImage
            (fun w : Word Sigma => theta (H.h w))
            H profile Rrules S0)
          (theta ((profile X).lt))
          (theta ((profile X).rt))
        ⊆
      CarrierConceptSemantics
          (CarrierStartImage
            (fun w : Word Sigma => theta (H.h w))
            H profile Rrules S0)
          (fun w : Word Sigma => theta (H.h w))
          H profile Rrules X) :
    ConceptClosure
        (CarrierStartImage
          (fun w : Word Sigma => theta (H.h w))
          H profile Rrules S0)
        (TwoSidedResidual
          (CarrierStartImage
            (fun w : Word Sigma => theta (H.h w))
            H profile Rrules S0)
          (theta ((profile X).lt))
          (theta ((profile X).rt)))
      =
      CarrierConceptSemantics
        (CarrierStartImage
          (fun w : Word Sigma => theta (H.h w))
          H profile Rrules S0)
        (fun w : Word Sigma => theta (H.h w))
        H profile Rrules X := by
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
  have hcover' :
      TwoSidedResidual
          (CarrierStartImage
            (fun w : Word Sigma => theta (H.h w))
            H profile Rrules S0)
          (theta ((profile X).lt))
          (theta ((profile X).rt))
        ⊆
      ConceptClosure
        (CarrierStartImage
          (fun w : Word Sigma => theta (H.h w))
          H profile Rrules S0)
        (CarrierStateSemantics
          (fun w : Word Sigma => theta (H.h w))
          H profile Rrules X) := by
    simpa [CarrierConceptSemantics] using hcover
  unfold CarrierConceptSemantics
  exact adequacy_of_residual_coverage
    (CarrierStartImage
      (fun w : Word Sigma => theta (H.h w))
      H profile Rrules S0)
    (CarrierStateSemantics
      (fun w : Word Sigma => theta (H.h w))
      H profile Rrules X)
    (TwoSidedResidual
      (CarrierStartImage
        (fun w : Word Sigma => theta (H.h w))
        H profile Rrules S0)
      (theta ((profile X).lt))
      (theta ((profile X).rt)))
    hsound hcover'

end LeanCfgProject
