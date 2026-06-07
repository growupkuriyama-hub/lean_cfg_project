import LeanCfgProject.SaturationFrameBridge
import LeanCfgProject.CarrierSaturationConceptSoundness

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u

/--
Closure-intent version of frame soundness for the existing carrier concept
semantics.  If a state occurrence has typed external frame `(lt,rt)`, then
that frame is not only a common context of the raw state semantics; it remains
in the intent of the residual concept closure of that state.
-/
theorem carrier_frame_mem_commonContexts_carrierConcept_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    ((profile X).lt, (profile X).rt) ∈
      CommonContexts
        (CarrierStartImage H.h H profile R S0)
        (CarrierConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R X) := by
  unfold CarrierConceptSemantics
  unfold CarrierStartImage
  exact commonContexts_conceptClosure _ _
    (carrier_frame_mem_commonContexts_h H profile R S0 hStartFrame hctx)

/--
Closure-intent version of the saturation-frame bridge.  The typed frame belongs
to the intent of the concept obtained by closing the finite saturation image.
This is the saturation-computed version of
`carrier_frame_mem_commonContexts_carrierConcept_h`.
-/
theorem carrier_frame_mem_commonContexts_saturationConcept_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    ((profile X).lt, (profile X).rt) ∈
      CommonContexts
        (CarrierStartImage H.h H profile R S0)
        (CarrierSaturationConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R X) := by
  unfold CarrierSaturationConceptSemantics
  unfold CarrierStartImage
  exact commonContexts_conceptClosure _ _
    (carrier_frame_mem_commonContexts_saturation_h H profile R S0 hStartFrame hctx)

/--
The saturation-computed and ordinary carrier concept semantics have the same
frame-intent membership statement for the standard observation `h`.
-/
theorem carrier_frame_mem_commonContexts_saturationConcept_eq_carrierConcept_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    ((profile X).lt, (profile X).rt) ∈
      CommonContexts
        (CarrierStartImage H.h H profile R S0)
        (CarrierConceptSemantics
          (CarrierStartImage H.h H profile R S0)
          H.h H profile R X) := by
  exact carrier_frame_mem_commonContexts_carrierConcept_h
    H profile R S0 hStartFrame hctx

/--
Residual-closure bound stated with the named saturation concept semantics.
This packages `carrier_saturationConcept_subset_frame_residual_closure_h` using
`CarrierSaturationConceptSemantics` and `CarrierStartImage`.
-/
theorem carrierSaturationConceptSemantics_subset_frame_residual_closure_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    CarrierSaturationConceptSemantics
        (CarrierStartImage H.h H profile R S0)
        H.h H profile R X ⊆
      ConceptClosure
        (CarrierStartImage H.h H profile R S0)
        (TwoSidedResidual
          (CarrierStartImage H.h H profile R S0)
          (profile X).lt
          (profile X).rt) := by
  unfold CarrierSaturationConceptSemantics
  unfold CarrierStartImage
  exact carrier_saturationConcept_subset_frame_residual_closure_h
    H profile R S0 hStartFrame hctx

/--
The same residual-closure bound for the existing carrier concept semantics,
obtained through the equality between saturation-computed and ordinary concept
semantics for the standard observation.
-/
theorem carrierConceptSemantics_subset_frame_residual_closure_via_saturation_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    CarrierConceptSemantics
        (CarrierStartImage H.h H profile R S0)
        H.h H profile R X ⊆
      ConceptClosure
        (CarrierStartImage H.h H profile R S0)
        (TwoSidedResidual
          (CarrierStartImage H.h H profile R S0)
          (profile X).lt
          (profile X).rt) := by
  have hsat :=
    carrierSaturationConceptSemantics_subset_frame_residual_closure_h
      H profile R S0 hStartFrame hctx
  rw [← carrierSaturationConceptSemantics_eq_carrierConceptSemantics_h
    (CarrierStartImage H.h H profile R S0) H profile R X]
  exact hsat

end LeanCfgProject
