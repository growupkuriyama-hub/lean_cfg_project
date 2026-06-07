import LeanCfgProject.FrameSoundness
import LeanCfgProject.CarrierSaturationCorrectness

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/--
Combining saturation correctness with frame residual soundness:
for the standard observation `q = h`, the finite-stage saturation image of
state `X` is contained in the residual determined by the typed external frame
of any witnessed context of `X`.
-/
theorem carrier_saturationImage_subset_frame_residual_h
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
    CarrierSaturationImage H.h H profile R X ⊆
      TwoSidedResidual
        (ImageOfLanguage H.h (CarrierStartLanguage H profile R S0))
        (profile X).lt
        (profile X).rt := by
  rw [carrier_saturationImage_eq_stateSemantics H.h H.map_append H profile R X]
  exact carrier_state_semantics_subset_frame_residual_h
    H profile R S0 hStartFrame hctx

/--
Intent form of the saturation-frame bridge: the typed frame `(lt,rt)` is a
common context of the finite saturation image.  In FCA terminology, the frame
belongs to the intent of the saturated state semantics.
-/
theorem carrier_frame_mem_commonContexts_saturation_h
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
        (ImageOfLanguage H.h (CarrierStartLanguage H profile R S0))
        (CarrierSaturationImage H.h H profile R X) := by
  intro gamma hgamma
  exact carrier_saturationImage_subset_frame_residual_h
    H profile R S0 hStartFrame hctx hgamma

/--
Closure-level bridge: the concept closure of the finite saturation image is
contained in the closure of the residual determined by the typed frame.
-/
theorem carrier_saturationConcept_subset_frame_residual_closure_h
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
    ConceptClosure
        (ImageOfLanguage H.h (CarrierStartLanguage H profile R S0))
        (CarrierSaturationImage H.h H profile R X) ⊆
      ConceptClosure
        (ImageOfLanguage H.h (CarrierStartLanguage H profile R S0))
        (TwoSidedResidual
          (ImageOfLanguage H.h (CarrierStartLanguage H profile R S0))
          (profile X).lt
          (profile X).rt) := by
  exact conceptClosure_mono _
    (carrier_saturationImage_subset_frame_residual_h
      H profile R S0 hStartFrame hctx)

/--
The concept semantics computed from the finite saturation image agrees with
existing carrier concept semantics.
-/
theorem carrier_saturationConcept_eq_carrierConceptSemantics_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S : Set M)
    (X : W) :
    ConceptClosure S (CarrierSaturationImage H.h H profile R X) =
      CarrierConceptSemantics S H.h H profile R X := by
  unfold CarrierConceptSemantics
  rw [carrier_saturationImage_eq_stateSemantics H.h H.map_append H profile R X]

/--
The saturation-based concept semantics is a concept extent.
-/
theorem carrier_saturationConcept_isConceptExtent_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S : Set M)
    (X : W) :
    IsConceptExtent S
      (ConceptClosure S (CarrierSaturationImage H.h H profile R X)) := by
  exact conceptClosure_isConceptExtent S
    (CarrierSaturationImage H.h H profile R X)

/--
Factored-observation version of the saturation-frame bridge.  If the chosen
observation is `theta ∘ h`, then the residual bound of the finite saturation
image is determined by the typed frame through `theta`.
-/
theorem carrier_saturationImage_subset_frame_residual_factor
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (theta : M →* Q)
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
    CarrierSaturationImage (fun w : Word Sigma => theta (H.h w)) H profile R X ⊆
      TwoSidedResidual
        (ImageOfLanguage (fun w : Word Sigma => theta (H.h w))
          (CarrierStartLanguage H profile R S0))
        (theta ((profile X).lt))
        (theta ((profile X).rt)) := by
  let q : Word Sigma → Q := fun w => theta (H.h w)
  have q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v := by
    intro u v
    dsimp [q]
    rw [H.map_append]
    simp
  rw [carrier_saturationImage_eq_stateSemantics q q_mul H profile R X]
  exact carrier_state_semantics_subset_frame_residual_factor
    theta H profile R S0 hStartFrame hctx

end LeanCfgProject
