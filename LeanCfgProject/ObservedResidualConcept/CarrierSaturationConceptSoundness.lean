import LeanCfgProject.CarrierSaturationLeast
import LeanCfgProject.CarrierConceptSemantics

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/--
Saturation-based carrier concept semantics: first compute the finite-stage
carrier saturation image, then close it in the residual concept closure.

By `carrier_saturationImage_eq_stateSemantics`, this agrees with the earlier
`CarrierConceptSemantics`, but this definition exposes the algorithmic route
through saturation.
-/
def CarrierSaturationConceptSemantics
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (X : W) : Set Q :=
  ConceptClosure S (CarrierSaturationImage q H profile R X)

/--
The saturation-based carrier concept semantics is a residual concept extent.
-/
theorem carrierSaturationConceptSemantics_isConceptExtent
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (X : W) :
    IsConceptExtent S
      (CarrierSaturationConceptSemantics S q H profile R X) := by
  unfold CarrierSaturationConceptSemantics
  exact conceptClosure_isConceptExtent S
    (CarrierSaturationImage q H profile R X)

/--
Binary soundness at the saturation-concept level, stated for the abstract
carrier binary relation.  If `X → Y Z` is a carrier binary rule, then the
concept product of the saturated images of `Y` and `Z` is included in the
saturation concept semantics of `X`.
-/
theorem carrier_binaryRel_sound_as_saturationConceptSemantics
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    {X Y Z : W}
    (hbin : CarrierBinaryRel H profile R X Y Z) :
    ConceptProduct S
      (CarrierSaturationImage q H profile R Y)
      (CarrierSaturationImage q H profile R Z)
      ⊆
    CarrierSaturationConceptSemantics S q H profile R X := by
  unfold CarrierSaturationConceptSemantics
  unfold ConceptProduct
  exact conceptClosure_mono S (by
    intro x hx
    rcases hx with ⟨b, hb, c, hc, hxEq⟩
    rw [hxEq]
    exact carrier_binary_mul_mem_saturationImage
      q H profile R hbin hb hc)

/--
Binary soundness at the saturation-concept level, stated directly for a
listed carrier binary rule.
-/
theorem carrier_binaryRule_sound_as_saturationConceptSemantics
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (br : CarrierBinaryRule profile)
    (hmem : List.Mem (CarrierTypedRule.binary br) R) :
    ConceptProduct S
      (CarrierSaturationImage q H profile R br.Y)
      (CarrierSaturationImage q H profile R br.Z)
      ⊆
    CarrierSaturationConceptSemantics S q H profile R br.X := by
  exact carrier_binaryRel_sound_as_saturationConceptSemantics
    S q H profile R ⟨br, hmem, rfl, rfl, rfl⟩

/--
The saturation-based concept semantics agrees with the existing carrier
concept semantics.  This packages the finite-stage saturation correctness
as an equality of concept-level interpretations.
-/
theorem carrierSaturationConceptSemantics_eq_carrierConceptSemantics
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
    (X : W) :
    CarrierSaturationConceptSemantics S q H profile R X =
      CarrierConceptSemantics S q H profile R X := by
  unfold CarrierSaturationConceptSemantics
  unfold CarrierConceptSemantics
  rw [carrier_saturationImage_eq_stateSemantics q q_mul H profile R X]

/--
A saturation-form version of the existing carrier concept-product soundness:
a listed binary rule is sound after computing state meanings by saturation.
-/
theorem carrier_binaryRule_sound_as_saturationConceptSemantics_eq
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
    (br : CarrierBinaryRule profile)
    (hmem : List.Mem (CarrierTypedRule.binary br) R) :
    ConceptProduct S
      (CarrierSaturationImage q H profile R br.Y)
      (CarrierSaturationImage q H profile R br.Z)
      ⊆
    CarrierConceptSemantics S q H profile R br.X := by
  rw [← carrierSaturationConceptSemantics_eq_carrierConceptSemantics
    S q q_mul H profile R br.X]
  exact carrier_binaryRule_sound_as_saturationConceptSemantics
    S q H profile R br hmem

/--
For the standard observation `q = h`, the saturation-based concept semantics
agrees with the existing carrier concept semantics without requiring an
extra multiplication hypothesis.
-/
theorem carrierSaturationConceptSemantics_eq_carrierConceptSemantics_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (S : Set M)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (X : W) :
    CarrierSaturationConceptSemantics S H.h H profile R X =
      CarrierConceptSemantics S H.h H profile R X := by
  exact carrierSaturationConceptSemantics_eq_carrierConceptSemantics
    S H.h H.map_append H profile R X

end LeanCfgProject
