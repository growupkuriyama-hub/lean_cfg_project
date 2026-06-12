import LeanCfgProject.ObservedResidualConcept.DescriptorResidualSemantics
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

def CarrierStartImage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v}
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W) : Set Q :=
  ImageOfLanguage q (CarrierStartLanguage H profile R S0)

def CarrierConceptSemantics
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
  ConceptClosure S (CarrierStateSemantics q H profile R X)

theorem carrierConceptSemantics_isConceptExtent
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
    IsConceptExtent S (CarrierConceptSemantics S q H profile R X) := by
  unfold CarrierConceptSemantics
  exact conceptClosure_isConceptExtent S (CarrierStateSemantics q H profile R X)

theorem carrier_binary_sound_as_conceptSemantics
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
      (CarrierStateSemantics q H profile R br.Y)
      (CarrierStateSemantics q H profile R br.Z)
      ⊆
    CarrierConceptSemantics S q H profile R br.X := by
  unfold CarrierConceptSemantics
  exact carrier_binary_sound_as_conceptProduct S q q_mul H profile R br hmem

theorem carrier_context_concept_subset_residual_closure
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
    (S0 : Finset W)
    {X : W}
    (ell r : Word Sigma)
    (hctx : ContextFamily H profile R S0 X ell r) :
    CarrierConceptSemantics S q H profile R X ⊆
      ConceptClosure S
        (TwoSidedResidual
          (CarrierStartImage q H profile R S0)
          (q ell)
          (q r)) := by
  unfold CarrierConceptSemantics
  unfold CarrierStartImage
  exact conceptClosure_mono S
    (carrier_state_semantics_subset_residual q q_mul H profile R S0 ell r hctx)

end LeanCfgProject
