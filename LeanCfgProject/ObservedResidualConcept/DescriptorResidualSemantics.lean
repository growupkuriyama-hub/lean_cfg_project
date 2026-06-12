import LeanCfgProject.ObservedResidualConcept.DescriptorSemantics
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

theorem context_yield_mem_startLanguage_aux
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    ∀ w : Word Sigma,
      YieldFamily H profile R X w →
      ell ++ w ++ r ∈ CarrierStartLanguage H profile R S0 := by
  induction hctx with
  | start x hmem =>
      intro w hy
      exact ⟨x, hmem, by simpa using hy⟩
  | binary_left br hmem hctx hz ih =>
      intro w hy
      have hparent := YieldFamily.binary br hmem hy hz
      have hstart := ih _ hparent
      simpa [List.append_assoc] using hstart
  | binary_right br hmem hctx hyLeft ih =>
      intro w hy
      have hparent := YieldFamily.binary br hmem hyLeft hy
      have hstart := ih _ hparent
      simpa [List.append_assoc] using hstart

theorem context_yield_mem_startLanguage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    {X : W}
    {ell r w : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r)
    (hy : YieldFamily H profile R X w) :
    ell ++ w ++ r ∈ CarrierStartLanguage H profile R S0 :=
  context_yield_mem_startLanguage_aux H profile R S0 hctx w hy

theorem carrier_state_semantics_subset_residual
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
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
    CarrierStateSemantics q H profile R X ⊆
      TwoSidedResidual
        (ImageOfLanguage q (CarrierStartLanguage H profile R S0))
        (q ell)
        (q r) := by
  exact state_semantics_subset_residual q q_mul
    (CarrierStartLanguage H profile R S0)
    (CarrierYieldSet H profile R X)
    ell r
    (fun w hw =>
      context_yield_mem_startLanguage H profile R S0 hctx hw)

end LeanCfgProject
