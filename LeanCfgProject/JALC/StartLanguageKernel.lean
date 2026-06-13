import LeanCfgProject.JALC.DerivationLiftKernel

namespace LeanCfgProject
namespace JALC
namespace StartLanguageKernel

/-
Start-language kernel for the intended-copy construction.

This module packages the previous derivation-lift result into preservation and
reflection of the generated start language of the lifted structure.
-/

universe u v w

open InverseKernel RoundTripKernel DerivationLiftKernel


/-- Generated language of an untyped rule structure from its start declarations. -/
def UntypedStartLanguage {V : Type u} {Sigma : Type w}
    (G : UntypedStructure V Sigma) (word : List Sigma) : Prop :=
  ∃ s : StartRule V, G.start s ∧ UntypedDeriv G s.state word


/-- Generated language of a typed rule structure from its start declarations. -/
def TypedStartLanguage {V : Type u} {M : Type v} {Sigma : Type w}
    (H : TypedStructure V M Sigma) (word : List Sigma) : Prop :=
  ∃ s : TypedStartRule V M, H.start s ∧ TypedRuleDeriv H s.state word


/-- Start-language membership is preserved by intended-copy lifting. -/
theorem start_language_preserved
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    {word : List Sigma}
    (h : UntypedStartLanguage G word) :
    TypedStartLanguage (liftStructure T G) word := by
  rcases h with ⟨s, hs, hd⟩
  exact ⟨liftStart T s, start_preserved T G hs,
    derivation_preserved T G hd⟩


/-- Start-language membership is reflected by intended-copy lifting. -/
theorem start_language_reflected
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    {word : List Sigma}
    (h : TypedStartLanguage (liftStructure T G) word) :
    UntypedStartLanguage G word := by
  rcases h with ⟨s, hs, hd⟩
  rcases hs with ⟨s0, hs0, heq⟩
  cases heq
  exact ⟨s0, hs0, derivation_reflected T G hd⟩


/-- Start-language preservation and reflection as an equivalence. -/
theorem start_language_lift_iff
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    (word : List Sigma) :
    TypedStartLanguage (liftStructure T G) word ↔
      UntypedStartLanguage G word := by
  constructor
  · intro h
    exact start_language_reflected T G h
  · intro h
    exact start_language_preserved T G h


/--
Paper-facing start-language kernel.

The lifted intended-copy structure generates exactly the same start language
as the original structure.
-/
theorem start_language_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma) :
    ∀ word : List Sigma,
      TypedStartLanguage (liftStructure T G) word ↔
        UntypedStartLanguage G word := by
  intro word
  exact start_language_lift_iff T G word

end StartLanguageKernel
end JALC
end LeanCfgProject
