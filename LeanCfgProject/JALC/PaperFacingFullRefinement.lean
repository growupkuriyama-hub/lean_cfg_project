import LeanCfgProject.JALC.FullRefinementLanguageKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingFullRefinement

/-
Paper-facing full-refinement checks.
-/

universe u v w

open InverseKernel RoundTripKernel
open DerivationLiftKernel StartLanguageKernel
open FullRefinementKernel FullRefinementLanguageKernel


/-- Paper-facing check: the intended lift is contained in the full refinement. -/
theorem checked_liftStructure_included_in_full
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G) :
    TypedStructureIncluded (liftStructure T G) (fullTypedStructure tau G) :=
  liftStructure_included_in_full T tau G comp


/-- Paper-facing check: original derivations lift into the full refinement. -/
theorem checked_full_refinement_derivation_preserved
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    {X : V} {word : List Sigma}
    (d : UntypedDeriv G X word) :
    TypedRuleDeriv (fullTypedStructure tau G) (intendedCopy T X) word :=
  full_refinement_derivation_preserved T tau G comp d


/-- Paper-facing check: original start-language membership lifts into the full refinement. -/
theorem checked_full_refinement_language_preserved
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    {word : List Sigma}
    (h : UntypedStartLanguage G word) :
    TypedStartLanguage (fullTypedStructure tau G) word :=
  full_refinement_language_preserved T tau G comp h


/-- Paper-facing kernel: full-refinement language inclusion. -/
theorem checked_full_refinement_language_inclusion_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G) :
    ∀ word : List Sigma,
      UntypedStartLanguage G word →
        TypedStartLanguage (fullTypedStructure tau G) word :=
  full_refinement_language_inclusion_kernel T tau G comp

end PaperFacingFullRefinement
end JALC
end LeanCfgProject
