import LeanCfgProject.JALC.FullRefinementKernel

namespace LeanCfgProject
namespace JALC
namespace FullRefinementLanguageKernel

/-
Language-preservation kernels from the original structure into the full
all-copy typed refinement.
-/

universe u v w

open InverseKernel RoundTripKernel
open DerivationLiftKernel StartLanguageKernel
open FullRefinementKernel


/-- Derivations are monotone under inclusion of typed rule structures. -/
theorem typed_derivation_mono
    {V : Type u} {M : Type v} {Sigma : Type w}
    {H K : TypedStructure V M Sigma}
    (inc : TypedStructureIncluded H K)
    {s : TypedState V M} {word : List Sigma}
    (d : TypedRuleDeriv H s word) :
    TypedRuleDeriv K s word := by
  induction d with
  | terminal h =>
      exact TypedRuleDeriv.terminal (inc.terminal _ h)
  | binary h left right ihLeft ihRight =>
      exact TypedRuleDeriv.binary (inc.binary _ h) ihLeft ihRight


/-- Typed start languages are monotone under inclusion of typed structures. -/
theorem typed_start_language_mono
    {V : Type u} {M : Type v} {Sigma : Type w}
    {H K : TypedStructure V M Sigma}
    (inc : TypedStructureIncluded H K)
    {word : List Sigma}
    (h : TypedStartLanguage H word) :
    TypedStartLanguage K word := by
  rcases h with ⟨s, hs, hd⟩
  exact ⟨s, inc.start _ hs, typed_derivation_mono inc hd⟩


/--
Every original derivation appears in the full all-copy typed refinement at the
intended copy, under rule-typing compatibility.
-/
theorem full_refinement_derivation_preserved
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    {X : V} {word : List Sigma}
    (d : UntypedDeriv G X word) :
    TypedRuleDeriv (fullTypedStructure tau G) (intendedCopy T X) word := by
  exact typed_derivation_mono
    (liftStructure_included_in_full T tau G comp)
    (derivation_preserved T G d)


/--
The original start language is included in the start language of the full
all-copy typed refinement, under rule-typing compatibility.
-/
theorem full_refinement_language_preserved
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    {word : List Sigma}
    (h : UntypedStartLanguage G word) :
    TypedStartLanguage (fullTypedStructure tau G) word := by
  exact typed_start_language_mono
    (liftStructure_included_in_full T tau G comp)
    (start_language_preserved T G h)


/--
Paper-facing language inclusion kernel from the original structure into the full
all-copy typed refinement.
-/
theorem full_refinement_language_inclusion_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G) :
    ∀ word : List Sigma,
      UntypedStartLanguage G word →
        TypedStartLanguage (fullTypedStructure tau G) word := by
  intro word h
  exact full_refinement_language_preserved T tau G comp h

end FullRefinementLanguageKernel
end JALC
end LeanCfgProject
