import LeanCfgProject.JALC.FullKeptDecidabilityKernel
import LeanCfgProject.JALC.FullFiniteMainKernel

namespace LeanCfgProject
namespace JALC
namespace AlgorithmicFiniteMainKernel

/-
Algorithmic finite-main package.

This module uses the checked Algorithm 1 / FullKept agreement to supply the
FullKept decidability needed by the finite full-main theorem package, provided
the certified computed kept predicate is decidable.
-/

universe u v w

open InverseKernel RoundTripKernel
open ReachableProductiveKernel
open FullRefinementKernel
open FullYieldKernel
open FullKeptCorrectnessKernel
open FullTrimmedLanguageKernel FullMainTheoremKernel
open AlgorithmicExtractionKernel
open AlgorithmicFullBridgeKernel
open FullAlgorithmicAgreementKernel
open FullKeptDecidabilityKernel
open FiniteRepresentationBundle
open FullFiniteMainKernel


/--
Algorithmic finite-main package with the decidability boundary moved to the
computed predicate of the certified Algorithm 1 run.
-/
structure AlgorithmicFiniteMainPackage
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M] [Fintype V] [Fintype M] [Fintype Sigma]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G)
    (E : CertifiedExtraction (fullExtractionRuleData tau G)) : Prop where
  agreement :
    ComputedAgreesWithFullKept E tau G
  fullkept_decidable :
    Nonempty (DecidablePred (FullKept tau G))
  typed_finite :
    TypedFiniteBundle V M Sigma
  kept_finite :
    KeptFiniteBundle Sigma (FullKept tau G)
  language :
    ∀ word : List Sigma,
      KeptStartLanguage (fullKeptStructure T tau G comp red) word ↔
        StartLanguageKernel.UntypedStartLanguage G word
  representation :
    RepresentationKernel.RepresentationKernel T G (FullKept tau G)


/-- Build the algorithmic finite-main package from a decidable certified run. -/
theorem algorithmic_finite_main_package
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M] [Fintype V] [Fintype M] [Fintype Sigma]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    [DecidablePred (computedKept E)] :
    AlgorithmicFiniteMainPackage T tau G comp sound red E := by
  letI : DecidablePred (FullKept tau G) :=
    fullKeptDecidable_of_fullExtraction tau G E
  exact
    { agreement := fullAlgorithmicComputedKept_agrees tau G E,
      fullkept_decidable := ⟨inferInstance⟩,
      typed_finite := typedFiniteBundle_of_finite V M Sigma,
      kept_finite := keptFiniteBundle_of_finite Sigma (FullKept tau G),
      language := full_finite_main_language T tau G comp sound red,
      representation := full_refinement_main_representation T tau G comp sound red }


/-- Kept finiteness component supplied from Algorithm 1 decidability. -/
theorem algorithmic_finite_main_kept_finite
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M] [Fintype V] [Fintype M] [Fintype Sigma]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    [DecidablePred (computedKept E)] :
    KeptFiniteBundle Sigma (FullKept tau G) :=
  (algorithmic_finite_main_package T tau G comp sound red E).kept_finite

end AlgorithmicFiniteMainKernel
end JALC
end LeanCfgProject
