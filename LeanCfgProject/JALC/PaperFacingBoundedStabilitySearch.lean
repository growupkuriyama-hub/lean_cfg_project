import LeanCfgProject.JALC.BoundedListStabilitySearchKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingBoundedStabilitySearch

/-
Paper-facing target for bounded list-stability search.
-/

universe u v w

open BoundedListStabilitySearchKernel
open FinalArtifactKernel


/-- The previous final artifact target remains available. -/
theorem checked_previous_final_artifact_from_bounded_search :
    FinalArtifactChecked :=
  final_artifact_checked


/-- Paper-facing bounded search for a productive stability witness. -/
def checked_findProductiveStabilityWitness
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (B : ConcreteBoundedSearchData tau G)
    (fuel : Nat) :
    Option
      (ListStabilityWitness
        B.rule_universes.states
        (ProductiveFullStep tau G)) :=
  findProductiveStabilityWitness tau G B fuel


/-- Paper-facing bounded search for a reachable stability witness. -/
def checked_findReachableStabilityWitness
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (B : ConcreteBoundedSearchData tau G)
    (productive_height fuel : Nat) :
    Option
      (ListStabilityWitness
        B.rule_universes.states
        (ReachableFullStepAt tau G productive_height)) :=
  findReachableStabilityWitness tau G B productive_height fuel


/-- Paper-facing successful bounded search to FullKept decidability. -/
theorem checked_boundedSearchSuccess_to_fullKept_decidable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    [DecidableEq (InverseKernel.TypedState V M)]
    (tau : Sigma → M)
    (G : RoundTripKernel.UntypedStructure V Sigma)
    (S : ConcreteBoundedSearchSuccess tau G) :
    Nonempty (DecidablePred (FullKeptCorrectnessKernel.FullKept tau G)) :=
  boundedSearchSuccess_to_fullKept_decidable tau G S

end PaperFacingBoundedStabilitySearch
end JALC
end LeanCfgProject
