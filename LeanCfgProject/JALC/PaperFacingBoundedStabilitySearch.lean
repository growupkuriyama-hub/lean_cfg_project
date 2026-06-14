import LeanCfgProject.JALC.BoundedListStabilitySearchKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingBoundedStabilitySearch

/-
Paper-facing target for generic bounded list-stability search.
-/

universe u

open BoundedListStabilitySearchKernel
open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open FinalArtifactKernel


/-- The previous final artifact target remains available. -/
theorem checked_previous_final_artifact_from_bounded_search :
    FinalArtifactChecked :=
  final_artifact_checked


/-- Paper-facing bounded search for a generic finite-stability witness. -/
def checked_findListStabilityWitness
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (ListStabilityKernel.AgreeOnList U.support
            (F (Iter F n))
            (Iter F n)))
    (fuel : Nat) :
    Option (ListStabilityWitness U F) :=
  findListStabilityWitness U F dec fuel


/-- Paper-facing conversion from a bounded-search witness to a certificate. -/
def checked_closureCertificate_of_listStabilityWitness
    {α : Type u}
    {U : UniverseList α}
    {F : (α → Prop) → α → Prop}
    (W : ListStabilityWitness U F) :
    ClosureCertificate F :=
  closureCertificate_of_listStabilityWitness W


/-- Paper-facing stable-at result from a bounded-search witness. -/
theorem checked_stableAt_of_listStabilityWitness
    {α : Type u}
    {U : UniverseList α}
    {F : (α → Prop) → α → Prop}
    (W : ListStabilityWitness U F) :
    StableAt F W.height :=
  stableAt_of_listStabilityWitness W

end PaperFacingBoundedStabilitySearch
end JALC
end LeanCfgProject
