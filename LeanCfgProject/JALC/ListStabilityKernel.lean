import LeanCfgProject.JALC.FiniteStabilizationBoundaryKernel

namespace LeanCfgProject
namespace JALC
namespace ListStabilityKernel

/-
List stability for finite closure certificates.

A finite universe list turns an equality check on the listed support into the
global `StableAt` proof required by `ClosureCertificate`.
-/

universe u

open FiniteClosureKernel
open ProductiveReachableClosureKernel
open AlgorithmicExtractionKernel
open FiniteUniverseListEnumerationKernel
open FiniteStabilizationBoundaryKernel


/-- Two predicates agree on every element of a finite list. -/
def AgreeOnList
    {α : Type u}
    (xs : List α)
    (P Q : α → Prop) : Prop :=
  ∀ x : α, x ∈ xs → (P x ↔ Q x)


/-- List agreement over a complete universe list gives global predicate agreement. -/
theorem agreeOnUniverse
    {α : Type u}
    (U : UniverseList α)
    {P Q : α → Prop}
    (h : AgreeOnList U.support P Q) :
    ∀ x : α, P x ↔ Q x :=
  fun x => h x (U.complete x)


/-- List stability over a complete universe gives `StableAt`. -/
theorem stableAt_of_listStability
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (n : Nat)
    (h :
      AgreeOnList U.support
        (F (Iter F n))
        (Iter F n)) :
    StableAt F n :=
  agreeOnUniverse U h


/-- A closure certificate obtained from a finite list-stability proof. -/
def closureCertificate_of_listStability
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (n : Nat)
    (h :
      AgreeOnList U.support
        (F (Iter F n))
        (Iter F n)) :
    ClosureCertificate F :=
  { height := n,
    stable := stableAt_of_listStability U F n h }


/--
List-stability data for the two-stage productive/reachable extraction.
-/
structure ListStableHeightData
    {α : Type u}
    (D : ExtractionRuleData α) : Type u where
  state_universe :
    UniverseList α
  productive_height :
    Nat
  productive_stable_on_list :
    AgreeOnList state_universe.support
      (ProductiveStep D.terminal D.binary
        (Iter (ProductiveStep D.terminal D.binary) productive_height))
      (Iter (ProductiveStep D.terminal D.binary) productive_height)
  reachable_height :
    Nat
  reachable_stable_on_list :
    AgreeOnList state_universe.support
      (ReachableStep D.start D.binary
        (Iter (ProductiveStep D.terminal D.binary) productive_height)
        (Iter
          (ReachableStep D.start D.binary
            (Iter (ProductiveStep D.terminal D.binary) productive_height))
          reachable_height))
      (Iter
        (ReachableStep D.start D.binary
          (Iter (ProductiveStep D.terminal D.binary) productive_height))
        reachable_height)


/-- Convert list-stability data to stable-height data. -/
def stableHeightData_of_listStability
    {α : Type u}
    {D : ExtractionRuleData α}
    (H : ListStableHeightData D) :
    StableHeightData D :=
  { productive_height := H.productive_height,
    productive_stable :=
      stableAt_of_listStability
        H.state_universe
        (ProductiveStep D.terminal D.binary)
        H.productive_height
        H.productive_stable_on_list,
    reachable_height := H.reachable_height,
    reachable_stable :=
      stableAt_of_listStability
        H.state_universe
        (ReachableStep D.start D.binary
          (Iter (ProductiveStep D.terminal D.binary) H.productive_height))
        H.reachable_height
        H.reachable_stable_on_list }


/-- Certified extraction obtained from finite list-stability data. -/
def certifiedExtraction_of_listStability
    {α : Type u}
    {D : ExtractionRuleData α}
    (H : ListStableHeightData D) :
    CertifiedExtraction D :=
  certifiedExtraction_of_stableHeights
    (stableHeightData_of_listStability H)


/-- List-stability data exposes the certified extraction kernel. -/
theorem listStability_certifiedExtractionKernel
    {α : Type u}
    {D : ExtractionRuleData α}
    (H : ListStableHeightData D) :
    CertifiedExtractionKernel
      (certifiedExtraction_of_listStability H) :=
  certifiedExtractionKernel_holds
    (certifiedExtraction_of_listStability H)

end ListStabilityKernel
end JALC
end LeanCfgProject
