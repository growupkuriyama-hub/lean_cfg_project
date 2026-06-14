import LeanCfgProject.JALC.BoundedSearchOffsetCompletenessKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingBoundedSearchOffsetCompleteness

/-
Paper-facing target for offset completeness of bounded list-stability search.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel
open BoundedListStabilitySearchKernel
open BoundedSearchOffsetCompletenessKernel


/-- Paper-facing monotonicity of successful bounded search under successor fuel. -/
theorem checked_findListStabilityWitness_some_monotone_succ
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n)))
    (fuel : Nat)
    {W : ListStabilityWitness U F}
    (h :
      findListStabilityWitness U F dec fuel = some W) :
    ∃ W' : ListStabilityWitness U F,
      findListStabilityWitness U F dec (Nat.succ fuel) = some W' :=
  findListStabilityWitness_some_monotone_succ
    U F dec fuel h


/-- Paper-facing offset completeness from list-stability at height n. -/
theorem checked_findListStabilityWitness_exists_of_stable_at_offset
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n)))
    (n k : Nat)
    (hstable :
      AgreeOnList U.support
        (F (Iter F n))
        (Iter F n)) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec (n + k) = some W :=
  findListStabilityWitness_exists_of_stable_at_offset
    U F dec n k hstable


/-- Paper-facing offset completeness from global stability at height n. -/
theorem checked_findListStabilityWitness_exists_of_global_stable_at_offset
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n)))
    (n k : Nat)
    (hstable : StableAt F n) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec (n + k) = some W :=
  findListStabilityWitness_exists_of_global_stable_at_offset
    U F dec n k hstable


/-- Paper-facing closure certificate from offset list-stability. -/
theorem checked_closureCertificate_exists_of_stable_at_offset
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n)))
    (n k : Nat)
    (hstable :
      AgreeOnList U.support
        (F (Iter F n))
        (Iter F n)) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec (n + k) = some W ∧
      StableAt F W.height :=
  closureCertificate_exists_of_stable_at_offset
    U F dec n k hstable


/-- Paper-facing `StableWithinOffset` to successful bounded search. -/
theorem checked_findListStabilityWitness_exists_of_stableWithinOffset
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n)))
    (H : StableWithinOffset U F) :
    ∃ W : ListStabilityWitness U F,
      findListStabilityWitness U F dec H.fuel = some W :=
  findListStabilityWitness_exists_of_stableWithinOffset
    U F dec H

end PaperFacingBoundedSearchOffsetCompleteness
end JALC
end LeanCfgProject
