import LeanCfgProject.JALC.ProductiveReachableClosureKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingFixedPoint

/-
Paper-facing finite fixed-point closure checks.
-/

universe u

open FiniteClosureKernel
open ProductiveReachableClosureKernel


/-- Paper-facing check: a certified monotone closure is a fixed point. -/
theorem checked_certifiedClosure_fixed
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (c : ClosureCertificate F) :
    PredFixed F (certifiedClosure c) :=
  certifiedClosure_fixed c


/-- Paper-facing check: a certified monotone closure is least among pre-fixed predicates. -/
theorem checked_certifiedClosure_least_prefixed
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    (c : ClosureCertificate F)
    {Q : α → Prop}
    (closed : PredPreFixed F Q) :
    PredSubset (certifiedClosure c) Q :=
  certifiedClosure_least_prefixed mono c closed


/-- Paper-facing check: productivity closure is monotone and certificate-fixed. -/
theorem checked_productiveClosure_fixed
    {α : Type u}
    (terminal : α → Prop)
    (binary : α → α → α → Prop)
    (c : ProductiveCertificate terminal binary) :
    PredFixed (ProductiveStep terminal binary)
      (ProductiveClosure terminal binary c) :=
  productiveClosure_fixed terminal binary c


/-- Paper-facing check: productive-part reachability closure is certificate-fixed. -/
theorem checked_reachableClosure_fixed
    {α : Type u}
    (start : α → Prop)
    (binary : α → α → α → Prop)
    (productive : α → Prop)
    (c : ReachableCertificate start binary productive) :
    PredFixed (ReachableStep start binary productive)
      (ReachableClosure start binary productive c) :=
  reachableClosure_fixed start binary productive c


/-- Paper-facing check: computed keptness has fixed productivity and reachability components. -/
theorem checked_computedKept_fixed_components
    {α : Type u}
    (terminal : α → Prop)
    (binary : α → α → α → Prop)
    (start : α → Prop)
    (pc : ProductiveCertificate terminal binary)
    (rc : ReachableCertificate start binary
      (ProductiveClosure terminal binary pc)) :
    PredFixed (ProductiveStep terminal binary)
        (ProductiveClosure terminal binary pc) ∧
      PredFixed
        (ReachableStep start binary
          (ProductiveClosure terminal binary pc))
        (ReachableClosure start binary
          (ProductiveClosure terminal binary pc) rc) := by
  exact ⟨computedKept_productive_fixed terminal binary start pc rc,
    computedKept_reachable_fixed terminal binary start pc rc⟩

end PaperFacingFixedPoint
end JALC
end LeanCfgProject
