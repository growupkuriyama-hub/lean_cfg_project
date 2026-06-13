import LeanCfgProject.JALC.FiniteClosureKernel

namespace LeanCfgProject
namespace JALC
namespace ProductiveReachableClosureKernel

/-
Productivity and reachability closure kernels.

This module instantiates the finite closure certificate mechanism for two
closure operators used by the extraction procedure: productivity and
reachability inside the productive part.
-/

universe u

open FiniteClosureKernel


/-- One productivity step for terminal and binary rule predicates. -/
def ProductiveStep {α : Type u}
    (terminal : α → Prop)
    (binary : α → α → α → Prop)
    (P : α → Prop) : α → Prop :=
  fun x =>
    P x ∨ terminal x ∨
      ∃ y z, binary x y z ∧ P y ∧ P z


/-- Productivity step is monotone. -/
theorem productiveStep_monotone
    {α : Type u}
    (terminal : α → Prop)
    (binary : α → α → α → Prop) :
    PredMonotone (ProductiveStep terminal binary) := by
  intro P Q hsub x hx
  rcases hx with hp | ht | hb
  · exact Or.inl (hsub x hp)
  · exact Or.inr (Or.inl ht)
  · rcases hb with ⟨y, z, hbin, hy, hz⟩
    exact Or.inr (Or.inr ⟨y, z, hbin, hsub y hy, hsub z hz⟩)


/-- Certificate type for a finite productivity closure. -/
abbrev ProductiveCertificate {α : Type u}
    (terminal : α → Prop)
    (binary : α → α → α → Prop) :=
  ClosureCertificate (ProductiveStep terminal binary)


/-- Productive closure computed from a certificate. -/
def ProductiveClosure {α : Type u}
    (terminal : α → Prop)
    (binary : α → α → α → Prop)
    (c : ProductiveCertificate terminal binary) : α → Prop :=
  certifiedClosure c


/-- Certified productivity closure is fixed. -/
theorem productiveClosure_fixed
    {α : Type u}
    (terminal : α → Prop)
    (binary : α → α → α → Prop)
    (c : ProductiveCertificate terminal binary) :
    PredFixed (ProductiveStep terminal binary)
      (ProductiveClosure terminal binary c) :=
  certifiedClosure_fixed c


/-- Certified productivity closure is least among pre-fixed predicates. -/
theorem productiveClosure_least_prefixed
    {α : Type u}
    (terminal : α → Prop)
    (binary : α → α → α → Prop)
    (c : ProductiveCertificate terminal binary)
    {Q : α → Prop}
    (closed : PredPreFixed (ProductiveStep terminal binary) Q) :
    PredSubset (ProductiveClosure terminal binary c) Q :=
  certifiedClosure_least_prefixed
    (productiveStep_monotone terminal binary) c closed


/--
One reachability step inside a fixed productive predicate.

A left-child step requires the right sibling to be productive; a right-child
step requires the left sibling to be productive.
-/
def ReachableStep {α : Type u}
    (start : α → Prop)
    (binary : α → α → α → Prop)
    (productive : α → Prop)
    (R : α → Prop) : α → Prop :=
  fun x =>
    R x ∨
    (productive x ∧ start x) ∨
    (productive x ∧
      ∃ p z, R p ∧ binary p x z ∧ productive z) ∨
    (productive x ∧
      ∃ p y, R p ∧ binary p y x ∧ productive y)


/-- Reachability step is monotone in the current reachable predicate. -/
theorem reachableStep_monotone
    {α : Type u}
    (start : α → Prop)
    (binary : α → α → α → Prop)
    (productive : α → Prop) :
    PredMonotone (ReachableStep start binary productive) := by
  intro P Q hsub x hx
  rcases hx with hr | hstart | hleft | hright
  · exact Or.inl (hsub x hr)
  · exact Or.inr (Or.inl hstart)
  · rcases hleft with ⟨hxprod, p, z, hp, hbin, hzprod⟩
    exact Or.inr (Or.inr (Or.inl
      ⟨hxprod, p, z, hsub p hp, hbin, hzprod⟩))
  · rcases hright with ⟨hxprod, p, y, hp, hbin, hyprod⟩
    exact Or.inr (Or.inr (Or.inr
      ⟨hxprod, p, y, hsub p hp, hbin, hyprod⟩))


/-- Certificate type for a finite reachability closure. -/
abbrev ReachableCertificate {α : Type u}
    (start : α → Prop)
    (binary : α → α → α → Prop)
    (productive : α → Prop) :=
  ClosureCertificate (ReachableStep start binary productive)


/-- Reachability closure computed from a certificate. -/
def ReachableClosure {α : Type u}
    (start : α → Prop)
    (binary : α → α → α → Prop)
    (productive : α → Prop)
    (c : ReachableCertificate start binary productive) : α → Prop :=
  certifiedClosure c


/-- Certified reachability closure is fixed. -/
theorem reachableClosure_fixed
    {α : Type u}
    (start : α → Prop)
    (binary : α → α → α → Prop)
    (productive : α → Prop)
    (c : ReachableCertificate start binary productive) :
    PredFixed (ReachableStep start binary productive)
      (ReachableClosure start binary productive c) :=
  certifiedClosure_fixed c


/-- Certified reachability closure is least among pre-fixed predicates. -/
theorem reachableClosure_least_prefixed
    {α : Type u}
    (start : α → Prop)
    (binary : α → α → α → Prop)
    (productive : α → Prop)
    (c : ReachableCertificate start binary productive)
    {Q : α → Prop}
    (closed : PredPreFixed (ReachableStep start binary productive) Q) :
    PredSubset (ReachableClosure start binary productive c) Q :=
  certifiedClosure_least_prefixed
    (reachableStep_monotone start binary productive) c closed


/-- Computed kept predicate from certified productivity and reachability closures. -/
def ComputedKept {α : Type u}
    (terminal : α → Prop)
    (binary : α → α → α → Prop)
    (start : α → Prop)
    (pc : ProductiveCertificate terminal binary)
    (rc : ReachableCertificate start binary
      (ProductiveClosure terminal binary pc)) : α → Prop :=
  fun x =>
    ProductiveClosure terminal binary pc x ∧
      ReachableClosure start binary
        (ProductiveClosure terminal binary pc) rc x


/-- Computed kept states are productive. -/
theorem computedKept_productive
    {α : Type u}
    (terminal : α → Prop)
    (binary : α → α → α → Prop)
    (start : α → Prop)
    (pc : ProductiveCertificate terminal binary)
    (rc : ReachableCertificate start binary
      (ProductiveClosure terminal binary pc)) :
    PredSubset (ComputedKept terminal binary start pc rc)
      (ProductiveClosure terminal binary pc) := by
  intro x hx
  exact hx.1


/-- Computed kept states are reachable inside the computed productive part. -/
theorem computedKept_reachable
    {α : Type u}
    (terminal : α → Prop)
    (binary : α → α → α → Prop)
    (start : α → Prop)
    (pc : ProductiveCertificate terminal binary)
    (rc : ReachableCertificate start binary
      (ProductiveClosure terminal binary pc)) :
    PredSubset (ComputedKept terminal binary start pc rc)
      (ReachableClosure start binary
        (ProductiveClosure terminal binary pc) rc) := by
  intro x hx
  exact hx.2


/-- The productivity component of computed keptness is fixed. -/
theorem computedKept_productive_fixed
    {α : Type u}
    (terminal : α → Prop)
    (binary : α → α → α → Prop)
    (start : α → Prop)
    (pc : ProductiveCertificate terminal binary)
    (_rc : ReachableCertificate start binary
      (ProductiveClosure terminal binary pc)) :
    PredFixed (ProductiveStep terminal binary)
      (ProductiveClosure terminal binary pc) :=
  productiveClosure_fixed terminal binary pc


/-- The reachability component of computed keptness is fixed. -/
theorem computedKept_reachable_fixed
    {α : Type u}
    (terminal : α → Prop)
    (binary : α → α → α → Prop)
    (start : α → Prop)
    (pc : ProductiveCertificate terminal binary)
    (rc : ReachableCertificate start binary
      (ProductiveClosure terminal binary pc)) :
    PredFixed
      (ReachableStep start binary (ProductiveClosure terminal binary pc))
      (ReachableClosure start binary
        (ProductiveClosure terminal binary pc) rc) :=
  reachableClosure_fixed start binary
    (ProductiveClosure terminal binary pc) rc

end ProductiveReachableClosureKernel
end JALC
end LeanCfgProject
