import LeanCfgProject.JALC.PaperFacingFixedPoint

namespace LeanCfgProject
namespace JALC
namespace AlgorithmicExtractionKernel

/-
Certified algorithmic extraction kernel.

This module packages the fixed-point closure kernels in the shape used by
Algorithm 1 in the paper: first compute productivity, then compute reachability
inside the productive part, and finally take the intersection as the kept
predicate.
-/

universe u

open FiniteClosureKernel
open ProductiveReachableClosureKernel


/-- Abstract rule data for the finite extraction algorithm. -/
structure ExtractionRuleData (α : Type u) : Type u where
  terminal : α → Prop
  binary : α → α → α → Prop
  start : α → Prop


/--
A certified run of the productive-first extraction algorithm.

The first certificate stabilizes the productivity iteration.  The second
certificate stabilizes reachability after productivity has already been fixed.
-/
structure CertifiedExtraction {α : Type u}
    (D : ExtractionRuleData α) : Type u where
  productiveCert : ProductiveCertificate D.terminal D.binary
  reachableCert :
    ReachableCertificate D.start D.binary
      (ProductiveClosure D.terminal D.binary productiveCert)


/-- The computed productive predicate of a certified extraction. -/
def computedProductive {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) : α → Prop :=
  ProductiveClosure D.terminal D.binary E.productiveCert


/-- The computed reachable predicate of a certified extraction. -/
def computedReachable {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) : α → Prop :=
  ReachableClosure D.start D.binary
    (computedProductive E) E.reachableCert


/-- The computed kept predicate of a certified extraction. -/
def computedKept {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) : α → Prop :=
  fun x => computedProductive E x ∧ computedReachable E x


/-- The computed productive predicate is a fixed point of the productivity step. -/
theorem computedProductive_fixed
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) :
    PredFixed (ProductiveStep D.terminal D.binary)
      (computedProductive E) :=
  productiveClosure_fixed D.terminal D.binary E.productiveCert


/--
The computed productive predicate is least among pre-fixed predicates for the
productivity step.
-/
theorem computedProductive_least_prefixed
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D)
    {Q : α → Prop}
    (closed : PredPreFixed (ProductiveStep D.terminal D.binary) Q) :
    PredSubset (computedProductive E) Q :=
  productiveClosure_least_prefixed D.terminal D.binary
    E.productiveCert closed


/--
The computed reachable predicate is a fixed point of reachability inside the
computed productive part.
-/
theorem computedReachable_fixed
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) :
    PredFixed
      (ReachableStep D.start D.binary (computedProductive E))
      (computedReachable E) :=
  reachableClosure_fixed D.start D.binary
    (computedProductive E) E.reachableCert


/--
The computed reachable predicate is least among pre-fixed predicates for
reachability inside the computed productive part.
-/
theorem computedReachable_least_prefixed
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D)
    {Q : α → Prop}
    (closed :
      PredPreFixed
        (ReachableStep D.start D.binary (computedProductive E)) Q) :
    PredSubset (computedReachable E) Q :=
  reachableClosure_least_prefixed D.start D.binary
    (computedProductive E) E.reachableCert closed


/-- Computed kept states are productive. -/
theorem computedKept_subset_productive
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) :
    PredSubset (computedKept E) (computedProductive E) := by
  intro x hx
  exact hx.1


/-- Computed kept states are reachable inside the computed productive part. -/
theorem computedKept_subset_reachable
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) :
    PredSubset (computedKept E) (computedReachable E) := by
  intro x hx
  exact hx.2


/-- The computed kept predicate is exactly the intersection of the two stages. -/
theorem computedKept_iff
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D)
    (x : α) :
    computedKept E x ↔ computedProductive E x ∧ computedReachable E x :=
  Iff.rfl


/-- Bundled correctness facts for a certified extraction run. -/
structure CertifiedExtractionKernel {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) : Prop where
  productive_fixed :
    PredFixed (ProductiveStep D.terminal D.binary)
      (computedProductive E)
  reachable_fixed :
    PredFixed
      (ReachableStep D.start D.binary (computedProductive E))
      (computedReachable E)
  productive_least :
    ∀ {Q : α → Prop},
      PredPreFixed (ProductiveStep D.terminal D.binary) Q →
        PredSubset (computedProductive E) Q
  reachable_least :
    ∀ {Q : α → Prop},
      PredPreFixed
        (ReachableStep D.start D.binary (computedProductive E)) Q →
        PredSubset (computedReachable E) Q
  kept_productive :
    PredSubset (computedKept E) (computedProductive E)
  kept_reachable :
    PredSubset (computedKept E) (computedReachable E)


/-- The certified extraction kernel follows from the two closure certificates. -/
theorem certifiedExtractionKernel_holds
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) :
    CertifiedExtractionKernel E := by
  exact
    { productive_fixed := computedProductive_fixed E,
      reachable_fixed := computedReachable_fixed E,
      productive_least := by
        intro Q hQ
        exact computedProductive_least_prefixed E hQ,
      reachable_least := by
        intro Q hQ
        exact computedReachable_least_prefixed E hQ,
      kept_productive := computedKept_subset_productive E,
      kept_reachable := computedKept_subset_reachable E }


/--
A compact theorem corresponding to Algorithm 1: a certified run computes fixed
productivity and productive-part reachability predicates, and keptness is their
intersection.
-/
theorem algorithmic_extraction_kernel
    {α : Type u}
    {D : ExtractionRuleData α}
    (E : CertifiedExtraction D) :
    PredFixed (ProductiveStep D.terminal D.binary)
        (computedProductive E) ∧
      PredFixed
        (ReachableStep D.start D.binary (computedProductive E))
        (computedReachable E) ∧
      (∀ x : α,
        computedKept E x ↔
          computedProductive E x ∧ computedReachable E x) := by
  exact ⟨computedProductive_fixed E,
    computedReachable_fixed E,
    computedKept_iff E⟩

end AlgorithmicExtractionKernel
end JALC
end LeanCfgProject
