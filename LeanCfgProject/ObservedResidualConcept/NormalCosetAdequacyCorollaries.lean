import LeanCfgProject.ObservedResidualConcept.NormalCosetAdequacy
import LeanCfgProject.ObservedResidualConcept.UniformAdequacy
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject
namespace NormalCosetAdequacyCorollaries

open NormalCosetAdequacy

/-
Normal-coset uniform adequacy.

The previous module `NormalCosetAdequacy` proved the group-theoretic core:
each normal-coset residual lies in one observed-syntactic block.

This module connects that core to the already checked abstract theorem

  uniformAdequacyOn_iff_singleObservedSyntacticBlockOn_residual

from `UniformAdequacy.lean`.

It is theorem-body work only.  It is not a release, summary, certificate,
audit, package, metadata, checklist, or smoke-test module.
-/

variable {G : Type*} [Group G] {N : Set G}

/--
A normal-coset residual is a single observed-syntactic block, stated using the
abstract predicate from `UniformAdequacy.lean`.
-/
theorem normalCoset_residual_singleBlockOn
    (hN : NormalSubgroupSet G N) (s a b : G) :
    SingleObservedSyntacticBlockOn
      (LeftCosetSet N s)
      (TwoSidedResidual (LeftCosetSet N s) a b) := by
  intro x hx y hy
  exact normalCoset_residual_single_observed_block
    hN s a b x y hx hy

/--
Normal-coset residuals satisfy uniform adequacy.

Equivalently, every nonempty observed state image inside the residual generates
the whole residual by residual concept closure.
-/
theorem normalCoset_uniformAdequacyOn_residual
    (hN : NormalSubgroupSet G N) (s a b : G) :
    UniformAdequacyOn
      (LeftCosetSet N s)
      (TwoSidedResidual (LeftCosetSet N s) a b) := by
  exact
    (uniformAdequacyOn_iff_singleObservedSyntacticBlockOn_residual
      (LeftCosetSet N s) a b).2
      (normalCoset_residual_singleBlockOn hN s a b)

/--
Concrete nonempty-subset form.

If `U` is a nonempty subset of a normal-coset residual, then its concept closure
is exactly that residual.
-/
theorem normalCoset_nonempty_subset_generates_residual
    (hN : NormalSubgroupSet G N) (s a b : G)
    (U : Set G)
    (hne : ∃ x : G, x ∈ U)
    (hU : U ⊆ TwoSidedResidual (LeftCosetSet N s) a b) :
    ConceptClosure (LeftCosetSet N s) U =
      TwoSidedResidual (LeftCosetSet N s) a b := by
  exact normalCoset_uniformAdequacyOn_residual hN s a b U hne hU

/--
Singleton form.

Every point of a normal-coset residual generates the whole residual by concept
closure.
-/
theorem normalCoset_singleton_generates_residual
    (hN : NormalSubgroupSet G N) (s a b ρ : G)
    (hρ : ρ ∈ TwoSidedResidual (LeftCosetSet N s) a b) :
    ConceptClosure (LeftCosetSet N s) ({ρ} : Set G) =
      TwoSidedResidual (LeftCosetSet N s) a b := by
  have hU :
      ({ρ} : Set G) ⊆ TwoSidedResidual (LeftCosetSet N s) a b := by
    intro x hx
    have hx_eq : x = ρ := by
      simpa using hx
    simpa [hx_eq] using hρ
  exact normalCoset_nonempty_subset_generates_residual
    hN s a b ({ρ} : Set G) ⟨ρ, by simp⟩ hU

/--
Package theorem for paper use.
-/
theorem normalCoset_uniformAdequacy_package
    (hN : NormalSubgroupSet G N) (s a b : G) :
    SingleObservedSyntacticBlockOn
      (LeftCosetSet N s)
      (TwoSidedResidual (LeftCosetSet N s) a b)
    ∧
    UniformAdequacyOn
      (LeftCosetSet N s)
      (TwoSidedResidual (LeftCosetSet N s) a b) := by
  exact ⟨normalCoset_residual_singleBlockOn hN s a b,
    normalCoset_uniformAdequacyOn_residual hN s a b⟩

end NormalCosetAdequacyCorollaries
end LeanCfgProject
