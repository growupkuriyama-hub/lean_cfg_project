import LeanCfgProject.CanonicalPointFrame
import LeanCfgProject.ObservedFrameStructure

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
UniversalFrameModelCore.lean

Core paper-facing package for the canonical reduced frame representation
section. This file verifies the point-frame incidence and point-collapse
components that drive the representation theorem.
-/

variable {Q : Type u} [Mul Q]

/--
The canonical observed frame structure realizes the two-sided incidence
relation through point concepts and frame residuals.
-/
theorem canonicalObservedFrameStructure_represents_incidence
    (S : Set Q) (gamma a b : Q) :
    CanonicalPoint S gamma ⊆
        (canonicalObservedFrameStructure (Q := Q) S).residual a b
      ↔ a * gamma * b ∈ S := by
  simpa [CanonicalPoint, canonicalObservedFrameStructure, FrameResidual]
    using singletonConcept_subset_residual_iff S gamma a b

/--
The point-collapse relation of the canonical representation is the observed
syntactic congruence.
-/
theorem canonicalObservedFrameStructure_pointCollapse
    (S : Set Q) (x y : Q) :
    CanonicalPoint S x = CanonicalPoint S y
      ↔ (canonicalObservedFrameStructure (Q := Q) S).rel x y := by
  simpa [canonicalObservedFrameStructure] using
    canonicalPoint_eq_iff_sameObservedSyntactic S x y

/--
Summary of the two checked pillars for the canonical representation layer.
-/
theorem universalFrameModelCore_summary
    (S : Set Q) :
    (∀ gamma a b : Q,
      CanonicalPoint S gamma ⊆
          (canonicalObservedFrameStructure (Q := Q) S).residual a b
        ↔ a * gamma * b ∈ S)
    ∧
    (∀ x y : Q,
      CanonicalPoint S x = CanonicalPoint S y
        ↔ (canonicalObservedFrameStructure (Q := Q) S).rel x y) := by
  constructor
  · intro gamma a b
    exact canonicalObservedFrameStructure_represents_incidence S gamma a b
  · intro x y
    exact canonicalObservedFrameStructure_pointCollapse S x y

end LeanCfgProject
