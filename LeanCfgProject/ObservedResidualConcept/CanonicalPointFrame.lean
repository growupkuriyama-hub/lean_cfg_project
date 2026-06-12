import LeanCfgProject.SingletonClosureIncidence

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
CanonicalPointFrame.lean

Point/frame representation lemmas for the observed syntactic concept object.
-/

variable {Q : Type u} [Mul Q]

/-- Canonical point interpretation. -/
def CanonicalPoint (S : Set Q) (gamma : Q) : Set Q :=
  SingletonConcept S gamma

/-- Canonical frame interpretation. -/
def CanonicalFrame (S : Set Q) (a b : Q) : Set Q :=
  TwoSidedResidual S a b

/--
Canonical point-frame incidence is exactly the two-sided observed membership
test.
-/
theorem canonicalPoint_subset_frame_iff
    (S : Set Q) (gamma a b : Q) :
    CanonicalPoint S gamma ⊆ CanonicalFrame S a b
      ↔ a * gamma * b ∈ S := by
  simpa [CanonicalPoint, CanonicalFrame] using
    singletonConcept_subset_residual_iff S gamma a b

/--
Equality of canonical point concepts is the same as observed syntactic
equivalence.
-/
theorem canonicalPoint_eq_iff_sameObservedSyntactic
    (S : Set Q) (x y : Q) :
    CanonicalPoint S x = CanonicalPoint S y
      ↔ SameObservedSyntactic S x y := by
  constructor
  · intro hEq
    intro a b
    constructor
    · intro hx
      have hxsub :
          CanonicalPoint S x ⊆ CanonicalFrame S a b := by
        exact (canonicalPoint_subset_frame_iff S x a b).2 hx
      have hysub :
          CanonicalPoint S y ⊆ CanonicalFrame S a b := by
        intro eta heta
        have hetaX : eta ∈ CanonicalPoint S x := by
          rw [hEq]
          exact heta
        exact hxsub hetaX
      exact (canonicalPoint_subset_frame_iff S y a b).1 hysub
    · intro hy
      have hysub :
          CanonicalPoint S y ⊆ CanonicalFrame S a b := by
        exact (canonicalPoint_subset_frame_iff S y a b).2 hy
      have hxsub :
          CanonicalPoint S x ⊆ CanonicalFrame S a b := by
        intro eta heta
        have hetaY : eta ∈ CanonicalPoint S y := by
          rw [← hEq]
          exact heta
        exact hysub hetaY
      exact (canonicalPoint_subset_frame_iff S x a b).1 hxsub
  · intro hxy
    apply Set.ext
    intro gamma
    constructor
    · intro hgamma ab hab
      have habx : ab ∈ CommonContexts S ({x} : Set Q) := by
        intro z hz
        have hz' : z = x := by
          simpa using hz
        rw [hz']
        have hymem : ab.1 * y * ab.2 ∈ S := by
          exact hab y (by simp)
        exact (hxy ab.1 ab.2).mpr hymem
      exact hgamma ab habx
    · intro hgamma ab hab
      have haby : ab ∈ CommonContexts S ({y} : Set Q) := by
        intro z hz
        have hz' : z = y := by
          simpa using hz
        rw [hz']
        have hxmem : ab.1 * x * ab.2 ∈ S := by
          exact hab x (by simp)
        exact (hxy ab.1 ab.2).mp hxmem
      exact hgamma ab haby

/--
Observed syntactic equivalence identifies exactly the canonical point concepts.
-/
theorem sameObservedSyntactic_iff_canonicalPoint_eq
    (S : Set Q) (x y : Q) :
    SameObservedSyntactic S x y
      ↔ CanonicalPoint S x = CanonicalPoint S y := by
  exact (canonicalPoint_eq_iff_sameObservedSyntactic S x y).symm

end LeanCfgProject
