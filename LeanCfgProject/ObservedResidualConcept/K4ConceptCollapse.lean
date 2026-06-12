import LeanCfgProject.ObservedResidualConcept.K4AdequacyStrictness
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject
namespace AnbnAdequacy

open K4

/-
K4 concept collapse.

This file records another nontrivial feature of the K4 worked example.

The raw singleton state images {x} and {y} are different as subsets of K4.
However, they induce the same residual concept closure O={x,y}.  Thus the
residual-concept layer both fills the missing frame residual elements and
identifies raw powerset images that belong to the same residual concept.

This version avoids fragile `dsimp` calls and uses explicit singleton
membership equalities.
-/

/-- The singleton a-side and b-side raw images are distinct. -/
theorem raw_singletons_A_B_distinct :
    UA ≠ UB := by
  intro hEq
  have hxA : x ∈ UA := by
    change x = x
    rfl
  have hxB : x ∈ UB := by
    simpa [hEq] using hxA
  change x = y at hxB
  cases hxB

/-- The a-side and b-side frame residuals coincide. -/
theorem residual_A_eq_residual_B :
    TwoSidedResidual Sset e y =
      TwoSidedResidual Sset x e := by
  rw [res_ey, res_xe]

/-- The singleton a-side and b-side raw images have the same concept closure. -/
theorem conceptClosure_UA_eq_UB :
    ConceptClosure Sset UA =
      ConceptClosure Sset UB := by
  rw [cl_UA, cl_UB]

/-- The common concept closure of the two singleton raw images is O. -/
theorem conceptClosure_singletons_eq_O :
    ConceptClosure Sset UA = OSet
      ∧ ConceptClosure Sset UB = OSet := by
  exact ⟨cl_UA, cl_UB⟩

/--
The a-side and b-side raw images are distinct, but their residual concepts are
equal.
-/
theorem distinct_raw_images_same_concept :
    UA ≠ UB
      ∧ ConceptClosure Sset UA =
          ConceptClosure Sset UB := by
  exact ⟨raw_singletons_A_B_distinct, conceptClosure_UA_eq_UB⟩

/--
The two different singleton raw images also have the same frame residual
concept.
-/
theorem singleton_concepts_equal_common_residual_concept :
    ConceptClosure Sset UA =
      ConceptClosure Sset (TwoSidedResidual Sset e y)
    ∧
    ConceptClosure Sset UB =
      ConceptClosure Sset (TwoSidedResidual Sset x e) := by
  constructor
  · symm
    exact adequacy_A
  · symm
    exact adequacy_B

/--
The K4 example simultaneously exhibits:
  1. raw singleton images are distinct;
  2. both are strict subsets of their frame residuals;
  3. both induce the same residual concept.
-/
theorem k4_raw_distinct_strict_but_same_concept :
    UA ≠ UB
    ∧ UA ≠ TwoSidedResidual Sset e y
    ∧ UB ≠ TwoSidedResidual Sset x e
    ∧ ConceptClosure Sset UA =
        ConceptClosure Sset UB := by
  exact ⟨raw_singletons_A_B_distinct,
         raw_A_ne_residual,
         raw_B_ne_residual,
         conceptClosure_UA_eq_UB⟩

/--
The K4 worked example has exactly the intended nontrivial pattern:
singleton raw images are too small and mutually distinct, while residual
concept closure places them in the same O-concept, which is also the concept
of their corresponding frame residuals.
-/
theorem k4_nontrivial_collapse_summary :
    UA ≠ UB
    ∧ UA ≠ TwoSidedResidual Sset e y
    ∧ UB ≠ TwoSidedResidual Sset x e
    ∧ ConceptClosure Sset UA = OSet
    ∧ ConceptClosure Sset UB = OSet
    ∧ ConceptClosure Sset (TwoSidedResidual Sset e y) = OSet
    ∧ ConceptClosure Sset (TwoSidedResidual Sset x e) = OSet := by
  constructor
  · exact raw_singletons_A_B_distinct
  constructor
  · exact raw_A_ne_residual
  constructor
  · exact raw_B_ne_residual
  constructor
  · exact cl_UA
  constructor
  · exact cl_UB
  constructor
  · rw [res_ey, cl_O]
  · rw [res_xe, cl_O]

end AnbnAdequacy
end LeanCfgProject
