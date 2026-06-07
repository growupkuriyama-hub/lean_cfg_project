import LeanCfgProject.K4ResidualAdequacyExample

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject
namespace AnbnAdequacy

open K4

/-
K4 adequacy strictness.

This file strengthens the worked K4 adequacy example by recording the
nontriviality of the phenomenon:

  raw state image  ⊊  frame residual,
  but
  concept closure of the state image = concept closure of the frame residual.

Thus the residual-concept closure is genuinely doing work.  The singleton
state images {x} and {y} do not equal their frame residual O={x,y}; nevertheless
their residual concepts coincide with the residual concept determined by the
two-sided frame.
-/

/--
For the a-side singleton state, the raw image is included in the frame
residual but does not cover it.
-/
theorem raw_A_strictly_smaller_than_residual :
    UA ⊆ TwoSidedResidual Sset e y
      ∧ ¬ TwoSidedResidual Sset e y ⊆ UA := by
  constructor
  · exact sound_A
  · intro hcoverRaw
    have hy_res : y ∈ TwoSidedResidual Sset e y := by
      rw [res_ey]
      dsimp [OSet]
      exact Or.inr rfl
    have hy_UA : y ∈ UA := hcoverRaw hy_res
    dsimp [UA] at hy_UA
    cases hy_UA

/--
For the b-side singleton state, the raw image is included in the frame
residual but does not cover it.
-/
theorem raw_B_strictly_smaller_than_residual :
    UB ⊆ TwoSidedResidual Sset x e
      ∧ ¬ TwoSidedResidual Sset x e ⊆ UB := by
  constructor
  · exact sound_B
  · intro hcoverRaw
    have hx_res : x ∈ TwoSidedResidual Sset x e := by
      rw [res_xe]
      dsimp [OSet]
      exact Or.inl rfl
    have hx_UB : x ∈ UB := hcoverRaw hx_res
    dsimp [UB] at hx_UB
    cases hx_UB

/--
The a-side raw image and its frame residual are not equal as sets.
-/
theorem raw_A_ne_residual :
    UA ≠ TwoSidedResidual Sset e y := by
  intro hEq
  have hcoverRaw : TwoSidedResidual Sset e y ⊆ UA := by
    intro g hg
    rw [hEq]
    exact hg
  exact raw_A_strictly_smaller_than_residual.2 hcoverRaw

/--
The b-side raw image and its frame residual are not equal as sets.
-/
theorem raw_B_ne_residual :
    UB ≠ TwoSidedResidual Sset x e := by
  intro hEq
  have hcoverRaw : TwoSidedResidual Sset x e ⊆ UB := by
    intro g hg
    rw [hEq]
    exact hg
  exact raw_B_strictly_smaller_than_residual.2 hcoverRaw

/--
Although the a-side raw image is not equal to the frame residual, their concept
closures are equal.
-/
theorem A_strict_raw_but_adequate_concept :
    UA ≠ TwoSidedResidual Sset e y
      ∧ ConceptClosure Sset (TwoSidedResidual Sset e y) =
          ConceptClosure Sset UA := by
  exact ⟨raw_A_ne_residual, adequacy_A⟩

/--
Although the b-side raw image is not equal to the frame residual, their concept
closures are equal.
-/
theorem B_strict_raw_but_adequate_concept :
    UB ≠ TwoSidedResidual Sset x e
      ∧ ConceptClosure Sset (TwoSidedResidual Sset x e) =
          ConceptClosure Sset UB := by
  exact ⟨raw_B_ne_residual, adequacy_B⟩

/--
The worked K4 example has genuine concept-level adequacy: at least two states
have raw images strictly smaller than their frame residuals, but the corresponding
residual concepts coincide.
-/
theorem k4_adequacy_is_nontrivial :
    (UA ≠ TwoSidedResidual Sset e y
      ∧ ConceptClosure Sset (TwoSidedResidual Sset e y) =
          ConceptClosure Sset UA)
    ∧
    (UB ≠ TwoSidedResidual Sset x e
      ∧ ConceptClosure Sset (TwoSidedResidual Sset x e) =
          ConceptClosure Sset UB) := by
  exact ⟨A_strict_raw_but_adequate_concept,
         B_strict_raw_but_adequate_concept⟩

/--
A compact summary theorem for the K4 example: the bridge is bidirectional at
the residual-concept level, and this bidirectionality is nontrivial for the
singleton a-side and b-side state images.
-/
theorem k4_bidirectional_and_nontrivial :
    ((ConceptClosure Sset (TwoSidedResidual Sset e e) =
        ConceptClosure Sset US)
    ∧ (ConceptClosure Sset (TwoSidedResidual Sset e y) =
        ConceptClosure Sset UA)
    ∧ (ConceptClosure Sset (TwoSidedResidual Sset x e) =
        ConceptClosure Sset UB)
    ∧ (ConceptClosure Sset (TwoSidedResidual Sset x e) =
        ConceptClosure Sset UT))
    ∧
    ((UA ≠ TwoSidedResidual Sset e y)
      ∧ (UB ≠ TwoSidedResidual Sset x e)) := by
  exact ⟨k4_bridge_bidirectional,
         ⟨raw_A_ne_residual, raw_B_ne_residual⟩⟩

end AnbnAdequacy
end LeanCfgProject
