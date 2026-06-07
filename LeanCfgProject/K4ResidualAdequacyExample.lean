import LeanCfgProject.FrameAdequacyCriterion

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject
namespace AnbnAdequacy

/-
K4 residual-concept adequacy example.

This file is the first concrete adequacy example, independent of any grammar
carrier definitions.

It models the observation group K4 = (Z/2)^2 used for the language a^n b^n
with q(a)=x and q(b)=y.  The observed start image is D={e,z}; the other coset
is O={x,y}.  The example verifies that some singleton state images are strictly
smaller than their frame residuals at the raw powerset level, but become equal
after residual concept closure.

This v3 avoids `decide` for `ConceptClosure` computations.  Those goals are
proved by explicit finite case analysis and `simp [mulK4]`, because `decide`
can get stuck on classical decidability for arbitrary set membership.
-/

inductive K4 where
  | e | x | y | z
  deriving DecidableEq, Repr

open K4

instance : Fintype K4 where
  elems := {e, x, y, z}
  complete := by
    intro a
    cases a <;> simp

/-- Multiplication in the Klein four group, written multiplicatively. -/
def mulK4 : K4 → K4 → K4
  | e, b => b
  | a, e => a
  | x, x => e
  | y, y => e
  | z, z => e
  | x, y => z
  | y, x => z
  | x, z => y
  | z, x => y
  | y, z => x
  | z, y => x

instance : Mul K4 := ⟨mulK4⟩

attribute [local reducible]
  TwoSidedResidual CommonContexts ElementsOfContexts ConceptClosure

/-- The diagonal subgroup D={e,z}, which is q[{a^n b^n}]. -/
def DSet : Set K4 := fun g => g = e ∨ g = z

/-- The other coset O={x,y}. -/
def OSet : Set K4 := fun g => g = x ∨ g = y

/-- Start image. -/
def Sset : Set K4 := DSet

/-- State image for the start-like state. -/
def US : Set K4 := DSet

/-- Singleton image for an a-side state. -/
def UA : Set K4 := fun g => g = x

/-- Singleton image for a b-side state. -/
def UB : Set K4 := fun g => g = y

/-- State image for the mixed/parity coset. -/
def UT : Set K4 := OSet

/-- Residual at frame (e,e) is D. -/
theorem res_ee :
    TwoSidedResidual Sset e e = DSet := by
  apply Set.ext
  intro g
  cases g <;> simp [TwoSidedResidual, Sset, DSet, mulK4]

/-- Residual at frame (e,y) is O. -/
theorem res_ey :
    TwoSidedResidual Sset e y = OSet := by
  apply Set.ext
  intro g
  cases g <;> simp [TwoSidedResidual, Sset, DSet, OSet, mulK4]

/-- Residual at frame (x,e) is O. -/
theorem res_xe :
    TwoSidedResidual Sset x e = OSet := by
  apply Set.ext
  intro g
  cases g <;> simp [TwoSidedResidual, Sset, DSet, OSet, mulK4]

/-- The context (e,e) is common for D. -/
lemma ctx_ee_common_D :
    (e, e) ∈ CommonContexts Sset DSet := by
  intro gamma hgamma
  cases gamma <;> simp [CommonContexts, Sset, DSet, mulK4] at hgamma ⊢

/-- The context (e,y) is common for {x}. -/
lemma ctx_ey_common_UA :
    (e, y) ∈ CommonContexts Sset UA := by
  intro gamma hgamma
  cases gamma <;> simp [CommonContexts, Sset, DSet, UA, mulK4] at hgamma ⊢

/-- The context (x,e) is common for {y}. -/
lemma ctx_xe_common_UB :
    (x, e) ∈ CommonContexts Sset UB := by
  intro gamma hgamma
  cases gamma <;> simp [CommonContexts, Sset, DSet, UB, mulK4] at hgamma ⊢

/-- The context (e,y) is common for O. -/
lemma ctx_ey_common_O :
    (e, y) ∈ CommonContexts Sset OSet := by
  intro gamma hgamma
  cases gamma <;> simp [CommonContexts, Sset, DSet, OSet, mulK4] at hgamma ⊢

/-- The concept closure of D is D. -/
theorem cl_D :
    ConceptClosure Sset DSet = DSet := by
  apply Set.Subset.antisymm
  · intro g hg
    cases g
    · exact Or.inl rfl
    · have hx := hg (e, e) ctx_ee_common_D
      simp [Sset, DSet, mulK4] at hx
    · have hy := hg (e, e) ctx_ee_common_D
      simp [Sset, DSet, mulK4] at hy
    · exact Or.inr rfl
  · exact subset_conceptClosure Sset DSet

/-- The concept closure of {x} is O. -/
theorem cl_UA :
    ConceptClosure Sset UA = OSet := by
  apply Set.Subset.antisymm
  · intro g hg
    cases g
    · have he := hg (e, y) ctx_ey_common_UA
      simp [Sset, DSet, mulK4] at he
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have hz := hg (e, y) ctx_ey_common_UA
      simp [Sset, DSet, mulK4] at hz
  · intro g hg
    cases hg with
    | inl hx =>
        subst g
        exact subset_conceptClosure Sset UA rfl
    | inr hy =>
        subst g
        intro ab hab
        rcases ab with ⟨a, b⟩
        cases a <;> cases b <;>
          simp [CommonContexts, Sset, DSet, UA, mulK4] at hab ⊢

/-- The concept closure of {y} is O. -/
theorem cl_UB :
    ConceptClosure Sset UB = OSet := by
  apply Set.Subset.antisymm
  · intro g hg
    cases g
    · have he := hg (x, e) ctx_xe_common_UB
      simp [Sset, DSet, mulK4] at he
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have hz := hg (x, e) ctx_xe_common_UB
      simp [Sset, DSet, mulK4] at hz
  · intro g hg
    cases hg with
    | inl hx =>
        subst g
        intro ab hab
        rcases ab with ⟨a, b⟩
        cases a <;> cases b <;>
          simp [CommonContexts, Sset, DSet, UB, mulK4] at hab ⊢
    | inr hy =>
        subst g
        exact subset_conceptClosure Sset UB rfl

/-- The concept closure of O is O. -/
theorem cl_O :
    ConceptClosure Sset OSet = OSet := by
  apply Set.Subset.antisymm
  · intro g hg
    cases g
    · have he := hg (e, y) ctx_ey_common_O
      simp [Sset, DSet, mulK4] at he
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have hz := hg (e, y) ctx_ey_common_O
      simp [Sset, DSet, mulK4] at hz
  · intro g hg
    exact subset_conceptClosure Sset OSet hg

/-- Raw soundness for the start-like state. -/
theorem sound_S :
    US ⊆ TwoSidedResidual Sset e e := by
  rw [res_ee]
  exact subset_rfl

/-- Raw soundness for the singleton a-side state: {x} ⊆ O. -/
theorem sound_A :
    UA ⊆ TwoSidedResidual Sset e y := by
  rw [res_ey]
  intro g hg
  change g = x ∨ g = y
  left
  change g = x at hg
  exact hg

/-- Raw soundness for the singleton b-side state: {y} ⊆ O. -/
theorem sound_B :
    UB ⊆ TwoSidedResidual Sset x e := by
  rw [res_xe]
  intro g hg
  change g = x ∨ g = y
  right
  change g = y at hg
  exact hg

/-- Raw soundness for the O-state. -/
theorem sound_T :
    UT ⊆ TwoSidedResidual Sset x e := by
  rw [res_xe]
  exact subset_rfl

/-- Coverage for the start-like state. -/
theorem cover_S :
    TwoSidedResidual Sset e e ⊆ ConceptClosure Sset US := by
  rw [res_ee, US, cl_D]
  exact subset_rfl

/-- Coverage for the singleton a-side state. -/
theorem cover_A :
    TwoSidedResidual Sset e y ⊆ ConceptClosure Sset UA := by
  rw [res_ey, cl_UA]
  exact subset_rfl

/-- Coverage for the singleton b-side state. -/
theorem cover_B :
    TwoSidedResidual Sset x e ⊆ ConceptClosure Sset UB := by
  rw [res_xe, cl_UB]
  exact subset_rfl

/-- Coverage for the O-state. -/
theorem cover_T :
    TwoSidedResidual Sset x e ⊆ ConceptClosure Sset UT := by
  rw [res_xe, UT, cl_O]
  exact subset_rfl

/--
Adequacy for the start-like state:
the frame residual concept and the state concept coincide.
-/
theorem adequacy_S :
    ConceptClosure Sset (TwoSidedResidual Sset e e) =
      ConceptClosure Sset US :=
  adequacy_of_residual_coverage Sset US
    (TwoSidedResidual Sset e e)
    sound_S cover_S

/--
Adequacy for the singleton a-side state.

This is the nontrivial pattern: raw image {x} is strictly smaller than the
frame residual O, but their concept closures coincide.
-/
theorem adequacy_A :
    ConceptClosure Sset (TwoSidedResidual Sset e y) =
      ConceptClosure Sset UA :=
  adequacy_of_residual_coverage Sset UA
    (TwoSidedResidual Sset e y)
    sound_A cover_A

/--
Adequacy for the singleton b-side state.

Again, raw image {y} is strictly smaller than the frame residual O, but the
concept closures coincide.
-/
theorem adequacy_B :
    ConceptClosure Sset (TwoSidedResidual Sset x e) =
      ConceptClosure Sset UB :=
  adequacy_of_residual_coverage Sset UB
    (TwoSidedResidual Sset x e)
    sound_B cover_B

/-- Adequacy for the O-state. -/
theorem adequacy_T :
    ConceptClosure Sset (TwoSidedResidual Sset x e) =
      ConceptClosure Sset UT :=
  adequacy_of_residual_coverage Sset UT
    (TwoSidedResidual Sset x e)
    sound_T cover_T

/--
The worked K4 bridge is bidirectional at the frame-indexed concept level for
the four displayed state images.
-/
theorem k4_bridge_bidirectional :
    (ConceptClosure Sset (TwoSidedResidual Sset e e) =
      ConceptClosure Sset US)
  ∧ (ConceptClosure Sset (TwoSidedResidual Sset e y) =
      ConceptClosure Sset UA)
  ∧ (ConceptClosure Sset (TwoSidedResidual Sset x e) =
      ConceptClosure Sset UB)
  ∧ (ConceptClosure Sset (TwoSidedResidual Sset x e) =
      ConceptClosure Sset UT) := by
  exact ⟨adequacy_S, adequacy_A, adequacy_B, adequacy_T⟩

end AnbnAdequacy
end LeanCfgProject
