import LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCore

/-!
# Cut adequacy core

This file proves the Lean-checked set-theoretic core behind the new
"presentation-universal adequacy is cut density" theorem in the paper.

The full paper theorem has two CFG-specific ingredients:

* cut realization: every occupied two-sided cut can be realized by some reduced
  binary CFG presentation;
* substitution soundness: a witnessed state image lies inside the residual
  selected by its witnessed frame.

Those ingredients are intentionally left at the paper level.  This file checks
the algebraic/conceptual heart used once such a cut and a sound state image are
given:

* if an occupied cut point `g` generates the frame residual, then every sound
  state image containing `g` generates the same residual;
* conversely, singleton adequacy at each occupied cut is exactly cut density;
* the statement can be bundled as an abstract theorem over an arbitrary finite
  or infinite set of observed cuts;
* the usual single-`Approx`-block condition implies cut density.

This is the cheap Lean core for Theorem F, while avoiding a heavy formalization
of CFG construction.
-/

open Set

universe u

namespace ObservedResidualConcept

variable {Q : Type u} [Monoid Q]

/-- An observed cut point `(left, middle, right)`.

In the paper this represents a factorization `ell w r ∈ L` observed as
`(q ell, q w, q r)`. -/
structure ObservedCutPoint (Q : Type u) where
  left : Q
  middle : Q
  right : Q

namespace ObservedCutPoint

variable (S : Set Q)

/-- The residual selected by an observed cut's outer frame. -/
def residual (c : ObservedCutPoint Q) : Set Q :=
  Res S c.left c.right

/-- A cut is occupied, in the abstract observed-pair sense, when its middle point
belongs to its selected residual. -/
def Occupied (c : ObservedCutPoint Q) : Prop :=
  c.middle ∈ c.residual S

/-- A cut is point-dense when its singleton point concept is exactly the selected
residual. -/
def PointDense (c : ObservedCutPoint Q) : Prop :=
  point S c.middle = c.residual S

/-- A state image is sound for the frame of the cut. -/
def SoundImage (c : ObservedCutPoint Q) (U : Set Q) : Prop :=
  U ⊆ c.residual S

/-- A state image contains the observed middle point of the cut. -/
def ContainsMiddle (c : ObservedCutPoint Q) (U : Set Q) : Prop :=
  c.middle ∈ U

/-- Adequacy of a state image for the cut's frame. -/
def AdequateImage (c : ObservedCutPoint Q) (U : Set Q) : Prop :=
  cl S U = c.residual S

end ObservedCutPoint

open ObservedCutPoint

/-- A set of observed cuts is cut-dense when every occupied cut point generates
its selected residual. -/
def CutDense (S : Set Q) (C : Set (ObservedCutPoint Q)) : Prop :=
  ∀ c ∈ C, c.PointDense S

/-- The set-theoretic core of Theorem F, forward direction.

If a cut point generates its residual, then any sound image containing that
point also generates the residual. -/
theorem cut_dense_point_generates_sound_image
    {S : Set Q} {c : ObservedCutPoint Q} {U : Set Q}
    (hdense : c.PointDense S)
    (hsound : c.SoundImage S U)
    (hcontains : c.ContainsMiddle U) :
    c.AdequateImage S U := by
  apply Set.Subset.antisymm
  · have hcl : cl S U ⊆ cl S (c.residual S) :=
      cl_mono (S := S) hsound
    have hclosed : cl S (c.residual S) = c.residual S :=
      Res_closed S c.left c.right
    rw [hclosed] at hcl
    simpa [ObservedCutPoint.residual] using hcl
  · have hsingleton : ({c.middle} : Set Q) ⊆ U := by
      intro x hx
      simp at hx
      subst x
      exact hcontains
    have hmono : cl S ({c.middle} : Set Q) ⊆ cl S U :=
      cl_mono (S := S) hsingleton
    have hpointSub : point S c.middle ⊆ cl S U := by
      simpa [point] using hmono
    rw [hdense] at hpointSub
    exact hpointSub

/-- A convenient formulation using an explicit cut set. -/
theorem cut_dense_generates_sound_image
    {S : Set Q} {C : Set (ObservedCutPoint Q)} {c : ObservedCutPoint Q} {U : Set Q}
    (hC : CutDense S C) (hc : c ∈ C)
    (hsound : c.SoundImage S U)
    (hcontains : c.ContainsMiddle U) :
    c.AdequateImage S U := by
  exact cut_dense_point_generates_sound_image
    (S := S) (c := c) (U := U) (hC c hc) hsound hcontains

/-- Singleton adequacy is exactly point-density. -/
theorem singleton_adequacy_iff_pointDense
    (S : Set Q) (c : ObservedCutPoint Q) :
    c.AdequateImage S ({c.middle} : Set Q) ↔ c.PointDense S := by
  constructor
  · intro h
    simpa [ObservedCutPoint.AdequateImage, ObservedCutPoint.PointDense,
      ObservedCutPoint.residual, point] using h
  · intro h
    simpa [ObservedCutPoint.AdequateImage, ObservedCutPoint.PointDense,
      ObservedCutPoint.residual, point] using h

/-- Abstract Theorem-F core.

Assuming every declared cut is occupied, cut density is equivalent to universal
adequacy for all sound images containing the cut's middle point. -/
theorem universal_adequacy_iff_cut_density_core
    (S : Set Q) (C : Set (ObservedCutPoint Q))
    (hOcc : ∀ c ∈ C, c.Occupied S) :
    CutDense S C ↔
      ∀ c ∈ C, ∀ U : Set Q,
        c.SoundImage S U →
        c.ContainsMiddle U →
        c.AdequateImage S U := by
  constructor
  · intro hDense c hc U hsound hcontains
    exact cut_dense_generates_sound_image
      (S := S) (C := C) (c := c) (U := U)
      hDense hc hsound hcontains
  · intro hUniversal c hc
    have hsound : c.SoundImage S ({c.middle} : Set Q) := by
      intro x hx
      simp at hx
      subst x
      exact hOcc c hc
    have hcontains : c.ContainsMiddle ({c.middle} : Set Q) := by
      simp [ObservedCutPoint.ContainsMiddle]
    have hAdeq :=
      hUniversal c hc ({c.middle} : Set Q) hsound hcontains
    exact (singleton_adequacy_iff_pointDense S c).mp hAdeq

/-- One-cut version of the abstract Theorem-F core. -/
theorem universal_adequacy_for_one_cut_iff_pointDense
    (S : Set Q) (c : ObservedCutPoint Q)
    (hOcc : c.Occupied S) :
    c.PointDense S ↔
      ∀ U : Set Q,
        c.SoundImage S U →
        c.ContainsMiddle U →
        c.AdequateImage S U := by
  constructor
  · intro hdense U hsound hcontains
    exact cut_dense_point_generates_sound_image
      (S := S) (c := c) (U := U) hdense hsound hcontains
  · intro hUniversal
    have hsound : c.SoundImage S ({c.middle} : Set Q) := by
      intro x hx
      simp at hx
      subst x
      exact hOcc
    have hcontains : c.ContainsMiddle ({c.middle} : Set Q) := by
      simp [ObservedCutPoint.ContainsMiddle]
    have hAdeq := hUniversal ({c.middle} : Set Q) hsound hcontains
    exact (singleton_adequacy_iff_pointDense S c).mp hAdeq

/-- If every element of a residual is observed-syntactically equivalent to the
cut middle, then the cut is point-dense.  This is the Lean core of the
single-block sufficient condition. -/
theorem pointDense_of_residual_single_Approx_block
    {S : Set Q} {c : ObservedCutPoint Q}
    (hOcc : c.Occupied S)
    (hBlock : ∀ x ∈ c.residual S, Approx S x c.middle) :
    c.PointDense S := by
  apply Set.Subset.antisymm
  · have hsingleton : ({c.middle} : Set Q) ⊆ c.residual S := by
      intro x hx
      simp at hx
      subst x
      exact hOcc
    have hcl : cl S ({c.middle} : Set Q) ⊆ cl S (c.residual S) :=
      cl_mono (S := S) hsingleton
    have hclosed : cl S (c.residual S) = c.residual S :=
      Res_closed S c.left c.right
    rw [hclosed] at hcl
    simpa [ObservedCutPoint.PointDense, ObservedCutPoint.residual, point]
      using hcl
  · intro x hx
    have hApprox : Approx S x c.middle := hBlock x hx
    have hPointEq : point S x = point S c.middle :=
      (point_eq_iff_Approx S x c.middle).mpr hApprox
    have hxPoint : x ∈ point S x := by
      exact subset_cl S ({x} : Set Q) (by simp)
    rw [hPointEq] at hxPoint
    exact hxPoint

/-- A cut set whose occupied residuals are single `Approx`-blocks is cut-dense. -/
theorem cutDense_of_residual_single_Approx_blocks
    {S : Set Q} {C : Set (ObservedCutPoint Q)}
    (hOcc : ∀ c ∈ C, c.Occupied S)
    (hBlock : ∀ c ∈ C, ∀ x ∈ c.residual S, Approx S x c.middle) :
    CutDense S C := by
  intro c hc
  exact pointDense_of_residual_single_Approx_block
    (S := S) (c := c) (hOcc c hc) (hBlock c hc)

/-- Paper-facing package for the cut-adequacy core. -/
theorem cut_adequacy_core_package
    (S : Set Q) (C : Set (ObservedCutPoint Q))
    (hOcc : ∀ c ∈ C, c.Occupied S) :
    (CutDense S C ↔
      ∀ c ∈ C, ∀ U : Set Q,
        c.SoundImage S U →
        c.ContainsMiddle U →
        c.AdequateImage S U)
      ∧
    (∀ c ∈ C, (∀ x ∈ c.residual S, Approx S x c.middle) → c.PointDense S) := by
  constructor
  · exact universal_adequacy_iff_cut_density_core S C hOcc
  · intro c hc hBlock
    exact pointDense_of_residual_single_Approx_block
      (S := S) (c := c) (hOcc c hc) hBlock

end ObservedResidualConcept
