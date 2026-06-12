import LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCore

/-!
# Pointed boundary core

This file proves the Lean-checked core of the paper's first regular-boundary
statement.

The paper's word-level statement says that the pointed syntactic stabilization
of a finite `h`-typed two-sided observation collapses to ordinary syntactic
equivalence intersected with the kernel of `h`.

This file proves the abstract monoid version.  We work in an arbitrary source
monoid `W` with an observed language/membership set `L : Set W` and a monoid
observation `h : W -> M`.  We define:

* raw two-sided context observation;
* pointed observation, which also remembers exact membership;
* pointed syntactic observation, obtained by stabilizing under all two-sided
  contexts;
* ordinary syntactic equivalence of `L`.

The main theorem is:

`PointedSynObs L h x y ↔ SyntacticEquiv L x y ∧ h x = h y`.

This is precisely the theorem-body core behind the paper's first regular
boundary.  The finite-index / regular-language corollary is intentionally left
to the paper text, since it depends on the usual Myhill--Nerode theorem for
languages over a finite alphabet.
-/

open Set

universe u v

namespace ObservedResidualConcept

variable {W : Type u} {M : Type v} [Monoid W] [Monoid M]

/-- A multiplicative monoid observation. -/
structure MonoidObservation (W : Type u) (M : Type v) [Monoid W] [Monoid M] where
  toFun : W → M
  map_one : toFun 1 = 1
  map_mul : ∀ x y : W, toFun (x * y) = toFun x * toFun y

namespace MonoidObservation

variable (h : MonoidObservation W M)

@[simp] theorem map_one_apply : h.toFun 1 = 1 :=
  h.map_one

/-- Triple-product form of multiplicativity. -/
theorem map_mul3 (a x b : W) :
    h.toFun (a * x * b) = h.toFun a * h.toFun x * h.toFun b := by
  rw [h.map_mul, h.map_mul]

end MonoidObservation

/-- Ordinary two-sided syntactic equivalence of a membership set `L`. -/
def SyntacticEquiv (L : Set W) (x y : W) : Prop :=
  ∀ a b : W, a * x * b ∈ L ↔ a * y * b ∈ L

/-- Kernel equivalence of an observation. -/
def ObservationKernel (h : MonoidObservation W M) (x y : W) : Prop :=
  h.toFun x = h.toFun y

/-- Raw finite two-sided observation used before syntactic stabilization.

For a word/element `u`, this records the observed left and right `h`-types of
contexts that accept `u`. -/
def HTypedContextObservation (L : Set W) (h : MonoidObservation W M) (u : W) :
    Set (M × M) :=
  {p | ∃ a b : W, h.toFun a = p.1 ∧ h.toFun b = p.2 ∧ a * u * b ∈ L}

/-- Raw observation equivalence: same observed value and same observed
two-sided context signature. -/
def RawObsEquiv (L : Set W) (h : MonoidObservation W M) (x y : W) : Prop :=
  h.toFun x = h.toFun y
    ∧ HTypedContextObservation L h x = HTypedContextObservation L h y

/-- Pointed observation also remembers exact membership. -/
def PointedObs (L : Set W) (h : MonoidObservation W M) (x y : W) : Prop :=
  h.toFun x = h.toFun y
    ∧ (x ∈ L ↔ y ∈ L)
    ∧ HTypedContextObservation L h x = HTypedContextObservation L h y

/-- Syntactic stabilization of raw observation. -/
def SynObs (L : Set W) (h : MonoidObservation W M) (x y : W) : Prop :=
  ∀ a b : W, RawObsEquiv L h (a * x * b) (a * y * b)

/-- Syntactic stabilization of pointed observation. -/
def PointedSynObs (L : Set W) (h : MonoidObservation W M) (x y : W) : Prop :=
  ∀ a b : W, PointedObs L h (a * x * b) (a * y * b)

variable {L : Set W} {h : MonoidObservation W M}

/-- The raw context signature is transported by syntactic equivalence. -/
theorem contextObservation_eq_of_syntacticEquiv
    {x y : W} (hsyn : SyntacticEquiv L x y) :
    HTypedContextObservation L h x = HTypedContextObservation L h y := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨a, b, ha, hb, hmem⟩
    refine ⟨a, b, ha, hb, ?_⟩
    exact (hsyn a b).mp hmem
  · intro hp
    rcases hp with ⟨a, b, ha, hb, hmem⟩
    refine ⟨a, b, ha, hb, ?_⟩
    exact (hsyn a b).mpr hmem

/-- Syntactic equivalence is stable under inserting a common two-sided context. -/
theorem syntacticEquiv_context
    {x y : W} (hsyn : SyntacticEquiv L x y) (a b : W) :
    SyntacticEquiv L (a * x * b) (a * y * b) := by
  intro l r
  constructor
  · intro hmem
    have hmem' : (l * a) * x * (b * r) ∈ L := by
      simpa [mul_assoc] using hmem
    have hres : (l * a) * y * (b * r) ∈ L :=
      (hsyn (l * a) (b * r)).mp hmem'
    simpa [mul_assoc] using hres
  · intro hmem
    have hmem' : (l * a) * y * (b * r) ∈ L := by
      simpa [mul_assoc] using hmem
    have hres : (l * a) * x * (b * r) ∈ L :=
      (hsyn (l * a) (b * r)).mpr hmem'
    simpa [mul_assoc] using hres

/-- Observation-kernel equality is stable under inserting a common context. -/
theorem observationKernel_context
    {x y : W} (hxy : h.toFun x = h.toFun y) (a b : W) :
    h.toFun (a * x * b) = h.toFun (a * y * b) := by
  calc
    h.toFun (a * x * b)
        = h.toFun a * h.toFun x * h.toFun b := h.map_mul3 a x b
    _ = h.toFun a * h.toFun y * h.toFun b := by rw [hxy]
    _ = h.toFun (a * y * b) := (h.map_mul3 a y b).symm

/-- Pointed syntactic observation implies ordinary syntactic equivalence. -/
theorem syntacticEquiv_of_pointedSynObs
    {x y : W} (hp : PointedSynObs L h x y) :
    SyntacticEquiv L x y := by
  intro a b
  exact (hp a b).2.1

/-- Pointed syntactic observation implies equality of observed values. -/
theorem observationKernel_of_pointedSynObs
    {x y : W} (hp : PointedSynObs L h x y) :
    h.toFun x = h.toFun y := by
  have hker := (hp 1 1).1
  simpa using hker

/-- Ordinary syntactic equivalence plus observation-kernel equality implies
pointed syntactic observation. -/
theorem pointedSynObs_of_syntacticEquiv_and_kernel
    {x y : W} (hsyn : SyntacticEquiv L x y)
    (hker : h.toFun x = h.toFun y) :
    PointedSynObs L h x y := by
  intro a b
  have hsyn_ab : SyntacticEquiv L (a * x * b) (a * y * b) :=
    syntacticEquiv_context (L := L) (h := h) hsyn a b
  refine ⟨?_, ?_, ?_⟩
  · exact observationKernel_context (h := h) hker a b
  · exact hsyn_ab 1 1
  · exact contextObservation_eq_of_syntacticEquiv (L := L) (h := h) hsyn_ab

/-- First-boundary theorem-body core.

The pointed syntactic stabilization of the finite observed context signature
collapses to ordinary syntactic equivalence intersected with the kernel of the
observation. -/
theorem pointedSynObs_iff_syntacticEquiv_and_kernel
    (L : Set W) (h : MonoidObservation W M) (x y : W) :
    PointedSynObs L h x y ↔
      SyntacticEquiv L x y ∧ h.toFun x = h.toFun y := by
  constructor
  · intro hp
    exact ⟨syntacticEquiv_of_pointedSynObs (L := L) (h := h) hp,
      observationKernel_of_pointedSynObs (L := L) (h := h) hp⟩
  · intro hpair
    exact pointedSynObs_of_syntacticEquiv_and_kernel
      (L := L) (h := h) hpair.1 hpair.2

/-- Equivalent formulation using the named observation-kernel predicate. -/
theorem pointedSynObs_iff_syntacticEquiv_and_observationKernel
    (L : Set W) (h : MonoidObservation W M) (x y : W) :
    PointedSynObs L h x y ↔
      SyntacticEquiv L x y ∧ ObservationKernel h x y := by
  exact pointedSynObs_iff_syntacticEquiv_and_kernel L h x y

/-- The unpointed syntactic observation contains the pointed syntactic
observation after forgetting the membership component. -/
theorem pointedSynObs_implies_synObs
    {x y : W} (hp : PointedSynObs L h x y) :
    SynObs L h x y := by
  intro a b
  exact ⟨(hp a b).1, (hp a b).2.2⟩

/-- Paper-facing first-boundary package. -/
theorem pointed_boundary_core_package
    (L : Set W) (h : MonoidObservation W M) (x y : W) :
    (PointedSynObs L h x y ↔
      SyntacticEquiv L x y ∧ h.toFun x = h.toFun y)
      ∧ (PointedSynObs L h x y → SynObs L h x y) := by
  exact ⟨pointedSynObs_iff_syntacticEquiv_and_kernel L h x y,
    fun hp => pointedSynObs_implies_synObs (L := L) (h := h) hp⟩

end ObservedResidualConcept
