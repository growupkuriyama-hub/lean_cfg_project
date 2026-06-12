import LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCore

/-!
# Clark-collapse core for surjective recognizing observations

This file proves the theorem-body core behind the paper's second regular
boundary / Clark-collapse statement.

The paper-level statement says that when an observation is surjective and
recognizing, the observed residual-concept object is not losing any residual
concept information: the concept structure is transported exactly from the
source monoid to the observed monoid.

This file avoids quotient construction and formal languages.  It proves the
abstract monoid-pair theorem needed for that statement:

if `q : W -> Q` is a surjective monoid homomorphism and `S` has exact pullback
`L`, then `q` transports residuals, closures, point concepts, products, the
marked membership object, and the observed syntactic congruence.

This is the Lean-checked core of the Clark-collapse direction used in the
Information-and-Computation version of the paper.
-/

open Set

universe u v

namespace ObservedResidualConcept

variable {W : Type u} {Q : Type v} [Monoid W] [Monoid Q]

/-- A surjective recognizing observation between observed monoid pairs.

Think of `W` as the word monoid or syntactic source monoid, `Q` as the observed
monoid, `L` as the source membership set, and `S` as its observed image. -/
structure SurjectiveRecognizingObservation (L : Set W) (S : Set Q) where
  toFun : W → Q
  map_one : toFun 1 = 1
  map_mul : ∀ x y : W, toFun (x * y) = toFun x * toFun y
  surj : Function.Surjective toFun
  mem_iff : ∀ x : W, toFun x ∈ S ↔ x ∈ L

namespace SurjectiveRecognizingObservation

variable {L : Set W} {S : Set Q} (e : SurjectiveRecognizingObservation L S)

@[simp] theorem map_one_apply : e.toFun 1 = 1 :=
  e.map_one

/-- `toFun` maps triple products to triple products. -/
theorem map_mul3 (a x b : W) :
    e.toFun (a * x * b) = e.toFun a * e.toFun x * e.toFun b := by
  rw [e.map_mul, e.map_mul]

/-- Exact pullback of the marked membership object. -/
theorem preimage_observed_set :
    e.toFun ⁻¹' S = L := by
  ext x
  exact e.mem_iff x

/-- Since the observation is surjective and recognizing, the image of `L` is
exactly `S`. -/
theorem image_observed_set :
    e.toFun '' L = S := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    exact (e.mem_iff x).mpr hx
  · intro hy
    rcases e.surj y with ⟨x, rfl⟩
    exact ⟨x, (e.mem_iff x).mp hy, rfl⟩

/-- Inverse-image form of residual transport. -/
theorem preimage_Res (a b : W) :
    e.toFun ⁻¹' Res S (e.toFun a) (e.toFun b) = Res L a b := by
  ext x
  constructor
  · intro hx
    have hx' : e.toFun (a * x * b) ∈ S := by
      simpa [e.map_mul3 a x b] using hx
    exact (e.mem_iff (a * x * b)).mp hx'
  · intro hx
    have hx' : e.toFun (a * x * b) ∈ S :=
      (e.mem_iff (a * x * b)).mpr hx
    simpa [e.map_mul3 a x b] using hx'

/-- Image form of residual transport. -/
theorem image_Res (a b : W) :
    e.toFun '' Res L a b = Res S (e.toFun a) (e.toFun b) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx' : e.toFun (a * x * b) ∈ S :=
      (e.mem_iff (a * x * b)).mpr hx
    simpa [e.map_mul3 a x b] using hx'
  · intro hy
    rcases e.surj y with ⟨x, rfl⟩
    refine ⟨x, ?_, rfl⟩
    have hy' : e.toFun (a * x * b) ∈ S := by
      simpa [e.map_mul3 a x b] using hy
    exact (e.mem_iff (a * x * b)).mp hy'

/-- Image of explicit subset product. -/
theorem image_mulSet (A B : Set W) :
    e.toFun '' mulSet A B = mulSet (e.toFun '' A) (e.toFun '' B) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases hw with ⟨a, ha, b, hb, hmul⟩
    subst hmul
    refine ⟨e.toFun a, ⟨a, ha, rfl⟩, e.toFun b, ⟨b, hb, rfl⟩, ?_⟩
    exact (e.map_mul a b).symm
  · intro hz
    rcases hz with ⟨fa, hfa, fb, hfb, hmul⟩
    rcases hfa with ⟨a, ha, rfl⟩
    rcases hfb with ⟨b, hb, rfl⟩
    refine ⟨a * b, ?_, ?_⟩
    · exact ⟨a, ha, b, hb, rfl⟩
    · exact Eq.trans (e.map_mul a b) hmul

/-- Closure transport along a surjective recognizing observation. -/
theorem image_cl (U : Set W) :
    e.toFun '' cl L U = cl S (e.toFun '' U) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [cl, Extent] at hx ⊢
    intro p hp
    rcases e.surj p.1 with ⟨a, rfl⟩
    rcases e.surj p.2 with ⟨b, rfl⟩
    have hIntent : (a, b) ∈ Intent L U := by
      intro u hu
      have ht : e.toFun a * e.toFun u * e.toFun b ∈ S :=
        hp (e.toFun u) ⟨u, hu, rfl⟩
      have ht' : e.toFun (a * u * b) ∈ S := by
        simpa [e.map_mul3 a u b] using ht
      exact (e.mem_iff (a * u * b)).mp ht'
    have hs : a * x * b ∈ L := hx (a, b) hIntent
    have ht : e.toFun (a * x * b) ∈ S :=
      (e.mem_iff (a * x * b)).mpr hs
    simpa [e.map_mul3 a x b] using ht
  · intro hy
    rcases e.surj y with ⟨x, rfl⟩
    refine ⟨x, ?_, rfl⟩
    rw [cl, Extent] at hy ⊢
    intro p hp
    have hIntent : (e.toFun p.1, e.toFun p.2) ∈ Intent S (e.toFun '' U) := by
      intro z hz
      rcases hz with ⟨u, hu, rfl⟩
      have hs : p.1 * u * p.2 ∈ L := hp u hu
      have ht : e.toFun (p.1 * u * p.2) ∈ S :=
        (e.mem_iff (p.1 * u * p.2)).mpr hs
      simpa [e.map_mul3 p.1 u p.2] using ht
    have ht : e.toFun p.1 * e.toFun x * e.toFun p.2 ∈ S :=
      hy (e.toFun p.1, e.toFun p.2) hIntent
    have ht' : e.toFun (p.1 * x * p.2) ∈ S := by
      simpa [e.map_mul3 p.1 x p.2] using ht
    exact (e.mem_iff (p.1 * x * p.2)).mp ht'

/-- Point concepts are transported exactly. -/
theorem image_point (x : W) :
    e.toFun '' point L x = point S (e.toFun x) := by
  simpa [point] using e.image_cl ({x} : Set W)

/-- Concept products are transported exactly. -/
theorem image_odot (A B : Set W) :
    e.toFun '' odot L A B =
      odot S (e.toFun '' A) (e.toFun '' B) := by
  calc
    e.toFun '' odot L A B
        = e.toFun '' cl L (mulSet A B) := rfl
    _ = cl S (e.toFun '' mulSet A B) := e.image_cl (mulSet A B)
    _ = cl S (mulSet (e.toFun '' A) (e.toFun '' B)) := by
          rw [e.image_mulSet A B]
    _ = odot S (e.toFun '' A) (e.toFun '' B) := rfl

/-- Observed syntactic equivalence is preserved and reflected by a surjective
recognizing observation. -/
theorem approx_iff (x y : W) :
    Approx L x y ↔ Approx S (e.toFun x) (e.toFun y) := by
  constructor
  · intro h a₂ b₂
    rcases e.surj a₂ with ⟨a, rfl⟩
    rcases e.surj b₂ with ⟨b, rfl⟩
    constructor
    · intro hx₂
      have hx₂' : e.toFun (a * x * b) ∈ S := by
        simpa [e.map_mul3 a x b] using hx₂
      have hx₁ : a * x * b ∈ L :=
        (e.mem_iff (a * x * b)).mp hx₂'
      have hy₁ : a * y * b ∈ L :=
        (h a b).mp hx₁
      have hy₂ : e.toFun (a * y * b) ∈ S :=
        (e.mem_iff (a * y * b)).mpr hy₁
      simpa [e.map_mul3 a y b] using hy₂
    · intro hy₂
      have hy₂' : e.toFun (a * y * b) ∈ S := by
        simpa [e.map_mul3 a y b] using hy₂
      have hy₁ : a * y * b ∈ L :=
        (e.mem_iff (a * y * b)).mp hy₂'
      have hx₁ : a * x * b ∈ L :=
        (h a b).mpr hy₁
      have hx₂ : e.toFun (a * x * b) ∈ S :=
        (e.mem_iff (a * x * b)).mpr hx₁
      simpa [e.map_mul3 a x b] using hx₂
  · intro h a b
    constructor
    · intro hx₁
      have hx₂ : e.toFun (a * x * b) ∈ S :=
        (e.mem_iff (a * x * b)).mpr hx₁
      have hx₂' : e.toFun a * e.toFun x * e.toFun b ∈ S := by
        simpa [e.map_mul3 a x b] using hx₂
      have hy₂ : e.toFun a * e.toFun y * e.toFun b ∈ S :=
        (h (e.toFun a) (e.toFun b)).mp hx₂'
      have hy₂' : e.toFun (a * y * b) ∈ S := by
        simpa [e.map_mul3 a y b] using hy₂
      exact (e.mem_iff (a * y * b)).mp hy₂'
    · intro hy₁
      have hy₂ : e.toFun (a * y * b) ∈ S :=
        (e.mem_iff (a * y * b)).mpr hy₁
      have hy₂' : e.toFun a * e.toFun y * e.toFun b ∈ S := by
        simpa [e.map_mul3 a y b] using hy₂
      have hx₂ : e.toFun a * e.toFun x * e.toFun b ∈ S :=
        (h (e.toFun a) (e.toFun b)).mpr hy₂'
      have hx₂' : e.toFun (a * x * b) ∈ S := by
        simpa [e.map_mul3 a x b] using hx₂
      exact (e.mem_iff (a * x * b)).mp hx₂'

/-- Paper-facing Clark-collapse core package. -/
theorem clark_collapse_core_package (x y : W) (A B U : Set W) :
    e.toFun '' L = S
      ∧ e.toFun '' point L x = point S (e.toFun x)
      ∧ e.toFun '' cl L U = cl S (e.toFun '' U)
      ∧ e.toFun '' odot L A B =
          odot S (e.toFun '' A) (e.toFun '' B)
      ∧ (Approx L x y ↔ Approx S (e.toFun x) (e.toFun y)) := by
  exact ⟨e.image_observed_set,
    e.image_point x,
    e.image_cl U,
    e.image_odot A B,
    e.approx_iff x y⟩

end SurjectiveRecognizingObservation

end ObservedResidualConcept
