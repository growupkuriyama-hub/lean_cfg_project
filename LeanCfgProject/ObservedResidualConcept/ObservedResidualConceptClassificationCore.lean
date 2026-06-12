import LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCore

/-!
# Observed pair isomorphisms and transport of the concept object

This file is the classification-core layer on top of
`ObservedResidualConceptCore`.

It proves the forward direction needed for the paper's observed
Myhill--Nerode classification:

if two observed pairs `(Q₁,S₁)` and `(Q₂,S₂)` are isomorphic as monoid pairs,
then the residual/concept structure is transported exactly.

The checked content includes transport of:

* two-sided residuals;
* two-sided Galois closures;
* point concepts;
* explicit subset product;
* concept product `odot`;
* observed syntactic congruence `Approx`.

This deliberately avoids quotient construction and bundled quantale
isomorphism.  It is the theorem-body layer immediately below those statements.
-/

open Set

universe u v

namespace ObservedResidualConcept

variable {Q₁ : Type u} {Q₂ : Type v} [Monoid Q₁] [Monoid Q₂]

/-- Isomorphism of observed monoid pairs `(Q₁,S₁)` and `(Q₂,S₂)`.

The membership condition is oriented so that `toFun` sends `S₁` exactly to
`S₂`. -/
structure ObservedPairIso (S₁ : Set Q₁) (S₂ : Set Q₂) where
  toFun : Q₁ → Q₂
  invFun : Q₂ → Q₁
  left_inv : ∀ x : Q₁, invFun (toFun x) = x
  right_inv : ∀ y : Q₂, toFun (invFun y) = y
  map_one : toFun 1 = 1
  map_mul : ∀ x y : Q₁, toFun (x * y) = toFun x * toFun y
  inv_map_one : invFun 1 = 1
  inv_map_mul : ∀ x y : Q₂, invFun (x * y) = invFun x * invFun y
  mem_iff : ∀ x : Q₁, toFun x ∈ S₂ ↔ x ∈ S₁

namespace ObservedPairIso

variable {S₁ : Set Q₁} {S₂ : Set Q₂} (e : ObservedPairIso S₁ S₂)

@[simp] theorem left_inv_apply (x : Q₁) : e.invFun (e.toFun x) = x :=
  e.left_inv x

@[simp] theorem right_inv_apply (y : Q₂) : e.toFun (e.invFun y) = y :=
  e.right_inv y

/-- `toFun` maps a triple product to the triple product of images. -/
theorem map_mul3 (a x b : Q₁) :
    e.toFun (a * x * b) = e.toFun a * e.toFun x * e.toFun b := by
  rw [e.map_mul, e.map_mul]
  simp [mul_assoc]

/-- `invFun` maps a triple product to the triple product of inverse images. -/
theorem inv_map_mul3 (a x b : Q₂) :
    e.invFun (a * x * b) = e.invFun a * e.invFun x * e.invFun b := by
  rw [e.inv_map_mul, e.inv_map_mul]
  simp [mul_assoc]

/-- Membership of an image triple is equivalent to membership of the original
triple. -/
theorem toFun_mul3_mem_iff (a x b : Q₁) :
    e.toFun a * e.toFun x * e.toFun b ∈ S₂ ↔ a * x * b ∈ S₁ := by
  have h := e.mem_iff (a * x * b)
  rw [e.map_mul3 a x b] at h
  exact h

/-- Membership of an inverse-image triple is equivalent to membership of the
target triple. -/
theorem invFun_mul3_mem_iff (a x b : Q₂) :
    e.invFun a * e.invFun x * e.invFun b ∈ S₁ ↔ a * x * b ∈ S₂ := by
  have h := e.mem_iff (e.invFun a * e.invFun x * e.invFun b)
  have hmap :
      e.toFun (e.invFun a * e.invFun x * e.invFun b) = a * x * b := by
    rw [e.map_mul3]
    simp
  rw [hmap] at h
  exact h.symm

/-- Inverse-image form of residual transport. -/
theorem preimage_Res (a b : Q₁) :
    e.toFun ⁻¹' Res S₂ (e.toFun a) (e.toFun b) = Res S₁ a b := by
  ext x
  exact e.toFun_mul3_mem_iff a x b

/-- Image form of residual transport. -/
theorem image_Res (a b : Q₁) :
    e.toFun '' Res S₁ a b = Res S₂ (e.toFun a) (e.toFun b) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    exact (e.toFun_mul3_mem_iff a x b).mpr hx
  · intro hy
    refine ⟨e.invFun y, ?_, e.right_inv y⟩
    have hy' : e.toFun a * e.toFun (e.invFun y) * e.toFun b ∈ S₂ := by
      simpa using hy
    exact (e.toFun_mul3_mem_iff a (e.invFun y) b).mp hy'

/-- Image of explicit set product under an observed pair isomorphism. -/
theorem image_mulSet (A B : Set Q₁) :
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

/-- Closure transport under an observed pair isomorphism. -/
theorem image_cl (U : Set Q₁) :
    e.toFun '' cl S₁ U = cl S₂ (e.toFun '' U) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [cl, Extent] at hx ⊢
    intro p hp
    let a : Q₁ := e.invFun p.1
    let b : Q₁ := e.invFun p.2
    have hIntent : (a, b) ∈ Intent S₁ U := by
      intro u hu
      have hTarget : p.1 * e.toFun u * p.2 ∈ S₂ :=
        hp (e.toFun u) ⟨u, hu, rfl⟩
      have hTarget' : e.toFun a * e.toFun u * e.toFun b ∈ S₂ := by
        simpa [a, b] using hTarget
      exact (e.toFun_mul3_mem_iff a u b).mp hTarget'
    have hSource : a * x * b ∈ S₁ := hx (a, b) hIntent
    have hTarget : e.toFun a * e.toFun x * e.toFun b ∈ S₂ :=
      (e.toFun_mul3_mem_iff a x b).mpr hSource
    simpa [a, b] using hTarget
  · intro hy
    refine ⟨e.invFun y, ?_, e.right_inv y⟩
    rw [cl, Extent] at hy ⊢
    intro p hp
    have hIntent : (e.toFun p.1, e.toFun p.2) ∈ Intent S₂ (e.toFun '' U) := by
      intro z hz
      rcases hz with ⟨u, hu, rfl⟩
      exact (e.toFun_mul3_mem_iff p.1 u p.2).mpr (hp u hu)
    have hTarget : e.toFun p.1 * y * e.toFun p.2 ∈ S₂ :=
      hy (e.toFun p.1, e.toFun p.2) hIntent
    have hTarget' :
        e.toFun p.1 * e.toFun (e.invFun y) * e.toFun p.2 ∈ S₂ := by
      simpa using hTarget
    exact (e.toFun_mul3_mem_iff p.1 (e.invFun y) p.2).mp hTarget'

/-- Point concepts are transported by observed pair isomorphisms. -/
theorem image_point (x : Q₁) :
    e.toFun '' point S₁ x = point S₂ (e.toFun x) := by
  simpa [point] using e.image_cl ({x} : Set Q₁)

/-- Concept products are transported by observed pair isomorphisms. -/
theorem image_odot (A B : Set Q₁) :
    e.toFun '' odot S₁ A B =
      odot S₂ (e.toFun '' A) (e.toFun '' B) := by
  calc
    e.toFun '' odot S₁ A B
        = e.toFun '' cl S₁ (mulSet A B) := rfl
    _ = cl S₂ (e.toFun '' mulSet A B) := e.image_cl (mulSet A B)
    _ = cl S₂ (mulSet (e.toFun '' A) (e.toFun '' B)) := by
          rw [e.image_mulSet A B]
    _ = odot S₂ (e.toFun '' A) (e.toFun '' B) := rfl

/-- Observed syntactic congruence is transported by an observed pair
isomorphism. -/
theorem approx_iff (x y : Q₁) :
    Approx S₁ x y ↔ Approx S₂ (e.toFun x) (e.toFun y) := by
  constructor
  · intro h a₂ b₂
    constructor
    · intro hx₂
      have hx₂' :
          e.toFun (e.invFun a₂) * e.toFun x * e.toFun (e.invFun b₂) ∈ S₂ := by
        simpa using hx₂
      have hx₁ : e.invFun a₂ * x * e.invFun b₂ ∈ S₁ :=
        (e.toFun_mul3_mem_iff (e.invFun a₂) x (e.invFun b₂)).mp hx₂'
      have hy₁ : e.invFun a₂ * y * e.invFun b₂ ∈ S₁ :=
        (h (e.invFun a₂) (e.invFun b₂)).mp hx₁
      have hy₂ :
          e.toFun (e.invFun a₂) * e.toFun y * e.toFun (e.invFun b₂) ∈ S₂ :=
        (e.toFun_mul3_mem_iff (e.invFun a₂) y (e.invFun b₂)).mpr hy₁
      simpa using hy₂
    · intro hy₂
      have hy₂' :
          e.toFun (e.invFun a₂) * e.toFun y * e.toFun (e.invFun b₂) ∈ S₂ := by
        simpa using hy₂
      have hy₁ : e.invFun a₂ * y * e.invFun b₂ ∈ S₁ :=
        (e.toFun_mul3_mem_iff (e.invFun a₂) y (e.invFun b₂)).mp hy₂'
      have hx₁ : e.invFun a₂ * x * e.invFun b₂ ∈ S₁ :=
        (h (e.invFun a₂) (e.invFun b₂)).mpr hy₁
      have hx₂ :
          e.toFun (e.invFun a₂) * e.toFun x * e.toFun (e.invFun b₂) ∈ S₂ :=
        (e.toFun_mul3_mem_iff (e.invFun a₂) x (e.invFun b₂)).mpr hx₁
      simpa using hx₂
  · intro h a₁ b₁
    constructor
    · intro hx₁
      have hx₂ : e.toFun a₁ * e.toFun x * e.toFun b₁ ∈ S₂ :=
        (e.toFun_mul3_mem_iff a₁ x b₁).mpr hx₁
      have hy₂ : e.toFun a₁ * e.toFun y * e.toFun b₁ ∈ S₂ :=
        (h (e.toFun a₁) (e.toFun b₁)).mp hx₂
      exact (e.toFun_mul3_mem_iff a₁ y b₁).mp hy₂
    · intro hy₁
      have hy₂ : e.toFun a₁ * e.toFun y * e.toFun b₁ ∈ S₂ :=
        (e.toFun_mul3_mem_iff a₁ y b₁).mpr hy₁
      have hx₂ : e.toFun a₁ * e.toFun x * e.toFun b₁ ∈ S₂ :=
        (h (e.toFun a₁) (e.toFun b₁)).mpr hy₂
      exact (e.toFun_mul3_mem_iff a₁ x b₁).mp hx₂

/-- Paper-facing transport package for the forward direction of observed
classification. -/
theorem transport_package (x y : Q₁) (A B U : Set Q₁) :
    e.toFun '' point S₁ x = point S₂ (e.toFun x)
      ∧ e.toFun '' cl S₁ U = cl S₂ (e.toFun '' U)
      ∧ e.toFun '' odot S₁ A B =
          odot S₂ (e.toFun '' A) (e.toFun '' B)
      ∧ (Approx S₁ x y ↔ Approx S₂ (e.toFun x) (e.toFun y)) := by
  exact ⟨e.image_point x, e.image_cl U, e.image_odot A B, e.approx_iff x y⟩

end ObservedPairIso

end ObservedResidualConcept
