import Mathlib

/-!
# Observed residual concept quantales: point map and residuals

This file is intended as a relatively standalone Lean core for the paper section
on observed residual concept quantales.

It formalizes the following paper-level ingredients:

* two-sided residuals `Res`
* the Galois closure `cl`
* closed residuals
* the nucleus-style product inclusion
* the concept product `odot`
* the point concept map `point`
* `point x ⊙ point y = point (x*y)`
* kernel of the point map is the observed syntactic congruence `Approx`
* closed-form left/right residuals against a closed extent
* residuation adjunctions for `odot`
* residuals as divisions of the membership object `S`

The file avoids quotient-type bundling on purpose: it is the algebraic core on
which the classification and Clark-collapse modules can be layered.
-/

open Set

universe u

namespace ObservedResidualConcept

variable {Q : Type u} [Monoid Q]

/-- Two-sided observed residual selected by the frame `(a,b)`. -/
def Res (S : Set Q) (a b : Q) : Set Q :=
  {g | a * g * b ∈ S}

/-- The intent of a set of observed middle values. -/
def Intent (S : Set Q) (U : Set Q) : Set (Q × Q) :=
  {p | ∀ g ∈ U, p.1 * g * p.2 ∈ S}

/-- The extent selected by a set of frames. -/
def Extent (S : Set Q) (K : Set (Q × Q)) : Set Q :=
  {g | ∀ p ∈ K, p.1 * g * p.2 ∈ S}

/-- The two-sided Galois closure. -/
def cl (S : Set Q) (U : Set Q) : Set Q :=
  Extent S (Intent S U)

/-- Closed extents for the observed incidence. -/
def Closed (S : Set Q) (U : Set Q) : Prop :=
  cl S U = U

/-- Point concept. -/
def point (S : Set Q) (g : Q) : Set Q :=
  cl S ({g} : Set Q)

/-- Set multiplication, kept explicit to avoid instance conflicts. -/
def mulSet (A B : Set Q) : Set Q :=
  {z | ∃ a ∈ A, ∃ b ∈ B, a * b = z}

/-- Concept product. -/
def odot (S : Set Q) (A B : Set Q) : Set Q :=
  cl S (mulSet A B)

/-- Observed syntactic congruence on the observed monoid. -/
def Approx (S : Set Q) (x y : Q) : Prop :=
  ∀ a b : Q, a * x * b ∈ S ↔ a * y * b ∈ S

/-- Paper notation: `V \ W = {g | Vg ⊆ W}`. -/
def ldiv (V W : Set Q) : Set Q :=
  {g | ∀ v ∈ V, v * g ∈ W}

/-- Paper notation: `W / V = {g | gV ⊆ W}`. -/
def rdiv (W V : Set Q) : Set Q :=
  {g | ∀ v ∈ V, g * v ∈ W}

@[simp] theorem mem_Res {S : Set Q} {a b g : Q} :
    g ∈ Res S a b ↔ a * g * b ∈ S := Iff.rfl

@[simp] theorem mem_Intent {S U : Set Q} {p : Q × Q} :
    p ∈ Intent S U ↔ ∀ g ∈ U, p.1 * g * p.2 ∈ S := Iff.rfl

@[simp] theorem mem_Extent {S : Set Q} {K : Set (Q × Q)} {g : Q} :
    g ∈ Extent S K ↔ ∀ p ∈ K, p.1 * g * p.2 ∈ S := Iff.rfl

@[simp] theorem mem_cl {S U : Set Q} {g : Q} :
    g ∈ cl S U ↔ ∀ p ∈ Intent S U, p.1 * g * p.2 ∈ S := Iff.rfl

@[simp] theorem mem_mulSet {A B : Set Q} {z : Q} :
    z ∈ mulSet A B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = z := Iff.rfl

@[simp] theorem mem_point {S : Set Q} {x g : Q} :
    g ∈ point S x ↔ g ∈ cl S ({x} : Set Q) := Iff.rfl

@[simp] theorem mem_ldiv {V W : Set Q} {g : Q} :
    g ∈ ldiv V W ↔ ∀ v ∈ V, v * g ∈ W := Iff.rfl

@[simp] theorem mem_rdiv {W V : Set Q} {g : Q} :
    g ∈ rdiv W V ↔ ∀ v ∈ V, g * v ∈ W := Iff.rfl

/-- Extensivity of the Galois closure. -/
theorem subset_cl (S U : Set Q) : U ⊆ cl S U := by
  intro g hg
  rw [cl, Extent]
  intro p hp
  exact hp g hg

/-- Monotonicity of the Galois closure. -/
theorem cl_mono {S U V : Set Q} (hUV : U ⊆ V) :
    cl S U ⊆ cl S V := by
  intro g hg
  rw [cl, Extent] at hg ⊢
  intro p hp
  apply hg p
  intro x hx
  exact hp x (hUV hx)

/-- The intent is unchanged by closing. -/
theorem intent_cl_eq_intent (S U : Set Q) :
    Intent S (cl S U) = Intent S U := by
  ext p
  constructor
  · intro hp x hx
    exact hp x (subset_cl S U hx)
  · intro hp x hx
    exact hx p hp

/-- Idempotence of the Galois closure. -/
theorem cl_idem (S U : Set Q) :
    cl S (cl S U) = cl S U := by
  apply Set.Subset.antisymm
  · intro g hg
    rw [cl, Extent] at hg ⊢
    intro p hp
    exact hg p ((intent_cl_eq_intent S U).2 hp)
  · exact subset_cl S (cl S U)

/-- Closed membership may be tested by all accepting frames. -/
theorem mem_closed_iff {S W : Set Q} (hW : Closed S W) {g : Q} :
    g ∈ W ↔ ∀ p ∈ Intent S W, p.1 * g * p.2 ∈ S := by
  constructor
  · intro hg
    rw [← hW] at hg
    exact hg
  · intro hg
    rw [← hW]
    exact hg

/-- Every frame residual is closed. -/
theorem Res_closed (S : Set Q) (a b : Q) :
    Closed S (Res S a b) := by
  apply Set.Subset.antisymm
  · intro g hg
    rw [cl, Extent] at hg
    exact hg (a, b) (by
      intro x hx
      simpa [Res] using hx)
  · exact subset_cl S (Res S a b)

/-- The membership object `S` is the residual of the unit frame. -/
theorem Res_one_one_eq (S : Set Q) :
    Res S 1 1 = S := by
  ext g
  simp [Res]

/-- The membership object `S` is closed. -/
theorem S_closed (S : Set Q) : Closed S S := by
  simpa [Res_one_one_eq (S := S)] using Res_closed S 1 1

/-- Singleton product computes to singleton product. -/
theorem mulSet_singleton_singleton (x y : Q) :
    mulSet ({x} : Set Q) ({y} : Set Q) = ({x * y} : Set Q) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨a, ha, b, hb, hmul⟩
    simp at ha hb
    subst a
    subst b
    simpa using hmul
  · intro hz
    simp at hz
    subst z
    exact ⟨x, by simp, y, by simp, rfl⟩

/-- Monotonicity of explicit set multiplication. -/
theorem mulSet_mono {A A' B B' : Set Q}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    mulSet A B ⊆ mulSet A' B' := by
  intro z hz
  rcases hz with ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, hA ha, b, hB hb, rfl⟩

/-- The closure is a nucleus: closed products are included in the closure of products. -/
theorem mul_cl_subset_cl_mul (S A B : Set Q) :
    mulSet (cl S A) (cl S B) ⊆ cl S (mulSet A B) := by
  intro z hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  rw [cl, Extent] at hx hy ⊢
  intro p hp
  have hxFrame : (p.1, y * p.2) ∈ Intent S A := by
    intro a ha
    have hyFrame : (p.1 * a, p.2) ∈ Intent S B := by
      intro b hb
      have hmul : a * b ∈ mulSet A B := by
        exact ⟨a, ha, b, hb, rfl⟩
      have hS := hp (a * b) hmul
      simpa [mul_assoc] using hS
    have hS := hy (p.1 * a, p.2) hyFrame
    simpa [mul_assoc] using hS
  have hS := hx (p.1, y * p.2) hxFrame
  simpa [mul_assoc] using hS

/-- Monotonicity of concept product. -/
theorem odot_mono {S A A' B B' : Set Q}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    odot S A B ⊆ odot S A' B' := by
  exact cl_mono (S := S) (mulSet_mono hA hB)

/-- Point concepts multiply exactly. -/
theorem point_mul (S : Set Q) (x y : Q) :
    odot S (point S x) (point S y) = point S (x * y) := by
  apply Set.Subset.antisymm
  · intro z hz
    have hN :
        mulSet (point S x) (point S y) ⊆ cl S (mulSet ({x} : Set Q) ({y} : Set Q)) := by
      simpa [point] using mul_cl_subset_cl_mul S ({x} : Set Q) ({y} : Set Q)
    have hz' : z ∈ cl S (cl S (mulSet ({x} : Set Q) ({y} : Set Q))) :=
      cl_mono (S := S) hN hz
    have hz'' : z ∈ cl S (mulSet ({x} : Set Q) ({y} : Set Q)) := by
      simpa [cl_idem] using hz'
    simpa [point, mulSet_singleton_singleton] using hz''
  · intro z hz
    have hsub : ({x * y} : Set Q) ⊆ mulSet (point S x) (point S y) := by
      intro t ht
      simp at ht
      subst t
      exact ⟨x, subset_cl S ({x} : Set Q) (by simp),
             y, subset_cl S ({y} : Set Q) (by simp), rfl⟩
    have hz' : z ∈ cl S ({x * y} : Set Q) := by
      simpa [point] using hz
    exact cl_mono (S := S) hsub hz'

/-- Equality of point concepts is exactly the observed syntactic congruence. -/
theorem point_eq_iff_Approx (S : Set Q) (x y : Q) :
    point S x = point S y ↔ Approx S x y := by
  constructor
  · intro h a b
    constructor
    · intro hx
      have hy_in_px : y ∈ point S x := by
        rw [h]
        exact subset_cl S ({y} : Set Q) (by simp)
      have hFrame : (a, b) ∈ Intent S ({x} : Set Q) := by
        intro g hg
        simp at hg
        subst g
        exact hx
      exact hy_in_px (a, b) hFrame
    · intro hy
      have hx_in_py : x ∈ point S y := by
        rw [← h]
        exact subset_cl S ({x} : Set Q) (by simp)
      have hFrame : (a, b) ∈ Intent S ({y} : Set Q) := by
        intro g hg
        simp at hg
        subst g
        exact hy
      exact hx_in_py (a, b) hFrame
  · intro h
    apply Set.Subset.antisymm
    · intro z hz
      rw [point, cl, Extent] at hz ⊢
      intro p hpY
      apply hz p
      intro g hgx
      simp at hgx
      subst g
      exact (h p.1 p.2).mpr (hpY y (by simp))
    · intro z hz
      rw [point, cl, Extent] at hz ⊢
      intro p hpX
      apply hz p
      intro g hgy
      simp at hgy
      subst g
      exact (h p.1 p.2).mp (hpX x (by simp))

/-- Combined point-map theorem: multiplicativity and kernel. -/
theorem point_homomorphism_kernel (S : Set Q) (x y : Q) :
    odot S (point S x) (point S y) = point S (x * y)
      ∧ (point S x = point S y ↔ Approx S x y) := by
  exact ⟨point_mul S x y, point_eq_iff_Approx S x y⟩

/-- Left division against a closed extent, in closed form. -/
theorem mem_ldiv_closed_iff {S V W : Set Q} (hW : Closed S W) {g : Q} :
    g ∈ ldiv V W ↔
      ∀ v ∈ V, ∀ p ∈ Intent S W, (p.1 * v) * g * p.2 ∈ S := by
  constructor
  · intro hg v hv p hp
    have hvg : v * g ∈ W := hg v hv
    have hS := hp (v * g) hvg
    simpa [mul_assoc] using hS
  · intro h v hv
    rw [← hW]
    rw [cl, Extent]
    intro p hp
    have hS := h v hv p hp
    simpa [mul_assoc] using hS

/-- Right division against a closed extent, in closed form. -/
theorem mem_rdiv_closed_iff {S W V : Set Q} (hW : Closed S W) {g : Q} :
    g ∈ rdiv W V ↔
      ∀ v ∈ V, ∀ p ∈ Intent S W, p.1 * g * (v * p.2) ∈ S := by
  constructor
  · intro hg v hv p hp
    have hgv : g * v ∈ W := hg v hv
    have hS := hp (g * v) hgv
    simpa [mul_assoc] using hS
  · intro h v hv
    rw [← hW]
    rw [cl, Extent]
    intro p hp
    have hS := h v hv p hp
    simpa [mul_assoc] using hS

/-- Residuation: `X ⊙ V ≤ W` iff `X ≤ W / V`, for closed `W`. -/
theorem odot_subset_iff_rdiv {S X V W : Set Q} (hW : Closed S W) :
    odot S X V ⊆ W ↔ X ⊆ rdiv W V := by
  constructor
  · intro h x hx v hv
    apply h
    exact subset_cl S (mulSet X V) ⟨x, hx, v, hv, rfl⟩
  · intro h z hz
    rw [← hW]
    apply cl_mono (S := S) ?_ hz
    intro t ht
    rcases ht with ⟨x, hx, v, hv, rfl⟩
    exact h hx v hv

/-- Residuation: `V ⊙ X ≤ W` iff `X ≤ V \ W`, for closed `W`. -/
theorem odot_subset_iff_ldiv {S V X W : Set Q} (hW : Closed S W) :
    odot S V X ⊆ W ↔ X ⊆ ldiv V W := by
  constructor
  · intro h x hx v hv
    apply h
    exact subset_cl S (mulSet V X) ⟨v, hv, x, hx, rfl⟩
  · intro h z hz
    rw [← hW]
    apply cl_mono (S := S) ?_ hz
    intro t ht
    rcases ht with ⟨v, hv, x, hx, rfl⟩
    exact h hx v hv

/-- Frame residuals are singleton divisions of `S`. -/
theorem Res_eq_singleton_division (S : Set Q) (a b : Q) :
    Res S a b = ldiv ({a} : Set Q) (rdiv S ({b} : Set Q)) := by
  ext g
  constructor
  · intro hg v hv w hw
    simp at hv hw
    subst v
    subst w
    simpa [Res, mul_assoc] using hg
  · intro h
    have hS := h a (by simp) b (by simp)
    simpa [Res, mul_assoc] using hS

/--
Frame residuals are also divisions by point concepts.

This is the stronger paper statement:
`Res_S(a,b) = point(a) \ S / point(b)`.
-/
theorem Res_eq_point_division (S : Set Q) (a b : Q) :
    Res S a b = ldiv (point S a) (rdiv S (point S b)) := by
  ext g
  constructor
  · intro hg δ hδ ε hε
    have hδ' : δ * g * b ∈ S := by
      have hFrame : (1, g * b) ∈ Intent S ({a} : Set Q) := by
        intro x hx
        simp at hx
        subst x
        simpa [Res, mul_assoc] using hg
      have hS := hδ (1, g * b) hFrame
      simpa [mul_assoc] using hS
    have hFrameB : (δ * g, 1) ∈ Intent S ({b} : Set Q) := by
      intro x hx
      simp at hx
      subst x
      simpa [mul_assoc] using hδ'
    have hS := hε (δ * g, 1) hFrameB
    simpa [mul_assoc] using hS
  · intro h
    have ha : a ∈ point S a := subset_cl S ({a} : Set Q) (by simp)
    have hb : b ∈ point S b := subset_cl S ({b} : Set Q) (by simp)
    have hS := h a ha b hb
    simpa [Res, mul_assoc] using hS

/-- `Approx` is reflexive. -/
theorem Approx_refl (S : Set Q) (x : Q) : Approx S x x := by
  intro a b
  rfl

/-- `Approx` is symmetric. -/
theorem Approx_symm {S : Set Q} {x y : Q} (h : Approx S x y) :
    Approx S y x := by
  intro a b
  exact (h a b).symm

/-- `Approx` is transitive. -/
theorem Approx_trans {S : Set Q} {x y z : Q}
    (hxy : Approx S x y) (hyz : Approx S y z) :
    Approx S x z := by
  intro a b
  exact Iff.trans (hxy a b) (hyz a b)

/-- Left compatibility of `Approx`. -/
theorem Approx_mul_left {S : Set Q} {x y : Q} (h : Approx S x y) (u : Q) :
    Approx S (u * x) (u * y) := by
  intro a b
  simpa [mul_assoc] using h (a * u) b

/-- Right compatibility of `Approx`. -/
theorem Approx_mul_right {S : Set Q} {x y : Q} (h : Approx S x y) (u : Q) :
    Approx S (x * u) (y * u) := by
  intro a b
  simpa [mul_assoc] using h a (u * b)

/-- Two-sided compatibility of `Approx`. -/
theorem Approx_mul {S : Set Q} {x y u v : Q}
    (hxy : Approx S x y) (huv : Approx S u v) :
    Approx S (x * u) (y * v) := by
  intro a b
  constructor
  · intro hS
    have h1 : a * (y * u) * b ∈ S := by
      have := (hxy a (u * b)).mp
      simpa [mul_assoc] using this (by simpa [mul_assoc] using hS)
    have h2 := (huv (a * y) b).mp
    simpa [mul_assoc] using h2 (by simpa [mul_assoc] using h1)
  · intro hS
    have h1 : a * (x * v) * b ∈ S := by
      have := (hxy a (v * b)).mpr
      simpa [mul_assoc] using this (by simpa [mul_assoc] using hS)
    have h2 := (huv (a * x) b).mpr
    simpa [mul_assoc] using h2 (by simpa [mul_assoc] using h1)

end ObservedResidualConcept
