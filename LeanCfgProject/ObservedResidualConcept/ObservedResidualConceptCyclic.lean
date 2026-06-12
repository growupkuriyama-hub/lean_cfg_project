import LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCore

/-!
# Cyclic observed sets and the Girard/phase-collapse core

This file sits on top of `ObservedResidualConceptCore`.

It formalizes the core algebraic part of the paper's cyclic/Girard section:

* cyclicity of the observed membership set `S`;
* one-sided orthogonality `Perp`;
* two-sided closure collapses to double orthogonality under cyclicity;
* left and right divisions by `S` coincide with orthogonality;
* the dualizing equations for closed extents:
    `S / (U \ S) = U` and `(S / U) \ S = U`.

The file intentionally avoids introducing bundled quantale or Girard-quantale
structures.  It proves the theorem-body statements that can later be re-exported
as the paper's cyclic phase-collapse package.
-/

open Set

universe u

namespace ObservedResidualConcept

variable {Q : Type u} [Monoid Q]

/-- The observed membership set is cyclic if membership is invariant under
cyclic exchange of two factors. -/
def CyclicSet (S : Set Q) : Prop :=
  ∀ x y : Q, x * y ∈ S ↔ y * x ∈ S

/-- One-sided orthogonality induced by the observed set `S`. -/
def Perp (S : Set Q) (U : Set Q) : Set Q :=
  {d | ∀ u ∈ U, u * d ∈ S}

/-- The opposite one-sided orthogonality.  Under cyclicity it coincides with
`Perp`. -/
def LeftPerp (S : Set Q) (U : Set Q) : Set Q :=
  {d | ∀ u ∈ U, d * u ∈ S}

@[simp] theorem mem_Perp {S U : Set Q} {d : Q} :
    d ∈ Perp S U ↔ ∀ u ∈ U, u * d ∈ S := Iff.rfl

@[simp] theorem mem_LeftPerp {S U : Set Q} {d : Q} :
    d ∈ LeftPerp S U ↔ ∀ u ∈ U, d * u ∈ S := Iff.rfl

/-- Cyclicity rotates three factors. -/
theorem cyclic_rotate3 {S : Set Q} (hS : CyclicSet S) (a b c : Q) :
    a * b * c ∈ S ↔ b * c * a ∈ S := by
  simpa [mul_assoc] using hS a (b * c)

/-- The reverse rotation form. -/
theorem cyclic_rotate3' {S : Set Q} (hS : CyclicSet S) (a b c : Q) :
    b * c * a ∈ S ↔ a * b * c ∈ S := by
  exact (cyclic_rotate3 (S := S) hS a b c).symm

/-- Under cyclicity, right and left orthogonality coincide. -/
theorem Perp_eq_LeftPerp_of_cyclic {S U : Set Q} (hS : CyclicSet S) :
    Perp S U = LeftPerp S U := by
  ext d
  constructor
  · intro hd u hu
    exact (hS u d).mp (hd u hu)
  · intro hd u hu
    exact (hS u d).mpr (hd u hu)

/-- Orthogonality is antitone. -/
theorem Perp_antitone {S U V : Set Q} (hUV : U ⊆ V) :
    Perp S V ⊆ Perp S U := by
  intro d hd u hu
  exact hd u (hUV hu)

/-- A two-sided frame accepts `U` iff its cyclic product belongs to `Perp S U`. -/
theorem mem_Intent_iff_frameProduct_mem_Perp_of_cyclic
    {S U : Set Q} (hS : CyclicSet S) {p : Q × Q} :
    p ∈ Intent S U ↔ p.2 * p.1 ∈ Perp S U := by
  constructor
  · intro hp
    intro u hu
    exact (cyclic_rotate3 (S := S) hS p.1 u p.2).mp (hp u hu)
  · intro hp u hu
    exact (cyclic_rotate3 (S := S) hS p.1 u p.2).mpr (hp u hu)

/-- The Galois closure collapses to one-sided double orthogonality under
cyclicity. -/
theorem cl_eq_doublePerp_of_cyclic {S : Set Q} (hS : CyclicSet S) (U : Set Q) :
    cl S U = Perp S (Perp S U) := by
  apply Set.Subset.antisymm
  · intro g hg
    rw [cl, Extent] at hg
    intro d hd
    have hIntent : (1, d) ∈ Intent S U := by
      intro u hu
      have h := hd u hu
      simpa [mul_assoc] using h
    have h := hg (1, d) hIntent
    simpa [mul_assoc] using h
  · intro g hg
    rw [cl, Extent]
    intro p hp
    have hd : p.2 * p.1 ∈ Perp S U := by
      exact (mem_Intent_iff_frameProduct_mem_Perp_of_cyclic
        (S := S) (U := U) hS (p := p)).mp hp
    have hgd : g * (p.2 * p.1) ∈ S := hg (p.2 * p.1) hd
    exact (cyclic_rotate3 (S := S) hS p.1 g p.2).mpr
      (by simpa [mul_assoc] using hgd)

/-- Closed extents are fixed by double orthogonality under cyclicity. -/
theorem closed_eq_doublePerp_of_cyclic {S U : Set Q}
    (hS : CyclicSet S) (hU : Closed S U) :
    U = Perp S (Perp S U) := by
  calc
    U = cl S U := hU.symm
    _ = Perp S (Perp S U) := cl_eq_doublePerp_of_cyclic (S := S) hS U

/-- Left division by `S` is exactly orthogonality. -/
theorem ldiv_S_eq_Perp (S U : Set Q) :
    ldiv U S = Perp S U := by
  rfl

/-- Under cyclicity, right division by `S` is also orthogonality. -/
theorem rdiv_S_eq_Perp_of_cyclic {S U : Set Q} (hS : CyclicSet S) :
    rdiv S U = Perp S U := by
  ext g
  constructor
  · intro hg u hu
    exact (hS g u).mp (hg u hu)
  · intro hg u hu
    exact (hS g u).mpr (hg u hu)

/-- In cyclic observations, left and right divisions of `S` by a closed extent
coincide. -/
theorem ldiv_S_eq_rdiv_S_of_cyclic {S U : Set Q} (hS : CyclicSet S) :
    ldiv U S = rdiv S U := by
  calc
    ldiv U S = Perp S U := ldiv_S_eq_Perp S U
    _ = rdiv S U := (rdiv_S_eq_Perp_of_cyclic (S := S) (U := U) hS).symm

/-- First dualizing equation:
`S / (U \ S) = U` for closed `U`, under cyclicity. -/
theorem rdiv_S_ldiv_eq_of_closed_cyclic {S U : Set Q}
    (hS : CyclicSet S) (hU : Closed S U) :
    rdiv S (ldiv U S) = U := by
  calc
    rdiv S (ldiv U S)
        = Perp S (ldiv U S) :=
          rdiv_S_eq_Perp_of_cyclic (S := S) (U := ldiv U S) hS
    _ = Perp S (Perp S U) := by
          rw [ldiv_S_eq_Perp]
    _ = cl S U := (cl_eq_doublePerp_of_cyclic (S := S) hS U).symm
    _ = U := hU

/-- Second dualizing equation:
`(S / U) \ S = U` for closed `U`, under cyclicity. -/
theorem ldiv_rdiv_S_eq_of_closed_cyclic {S U : Set Q}
    (hS : CyclicSet S) (hU : Closed S U) :
    ldiv (rdiv S U) S = U := by
  calc
    ldiv (rdiv S U) S
        = Perp S (rdiv S U) := ldiv_S_eq_Perp S (rdiv S U)
    _ = Perp S (Perp S U) := by
          rw [rdiv_S_eq_Perp_of_cyclic (S := S) (U := U) hS]
    _ = cl S U := (cl_eq_doublePerp_of_cyclic (S := S) hS U).symm
    _ = U := hU

/-- Orthogonality is an involution on closed extents, in the paper-facing form. -/
theorem Perp_involutive_on_closed_of_cyclic {S U : Set Q}
    (hS : CyclicSet S) (hU : Closed S U) :
    Perp S (Perp S U) = U := by
  calc
    Perp S (Perp S U) = cl S U :=
      (cl_eq_doublePerp_of_cyclic (S := S) hS U).symm
    _ = U := hU

/-- The membership object `S` is closed and hence satisfies the cyclic
double-orthogonality law when `S` is cyclic. -/
theorem S_doublePerp_eq_of_cyclic {S : Set Q} (hS : CyclicSet S) :
    Perp S (Perp S S) = S := by
  exact Perp_involutive_on_closed_of_cyclic (S := S) (U := S) hS (S_closed S)

/-- Paper-facing cyclic package: closure collapse plus the two dualizing laws. -/
theorem cyclic_phase_collapse_package {S U : Set Q}
    (hS : CyclicSet S) (hU : Closed S U) :
    cl S U = Perp S (Perp S U)
      ∧ rdiv S (ldiv U S) = U
      ∧ ldiv (rdiv S U) S = U := by
  exact ⟨cl_eq_doublePerp_of_cyclic (S := S) hS U,
    rdiv_S_ldiv_eq_of_closed_cyclic (S := S) (U := U) hS hU,
    ldiv_rdiv_S_eq_of_closed_cyclic (S := S) (U := U) hS hU⟩

end ObservedResidualConcept
