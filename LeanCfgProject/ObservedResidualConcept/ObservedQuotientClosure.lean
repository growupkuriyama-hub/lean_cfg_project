import LeanCfgProject.ObservedResidualConcept.ObservedQuotientResidual
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u v

/-
ObservedQuotientClosure.lean

Planned theorem item 4(b,c), theorem-body experiment.

Goal:
  extend the residual pullback theorem from ObservedQuotientResidual.lean
  to common contexts and concept closure under an abstract multiplicative
  quotient/factor map.

This is not a release/summary/package/certificate/audit/metadata/manifest/
dependency-certificate/smoke-test module.

Mathematical content:
  Let π : Q → Qbar be a surjective multiplicative map.
  Assume Sbar has exactly S as its pullback:
      π x ∈ Sbar ↔ x ∈ S.

  Then for every observed subset Ubar ⊆ Qbar,

      CommonContexts_S(π⁻¹ Ubar)
        =
      π-frame-preimage(CommonContexts_Sbar(Ubar)),

  and

      cl_S(π⁻¹ Ubar)
        =
      π⁻¹(cl_Sbar(Ubar)).

The second theorem is the closure-commutation half needed for quotient
invariance.
-/

variable {Q : Type u} {Qbar : Type v}
variable [Semigroup Q] [Semigroup Qbar]

/--
Common contexts commute with pullback along a surjective multiplicative
observed factor map.
-/
theorem quotient_commonContexts_preimage_eq
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q) (Sbar : Set Qbar)
    (hS_pullback : ∀ x : Q, π x ∈ Sbar ↔ x ∈ S)
    (Ubar : Set Qbar) :
    CommonContexts S { gamma : Q | π gamma ∈ Ubar }
      =
    { ab : Q × Q |
        (π ab.1, π ab.2) ∈ CommonContexts Sbar Ubar } := by
  apply Set.ext
  intro ab
  constructor
  · intro hctx
    intro delta hdelta
    rcases hπ_surj delta with ⟨gamma, hgamma_eq⟩
    have hpreU : π gamma ∈ Ubar := by
      simpa [hgamma_eq] using hdelta
    have hS : ab.1 * gamma * ab.2 ∈ S :=
      hctx gamma hpreU
    have hSbar_pre : π (ab.1 * gamma * ab.2) ∈ Sbar :=
      (hS_pullback (ab.1 * gamma * ab.2)).mpr hS
    have hmap :
        π (ab.1 * gamma * ab.2) =
          π ab.1 * π gamma * π ab.2 :=
      map_three_mul π hπ_mul ab.1 gamma ab.2
    have hSbar :
        π ab.1 * π gamma * π ab.2 ∈ Sbar := by
      rw [← hmap]
      exact hSbar_pre
    simpa [hgamma_eq] using hSbar
  · intro hctxbar
    intro gamma hgamma
    have hSbar :
        π ab.1 * π gamma * π ab.2 ∈ Sbar :=
      hctxbar (π gamma) hgamma
    have hmap :
        π (ab.1 * gamma * ab.2) =
          π ab.1 * π gamma * π ab.2 :=
      map_three_mul π hπ_mul ab.1 gamma ab.2
    have hpre :
        π (ab.1 * gamma * ab.2) ∈ Sbar := by
      rw [hmap]
      exact hSbar
    exact (hS_pullback (ab.1 * gamma * ab.2)).mp hpre

/--
Concept closure commutes with pullback along a surjective multiplicative
observed factor map.

This is the Lean form of:

  cl_S(π⁻¹ Ubar) = π⁻¹(cl_Sbar(Ubar)).
-/
theorem quotient_conceptClosure_preimage_eq
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q) (Sbar : Set Qbar)
    (hS_pullback : ∀ x : Q, π x ∈ Sbar ↔ x ∈ S)
    (Ubar : Set Qbar) :
    ConceptClosure S { gamma : Q | π gamma ∈ Ubar }
      =
    { gamma : Q | π gamma ∈ ConceptClosure Sbar Ubar } := by
  apply Set.ext
  intro gamma
  constructor
  · intro hgamma
    intro abbar habbar
    rcases hπ_surj abbar.1 with ⟨a, ha_eq⟩
    rcases hπ_surj abbar.2 with ⟨b, hb_eq⟩
    have hctx :
        (a, b) ∈ CommonContexts S { delta : Q | π delta ∈ Ubar } := by
      intro delta hdelta
      have hSbar :
          abbar.1 * π delta * abbar.2 ∈ Sbar := by
        exact habbar (π delta) hdelta
      have hSbar' :
          π a * π delta * π b ∈ Sbar := by
        simpa [ha_eq, hb_eq] using hSbar
      have hmap :
          π (a * delta * b) =
            π a * π delta * π b :=
        map_three_mul π hπ_mul a delta b
      have hpre :
          π (a * delta * b) ∈ Sbar := by
        rw [hmap]
        exact hSbar'
      exact (hS_pullback (a * delta * b)).mp hpre
    have hS : a * gamma * b ∈ S :=
      hgamma (a, b) hctx
    have hSbar_pre : π (a * gamma * b) ∈ Sbar :=
      (hS_pullback (a * gamma * b)).mpr hS
    have hmap :
        π (a * gamma * b) =
          π a * π gamma * π b :=
      map_three_mul π hπ_mul a gamma b
    have hSbar :
        π a * π gamma * π b ∈ Sbar := by
      rw [← hmap]
      exact hSbar_pre
    simpa [ha_eq, hb_eq] using hSbar
  · intro hgamma_bar
    intro ab hab
    have hctxbar :
        (π ab.1, π ab.2) ∈ CommonContexts Sbar Ubar := by
      intro delta hdelta
      rcases hπ_surj delta with ⟨x, hx_eq⟩
      have hxU : π x ∈ Ubar := by
        simpa [hx_eq] using hdelta
      have hS : ab.1 * x * ab.2 ∈ S :=
        hab x hxU
      have hSbar_pre : π (ab.1 * x * ab.2) ∈ Sbar :=
        (hS_pullback (ab.1 * x * ab.2)).mpr hS
      have hmap :
          π (ab.1 * x * ab.2) =
            π ab.1 * π x * π ab.2 :=
        map_three_mul π hπ_mul ab.1 x ab.2
      have hSbar :
          π ab.1 * π x * π ab.2 ∈ Sbar := by
        rw [← hmap]
        exact hSbar_pre
      simpa [hx_eq] using hSbar
    have hSbar :
        π ab.1 * π gamma * π ab.2 ∈ Sbar :=
      hgamma_bar (π ab.1, π ab.2) hctxbar
    have hmap :
        π (ab.1 * gamma * ab.2) =
          π ab.1 * π gamma * π ab.2 :=
      map_three_mul π hπ_mul ab.1 gamma ab.2
    have hpre :
        π (ab.1 * gamma * ab.2) ∈ Sbar := by
      rw [hmap]
      exact hSbar
    exact (hS_pullback (ab.1 * gamma * ab.2)).mp hpre

/--
Closed extents pull back to closed extents under an observed factor map.
-/
theorem quotient_preimage_isConceptExtent
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q) (Sbar : Set Qbar)
    (hS_pullback : ∀ x : Q, π x ∈ Sbar ↔ x ∈ S)
    (Ubar : Set Qbar)
    (hUbar : IsConceptExtent Sbar Ubar) :
    IsConceptExtent S { gamma : Q | π gamma ∈ Ubar } := by
  unfold IsConceptExtent at *
  rw [quotient_conceptClosure_preimage_eq
    π hπ_mul hπ_surj S Sbar hS_pullback Ubar]
  apply Set.ext
  intro gamma
  constructor
  · intro hgamma
    have hclosed :
        ConceptClosure Sbar Ubar = Ubar := hUbar
    rw [hclosed] at hgamma
    exact hgamma
  · intro hgamma
    have hclosed :
        ConceptClosure Sbar Ubar = Ubar := hUbar
    rw [hclosed]
    exact hgamma

end LeanCfgProject
