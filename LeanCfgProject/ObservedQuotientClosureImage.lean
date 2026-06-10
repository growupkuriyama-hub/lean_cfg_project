import LeanCfgProject.ObservedQuotientClosure

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u v

/-
ObservedQuotientClosureImage.lean

Planned theorem item 4(c), theorem-body experiment.

Goal:
  prove the image-side closure preservation theorem for an abstract
  surjective multiplicative observed factor map:

      π(cl_S W) = cl_Sbar(π(W)).

This is the image-side companion to ObservedQuotientClosure.lean, which proved
the preimage-side theorem.  This file also proves direct image preservation for
frame residuals, point concepts, and ConceptProduct.

This is intentionally not a release/summary/package/certificate/audit/metadata/
manifest/dependency-certificate/smoke-test module.
-/

variable {Q : Type u} {Qbar : Type v}
variable [Semigroup Q] [Semigroup Qbar]

/--
Image of subset multiplication under a multiplicative map.
-/
theorem quotient_setMul_image_eq
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (A B : Set Q) :
    Set.image π (SetMul A B)
      =
    SetMul (Set.image π A) (Set.image π B) := by
  apply Set.ext
  intro z
  constructor
  · intro hz
    rcases hz with ⟨w, hw, hz_eq⟩
    rcases hw with ⟨a, ha, b, hb, hw_eq⟩
    refine ⟨π a, ?_, π b, ?_, ?_⟩
    · exact ⟨a, ha, rfl⟩
    · exact ⟨b, hb, rfl⟩
    · rw [← hz_eq, hw_eq, hπ_mul a b]
  · intro hz
    rcases hz with ⟨pa, hpa, pb, hpb, hz_eq⟩
    rcases hpa with ⟨a, ha, hpa_eq⟩
    rcases hpb with ⟨b, hb, hpb_eq⟩
    refine ⟨a * b, ?_, ?_⟩
    · exact ⟨a, ha, b, hb, rfl⟩
    · rw [hz_eq, ← hpa_eq, ← hpb_eq, hπ_mul a b]

/--
Image of a residual under a surjective multiplicative observed factor map.

This is the direct `Set.image` version of item 4(a)'s image half.
-/
theorem quotient_residual_image_eq
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q) (Sbar : Set Qbar)
    (hS_pullback : ∀ x : Q, π x ∈ Sbar ↔ x ∈ S)
    (a b : Q) :
    Set.image π (TwoSidedResidual S a b)
      =
    TwoSidedResidual Sbar (π a) (π b) := by
  apply Set.ext
  intro delta
  constructor
  · intro hdelta
    rcases hdelta with ⟨gamma, hgamma, hdelta_eq⟩
    have hpair :=
      (quotient_residual_image_surj
        π hπ_mul hπ_surj S Sbar hS_pullback a b).2
    have hbar : π gamma ∈ TwoSidedResidual Sbar (π a) (π b) :=
      hpair gamma hgamma
    simpa [hdelta_eq] using hbar
  · intro hdelta
    have hpair :=
      (quotient_residual_image_surj
        π hπ_mul hπ_surj S Sbar hS_pullback a b).1
    rcases hpair delta hdelta with ⟨gamma, hgamma, hgamma_eq⟩
    exact ⟨gamma, hgamma, hgamma_eq⟩

/--
Image-side concept-closure preservation:

  π(cl_S W) = cl_Sbar(π(W)).
-/
theorem quotient_conceptClosure_image_eq
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q) (Sbar : Set Qbar)
    (hS_pullback : ∀ x : Q, π x ∈ Sbar ↔ x ∈ S)
    (W : Set Q) :
    Set.image π (ConceptClosure S W)
      =
    ConceptClosure Sbar (Set.image π W) := by
  apply Set.ext
  intro delta
  constructor
  · intro hdelta
    rcases hdelta with ⟨gamma, hgamma, hdelta_eq⟩
    intro abbar habbar
    rcases hπ_surj abbar.1 with ⟨a, ha_eq⟩
    rcases hπ_surj abbar.2 with ⟨b, hb_eq⟩
    have hctx : (a, b) ∈ CommonContexts S W := by
      intro w hw
      have hWbar : π w ∈ Set.image π W := ⟨w, hw, rfl⟩
      have hSbar :
          abbar.1 * π w * abbar.2 ∈ Sbar :=
        habbar (π w) hWbar
      have hSbar' :
          π a * π w * π b ∈ Sbar := by
        simpa [ha_eq, hb_eq] using hSbar
      have hmap :
          π (a * w * b) =
            π a * π w * π b :=
        map_three_mul π hπ_mul a w b
      have hpre :
          π (a * w * b) ∈ Sbar := by
        rw [hmap]
        exact hSbar'
      exact (hS_pullback (a * w * b)).mp hpre
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
    simpa [hdelta_eq, ha_eq, hb_eq] using hSbar
  · intro hdelta
    rcases hπ_surj delta with ⟨gamma, hgamma_eq⟩
    refine ⟨gamma, ?_, hgamma_eq⟩
    intro ab hab
    have hctxbar :
        (π ab.1, π ab.2) ∈ CommonContexts Sbar (Set.image π W) := by
      intro eta heta
      rcases heta with ⟨w, hw, heta_eq⟩
      have hS : ab.1 * w * ab.2 ∈ S :=
        hab w hw
      have hSbar_pre : π (ab.1 * w * ab.2) ∈ Sbar :=
        (hS_pullback (ab.1 * w * ab.2)).mpr hS
      have hmap :
          π (ab.1 * w * ab.2) =
            π ab.1 * π w * π ab.2 :=
        map_three_mul π hπ_mul ab.1 w ab.2
      have hSbar :
          π ab.1 * π w * π ab.2 ∈ Sbar := by
        rw [← hmap]
        exact hSbar_pre
      simpa [heta_eq] using hSbar
    have hSbar :
        π ab.1 * delta * π ab.2 ∈ Sbar :=
      hdelta (π ab.1, π ab.2) hctxbar
    have hSbar' :
        π ab.1 * π gamma * π ab.2 ∈ Sbar := by
      simpa [hgamma_eq] using hSbar
    have hmap :
        π (ab.1 * gamma * ab.2) =
          π ab.1 * π gamma * π ab.2 :=
      map_three_mul π hπ_mul ab.1 gamma ab.2
    have hpre :
        π (ab.1 * gamma * ab.2) ∈ Sbar := by
      rw [hmap]
      exact hSbar'
    exact (hS_pullback (ab.1 * gamma * ab.2)).mp hpre

/--
Image preservation for point concepts.
-/
theorem quotient_pointConcept_image_eq
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q) (Sbar : Set Qbar)
    (hS_pullback : ∀ x : Q, π x ∈ Sbar ↔ x ∈ S)
    (gamma : Q) :
    Set.image π (ConceptClosure S ({gamma} : Set Q))
      =
    ConceptClosure Sbar ({π gamma} : Set Qbar) := by
  rw [quotient_conceptClosure_image_eq
    π hπ_mul hπ_surj S Sbar hS_pullback ({gamma} : Set Q)]
  apply congrArg (ConceptClosure Sbar)
  apply Set.ext
  intro delta
  constructor
  · intro hdelta
    rcases hdelta with ⟨x, hx, hdelta_eq⟩
    have hx_eq : x = gamma := by
      simpa using hx
    simpa [hdelta_eq, hx_eq]
  · intro hdelta
    have hdelta_eq : delta = π gamma := by
      simpa using hdelta
    exact ⟨gamma, by simp, hdelta_eq.symm⟩

/--
Image preservation for ConceptProduct.
-/
theorem quotient_conceptProduct_image_eq
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q) (Sbar : Set Qbar)
    (hS_pullback : ∀ x : Q, π x ∈ Sbar ↔ x ∈ S)
    (A B : Set Q) :
    Set.image π (ConceptProduct S A B)
      =
    ConceptProduct Sbar (Set.image π A) (Set.image π B) := by
  unfold ConceptProduct
  rw [quotient_conceptClosure_image_eq
    π hπ_mul hπ_surj S Sbar hS_pullback (SetMul A B)]
  rw [quotient_setMul_image_eq π hπ_mul A B]

end LeanCfgProject
