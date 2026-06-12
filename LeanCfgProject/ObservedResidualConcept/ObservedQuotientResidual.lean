import LeanCfgProject.UniformAdequacy

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u v

/-
ObservedQuotientResidual.lean

Planned theorem item 4(a), first theorem-body experiment.

Goal:
  prove the residual-pullback part of quotient invariance for an abstract
  multiplicative quotient/factor map.

This is intentionally not a release/summary/package/certificate/audit/metadata/
manifest/dependency-certificate/smoke-test module.

Mathematical statement:
  Let π : Q → Qbar be multiplicative.
  Let Sbar ⊆ Qbar be the observed image whose pullback is exactly S:
      π x ∈ Sbar ↔ x ∈ S.
  Then
      π⁻¹(Res_{Sbar}(π a, π b)) = Res_S(a,b).

This is the core calculation needed before instantiating π as the quotient map
Q → Q/≈_S.
-/

variable {Q : Type u} {Qbar : Type v}
variable [Semigroup Q] [Semigroup Qbar]

/--
Multiplicative maps preserve two-sided products.
-/
theorem map_three_mul
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (a gamma b : Q) :
    π (a * gamma * b) = π a * π gamma * π b := by
  rw [hπ_mul (a * gamma) b, hπ_mul a gamma]

/--
Residual pullback under a multiplicative factor map.

This is item 4(a), pullback half:

  π⁻¹(Res_{Sbar}(πa,πb)) = Res_S(a,b).

The only semantic hypothesis is that `Sbar` has exactly `S` as its pullback.
For the actual observed syntactic quotient, this hypothesis will be supplied by
the quotient map and the fact that `S` is saturated under `≈_S`.
-/
theorem quotient_residual_preimage_eq
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (S : Set Q) (Sbar : Set Qbar)
    (hS_pullback : ∀ x : Q, π x ∈ Sbar ↔ x ∈ S)
    (a b : Q) :
    { gamma : Q |
        π gamma ∈ TwoSidedResidual Sbar (π a) (π b) }
      =
    TwoSidedResidual S a b := by
  apply Set.ext
  intro gamma
  constructor
  · intro hgamma
    have hprod_bar :
        π a * π gamma * π b ∈ Sbar := by
      simpa [TwoSidedResidual] using hgamma
    have hmap :
        π (a * gamma * b) = π a * π gamma * π b :=
      map_three_mul π hπ_mul a gamma b
    have hpre :
        π (a * gamma * b) ∈ Sbar := by
      rw [hmap]
      exact hprod_bar
    exact (hS_pullback (a * gamma * b)).mp hpre
  · intro hgamma
    have hprod :
        a * gamma * b ∈ S := by
      simpa [TwoSidedResidual] using hgamma
    have hpre :
        π (a * gamma * b) ∈ Sbar :=
      (hS_pullback (a * gamma * b)).mpr hprod
    have hmap :
        π (a * gamma * b) = π a * π gamma * π b :=
      map_three_mul π hπ_mul a gamma b
    have hprod_bar :
        π a * π gamma * π b ∈ Sbar := by
      rw [← hmap]
      exact hpre
    simpa [TwoSidedResidual] using hprod_bar

/--
Image half of item 4(a), under surjectivity of the factor map.

This is stated as mutual subset by membership, avoiding additional set-image
API brittleness:

  every element of Res_{Sbar}(πa,πb) has a representative in Res_S(a,b),
  and every representative from Res_S(a,b) maps into Res_{Sbar}(πa,πb).
-/
theorem quotient_residual_image_surj
    (π : Q → Qbar)
    (hπ_mul : ∀ x y : Q, π (x * y) = π x * π y)
    (hπ_surj : ∀ y : Qbar, ∃ x : Q, π x = y)
    (S : Set Q) (Sbar : Set Qbar)
    (hS_pullback : ∀ x : Q, π x ∈ Sbar ↔ x ∈ S)
    (a b : Q) :
    (∀ delta : Qbar,
      delta ∈ TwoSidedResidual Sbar (π a) (π b) →
        ∃ gamma : Q,
          gamma ∈ TwoSidedResidual S a b ∧ π gamma = delta)
    ∧
    (∀ gamma : Q,
      gamma ∈ TwoSidedResidual S a b →
        π gamma ∈ TwoSidedResidual Sbar (π a) (π b)) := by
  constructor
  · intro delta hdelta
    rcases hπ_surj delta with ⟨gamma, hgamma_eq⟩
    have hpremem :
        gamma ∈
          { x : Q | π x ∈ TwoSidedResidual Sbar (π a) (π b) } := by
      simpa [hgamma_eq] using hdelta
    have hres :
        gamma ∈ TwoSidedResidual S a b := by
      have hset :=
        congrArg (fun T : Set Q => gamma ∈ T)
          (quotient_residual_preimage_eq π hπ_mul S Sbar hS_pullback a b)
      simpa using hset.mp hpremem
    exact ⟨gamma, hres, hgamma_eq⟩
  · intro gamma hgamma
    have hset :=
      congrArg (fun T : Set Q => gamma ∈ T)
        (quotient_residual_preimage_eq π hπ_mul S Sbar hS_pullback a b)
    have hpremem :
        gamma ∈
          { x : Q | π x ∈ TwoSidedResidual Sbar (π a) (π b) } := by
      simpa using hset.mpr hgamma
    exact hpremem

end LeanCfgProject
