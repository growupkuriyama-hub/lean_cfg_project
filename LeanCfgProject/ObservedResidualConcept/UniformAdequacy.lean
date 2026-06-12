import LeanCfgProject.PointwiseAdequacy

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanCfgProject

universe u

/-
UniformAdequacy.lean

Planned theorem item 3:
  uniform adequacy for a residual is equivalent to singleton adequacy and to
  containment in a single observed-syntactic block.

This file is intentionally theorem-body work only.  It is not a release,
summary, package, transport, certificate, audit, metadata, manifest, dependency
certificate, or smoke-test module.

Main paper form:
  for R = Res_S(a,b),

    (∀ nonempty U ⊆ R, cl_S(U)=R)
      ↔
    (∀ ρ∈R, cl_S({ρ})=R)
      ↔
    (∀ ρ σ∈R, ρ ≈_S σ).

The formal statement below is slightly stronger than the paper's nonempty-R
version: if R is empty, all three predicates are vacuously true.
-/

variable {Q : Type u} [Mul Q]

/-- Uniform adequacy over nonempty subsets of `R`. -/
def UniformAdequacyOn
    (S R : Set Q) : Prop :=
  ∀ U : Set Q, (∃ x : Q, x ∈ U) → U ⊆ R → ConceptClosure S U = R

/-- Singleton adequacy for every point in `R`. -/
def SingletonAdequacyOn
    (S R : Set Q) : Prop :=
  ∀ ρ : Q, ρ ∈ R → ConceptClosure S ({ρ} : Set Q) = R

/-- `R` is contained in one observed syntactic block. -/
def SingleObservedSyntacticBlockOn
    (S R : Set Q) : Prop :=
  ∀ ρ : Q, ρ ∈ R → ∀ σ : Q, σ ∈ R → SameObservedSyntactic S ρ σ

/--
If two observed elements are syntactically equivalent, then the second lies in
the singleton concept closure of the first.
-/
theorem mem_conceptClosure_singleton_of_sameObservedSyntactic
    (S : Set Q) (x y : Q)
    (hxy : SameObservedSyntactic S x y) :
    y ∈ ConceptClosure S ({x} : Set Q) := by
  intro ab hab
  have hxmem : ab.1 * x * ab.2 ∈ S := by
    exact hab x (by simp)
  exact (hxy ab.1 ab.2).1 hxmem

/--
Mutual singleton-closure membership implies observed syntactic equivalence.
-/
theorem sameObservedSyntactic_of_mutual_mem_conceptClosure_singletons
    (S : Set Q) (x y : Q)
    (hyx : y ∈ ConceptClosure S ({x} : Set Q))
    (hxy : x ∈ ConceptClosure S ({y} : Set Q)) :
    SameObservedSyntactic S x y := by
  intro a b
  constructor
  · intro hxS
    have hctx : (a, b) ∈ CommonContexts S ({x} : Set Q) := by
      intro gamma hgamma
      have hgamma_eq : gamma = x := by
        simpa using hgamma
      simpa [hgamma_eq] using hxS
    exact hyx (a, b) hctx
  · intro hyS
    have hctx : (a, b) ∈ CommonContexts S ({y} : Set Q) := by
      intro gamma hgamma
      have hgamma_eq : gamma = y := by
        simpa using hgamma
      simpa [hgamma_eq] using hyS
    exact hxy (a, b) hctx

theorem singleton_subset_twoSidedResidual
    (S : Set Q) (a b ρ : Q)
    (hρ : ρ ∈ TwoSidedResidual S a b) :
    ({ρ} : Set Q) ⊆ TwoSidedResidual S a b := by
  intro x hx
  have hx_eq : x = ρ := by
    simpa using hx
  simpa [hx_eq] using hρ

/--
Uniform adequacy is equivalent to singleton adequacy for a residual.
-/
theorem uniformAdequacyOn_iff_singletonAdequacyOn_residual
    (S : Set Q) (a b : Q) :
    UniformAdequacyOn S (TwoSidedResidual S a b)
      ↔
    SingletonAdequacyOn S (TwoSidedResidual S a b) := by
  constructor
  · intro hU ρ hρ
    have hnonempty : ∃ x : Q, x ∈ ({ρ} : Set Q) := by
      exact ⟨ρ, by simp⟩
    exact hU ({ρ} : Set Q) hnonempty
      (singleton_subset_twoSidedResidual S a b ρ hρ)
  · intro hSingle U hnonempty hUsub
    rcases hnonempty with ⟨ρ, hρU⟩
    have hρR : ρ ∈ TwoSidedResidual S a b := hUsub hρU
    have hρAdeq :
        ConceptClosure S ({ρ} : Set Q) =
          TwoSidedResidual S a b :=
      hSingle ρ hρR
    apply Set.Subset.antisymm
    · have hmono :
          ConceptClosure S U
            ⊆
          ConceptClosure S (TwoSidedResidual S a b) :=
        conceptClosure_mono S hUsub
      rw [conceptClosure_twoSidedResidual_eq S a b] at hmono
      exact hmono
    · intro σ hσR
      have hσ_in_cl_singleton :
          σ ∈ ConceptClosure S ({ρ} : Set Q) := by
        rw [hρAdeq]
        exact hσR
      have hsingleton_sub_U :
          ({ρ} : Set Q) ⊆ U := by
        intro x hx
        have hx_eq : x = ρ := by
          simpa using hx
        simpa [hx_eq] using hρU
      have hmono :
          ConceptClosure S ({ρ} : Set Q)
            ⊆
          ConceptClosure S U :=
        conceptClosure_mono S hsingleton_sub_U
      exact hmono hσ_in_cl_singleton

/--
Singleton adequacy for a residual is equivalent to the residual lying in one
observed syntactic block.
-/
theorem singletonAdequacyOn_iff_singleObservedSyntacticBlockOn_residual
    (S : Set Q) (a b : Q) :
    SingletonAdequacyOn S (TwoSidedResidual S a b)
      ↔
    SingleObservedSyntacticBlockOn S (TwoSidedResidual S a b) := by
  constructor
  · intro hSingle ρ hρ σ hσ
    have hρAdeq :
        ConceptClosure S ({ρ} : Set Q) =
          TwoSidedResidual S a b :=
      hSingle ρ hρ
    have hσAdeq :
        ConceptClosure S ({σ} : Set Q) =
          TwoSidedResidual S a b :=
      hSingle σ hσ
    have hσ_in_clρ :
        σ ∈ ConceptClosure S ({ρ} : Set Q) := by
      rw [hρAdeq]
      exact hσ
    have hρ_in_clσ :
        ρ ∈ ConceptClosure S ({σ} : Set Q) := by
      rw [hσAdeq]
      exact hρ
    exact sameObservedSyntactic_of_mutual_mem_conceptClosure_singletons
      S ρ σ hσ_in_clρ hρ_in_clσ
  · intro hBlock ρ hρ
    apply Set.Subset.antisymm
    · have hmono :
          ConceptClosure S ({ρ} : Set Q)
            ⊆
          ConceptClosure S (TwoSidedResidual S a b) :=
        conceptClosure_mono S
          (singleton_subset_twoSidedResidual S a b ρ hρ)
      rw [conceptClosure_twoSidedResidual_eq S a b] at hmono
      exact hmono
    · intro σ hσ
      exact mem_conceptClosure_singleton_of_sameObservedSyntactic
        S ρ σ (hBlock ρ hρ σ hσ)

/--
Uniform adequacy is equivalent to the single observed-syntactic-block condition
for a residual.
-/
theorem uniformAdequacyOn_iff_singleObservedSyntacticBlockOn_residual
    (S : Set Q) (a b : Q) :
    UniformAdequacyOn S (TwoSidedResidual S a b)
      ↔
    SingleObservedSyntacticBlockOn S (TwoSidedResidual S a b) :=
  (uniformAdequacyOn_iff_singletonAdequacyOn_residual S a b).trans
    (singletonAdequacyOn_iff_singleObservedSyntacticBlockOn_residual S a b)

/--
Triple theorem for item 3.
-/
theorem uniformAdequacy_equivalences_for_residual
    (S : Set Q) (a b : Q) :
    (UniformAdequacyOn S (TwoSidedResidual S a b)
      ↔
     SingletonAdequacyOn S (TwoSidedResidual S a b))
    ∧
    (SingletonAdequacyOn S (TwoSidedResidual S a b)
      ↔
     SingleObservedSyntacticBlockOn S (TwoSidedResidual S a b))
    ∧
    (UniformAdequacyOn S (TwoSidedResidual S a b)
      ↔
     SingleObservedSyntacticBlockOn S (TwoSidedResidual S a b)) := by
  exact ⟨uniformAdequacyOn_iff_singletonAdequacyOn_residual S a b,
    singletonAdequacyOn_iff_singleObservedSyntacticBlockOn_residual S a b,
    uniformAdequacyOn_iff_singleObservedSyntacticBlockOn_residual S a b⟩

end LeanCfgProject
