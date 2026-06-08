import LeanCfgProject.ObservedSyntacticCongruence

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
CanonicalResidualClosureSystem.lean

This file formalizes the v25.1 "canonical residual closure system" layer.

This v2 removes unsafe local reducibility attributes rejected by Lean 4.31.

The goal is to make precise, at the `(Q,S)` level and independently of any
grammar presentation, that residual concept extents are exactly intersections
of two-sided residuals.

The central definition is

  ResidualIntersection S K

for a family `K : Set (Q × Q)` of two-sided contexts.  It denotes the
intersection of all residuals `Res_S(a,b)` with `(a,b) ∈ K`.

Main statements:

* every residual intersection is concept-closed;
* every concept closure is the residual intersection over its common contexts;
* a subset is closed iff it is a residual intersection;
* single residuals and `Set.univ` are special residual intersections.

This gives the Lean counterpart of the paper theorem "Canonical residual
closure system".
-/

variable {Q : Type u} [Mul Q]

/--
The intersection of the two-sided residuals indexed by a set of contexts.
-/
def ResidualIntersection (S : Set Q) (K : Set (Q × Q)) : Set Q :=
  { gamma : Q |
    ∀ ab : Q × Q,
      ab ∈ K →
        gamma ∈ TwoSidedResidual S ab.1 ab.2 }

/--
The empty residual intersection is the whole carrier.
-/
theorem residualIntersection_empty
    (S : Set Q) :
    ResidualIntersection S (∅ : Set (Q × Q)) = Set.univ := by
  apply Set.ext
  intro gamma
  simp [ResidualIntersection]

/--
A singleton-indexed residual intersection is exactly the corresponding
two-sided residual.
-/
theorem residualIntersection_singleton
    (S : Set Q) (a b : Q) :
    ResidualIntersection S ({(a, b)} : Set (Q × Q)) =
      TwoSidedResidual S a b := by
  apply Set.ext
  intro gamma
  constructor
  · intro hgamma
    exact hgamma (a, b) (by simp)
  · intro hgamma ab hab
    have hab' : ab = (a, b) := by
      simpa using hab
    subst ab
    exact hgamma

/--
Every residual intersection is closed for the residual concept closure.
-/
theorem residualIntersection_closed
    (S : Set Q) (K : Set (Q × Q)) :
    ConceptClosure S (ResidualIntersection S K) =
      ResidualIntersection S K := by
  apply Set.Subset.antisymm
  · intro gamma hgamma
    intro ab hab
    have hcommon : ab ∈ CommonContexts S (ResidualIntersection S K) := by
      intro delta hdelta
      exact hdelta ab hab
    exact hgamma ab hcommon
  · exact subset_conceptClosure S (ResidualIntersection S K)

/--
The concept closure of `U` is the residual intersection over the common
two-sided contexts of `U`.
-/
theorem conceptClosure_eq_residualIntersection_commonContexts
    (S U : Set Q) :
    ConceptClosure S U =
      ResidualIntersection S (CommonContexts S U) := by
  apply Set.ext
  intro gamma
  constructor
  · intro hgamma ab hab
    exact hgamma ab hab
  · intro hgamma ab hab
    exact hgamma ab hab

/--
A set is a concept extent exactly when it is an intersection of two-sided
residuals.
-/
theorem isConceptExtent_iff_exists_residualIntersection
    (S U : Set Q) :
    ConceptClosure S U = U ↔
      ∃ K : Set (Q × Q), U = ResidualIntersection S K := by
  constructor
  · intro hclosed
    refine ⟨CommonContexts S U, ?_⟩
    calc
      U = ConceptClosure S U := hclosed.symm
      _ = ResidualIntersection S (CommonContexts S U) :=
          conceptClosure_eq_residualIntersection_commonContexts S U
  · intro h
    rcases h with ⟨K, rfl⟩
    exact residualIntersection_closed S K

/--
Every two-sided residual is a concept extent.
-/
theorem twoSidedResidual_isConceptExtent
    (S : Set Q) (a b : Q) :
    ConceptClosure S (TwoSidedResidual S a b) =
      TwoSidedResidual S a b := by
  exact conceptClosure_twoSidedResidual_eq S a b

/--
A residual is a residual intersection, hence a closed extent.
-/
theorem twoSidedResidual_exists_residualIntersection
    (S : Set Q) (a b : Q) :
    ∃ K : Set (Q × Q),
      TwoSidedResidual S a b = ResidualIntersection S K := by
  refine ⟨{(a, b)}, ?_⟩
  exact (residualIntersection_singleton S a b).symm

/--
The whole carrier is a residual intersection, corresponding to the empty
intersection.
-/
theorem univ_exists_residualIntersection
    (S : Set Q) :
    ∃ K : Set (Q × Q),
      (Set.univ : Set Q) = ResidualIntersection S K := by
  refine ⟨∅, ?_⟩
  exact (residualIntersection_empty S).symm

/--
If `U` is already closed, then it is exactly the residual intersection over
its own common contexts.
-/
theorem closed_eq_residualIntersection_commonContexts
    (S U : Set Q)
    (hclosed : ConceptClosure S U = U) :
    U = ResidualIntersection S (CommonContexts S U) := by
  calc
    U = ConceptClosure S U := hclosed.symm
    _ = ResidualIntersection S (CommonContexts S U) :=
        conceptClosure_eq_residualIntersection_commonContexts S U

/--
The family of residual intersections is closed under concept closure.
-/
theorem conceptClosure_residualIntersection
    (S : Set Q) (K : Set (Q × Q)) :
    ConceptClosure S (ResidualIntersection S K) =
      ResidualIntersection S K :=
  residualIntersection_closed S K

/--
Residual intersections are exactly the closed sets, packaged as a pair of
directions for convenient importing.
-/
theorem canonicalResidualClosureSystem_summary
    (S U : Set Q) :
    (ConceptClosure S U = U →
      ∃ K : Set (Q × Q), U = ResidualIntersection S K)
    ∧
    ((∃ K : Set (Q × Q), U = ResidualIntersection S K) →
      ConceptClosure S U = U) := by
  constructor
  · exact (isConceptExtent_iff_exists_residualIntersection S U).mp
  · exact (isConceptExtent_iff_exists_residualIntersection S U).mpr

end LeanCfgProject
