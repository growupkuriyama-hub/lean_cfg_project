import LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCutAdequacyCore

/-!
# Finite cut-observation core

This file checks the finite-observation core behind the paper's
"finite-observation collapse" lemma in the cut-structure section.

The paper-level statement says more: for finite `Q`, the observed image and
occupied cut relation of a language can be realized by finitely many witness
words/factorizations.  That representative-selection statement depends on the
word/factorization layer and is left in the paper.

This Lean file proves the finite observed-object core used by that argument:

* if the observed monoid `Q` is finite, every observed image in `Q` is finite;
* the observed cut universe `Q × Q × Q` is finite;
* every observed cut relation is finite;
* hence universal cut-density checks range over a finite observed relation;
* an abstract finite-support form packages finite image data and finite cut data.

This is intentionally modest, but it is not cosmetic: it supports the v2
claim that finite observation alone cannot carry context-freeness; the finite
observed image and finite cut relation are finite data determined inside
`Q` and `Q^3`.
-/

open Set

universe u v

namespace ObservedResidualConcept

variable {W : Type u} {Q : Type v}

/-- Observed image of a set under an arbitrary observation map. -/
def FinObsImage (q : W → Q) (L : Set W) : Set Q :=
  q '' L

/-- Observed cut triples, matching the paper's `Cut_q^+(L) ⊆ Q^3`. -/
abbrev ObservedCutTriple (Q : Type v) : Type v :=
  Q × Q × Q

/-- A word-level factorization witness before observation.

The paper's factorization is `ell w r ∈ L`; here we only keep the three
components abstractly. -/
structure CutFactor (W : Type u) where
  left : W
  middle : W
  right : W

/-- Image of a set of factorization witnesses as observed cut triples. -/
def FinObsCutImage (q : W → Q) (T : Set (CutFactor W)) :
    Set (ObservedCutTriple Q) :=
  {c | ∃ t ∈ T, c = (q t.left, q t.middle, q t.right)}

/-- Every observed image is finite when the observation carrier is finite. -/
theorem finObsImage_finite_of_fintype
    [Fintype Q] (q : W → Q) (L : Set W) :
    Set.Finite (FinObsImage q L) := by
  exact Set.finite_univ.subset (by intro x hx; trivial)

/-- The observed cut universe is finite when the observation carrier is finite. -/
theorem observedCutTriple_univ_finite [Fintype Q] :
    Set.Finite (Set.univ : Set (ObservedCutTriple Q)) := by
  exact Set.finite_univ

/-- Every observed cut relation is finite when the observation carrier is finite. -/
theorem finObsCutImage_finite_of_fintype
    [Fintype Q] (q : W → Q) (T : Set (CutFactor W)) :
    Set.Finite (FinObsCutImage q T) := by
  exact Set.finite_univ.subset (by intro c hc; trivial)

/-- Any abstract observed cut relation in `Q^3` is finite when `Q` is finite. -/
theorem observedCutRelation_finite_of_fintype
    [Fintype Q] (C : Set (ObservedCutTriple Q)) :
    Set.Finite C := by
  exact Set.finite_univ.subset (by intro c hc; trivial)

/-- A finite support package for finite observed image and finite observed cuts.

This is the Lean-side finite-data abstraction behind the paper's collapse
argument: after observation into a finite carrier, the image data and cut data
are finite sets. -/
structure FiniteObservedCutData (W : Type u) (Q : Type v) where
  q : W → Q
  language : Set W
  factors : Set (CutFactor W)
  imageFinite : Set.Finite (FinObsImage q language)
  cutsFinite : Set.Finite (FinObsCutImage q factors)

/-- Finite observed data is available automatically for finite observation
carriers. -/
def finiteObservedCutDataOfFintype
    [Fintype Q] (q : W → Q) (L : Set W) (T : Set (CutFactor W)) :
    FiniteObservedCutData W Q where
  q := q
  language := L
  factors := T
  imageFinite := finObsImage_finite_of_fintype q L
  cutsFinite := finObsCutImage_finite_of_fintype q T

/-- Convert a triple-based cut relation into the point-style cuts used by
`ObservedResidualConceptCutAdequacyCore`. -/
def cutPointOfTriple (c : ObservedCutTriple Q) : ObservedCutPoint Q :=
  ⟨c.1, c.2.1, c.2.2⟩

/-- The point-style image of a finite triple cut relation is finite.

This bridges the paper's `Q^3` cut notation with the previous file's
`ObservedCutPoint` abstraction. -/
theorem cutPoint_image_finite_of_finite_triples
    {C : Set (ObservedCutTriple Q)} (hC : Set.Finite C) :
    Set.Finite (cutPointOfTriple '' C) := by
  exact hC.image cutPointOfTriple

/-- In particular, the point-style observed cuts are finite for finite `Q`. -/
theorem cutPoint_image_finite_of_fintype
    [Fintype Q] (C : Set (ObservedCutTriple Q)) :
    Set.Finite (cutPointOfTriple '' C) := by
  exact cutPoint_image_finite_of_finite_triples
    (observedCutRelation_finite_of_fintype C)

/-- Finite-observation collapse core package.

This does not choose witness words.  It verifies the finite observed side of
the paper's collapse lemma: finite observed image, finite cut relation, and
finite point-style cut relation. -/
theorem finite_observation_collapse_core_package
    [Fintype Q] (q : W → Q) (L : Set W) (T : Set (CutFactor W))
    (C : Set (ObservedCutTriple Q)) :
    Set.Finite (FinObsImage q L)
      ∧ Set.Finite (FinObsCutImage q T)
      ∧ Set.Finite C
      ∧ Set.Finite (cutPointOfTriple '' C) := by
  exact ⟨finObsImage_finite_of_fintype q L,
    finObsCutImage_finite_of_fintype q T,
    observedCutRelation_finite_of_fintype C,
    cutPoint_image_finite_of_fintype C⟩

end ObservedResidualConcept
