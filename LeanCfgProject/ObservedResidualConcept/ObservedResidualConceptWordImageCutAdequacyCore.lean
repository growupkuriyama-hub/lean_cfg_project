import LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCutAdequacyCore
import LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptClosureHomCore

/-!
# Word-image cut adequacy core

This file moves the checked cut-adequacy theorem one step closer to the paper's
CFG statement.

`ObservedResidualConceptCutAdequacyCore` proves the abstract set-theoretic core:
if an observed cut point is dense, then any sound observed image containing that
point is adequate.

Here we add the word/image bridge used in the paper:

* a word-level cut occurrence `(ell,w,r)` observed by `q` gives an
  `ObservedCutPoint`;
* a state/yield set `Y` contributes the observed image `q '' Y`;
* if `w ∈ Y` and `q '' Y` is sound for the cut residual, then cut density implies
  adequacy of `q '' Y`;
* conversely, if every sound word-image containing the middle word is adequate,
  then the cut is dense, by testing the singleton yield `{w}`.

This is still not the full CFG cut-realization lemma.  It is the theorem-body
bridge from word-level state images to the observed cut-adequacy core.
-/

open Set

universe u v

namespace ObservedResidualConcept

variable {W : Type u} {Q : Type v}

section WordCut

variable [Monoid Q]

/-- A word-level cut occurrence `(left, middle, right)`.

In the paper this is a factorization `ell w r ∈ L`; the language membership
itself is intentionally not part of this lightweight structure. -/
structure WordCutOccurrence (W : Type u) where
  left : W
  middle : W
  right : W

namespace WordCutOccurrence

/-- Observe a word-level cut occurrence as an `ObservedCutPoint`. -/
def toObservedCutPoint (q : W → Q) (c : WordCutOccurrence W) :
    ObservedCutPoint Q :=
  ⟨q c.left, q c.middle, q c.right⟩

/-- The residual selected by the observed outer frame of a word cut. -/
def residual (S : Set Q) (q : W → Q) (c : WordCutOccurrence W) : Set Q :=
  (c.toObservedCutPoint q).residual S

/-- Occupancy of the observed cut point. -/
def Occupied (S : Set Q) (q : W → Q) (c : WordCutOccurrence W) : Prop :=
  (c.toObservedCutPoint q).Occupied S

/-- Point density of the observed middle word. -/
def PointDense (S : Set Q) (q : W → Q) (c : WordCutOccurrence W) : Prop :=
  (c.toObservedCutPoint q).PointDense S

/-- Soundness of a word/yield set for the cut frame after observation. -/
def WordImageSound (S : Set Q) (q : W → Q)
    (c : WordCutOccurrence W) (Y : Set W) : Prop :=
  q '' Y ⊆ c.residual S q

/-- Adequacy of a word/yield set for the cut frame after observation. -/
def WordImageAdequate (S : Set Q) (q : W → Q)
    (c : WordCutOccurrence W) (Y : Set W) : Prop :=
  cl S (q '' Y) = c.residual S q

end WordCutOccurrence

open WordCutOccurrence

/-- The image of a singleton word set is the singleton of the image. -/
theorem image_singleton_word (q : W → Q) (w : W) :
    q '' ({w} : Set W) = ({q w} : Set Q) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    simp at hy
    subst y
    simp
  · intro hx
    simp at hx
    subst x
    exact ⟨w, by simp, rfl⟩

/-- Forward bridge from cut density to adequacy of a word-level state image.

This is the direct Lean analogue of the main step in Theorem F:
a witnessed yield set whose observed image is sound and contains the occupied
middle word is adequate whenever the cut point is dense. -/
theorem word_cut_dense_generates_word_image
    {S : Set Q} {q : W → Q} {c : WordCutOccurrence W} {Y : Set W}
    (hdense : c.PointDense S q)
    (hsound : c.WordImageSound S q Y)
    (hcontains : c.middle ∈ Y) :
    c.WordImageAdequate S q Y := by
  have hcontainsObs :
      (c.toObservedCutPoint q).ContainsMiddle (q '' Y) := by
    exact ⟨c.middle, hcontains, rfl⟩
  have hAdeq :=
    cut_dense_point_generates_sound_image
      (S := S) (c := c.toObservedCutPoint q) (U := q '' Y)
      hdense hsound hcontainsObs
  simpa [WordCutOccurrence.WordImageAdequate,
    WordCutOccurrence.WordImageSound,
    WordCutOccurrence.residual] using hAdeq

/-- One-cut word-image version of the universal adequacy equivalence.

The reverse direction tests the singleton yield `{middle}`. -/
theorem universal_word_image_adequacy_for_one_cut_iff_pointDense
    (S : Set Q) (q : W → Q) (c : WordCutOccurrence W)
    (hOcc : c.Occupied S q) :
    c.PointDense S q ↔
      ∀ Y : Set W,
        c.WordImageSound S q Y →
        c.middle ∈ Y →
        c.WordImageAdequate S q Y := by
  constructor
  · intro hdense Y hsound hcontains
    exact word_cut_dense_generates_word_image
      (S := S) (q := q) (c := c) (Y := Y)
      hdense hsound hcontains
  · intro hUniversal
    have hsound : c.WordImageSound S q ({c.middle} : Set W) := by
      intro x hx
      have hx' : x ∈ ({q c.middle} : Set Q) := by
        simpa [image_singleton_word q c.middle] using hx
      simp at hx'
      subst x
      exact hOcc
    have hcontains : c.middle ∈ ({c.middle} : Set W) := by
      simp
    have hAdeqWord :=
      hUniversal ({c.middle} : Set W) hsound hcontains
    have hAdeqObs :
        (c.toObservedCutPoint q).AdequateImage S
          ({(c.toObservedCutPoint q).middle} : Set Q) := by
      simpa [WordCutOccurrence.WordImageAdequate,
        WordCutOccurrence.residual,
        WordCutOccurrence.toObservedCutPoint,
        image_singleton_word q c.middle] using hAdeqWord
    exact (singleton_adequacy_iff_pointDense S (c.toObservedCutPoint q)).mp hAdeqObs

/-- A set of word-level cuts is dense after observation. -/
def WordCutDense (S : Set Q) (q : W → Q)
    (C : Set (WordCutOccurrence W)) : Prop :=
  ∀ c ∈ C, c.PointDense S q

/-- Universal adequacy for all word images containing the middle word of each
declared word-level cut. -/
def UniversalWordImageAdequacy (S : Set Q) (q : W → Q)
    (C : Set (WordCutOccurrence W)) : Prop :=
  ∀ c ∈ C, ∀ Y : Set W,
    c.WordImageSound S q Y →
    c.middle ∈ Y →
    c.WordImageAdequate S q Y

/-- Cut-density is equivalent to universal adequacy for word images, over a set
of occupied word-level cuts. -/
theorem universal_word_image_adequacy_iff_word_cut_density
    (S : Set Q) (q : W → Q) (C : Set (WordCutOccurrence W))
    (hOcc : ∀ c ∈ C, c.Occupied S q) :
    WordCutDense S q C ↔ UniversalWordImageAdequacy S q C := by
  constructor
  · intro hDense c hc Y hsound hcontains
    exact word_cut_dense_generates_word_image
      (S := S) (q := q) (c := c) (Y := Y)
      (hDense c hc) hsound hcontains
  · intro hUniv c hc
    exact (universal_word_image_adequacy_for_one_cut_iff_pointDense
      (S := S) (q := q) (c := c) (hOcc c hc)).mpr
      (hUniv c hc)

/-- Single-block residuals imply word-level cut density. -/
theorem word_cut_pointDense_of_residual_single_Approx_block
    {S : Set Q} {q : W → Q} {c : WordCutOccurrence W}
    (hOcc : c.Occupied S q)
    (hBlock : ∀ x ∈ c.residual S q, Approx S x (q c.middle)) :
    c.PointDense S q := by
  exact pointDense_of_residual_single_Approx_block
    (S := S) (c := c.toObservedCutPoint q)
    hOcc hBlock

/-- Paper-facing package for the word-image cut adequacy bridge. -/
theorem word_image_cut_adequacy_core_package
    (S : Set Q) (q : W → Q) (C : Set (WordCutOccurrence W))
    (hOcc : ∀ c ∈ C, c.Occupied S q) :
    (WordCutDense S q C ↔ UniversalWordImageAdequacy S q C)
      ∧
    (∀ c ∈ C,
      (∀ x ∈ c.residual S q, Approx S x (q c.middle)) →
      c.PointDense S q) := by
  constructor
  · exact universal_word_image_adequacy_iff_word_cut_density S q C hOcc
  · intro c hc hBlock
    exact word_cut_pointDense_of_residual_single_Approx_block
      (S := S) (q := q) (c := c) (hOcc c hc) hBlock

end WordCut

end ObservedResidualConcept
