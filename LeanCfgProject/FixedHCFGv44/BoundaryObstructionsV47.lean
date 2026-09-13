import LeanCfgProject.FixedHCFGv44.Language

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Boundary lemmas from the current TCS v47 manuscript.

This file formalizes two abstract results from Section 8:

* the finite-monoid obstruction: an infinite family of pairwise context-sharing
  factors with pairwise different distributions cannot be captured by any
  finite-monoid observer;
* closure of fixed-`h` substitutability under quotient by a fixed suffix word.

The concrete counter and Dyck corollaries can be layered on top of the first
lemma without changing the learner development.
-/

/--
The manuscript class `RS`, with the universe of the finite observer monoid
made explicit for Lean.  Since the theorem below is universe-polymorphic, it
applies to every finite-monoid observer universe.
-/
def RecognizablySubstitutableAt {Sigma : Type u} (L : Language Sigma) : Prop :=
  ∃ Obs : Observer.{u, v} Sigma, HSubstitutable Obs L

/-- Right quotient by one fixed word: `L / z = {w | wz ∈ L}`. -/
def RightQuotient {Sigma : Type u} (L : Language Sigma) (z : Word Sigma) :
    Language Sigma :=
  fun w => w ++ z ∈ L

/--
Manuscript Lemma `lem:finite-monoid-obstruction`.

If an infinite nonempty-factor family has a shared context for every distinct
pair but no two distinct members have the same distribution, then no finite
observer can witness fixed-`h` substitutability.
-/
theorem finite_monoid_obstruction_v47
    {Sigma : Type u} (L : Language Sigma) (Xi : Set (Word Sigma))
    (hXi : Xi.Infinite)
    (hInternal : ∀ x : Word Sigma, x ∈ Xi → Internal x)
    (hSeparate : ∀ x : Word Sigma, x ∈ Xi →
      ∀ y : Word Sigma, y ∈ Xi → x ≠ y →
        ShareContext L x y ∧ ¬ SameDistribution L x y) :
    ¬ RecognizablySubstitutableAt.{u, v} L := by
  intro hRS
  rcases hRS with ⟨Obs, hSub⟩
  have hMaps : Set.MapsTo (obsValue Obs) Xi (Set.univ : Set Obs.M) := by
    intro x hx
    exact Set.mem_univ _
  obtain ⟨x, hx, y, hy, hxy, htype⟩ :=
    hXi.exists_ne_map_eq_of_mapsTo hMaps
      (Set.finite_univ : (Set.univ : Set Obs.M).Finite)
  rcases hSeparate x hx y hy hxy with ⟨hShare, hDifferent⟩
  apply hDifferent
  exact hSub x y (hInternal x hx) (hInternal y hy) htype hShare

/--
Manuscript Lemma `lem:rs-fixed-quotient`, in its stronger fixed-observer form.
If `L` is fixed-`h` substitutable, then quotienting by one fixed suffix word
preserves fixed-`h` substitutability for the same observer.
-/
theorem hSubstitutable_rightQuotient_v47
    {Sigma : Type u} (Obs : Observer Sigma) (L : Language Sigma)
    (z : Word Sigma)
    (hSub : HSubstitutable Obs L) :
    HSubstitutable Obs (RightQuotient L z) := by
  intro x y hx hy htype hShareQ
  rcases hShareQ with ⟨a, b, hxQ, hyQ⟩
  have hxL : InDistribution L x a (b ++ z) := by
    change (a ++ x ++ b) ++ z ∈ L at hxQ
    change a ++ x ++ (b ++ z) ∈ L
    simpa only [List.append_assoc] using hxQ
  have hyL : InDistribution L y a (b ++ z) := by
    change (a ++ y ++ b) ++ z ∈ L at hyQ
    change a ++ y ++ (b ++ z) ∈ L
    simpa only [List.append_assoc] using hyQ
  have hDistL : SameDistribution L x y :=
    hSub x y hx hy htype ⟨a, b ++ z, hxL, hyL⟩
  intro s t
  change (s ++ x ++ t) ++ z ∈ L ↔ (s ++ y ++ t) ++ z ∈ L
  have h := hDistL s (t ++ z)
  change s ++ x ++ (t ++ z) ∈ L ↔ s ++ y ++ (t ++ z) ∈ L at h
  simpa only [List.append_assoc] using h

/-- The corresponding fixed-universe closure statement for the manuscript union class. -/
theorem recognizablySubstitutable_rightQuotient_v47
    {Sigma : Type u} {L : Language Sigma} (z : Word Sigma)
    (hRS : RecognizablySubstitutableAt.{u, v} L) :
    RecognizablySubstitutableAt.{u, v} (RightQuotient L z) := by
  rcases hRS with ⟨Obs, hSub⟩
  exact ⟨Obs, hSubstitutable_rightQuotient_v47 Obs L z hSub⟩

end FixedHCFGv44
end LeanCfgProject
