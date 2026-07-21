/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.GoldIdentificationSkeleton

/-!
# FiniteTextCoverage.lean

Sixteenth clean Lean experiment for the fixed-observation MCFG project.

`GoldIdentificationSkeleton.lean` used an explicit assumption
`TextFor.EventuallyContains S`: the finite characteristic sample `S` is
eventually contained in every positive text.

This file proves that assumption from the definition of a text and finiteness
of `S`.

The key theorem is:

```lean
TextFor.eventuallyContains_of_subset
```

If `S ⊆ L` and `T` is a text for `L`, then every word of `S` appears by some
finite stage, hence all of `S` is contained in all sufficiently late prefix
samples.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v

section FiniteTextCoverage

variable {α : Type u}
variable [DecidableEq α]
variable {L : Set (Word α)}

namespace TextFor

/-- Every finite positive sample is eventually contained in every positive text.

This discharges the standard finite-coverage step in Gold identification. -/
theorem eventuallyContains_of_subset
    (T : TextFor L)
    (S : Finset (Word α))
    (hS : (S : Set (Word α)) ⊆ L) :
    T.EventuallyContains S := by
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      intro n _hn word hword
      simp at hword
  | insert a S ha ih =>
      have hS_tail : (S : Set (Word α)) ⊆ L := by
        intro word hword
        exact hS (Finset.mem_insert.mpr (Or.inr hword))
      rcases ih hS_tail with ⟨nS, hnS⟩
      have haL : a ∈ L := by
        exact hS (Finset.mem_insert_self a S)
      rcases T.covers a haL with ⟨m, hm⟩
      refine ⟨max (m + 1) nS, ?_⟩
      intro n hn word hword
      rcases Finset.mem_insert.mp hword with hwa | hwS
      · subst hwa
        have hm_lt : m < n := by
          have hm1 : m + 1 ≤ n :=
            le_trans (le_max_left (m + 1) nS) hn
          exact Nat.lt_of_succ_le hm1
        exact Finset.mem_image.mpr
          ⟨m, Finset.mem_range.mpr hm_lt, hm⟩
      · exact hnS n (le_trans (le_max_right (m + 1) nS) hn) word hwS

/-- Every finite subset of the target is eventually contained in every text for
the target language.  This is just `eventuallyContains_of_subset` with the
arguments ordered for use in identification theorems. -/
theorem eventuallyContains_finite_subset
    (S : Finset (Word α))
    (hS : (S : Set (Word α)) ⊆ L)
    (T : TextFor L) :
    T.EventuallyContains S :=
  T.eventuallyContains_of_subset S hS

end TextFor

end FiniteTextCoverage


section GoldIdentificationFromFiniteCharacteristicSample

variable {α : Type u} {Hyp : Type v}
variable [DecidableEq α]

/-- A finite characteristic sample gives eventual correctness on every positive
text, without separately assuming eventual containment. -/
theorem characteristicSample_eventual_correct_on_every_text
    {L : Set (Word α)}
    (lang : HypLanguage α Hyp)
    (learner : SetDrivenLearner α Hyp)
    (S : Finset (Word α))
    (hChar : CharacteristicSample lang learner S L) :
    ∀ T : TextFor L, EventuallyCorrectOnText lang learner T := by
  intro T
  exact characteristicSample_eventual_correct_on_text
    lang learner S hChar T
    (T.eventuallyContains_of_subset S hChar.1)

/-- Direct form: after the finite characteristic sample has appeared in a text,
all later hypotheses are correct. -/
theorem characteristicSample_correct_after_finite_coverage
    {L : Set (Word α)}
    (lang : HypLanguage α Hyp)
    (learner : SetDrivenLearner α Hyp)
    (S : Finset (Word α))
    (hChar : CharacteristicSample lang learner S L)
    (T : TextFor L) :
    ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
      lang (learner (T.prefixSample n)) = L := by
  exact characteristicSample_eventual_correct_on_every_text
    lang learner S hChar T

/-- Final Gold-style finite-sample wrapper for one target language.

This is the cleaned version of the finite-sufficient-sample principle:
a characteristic sample is finite by being a `Finset`, and every text for the
target eventually contains it. -/
theorem finiteCharacteristicSample_identifies_target
    {L : Set (Word α)}
    (lang : HypLanguage α Hyp)
    (learner : SetDrivenLearner α Hyp)
    (S : Finset (Word α))
    (hChar : CharacteristicSample lang learner S L) :
    ∀ T : TextFor L, EventuallyCorrectOnText lang learner T :=
  characteristicSample_eventual_correct_on_every_text
    lang learner S hChar

end GoldIdentificationFromFiniteCharacteristicSample

end MCFG
