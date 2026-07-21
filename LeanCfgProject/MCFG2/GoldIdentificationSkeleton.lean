/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ExactReconstructionSkeleton

/-!
# GoldIdentificationSkeleton.lean

Fifteenth clean Lean experiment for the fixed-observation MCFG project.

This file formalizes the Gold-identification skeleton used after exact
reconstruction.

The paper's learner is set-driven: it maps a finite positive sample to a
hypothesis.  Once a finite characteristic sample `S` is included in the current
prefix sample, all later hypotheses have the target language.

This file deliberately avoids committing to the concrete canonical learner.
It proves the general finite-sufficient-sample principle for any set-driven
finite-sample learner.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v

section Texts

variable {α : Type u}

/-- A positive text for a language `L`.

The text enumerates only elements of `L`, and every element of `L` appears at
least once. -/
structure TextFor (L : Set (Word α)) where
  text : Nat → Word α
  text_mem : ∀ n : Nat, text n ∈ L
  covers : ∀ word : Word α, word ∈ L → ∃ n : Nat, text n = word

namespace TextFor

variable [DecidableEq α]

/-- The finite set of examples seen before stage `n`. -/
def prefixSample (T : TextFor (α := α) L) (n : Nat) : Finset (Word α) :=
  (Finset.range n).image T.text

/-- Every prefix sample of a positive text is positive. -/
theorem prefixSample_subset
    {L : Set (Word α)}
    (T : TextFor L) (n : Nat) :
    (T.prefixSample n : Set (Word α)) ⊆ L := by
  intro word hword
  rcases Finset.mem_image.mp hword with ⟨i, _hi, rfl⟩
  exact T.text_mem i

/-- Prefix samples are monotone in the stage index. -/
theorem prefixSample_mono
    {L : Set (Word α)}
    (T : TextFor L) {m n : Nat}
    (hmn : m ≤ n) :
    (T.prefixSample m : Set (Word α)) ⊆
      (T.prefixSample n : Set (Word α)) := by
  intro word hword
  rcases Finset.mem_image.mp hword with ⟨i, hi, rfl⟩
  exact Finset.mem_image.mpr
    ⟨i, Finset.mem_range.mpr
      (Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) hmn), rfl⟩

/-- A finite set `S` is eventually contained in the prefix samples of a text. -/
def EventuallyContains
    {L : Set (Word α)}
    (T : TextFor L) (S : Finset (Word α)) : Prop :=
  ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
    (S : Set (Word α)) ⊆ (T.prefixSample n : Set (Word α))

/-- If `S` is eventually contained at stage `n0`, then it is contained in all
later prefix samples.  This is just the unpacked form, useful for later files. -/
theorem eventuallyContains_elim
    {L : Set (Word α)}
    (T : TextFor L) (S : Finset (Word α))
    (hS : T.EventuallyContains S) :
    ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
      (S : Set (Word α)) ⊆ (T.prefixSample n : Set (Word α)) :=
  hS

end TextFor

end Texts


section Identification

variable {α : Type u} {Hyp : Type v}
variable [DecidableEq α]

/-- A learner is represented by a function from finite samples to hypotheses,
together with a language interpretation for hypotheses. -/
abbrev SetDrivenLearner (α : Type u) (Hyp : Type v) :=
  Finset (Word α) → Hyp

/-- A learner is eventually correct on a particular text. -/
def EventuallyCorrectOnText
    {L : Set (Word α)}
    (lang : HypLanguage α Hyp)
    (learner : SetDrivenLearner α Hyp)
    (T : TextFor L) : Prop :=
  ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
    lang (learner (T.prefixSample n)) = L

/-- Finite characteristic samples imply eventual correctness on every text whose
prefix samples eventually contain the characteristic sample. -/
theorem characteristicSample_eventual_correct_on_text
    {L : Set (Word α)}
    (lang : HypLanguage α Hyp)
    (learner : SetDrivenLearner α Hyp)
    (S : Finset (Word α))
    (hChar : CharacteristicSample lang learner S L)
    (T : TextFor L)
    (hEvent : T.EventuallyContains S) :
    EventuallyCorrectOnText lang learner T := by
  rcases hEvent with ⟨n0, hcontains⟩
  refine ⟨n0, ?_⟩
  intro n hn
  exact hChar.2 (T.prefixSample n)
    (hcontains n hn)
    (T.prefixSample_subset n)

/-- A slightly more direct version using an already-known stage `n0`. -/
theorem characteristicSample_correct_after_stage
    {L : Set (Word α)}
    (lang : HypLanguage α Hyp)
    (learner : SetDrivenLearner α Hyp)
    (S : Finset (Word α))
    (hChar : CharacteristicSample lang learner S L)
    (T : TextFor L)
    {n0 : Nat}
    (hcontains : ∀ n : Nat, n0 ≤ n →
      (S : Set (Word α)) ⊆ (T.prefixSample n : Set (Word α))) :
    ∀ n : Nat, n0 ≤ n →
      lang (learner (T.prefixSample n)) = L := by
  intro n hn
  exact hChar.2 (T.prefixSample n)
    (hcontains n hn)
    (T.prefixSample_subset n)

/-- If a characteristic sample is eventually seen on every text, then the
learner identifies the target language on every text. -/
theorem characteristicSample_identifies_target
    {L : Set (Word α)}
    (lang : HypLanguage α Hyp)
    (learner : SetDrivenLearner α Hyp)
    (S : Finset (Word α))
    (hChar : CharacteristicSample lang learner S L)
    (hEveryText :
      ∀ T : TextFor L, T.EventuallyContains S) :
    ∀ T : TextFor L, EventuallyCorrectOnText lang learner T := by
  intro T
  exact characteristicSample_eventual_correct_on_text
    lang learner S hChar T (hEveryText T)

end Identification


section ExactReconstructionAsCharacteristicSample

variable {α : Type u} {Hyp : Type v}
variable [DecidableEq α]

/-- A reusable wrapper: if some exact-reconstruction theorem gives the
characteristic-sample condition for `S`, then the Gold-identification conclusion
follows immediately. -/
theorem exactReconstruction_characteristicSample_identifies
    {L : Set (Word α)}
    (lang : HypLanguage α Hyp)
    (learner : SetDrivenLearner α Hyp)
    (S : Finset (Word α))
    (hChar : CharacteristicSample lang learner S L)
    (hEveryText :
      ∀ T : TextFor L, T.EventuallyContains S) :
    ∀ T : TextFor L, EventuallyCorrectOnText lang learner T :=
  characteristicSample_identifies_target
    lang learner S hChar hEveryText

end ExactReconstructionAsCharacteristicSample

end MCFG
