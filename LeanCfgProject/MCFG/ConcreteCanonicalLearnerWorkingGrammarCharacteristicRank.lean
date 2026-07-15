/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarRepresentationRank

/-!
# ConcreteCanonicalLearnerWorkingGrammarCharacteristicRank.lean

The preceding file introduced two sample-length complexity measures:

* the least budget for any bounded cut-compiled grammar representation;
* the least positive-sample budget at which the concrete learner outputs the
  target exactly once.

This file adds the stronger Gold-style quantity.

## Characteristic-sample budget

At budget `n`, a language `L` has a characteristic sample for the actual
working-grammar learner when there is a finite sample `S` such that

```lean
sampleLengthBudget S ≤ n
```

and `S` is characteristic for `L`.

The least such budget is

```lean
correctedConcreteWorkingGrammarCharacteristicRank.
```

Unlike exact output on one sample, a characteristic sample forces every
positive finite superset to have the target language.  Therefore the three
complexities satisfy

```text
bounded representation rank
≤ exact learner-output rank
≤ characteristic-sample rank.
```

For every semantic start-rooted target, the selected characteristic sample
from the verified construction gives a finite upper bound.  The minimum is
attained: at the characteristic rank there is an actual finite positive
characteristic sample.

Main target-level results:

```lean
startRootedTarget_characteristicAt_rank
startRootedTargetExactOutputRank_le_characteristicRank
startRootedTarget_boundedRepresentationRank_le_characteristicRank
startRootedTargetCharacteristicRank_le_selectedCharacteristicSampleLength.
```

This is a semantic positive-data complexity measure.  The file does not claim
that the minimum characteristic sample or its rank is computable.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section CharacteristicBudget

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]

/-- At total sample-length budget `n`, the actual working-grammar learner has a
characteristic sample for `L`. -/
def CorrectedConcreteWorkingGrammarCharacteristicAtBudget
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (L : Set (Word α))
    (n : Nat) :
    Prop :=
  ∃ S : Finset (Word α),
    CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L ∧
      sampleLengthBudget S ≤ n

/-- A language has some finite characteristic-sample budget for the actual
working-grammar learner. -/
def HasCorrectedConcreteWorkingGrammarCharacteristicBudget
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (L : Set (Word α)) :
    Prop :=
  ∃ n : Nat,
    CorrectedConcreteWorkingGrammarCharacteristicAtBudget
      hα obs f L n

/-- Characteristic-sample existence is upward closed in the length budget. -/
theorem correctedConcreteWorkingGrammarCharacteristicAtBudget_mono
    {hα : Nonempty α}
    {obs : α → M}
    {f : Nat}
    {L : Set (Word α)}
    {n m : Nat}
    (hnm : n ≤ m)
    (h :
      CorrectedConcreteWorkingGrammarCharacteristicAtBudget
        hα obs f L n) :
    CorrectedConcreteWorkingGrammarCharacteristicAtBudget
      hα obs f L m := by

  rcases h with
    ⟨S, hS, hlength⟩

  exact
    ⟨S,
      hS,
      hlength.trans hnm⟩

/-- Every explicit characteristic sample gives a characteristic budget equal
to its own total word length. -/
theorem correctedConcreteWorkingGrammarCharacteristicAtBudget_of_sample
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (L : Set (Word α))
    (hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L) :
    CorrectedConcreteWorkingGrammarCharacteristicAtBudget
      hα obs f L
      (sampleLengthBudget S) := by

  exact
    ⟨S,
      hS,
      Nat.le_refl _⟩

/-- Every explicit characteristic sample proves existence of a finite
characteristic budget. -/
theorem hasCharacteristicBudget_of_characteristicSample
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (L : Set (Word α))
    (hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L) :
    HasCorrectedConcreteWorkingGrammarCharacteristicBudget
      hα obs f L := by

  exact
    ⟨sampleLengthBudget S,
      correctedConcreteWorkingGrammarCharacteristicAtBudget_of_sample
        hα obs f S L hS⟩

/-- Least total word length of a characteristic sample for the actual
working-grammar learner. -/
noncomputable def correctedConcreteWorkingGrammarCharacteristicRank
    {hα : Nonempty α}
    {obs : α → M}
    {f : Nat}
    {L : Set (Word α)}
    (hL :
      HasCorrectedConcreteWorkingGrammarCharacteristicBudget
        hα obs f L) :
    Nat :=
  Nat.find hL

namespace HasCorrectedConcreteWorkingGrammarCharacteristicBudget

variable {hα : Nonempty α}
variable {obs : α → M}
variable {f : Nat}
variable {L : Set (Word α)}

/-- The minimum characteristic budget is attained. -/
theorem rank_spec
    (hL :
      HasCorrectedConcreteWorkingGrammarCharacteristicBudget
        hα obs f L) :
    CorrectedConcreteWorkingGrammarCharacteristicAtBudget
      hα obs f L
      (correctedConcreteWorkingGrammarCharacteristicRank
        hL) := by

  exact
    Nat.find_spec hL

/-- Minimality of the characteristic rank. -/
theorem rank_le_of_characteristicAtBudget
    (hL :
      HasCorrectedConcreteWorkingGrammarCharacteristicBudget
        hα obs f L)
    {n : Nat}
    (hn :
      CorrectedConcreteWorkingGrammarCharacteristicAtBudget
        hα obs f L n) :
    correctedConcreteWorkingGrammarCharacteristicRank
        hL ≤
      n := by

  exact
    Nat.find_min' hL hn

/-- Having a characteristic sample at budget `n` is equivalent to being above
the characteristic rank. -/
theorem characteristicAtBudget_iff_rank_le
    (hL :
      HasCorrectedConcreteWorkingGrammarCharacteristicBudget
        hα obs f L)
    (n : Nat) :
    CorrectedConcreteWorkingGrammarCharacteristicAtBudget
        hα obs f L n ↔
      correctedConcreteWorkingGrammarCharacteristicRank
          hL ≤
        n := by

  constructor

  · intro hn
    exact
      hL.rank_le_of_characteristicAtBudget
        hn

  · intro hrank

    exact
      correctedConcreteWorkingGrammarCharacteristicAtBudget_mono
        hrank
        hL.rank_spec

/-- No budget below the characteristic rank contains a characteristic
sample. -/
theorem not_characteristicAtBudget_of_lt_rank
    (hL :
      HasCorrectedConcreteWorkingGrammarCharacteristicBudget
        hα obs f L)
    {n : Nat}
    (hn :
      n <
        correctedConcreteWorkingGrammarCharacteristicRank
          hL) :
    ¬
      CorrectedConcreteWorkingGrammarCharacteristicAtBudget
        hα obs f L n := by

  intro hcharacteristic

  have hle :=
    hL.rank_le_of_characteristicAtBudget
      hcharacteristic

  omega

/-- The characteristic rank is witnessed by an actual finite characteristic
sample. -/
theorem exists_characteristicSample_at_rank
    (hL :
      HasCorrectedConcreteWorkingGrammarCharacteristicBudget
        hα obs f L) :
    ∃ S : Finset (Word α),
      CharacteristicSample
          (correctedConcreteWorkingGrammarHypLanguage
            obs f)
          (correctedConcreteWorkingGrammarLearner
            hα obs f)
          S L ∧
        sampleLengthBudget S ≤
          correctedConcreteWorkingGrammarCharacteristicRank
            hL := by

  exact hL.rank_spec

/-- The numerical characteristic rank is independent of the existence proof
used in its definition. -/
theorem rank_proof_irrel
    (h₁ h₂ :
      HasCorrectedConcreteWorkingGrammarCharacteristicBudget
        hα obs f L) :
    correctedConcreteWorkingGrammarCharacteristicRank
        h₁ =
      correctedConcreteWorkingGrammarCharacteristicRank
        h₂ := by

  have hp :
      h₁ = h₂ :=
    Subsingleton.elim _ _

  subst h₂

  rfl

/-- Characteristic rank zero is exactly existence of a zero-total-length
characteristic sample. -/
theorem rank_eq_zero_iff
    (hL :
      HasCorrectedConcreteWorkingGrammarCharacteristicBudget
        hα obs f L) :
    correctedConcreteWorkingGrammarCharacteristicRank
          hL =
        0 ↔
      CorrectedConcreteWorkingGrammarCharacteristicAtBudget
        hα obs f L 0 := by

  constructor

  · intro hrank

    have hspec :=
      hL.rank_spec

    simpa [hrank] using hspec

  · intro hzero

    have hle :=
      hL.rank_le_of_characteristicAtBudget
        hzero

    omega

end HasCorrectedConcreteWorkingGrammarCharacteristicBudget

end CharacteristicBudget


section CharacteristicImpliesExactOutput

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]

/-- A characteristic sample at budget `n` gives an exact learner output at the
same budget. -/
theorem exactOutputAtBudget_of_characteristicAtBudget
    {hα : Nonempty α}
    {obs : α → M}
    {f : Nat}
    {L : Set (Word α)}
    {n : Nat}
    (h :
      CorrectedConcreteWorkingGrammarCharacteristicAtBudget
        hα obs f L n) :
    CorrectedConcreteWorkingGrammarExactOutputAtBudget
      hα obs f L n := by

  rcases h with
    ⟨S, hS, hlength⟩

  exact
    ⟨S,
      hS.1,
      hlength,
      hS.2 S
        Set.Subset.rfl
        hS.1⟩

/-- Every language with a finite characteristic budget has a finite exact
learner-output budget. -/
theorem hasExactOutputBudget_of_hasCharacteristicBudget
    {hα : Nonempty α}
    {obs : α → M}
    {f : Nat}
    {L : Set (Word α)}
    (hL :
      HasCorrectedConcreteWorkingGrammarCharacteristicBudget
        hα obs f L) :
    HasCorrectedConcreteWorkingGrammarExactOutputBudget
      hα obs f L := by

  rcases hL with
    ⟨n, hn⟩

  exact
    ⟨n,
      exactOutputAtBudget_of_characteristicAtBudget
        hn⟩

/-- Exact learner-output rank is no larger than characteristic-sample rank. -/
theorem exactOutputRank_le_characteristicRank
    {hα : Nonempty α}
    {obs : α → M}
    {f : Nat}
    {L : Set (Word α)}
    (hExact :
      HasCorrectedConcreteWorkingGrammarExactOutputBudget
        hα obs f L)
    (hCharacteristic :
      HasCorrectedConcreteWorkingGrammarCharacteristicBudget
        hα obs f L) :
    correctedConcreteWorkingGrammarExactOutputRank
        hExact ≤
      correctedConcreteWorkingGrammarCharacteristicRank
        hCharacteristic := by

  apply
    hExact.rank_le_of_exactOutputAtBudget

  exact
    exactOutputAtBudget_of_characteristicAtBudget
      hCharacteristic.rank_spec

/-- Every characteristic rank also gives a bounded representation at the same
budget. -/
theorem boundedRepresentation_of_characteristicAtBudget
    {hα : Nonempty α}
    {obs : α → M}
    {f : Nat}
    {L : Set (Word α)}
    {n : Nat}
    (h :
      CorrectedConcreteWorkingGrammarCharacteristicAtBudget
        hα obs f L n) :
    L ∈
      BoundedCutCompiledWorkingGrammarLanguageClass
        (w := max u v) α f n := by

  exact
    boundedRepresentation_of_exactOutputAtBudget
      (exactOutputAtBudget_of_characteristicAtBudget
        h)

/-- A finite characteristic budget implies a finite bounded grammar
representation. -/
theorem hasBoundedRepresentation_of_hasCharacteristicBudget
    {hα : Nonempty α}
    {obs : α → M}
    {f : Nat}
    {L : Set (Word α)}
    (hL :
      HasCorrectedConcreteWorkingGrammarCharacteristicBudget
        hα obs f L) :
    HasBoundedCutCompiledWorkingGrammarRepresentation
      (w := max u v) α f L := by

  rcases hL with
    ⟨n, hn⟩

  exact
    ⟨n,
      boundedRepresentation_of_characteristicAtBudget
        hn⟩

/-- The least bounded representation budget is no larger than the
characteristic-sample rank. -/
theorem boundedRepresentationRank_le_characteristicRank
    {hα : Nonempty α}
    {obs : α → M}
    {f : Nat}
    {L : Set (Word α)}
    (hCharacteristic :
      HasCorrectedConcreteWorkingGrammarCharacteristicBudget
        hα obs f L) :
    boundedCutCompiledWorkingGrammarRepresentationRank
        (w := max u v)
        α
        (hasBoundedRepresentation_of_hasCharacteristicBudget
          hCharacteristic) ≤
      correctedConcreteWorkingGrammarCharacteristicRank
        hCharacteristic := by

  apply
    (hasBoundedRepresentation_of_hasCharacteristicBudget
      hCharacteristic).rank_le_of_mem

  exact
    boundedRepresentation_of_characteristicAtBudget
      hCharacteristic.rank_spec

/-- Full generic rank chain. -/
theorem representationRank_le_exactOutputRank_le_characteristicRank
    {hα : Nonempty α}
    {obs : α → M}
    {f : Nat}
    {L : Set (Word α)}
    (hExact :
      HasCorrectedConcreteWorkingGrammarExactOutputBudget
        hα obs f L)
    (hCharacteristic :
      HasCorrectedConcreteWorkingGrammarCharacteristicBudget
        hα obs f L) :
    boundedCutCompiledWorkingGrammarRepresentationRank
          (w := max u v)
          α
          (hasBoundedRepresentation_of_hasExactOutputBudget
            hExact) ≤
        correctedConcreteWorkingGrammarExactOutputRank
          hExact ∧
      correctedConcreteWorkingGrammarExactOutputRank
          hExact ≤
        correctedConcreteWorkingGrammarCharacteristicRank
          hCharacteristic := by

  exact
    ⟨boundedRepresentationRank_le_exactOutputRank
        hExact,
      exactOutputRank_le_characteristicRank
        hExact hCharacteristic⟩

end CharacteristicImpliesExactOutput


section CharacteristicSampleBoundsRank

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]

/-- Every explicit characteristic sample upper-bounds the least
characteristic-sample rank. -/
theorem characteristicRank_le_sampleLength
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (L : Set (Word α))
    (hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L) :
    correctedConcreteWorkingGrammarCharacteristicRank
        (hasCharacteristicBudget_of_characteristicSample
          hα obs f S L hS) ≤
      sampleLengthBudget S := by

  exact
    (hasCharacteristicBudget_of_characteristicSample
      hα obs f S L hS).rank_le_of_characteristicAtBudget
        (correctedConcreteWorkingGrammarCharacteristicAtBudget_of_sample
          hα obs f S L hS)

/-- One explicit characteristic sample gives the complete three-rank upper
chain ending at its total word length. -/
theorem rank_chain_le_characteristicSampleLength
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (L : Set (Word α))
    (hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L) :
    correctedConcreteWorkingGrammarExactOutputRank
          (hasExactOutputBudget_of_characteristicSample
            hα obs f S L hS) ≤
        correctedConcreteWorkingGrammarCharacteristicRank
          (hasCharacteristicBudget_of_characteristicSample
            hα obs f S L hS) ∧
      correctedConcreteWorkingGrammarCharacteristicRank
          (hasCharacteristicBudget_of_characteristicSample
            hα obs f S L hS) ≤
        sampleLengthBudget S := by

  exact
    ⟨exactOutputRank_le_characteristicRank
        (hasExactOutputBudget_of_characteristicSample
          hα obs f S L hS)
        (hasCharacteristicBudget_of_characteristicSample
          hα obs f S L hS),
      characteristicRank_le_sampleLength
        hα obs f S L hS⟩

end CharacteristicSampleBoundsRank


section StartRootedCharacteristicRank

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Every semantic start-rooted target has a finite characteristic-sample
budget for the actual working-grammar learner. -/
theorem startRootedTarget_hasCharacteristicBudget
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    HasCorrectedConcreteWorkingGrammarCharacteristicBudget
      hα obs f L := by

  let S :=
    startRootedCorrectedConcreteTargetCharacteristicSample
      (v := w) obs f hL

  have hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L :=
    selectedStartRootedCharacteristicSample_workingGrammar_characteristic
      (v := w) hα obs f hL

  exact
    hasCharacteristicBudget_of_characteristicSample
      hα obs f S L hS

/-- Least characteristic-sample total word length of one semantic start-rooted
target. -/
noncomputable def startRootedTargetCharacteristicRank
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    Nat :=
  correctedConcreteWorkingGrammarCharacteristicRank
    (startRootedTarget_hasCharacteristicBudget
      (v := w) hα obs f hL)

/-- At the target's characteristic rank, there exists an actual finite
characteristic sample. -/
theorem startRootedTarget_characteristicAt_rank
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    CorrectedConcreteWorkingGrammarCharacteristicAtBudget
      hα obs f L
      (startRootedTargetCharacteristicRank
        (v := w) hα obs f hL) := by

  exact
    (startRootedTarget_hasCharacteristicBudget
      (v := w) hα obs f hL).rank_spec

/-- Expanded minimum witness: a finite positive characteristic sample exists
at the target's least characteristic budget. -/
theorem startRootedTarget_exists_characteristicSample_at_rank
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    ∃ S : Finset (Word α),
      CharacteristicSample
          (correctedConcreteWorkingGrammarHypLanguage
            obs f)
          (correctedConcreteWorkingGrammarLearner
            hα obs f)
          S L ∧
        sampleLengthBudget S ≤
          startRootedTargetCharacteristicRank
            (v := w) hα obs f hL := by

  exact
    (startRootedTarget_hasCharacteristicBudget
      (v := w) hα obs f hL).exists_characteristicSample_at_rank

/-- Exact learner-output rank is bounded by the target's characteristic rank. -/
theorem startRootedTargetExactOutputRank_le_characteristicRank
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    startRootedTargetExactOutputRank
        (v := w) hα obs f hL ≤
      startRootedTargetCharacteristicRank
        (v := w) hα obs f hL := by

  unfold
    startRootedTargetExactOutputRank
    startRootedTargetCharacteristicRank

  exact
    exactOutputRank_le_characteristicRank
      (startRootedTarget_hasExactOutputBudget
        (v := w) hα obs f hL)
      (startRootedTarget_hasCharacteristicBudget
        (v := w) hα obs f hL)

/-- The bounded grammar representation rank is bounded by the target's
characteristic rank. -/
theorem startRootedTarget_boundedRepresentationRank_le_characteristicRank
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    boundedCutCompiledWorkingGrammarRepresentationRank
        (w := max u v)
        α
        (hasBoundedRepresentation_of_hasExactOutputBudget
          (startRootedTarget_hasExactOutputBudget
            (v := w) hα obs f hL)) ≤
      startRootedTargetCharacteristicRank
        (v := w) hα obs f hL := by

  exact
    (startRootedTarget_boundedRepresentationRank_le_exactOutputRank
      (v := w) hα obs f hL).trans
        (startRootedTargetExactOutputRank_le_characteristicRank
          (v := w) hα obs f hL)

/-- The selected characteristic sample from the constructive theorem
upper-bounds the least characteristic rank. -/
theorem startRootedTargetCharacteristicRank_le_selectedCharacteristicSampleLength
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    startRootedTargetCharacteristicRank
        (v := w) hα obs f hL ≤
      sampleLengthBudget
        (startRootedCorrectedConcreteTargetCharacteristicSample
          (v := w) obs f hL) := by

  let S :=
    startRootedCorrectedConcreteTargetCharacteristicSample
      (v := w) obs f hL

  have hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L :=
    selectedStartRootedCharacteristicSample_workingGrammar_characteristic
      (v := w) hα obs f hL

  unfold
    startRootedTargetCharacteristicRank

  exact
    (startRootedTarget_hasCharacteristicBudget
      (v := w) hα obs f hL).rank_le_of_characteristicAtBudget
        (correctedConcreteWorkingGrammarCharacteristicAtBudget_of_sample
          hα obs f S L hS)

/-- Every characteristic sample for the target upper-bounds its canonical
characteristic rank. -/
theorem startRootedTargetCharacteristicRank_le_sampleLength_of_characteristic
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f)
    (S : Finset (Word α))
    (hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L) :
    startRootedTargetCharacteristicRank
        (v := w) hα obs f hL ≤
      sampleLengthBudget S := by

  unfold
    startRootedTargetCharacteristicRank

  exact
    (startRootedTarget_hasCharacteristicBudget
      (v := w) hα obs f hL).rank_le_of_characteristicAtBudget
        (correctedConcreteWorkingGrammarCharacteristicAtBudget_of_sample
          hα obs f S L hS)

/-- Complete target-level rank chain ending at the selected characteristic
sample. -/
theorem startRootedTarget_fullRankChain
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    boundedCutCompiledWorkingGrammarRepresentationRank
          (w := max u v)
          α
          (hasBoundedRepresentation_of_hasExactOutputBudget
            (startRootedTarget_hasExactOutputBudget
              (v := w) hα obs f hL)) ≤
        startRootedTargetExactOutputRank
          (v := w) hα obs f hL ∧
      startRootedTargetExactOutputRank
          (v := w) hα obs f hL ≤
        startRootedTargetCharacteristicRank
          (v := w) hα obs f hL ∧
      startRootedTargetCharacteristicRank
          (v := w) hα obs f hL ≤
        sampleLengthBudget
          (startRootedCorrectedConcreteTargetCharacteristicSample
            (v := w) obs f hL) := by

  exact
    ⟨startRootedTarget_boundedRepresentationRank_le_exactOutputRank
        (v := w) hα obs f hL,
      startRootedTargetExactOutputRank_le_characteristicRank
        (v := w) hα obs f hL,
      startRootedTargetCharacteristicRank_le_selectedCharacteristicSampleLength
        (v := w) hα obs f hL⟩

end StartRootedCharacteristicRank


section CharacteristicRankPackages

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Paper-facing characteristic-complexity package for every semantic
start-rooted target. -/
theorem correctedConcreteWorkingGrammarLearner_characteristicRank_package :
    ∀ L : Set (Word α),
      ∀ hL :
        L ∈ StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f,
      CorrectedConcreteWorkingGrammarCharacteristicAtBudget
          hα obs f L
          (startRootedTargetCharacteristicRank
            (v := w) hα obs f hL) ∧
        startRootedTargetExactOutputRank
            (v := w) hα obs f hL ≤
          startRootedTargetCharacteristicRank
            (v := w) hα obs f hL ∧
        startRootedTargetCharacteristicRank
            (v := w) hα obs f hL ≤
          sampleLengthBudget
            (startRootedCorrectedConcreteTargetCharacteristicSample
              (v := w) obs f hL) := by

  intro L hL

  exact
    ⟨startRootedTarget_characteristicAt_rank
        (v := w) hα obs f hL,
      startRootedTargetExactOutputRank_le_characteristicRank
        (v := w) hα obs f hL,
      startRootedTargetCharacteristicRank_le_selectedCharacteristicSampleLength
        (v := w) hα obs f hL⟩

/-- Final identification-and-rank endpoint.

Every target is identified by the actual grammar-valued learner and carries
the full finite complexity chain

```text
representation ≤ exact output ≤ characteristic ≤ selected sample length.
``` -/
theorem correctedConcreteWorkingGrammarLearner_identification_characteristicRank_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (∀ L : Set (Word α),
        ∀ hL :
          L ∈ StartRootedCorrectedConcreteTargetClass
            (v := w) α M obs f,
        boundedCutCompiledWorkingGrammarRepresentationRank
              (w := max u v)
              α
              (hasBoundedRepresentation_of_hasExactOutputBudget
                (startRootedTarget_hasExactOutputBudget
                  (v := w) hα obs f hL)) ≤
            startRootedTargetExactOutputRank
              (v := w) hα obs f hL ∧
          startRootedTargetExactOutputRank
              (v := w) hα obs f hL ≤
            startRootedTargetCharacteristicRank
              (v := w) hα obs f hL ∧
          startRootedTargetCharacteristicRank
              (v := w) hα obs f hL ≤
            sampleLengthBudget
              (startRootedCorrectedConcreteTargetCharacteristicSample
                (v := w) obs f hL)) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      fun L hL =>
        startRootedTarget_fullRankChain
          (v := w) hα obs f hL⟩

end CharacteristicRankPackages

end MCFG
