/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarFinalDescriptionPackage

/-!
# ConcreteCanonicalLearnerWorkingGrammarCheckedBitRepresentation.lean

The existing bounded-representation hierarchy records

* an actual finite `WorkingMCFG`;
* a complete finite nonterminal enumeration;
* the cut-compiled structural conditions;
* exact language equality; and
* a presentation-item budget indexed by total sample length.

The preceding description-size files add a checked, prefix-free, logarithmic
bit serialization of the actual learner output.  This file combines the two
layers into one reusable certified representation object.

A checked bit-bounded representation stores

```text
bounded working-grammar representation
+ presentation type and presentation value
+ bit list and decoder
+ decoder round trip
+ paper-power bit-length bound.
```

Its bit budget at level `n` is

```lean
correctedConcreteCompiledGrammarPaperPowerBitBound n f.
```

We first prove that this budget is monotone in `n`.  Hence the checked
bit-bounded language classes form an increasing hierarchy.

For every finite positive sample `K`, the actual canonical learner output
produces a member of the hierarchy at level

```lean
sampleLengthBudget K.
```

The stored bits are exactly

```lean
correctedConcreteWorkingGrammarLearnerLogarithmicBitList hα obs f K,
```

and their decoder returns the complete tagged presentation of the same actual
cut-compiled grammar.

Finally, every semantic start-rooted target belongs to some finite checked
bit-bounded level.  The witnessing level is the total length of one finite
positive characteristic sample.

This upgrades the earlier item-count hierarchy to an actual checked bit-length
hierarchy.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section PaperPowerBudgetMonotonicity

/-- The exponent of the final paper-power bit budget is monotone in total
sample length. -/
theorem
    correctedConcreteCompiledGrammarPaperPowerExponent_mono_sampleLength
    {s t f : Nat}
    (hst : s <= t) :
    correctedConcreteCompiledGrammarPaperPowerExponent s f <=
      correctedConcreteCompiledGrammarPaperPowerExponent t f := by

  unfold
    correctedConcreteCompiledGrammarPaperPowerExponent

  exact
    Nat.mul_le_mul_right
      13
      (correctedLearnerPaperExponent_mono_sampleLength
        hst)

/-- The final single-power checked bit budget is monotone in total sample
length. -/
theorem
    correctedConcreteCompiledGrammarPaperPowerBitBound_mono_sampleLength
    {s t f : Nat}
    (hst : s <= t) :
    correctedConcreteCompiledGrammarPaperPowerBitBound s f <=
      correctedConcreteCompiledGrammarPaperPowerBitBound t f := by

  unfold
    correctedConcreteCompiledGrammarPaperPowerBitBound

  exact
    nat_pow_le_pow_mixed
      (correctedLearnerPaperBase_mono_sampleLength
        hst)
      (correctedLearnerPaperBase_gt_one
        t f)
      (correctedConcreteCompiledGrammarPaperPowerExponent_mono_sampleLength
        hst)

end PaperPowerBudgetMonotonicity


section CheckedBitBoundedRepresentation

variable (α : Type u)

/-- An actual bounded cut-compiled working grammar equipped with a checked
finite bit presentation.

The abstract `Presentation` field lets this certificate be reused for any
checked presentation format.  The canonical learner instantiation below uses
the complete tagged presentation-entry list. -/
structure CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
    (f n : Nat)
    (L : Set (Word α)) where

  bounded :
    BoundedCutCompiledWorkingGrammarRepresentation
      (w := w) α f n L

  Presentation :
    Type z

  presentation :
    Presentation

  bits :
    List Bool

  decode :
    List Bool → Option Presentation

  decode_bits :
    decode bits = some presentation

  bitLength_le :
    bits.length <=
      correctedConcreteCompiledGrammarPaperPowerBitBound
        n f

/-- Languages possessing a checked bit-bounded cut-compiled representation at
budget level `n`. -/
def CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
    (f n : Nat) :
    Set (Set (Word α)) :=
  {L |
    Nonempty
      (CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) (z := z) α f n L)}

namespace CheckedBitBoundedCutCompiledWorkingGrammarRepresentation

variable {α : Type u}
variable {f n : Nat}
variable {L : Set (Word α)}

/-- Forget the checked bit presentation and retain the previously verified
bounded grammar representation. -/
def forgetBits
    (R :
      CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) (z := z) α f n L) :
    BoundedCutCompiledWorkingGrammarRepresentation
      (w := w) α f n L :=
  R.bounded

/-- The represented grammar has exactly the target language. -/
theorem grammar_language_eq
    (R :
      CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) (z := z) α f n L) :
    R.bounded.grammar.StringLanguage = L :=
  R.bounded.language_eq

/-- The stored bit list is accepted by its stored decoder. -/
theorem checked_decode
    (R :
      CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) (z := z) α f n L) :
    R.decode R.bits = some R.presentation :=
  R.decode_bits

/-- Raise the sample-length budget while retaining the same actual grammar and
the same checked bit presentation. -/
def raiseBudget
    {m : Nat}
    (R :
      CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) (z := z) α f n L)
    (hnm : n <= m) :
    CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
      (w := w) (z := z) α f m L where

  bounded :=
    R.bounded.mono hnm

  Presentation :=
    R.Presentation

  presentation :=
    R.presentation

  bits :=
    R.bits

  decode :=
    R.decode

  decode_bits :=
    R.decode_bits

  bitLength_le :=
    R.bitLength_le.trans
      (correctedConcreteCompiledGrammarPaperPowerBitBound_mono_sampleLength
        hnm)

/-- Every checked bit-bounded representation yields membership in the older
presentation-item hierarchy. -/
theorem target_mem_boundedClass
    (R :
      CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) (z := z) α f n L) :
    L ∈
      BoundedCutCompiledWorkingGrammarLanguageClass
        (w := w) α f n := by

  exact
    ⟨R.bounded⟩

end CheckedBitBoundedCutCompiledWorkingGrammarRepresentation

end CheckedBitBoundedRepresentation


section CheckedBitBoundedClassHierarchy

variable {α : Type u}

/-- The checked bit-bounded language classes form an increasing hierarchy. -/
theorem
    checkedBitBoundedCutCompiledWorkingGrammarLanguageClass_mono
    {f n m : Nat}
    (hnm : n <= m) :
    CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
        (w := w) (z := z) α f n ⊆
      CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
        (w := w) (z := z) α f m := by

  intro L hL

  rcases hL with
    ⟨R⟩

  exact
    ⟨R.raiseBudget hnm⟩

/-- Every checked bit-bounded class is contained in the earlier item-count
bounded class at the same sample-length level. -/
theorem
    checkedBitBoundedCutCompiledWorkingGrammarLanguageClass_subset_bounded
    (f n : Nat) :
    CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
        (w := w) (z := z) α f n ⊆
      BoundedCutCompiledWorkingGrammarLanguageClass
        (w := w) α f n := by

  intro L hL

  rcases hL with
    ⟨R⟩

  exact
    R.target_mem_boundedClass

/-- Existence of a checked bit-bounded representation implies existence of an
ordinary bounded representation. -/
theorem
    exists_checkedBitBoundedRepresentation_implies_bounded
    {f : Nat}
    {L : Set (Word α)}
    (hL :
      ∃ n : Nat,
        L ∈
          CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
            (w := w) (z := z) α f n) :
    ∃ n : Nat,
      L ∈
        BoundedCutCompiledWorkingGrammarLanguageClass
          (w := w) α f n := by

  rcases hL with
    ⟨n, hn⟩

  exact
    ⟨n,
      checkedBitBoundedCutCompiledWorkingGrammarLanguageClass_subset_bounded
        (w := w) (z := z) f n hn⟩

end CheckedBitBoundedClassHierarchy


section CanonicalLearnerCheckedBitRepresentation

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- The actual canonical learner output on `K`, equipped simultaneously with

* its complete bounded working-grammar representation;
* its complete tagged presentation;
* its checked logarithmic bit list;
* its decoder round trip; and
* the final paper-power bit budget at `sampleLengthBudget K`. -/
noncomputable def
    correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
      (w := max u v)
      (z := max u v)
      α f
      (sampleLengthBudget K)
      (CorrectedConcreteCanonicalLearnerLanguage
        K obs f) := by

  let H :=
    correctedConcreteFiniteHypothesis
      K obs f

  let dummy :=
    Classical.choice hα

  exact
    { bounded :=
        correctedConcreteWorkingGrammarLearner_boundedRepresentation
          hα obs f K

      Presentation :=
        List
          (CorrectedConcreteCompiledGrammarPresentationEntry
            H)

      presentation :=
        H.compiledGrammarPresentationEntries
          dummy

      bits :=
        correctedConcreteWorkingGrammarLearnerLogarithmicBitList
          hα obs f K

      decode :=
        correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
          hα obs f K

      decode_bits := by
        exact
          correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode_encode
            hα obs f K

      bitLength_le := by
        exact
          correctedConcreteWorkingGrammarLearnerLogarithmicBitList_length_le_paperPower
            hα obs f K }

/-- The grammar stored in the checked representation is the actual learner
output grammar. -/
@[simp] theorem
    correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation_grammar
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
        hα obs f K).bounded.grammar =
      (correctedConcreteWorkingGrammarLearner
        hα obs f K).grammar := by

  rfl

/-- The bit list stored in the checked representation is exactly the learner's
checked logarithmic bit list. -/
@[simp] theorem
    correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation_bits
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
        hα obs f K).bits =
      correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f K := by

  rfl

/-- The presentation stored in the checked representation is the complete
tagged presentation of the actual cut compilation. -/
@[simp] theorem
    correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation_presentation
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
        hα obs f K).presentation =
      (correctedConcreteFiniteHypothesis K obs f).
        compiledGrammarPresentationEntries
          (Classical.choice hα) := by

  rfl

/-- Every canonical sample language belongs to the checked bit-bounded
hierarchy at its own total sample length. -/
theorem
    correctedConcreteCanonicalLearnerLanguage_mem_checkedBitBoundedClass
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    CorrectedConcreteCanonicalLearnerLanguage
        K obs f ∈
      CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
        (w := max u v)
        (z := max u v)
        α f
        (sampleLengthBudget K) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
      hα obs f K⟩

/-- The actual learner output language belongs to the checked hierarchy at its
own sample-length level. -/
theorem
    correctedConcreteWorkingGrammarLearner_language_mem_checkedBitBoundedClass
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearner
        hα obs f K).grammar.StringLanguage ∈
      CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
        (w := max u v)
        (z := max u v)
        α f
        (sampleLengthBudget K) := by

  rw [
    correctedConcreteWorkingGrammarLearner_stringLanguage_eq_corrected
  ]

  exact
    correctedConcreteCanonicalLearnerLanguage_mem_checkedBitBoundedClass
      hα obs f K

/-- Compact certificate package for one finite learner output. -/
theorem
    correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation_package
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    ((correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
        hα obs f K).bounded.grammar =
      (correctedConcreteWorkingGrammarLearner
        hα obs f K).grammar) ∧
      ((correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
          hα obs f K).decode
          (correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
            hα obs f K).bits =
        some
          (correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
            hα obs f K).presentation) ∧
      ((correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
          hα obs f K).bits.length <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
          (sampleLengthBudget K) f) ∧
      ((correctedConcreteWorkingGrammarLearner
          hα obs f K).grammar.StringLanguage ∈
        CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
          (w := max u v)
          (z := max u v)
          α f
          (sampleLengthBudget K)) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation_grammar
        hα obs f K,
      (correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
        hα obs f K).decode_bits,
      (correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
        hα obs f K).bitLength_le,
      correctedConcreteWorkingGrammarLearner_language_mem_checkedBitBoundedClass
        hα obs f K⟩

end CanonicalLearnerCheckedBitRepresentation


section CheckedBitBoundedTargetWitness

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- A positive finite sample together with an exact checked bit-bounded actual
working-grammar representation of the target language. -/
structure CorrectedConcreteCheckedBitBoundedWorkingGrammarTargetWitness
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (L : Set (Word α)) where

  sample :
    Finset (Word α)

  sample_positive :
    (sample : Set (Word α)) ⊆ L

  representation :
    CheckedBitBoundedCutCompiledWorkingGrammarRepresentation
      (w := max u v)
      (z := max u v)
      α f
      (sampleLengthBudget sample)
      L

namespace CorrectedConcreteCheckedBitBoundedWorkingGrammarTargetWitness

variable {hα : Nonempty α}
variable {obs : α → M}
variable {f : Nat}
variable {L : Set (Word α)}

/-- A checked bit-bounded target witness gives membership at its finite sample
length level. -/
theorem target_mem_checkedBitBoundedClass
    (W :
      CorrectedConcreteCheckedBitBoundedWorkingGrammarTargetWitness
        hα obs f L) :
    L ∈
      CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
        (w := max u v)
        (z := max u v)
        α f
        (sampleLengthBudget W.sample) := by

  exact
    ⟨W.representation⟩

/-- Forget the bit-level certificate and retain the older bounded target
witness. -/
def forgetBits
    (W :
      CorrectedConcreteCheckedBitBoundedWorkingGrammarTargetWitness
        hα obs f L) :
    CorrectedConcreteBoundedWorkingGrammarTargetWitness
      hα obs f L where

  sample :=
    W.sample

  sample_positive :=
    W.sample_positive

  representation :=
    W.representation.bounded

end CorrectedConcreteCheckedBitBoundedWorkingGrammarTargetWitness

end CheckedBitBoundedTargetWitness


section CharacteristicSampleToCheckedBitWitness

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- A characteristic sample yields an exact target representation with a checked
bit presentation at that sample's total length. -/
noncomputable def
    correctedConcreteCheckedBitBoundedWorkingGrammarTargetWitness_of_characteristicSample
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
    CorrectedConcreteCheckedBitBoundedWorkingGrammarTargetWitness
      hα obs f L := by

  let checked :=
    correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
      hα obs f S

  let boundedWitness :=
    correctedConcreteBoundedWorkingGrammarTargetWitness_of_characteristicSample
      hα obs f S L hS

  exact
    { sample :=
        S

      sample_positive :=
        hS.1

      representation :=
        { bounded :=
            boundedWitness.representation

          Presentation :=
            checked.Presentation

          presentation :=
            checked.presentation

          bits :=
            checked.bits

          decode :=
            checked.decode

          decode_bits :=
            checked.decode_bits

          bitLength_le :=
            checked.bitLength_le } }

/-- Membership form of the characteristic-sample checked bit representation. -/
theorem
    target_mem_checkedBitBoundedClass_of_characteristicSample
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
    L ∈
      CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
        (w := max u v)
        (z := max u v)
        α f
        (sampleLengthBudget S) := by

  exact
    ⟨(correctedConcreteCheckedBitBoundedWorkingGrammarTargetWitness_of_characteristicSample
        hα obs f S L hS).representation⟩

end CharacteristicSampleToCheckedBitWitness


section StartRootedCheckedBitHierarchy

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Every semantic start-rooted target has a finite positive checked bit-bounded
actual grammar certificate. -/
theorem
    correctedConcreteWorkingGrammarLearner_exists_checkedBitBoundedTargetWitness
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    Nonempty
      (CorrectedConcreteCheckedBitBoundedWorkingGrammarTargetWitness
        hα obs f L) := by

  obtain
    ⟨S, hS⟩ :=
      correctedConcreteWorkingGrammarLearner_characteristicSample_for_startRootedTargetClass
        (v := w) hα obs f hL

  exact
    ⟨correctedConcreteCheckedBitBoundedWorkingGrammarTargetWitness_of_characteristicSample
      hα obs f S L hS⟩

/-- Every semantic target lies at some finite checked bit-bounded level. -/
theorem
    startRootedTarget_mem_some_checkedBitBoundedCutCompiledClass
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    ∃ n : Nat,
      L ∈
        CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
          (w := max u v)
          (z := max u v)
          α f n := by

  rcases
      correctedConcreteWorkingGrammarLearner_exists_checkedBitBoundedTargetWitness
        (v := w) hα obs f hL with
    ⟨W⟩

  exact
    ⟨sampleLengthBudget W.sample,
      W.target_mem_checkedBitBoundedClass⟩

/-- Class-level inclusion into the union of finite checked bit-bounded levels. -/
theorem
    startRootedTargetClass_subset_exists_checkedBitBoundedCutCompiledClass :
    StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f ⊆
      {L : Set (Word α) |
        ∃ n : Nat,
          L ∈
            CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
              (w := max u v)
              (z := max u v)
              α f n} := by

  intro L hL

  exact
    startRootedTarget_mem_some_checkedBitBoundedCutCompiledClass
      (v := w) hα obs f hL

/-- Expanded positive-sample witness form. -/
theorem
    correctedConcreteWorkingGrammarLearner_exists_positive_checkedBitBoundedRepresentation
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ L ∧
      L ∈
        CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
          (w := max u v)
          (z := max u v)
          α f
          (sampleLengthBudget S) := by

  rcases
      correctedConcreteWorkingGrammarLearner_exists_checkedBitBoundedTargetWitness
        (v := w) hα obs f hL with
    ⟨W⟩

  exact
    ⟨W.sample,
      W.sample_positive,
      W.target_mem_checkedBitBoundedClass⟩

end StartRootedCheckedBitHierarchy


section CheckedBitHierarchyPackages

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Paper-facing checked bit-bounded representation hierarchy package. -/
theorem
    correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentationHierarchy_package :
    (∀ n m : Nat,
      n <= m →
      CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
          (w := max u v)
          (z := max u v)
          α f n ⊆
        CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
          (w := max u v)
          (z := max u v)
          α f m) ∧
      (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f ⊆
        {L : Set (Word α) |
          ∃ n : Nat,
            L ∈
              CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
                (w := max u v)
                (z := max u v)
                α f n}) ∧
      (∀ K : Finset (Word α),
        CorrectedConcreteCanonicalLearnerLanguage
            K obs f ∈
          CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
            (w := max u v)
            (z := max u v)
            α f
            (sampleLengthBudget K)) ∧
      (∀ L : Set (Word α),
        L ∈ StartRootedCorrectedConcreteTargetClass
            (v := w) α M obs f →
        ∃ S : Finset (Word α),
          (S : Set (Word α)) ⊆ L ∧
          L ∈
            CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
              (w := max u v)
              (z := max u v)
              α f
              (sampleLengthBudget S)) := by

  exact
    ⟨fun n m hnm =>
        checkedBitBoundedCutCompiledWorkingGrammarLanguageClass_mono
          (w := max u v)
          (z := max u v)
          hnm,
      startRootedTargetClass_subset_exists_checkedBitBoundedCutCompiledClass
        (v := w) hα obs f,
      correctedConcreteCanonicalLearnerLanguage_mem_checkedBitBoundedClass
        hα obs f,
      fun L hL =>
        correctedConcreteWorkingGrammarLearner_exists_positive_checkedBitBoundedRepresentation
          (v := w) hα obs f hL⟩

/-- Combined identification and checked bit-bounded finite-representation
endpoint. -/
theorem
    correctedConcreteWorkingGrammarLearner_identification_checkedBitBoundedRepresentation_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f ⊆
        {L : Set (Word α) |
          ∃ n : Nat,
            L ∈
              CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
                (w := max u v)
                (z := max u v)
                α f n}) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearner
            hα obs f K).grammar.StringLanguage ∈
          CheckedBitBoundedCutCompiledWorkingGrammarLanguageClass
            (w := max u v)
            (z := max u v)
            α f
            (sampleLengthBudget K)) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
            hα obs f K).decode
            (correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
              hα obs f K).bits =
          some
            (correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
              hα obs f K).presentation) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
            hα obs f K).bits.length <=
          correctedConcreteCompiledGrammarPaperPowerBitBound
            (sampleLengthBudget K)
            f) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      startRootedTargetClass_subset_exists_checkedBitBoundedCutCompiledClass
        (v := w) hα obs f,
      correctedConcreteWorkingGrammarLearner_language_mem_checkedBitBoundedClass
        hα obs f,
      fun K =>
        (correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
          hα obs f K).decode_bits,
      fun K =>
        (correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
          hα obs f K).bitLength_le⟩

end CheckedBitHierarchyPackages

end MCFG
