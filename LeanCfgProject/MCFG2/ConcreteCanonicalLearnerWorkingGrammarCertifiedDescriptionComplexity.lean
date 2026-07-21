/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarCertifiedOutputMindChanges

/-!
# ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionComplexity.lean

The preceding file proves that every semantic start-rooted target has one exact
certified output obtained from a minimum-budget characteristic sample.  Its
checked code length and finite canonical-search size are explicitly bounded in
terms of the target characteristic rank.

This file turns those existence bounds into target-specific minimum complexity
measures.

## Certified bit-description complexity

A language has a certified description at bit budget `b` when there exists a

```lean
CorrectedConcreteCertifiedWorkingGrammarHypothesis α M obs f
```

whose actual grammar language is the target language and whose stored checked
code has length at most `b`.

The least such budget is

```lean
correctedConcreteCertifiedBitDescriptionComplexity.
```

Because the budgets are natural numbers, `Nat.find` gives an attained minimum.
We strengthen the ordinary specification theorem to an exact witness:

```text
there exists a certified output C with
  C.output.grammar.StringLanguage = L
and
  C.bits.length = certifiedBitDescriptionComplexity(L).
```

For every semantic start-rooted target, this minimum is bounded by

```text
correctedConcreteCompiledGrammarPaperPowerBitBound
  (startRootedTargetCharacteristicRank ...)
  f.
```

## Certified canonical-search complexity

Analogously, a language has a certified canonical search at budget `q` when
there exists an exact certified output whose finite canonical-search list has
length at most `q`.

The least such budget is

```lean
correctedConcreteCertifiedCanonicalSearchComplexity.
```

It too is attained exactly, and every semantic target satisfies

```text
certifiedCanonicalSearchComplexity(L)
  ≤
2 ^
  (paperPowerBitBound(characteristicRank(L), f) + 1).
```

## Interpretation

These are semantic minimum-description measures over the already defined
certified output type.  They do not assert an algorithm for computing the
minimum from the target language.  The characteristic-rank theorem supplies a
constructive upper witness, while `Nat.find` supplies the abstract least
natural budget.

The final class-level package combines

* positive-data identification by the certified learner;
* attainment of the minimum certified bit complexity;
* the characteristic-rank bit-complexity upper bound;
* attainment of the minimum finite-search complexity; and
* the characteristic-rank search-complexity upper bound.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w


section GenericCertifiedBitDescriptionComplexity

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]
variable {obs : α → M}
variable {f : Nat}

/-- A language has an exact certified working-grammar description whose checked
Boolean code has length at most `bitBudget`. -/
def CorrectedConcreteCertifiedBitDescriptionAtBudget
    (L : Set (Word α))
    (bitBudget : Nat) :
    Prop :=
  ∃
    C :
      CorrectedConcreteCertifiedWorkingGrammarHypothesis
        α M obs f,
    C.output.grammar.StringLanguage = L ∧
      C.bits.length <= bitBudget

/-- Existence of some finite certified checked bit description. -/
def HasCorrectedConcreteCertifiedBitDescription
    (L : Set (Word α)) :
    Prop :=
  ∃ bitBudget : Nat,
    CorrectedConcreteCertifiedBitDescriptionAtBudget
      (obs := obs)
      (f := f)
      L bitBudget

/-- Certified bit-description budgets are upward closed. -/
theorem correctedConcreteCertifiedBitDescriptionAtBudget_mono
    {L : Set (Word α)}
    {b c : Nat}
    (hbc : b <= c)
    (hb :
      CorrectedConcreteCertifiedBitDescriptionAtBudget
        (obs := obs)
        (f := f)
        L b) :
    CorrectedConcreteCertifiedBitDescriptionAtBudget
      (obs := obs)
      (f := f)
      L c := by

  rcases hb with
    ⟨C, hlanguage, hlength⟩

  exact
    ⟨C,
      hlanguage,
      hlength.trans hbc⟩

/-- Every explicit certified output proves existence of a finite certified bit
description. -/
theorem hasCorrectedConcreteCertifiedBitDescription_of_output
    {L : Set (Word α)}
    (C :
      CorrectedConcreteCertifiedWorkingGrammarHypothesis
        α M obs f)
    (hlanguage :
      C.output.grammar.StringLanguage = L) :
    HasCorrectedConcreteCertifiedBitDescription
      (obs := obs)
      (f := f)
      L := by

  exact
    ⟨C.bits.length,
      C,
      hlanguage,
      Nat.le_refl _⟩

/-- Least checked Boolean-code length of an exact certified working-grammar
description. -/
noncomputable def correctedConcreteCertifiedBitDescriptionComplexity
    {L : Set (Word α)}
    (hL :
      HasCorrectedConcreteCertifiedBitDescription
        (obs := obs)
        (f := f)
        L) :
    Nat :=
  Nat.find hL

namespace HasCorrectedConcreteCertifiedBitDescription

variable {L : Set (Word α)}

/-- The minimum certified bit-description budget is attained. -/
theorem complexity_spec
    (hL :
      HasCorrectedConcreteCertifiedBitDescription
        (obs := obs)
        (f := f)
        L) :
    CorrectedConcreteCertifiedBitDescriptionAtBudget
      (obs := obs)
      (f := f)
      L
      (correctedConcreteCertifiedBitDescriptionComplexity
        hL) := by

  exact
    Nat.find_spec hL

/-- Minimality of the certified bit-description complexity. -/
theorem complexity_le_of_atBudget
    (hL :
      HasCorrectedConcreteCertifiedBitDescription
        (obs := obs)
        (f := f)
        L)
    {bitBudget : Nat}
    (hbudget :
      CorrectedConcreteCertifiedBitDescriptionAtBudget
        (obs := obs)
        (f := f)
        L bitBudget) :
    correctedConcreteCertifiedBitDescriptionComplexity
        hL <=
      bitBudget := by

  exact
    Nat.find_min' hL hbudget

/-- Having a certified bit description at budget `b` is equivalent to being
above the minimum certified bit-description complexity. -/
theorem atBudget_iff_complexity_le
    (hL :
      HasCorrectedConcreteCertifiedBitDescription
        (obs := obs)
        (f := f)
        L)
    (bitBudget : Nat) :
    CorrectedConcreteCertifiedBitDescriptionAtBudget
        (obs := obs)
        (f := f)
        L bitBudget ↔
      correctedConcreteCertifiedBitDescriptionComplexity
          hL <=
        bitBudget := by

  constructor

  · exact
      hL.complexity_le_of_atBudget

  · intro hcomplexity

    exact
      correctedConcreteCertifiedBitDescriptionAtBudget_mono
        hcomplexity
        hL.complexity_spec

/-- The minimum is attained by a certified output whose checked code length is
exactly the complexity value. -/
theorem exists_output_exact_complexity
    (hL :
      HasCorrectedConcreteCertifiedBitDescription
        (obs := obs)
        (f := f)
        L) :
    ∃
      C :
        CorrectedConcreteCertifiedWorkingGrammarHypothesis
          α M obs f,
      C.output.grammar.StringLanguage = L ∧
        C.bits.length =
          correctedConcreteCertifiedBitDescriptionComplexity
            hL := by

  rcases hL.complexity_spec with
    ⟨C, hlanguage, hlength⟩

  have hminimum :
      correctedConcreteCertifiedBitDescriptionComplexity
          hL <=
        C.bits.length := by

    apply hL.complexity_le_of_atBudget

    exact
      ⟨C,
        hlanguage,
        Nat.le_refl _⟩

  exact
    ⟨C,
      hlanguage,
      Nat.le_antisymm
        hlength
        hminimum⟩

/-- The minimum certified bit complexity is no larger than the checked code
length of any exact certified output for the language. -/
theorem complexity_le_output_bitLength
    (hL :
      HasCorrectedConcreteCertifiedBitDescription
        (obs := obs)
        (f := f)
        L)
    (C :
      CorrectedConcreteCertifiedWorkingGrammarHypothesis
        α M obs f)
    (hlanguage :
      C.output.grammar.StringLanguage = L) :
    correctedConcreteCertifiedBitDescriptionComplexity
        hL <=
      C.bits.length := by

  apply hL.complexity_le_of_atBudget

  exact
    ⟨C,
      hlanguage,
      Nat.le_refl _⟩

end HasCorrectedConcreteCertifiedBitDescription

end GenericCertifiedBitDescriptionComplexity


section GenericCertifiedCanonicalSearchComplexity

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]
variable {obs : α → M}
variable {f : Nat}

/-- A language has an exact certified output whose finite canonical-search list
has length at most `searchBudget`. -/
def CorrectedConcreteCertifiedCanonicalSearchAtBudget
    (L : Set (Word α))
    (searchBudget : Nat) :
    Prop :=
  ∃
    C :
      CorrectedConcreteCertifiedWorkingGrammarHypothesis
        α M obs f,
    C.output.grammar.StringLanguage = L ∧
      C.canonicalSearch.length <= searchBudget

/-- Existence of some finite certified canonical search for the language. -/
def HasCorrectedConcreteCertifiedCanonicalSearch
    (L : Set (Word α)) :
    Prop :=
  ∃ searchBudget : Nat,
    CorrectedConcreteCertifiedCanonicalSearchAtBudget
      (obs := obs)
      (f := f)
      L searchBudget

/-- Certified canonical-search budgets are upward closed. -/
theorem correctedConcreteCertifiedCanonicalSearchAtBudget_mono
    {L : Set (Word α)}
    {b c : Nat}
    (hbc : b <= c)
    (hb :
      CorrectedConcreteCertifiedCanonicalSearchAtBudget
        (obs := obs)
        (f := f)
        L b) :
    CorrectedConcreteCertifiedCanonicalSearchAtBudget
      (obs := obs)
      (f := f)
      L c := by

  rcases hb with
    ⟨C, hlanguage, hlength⟩

  exact
    ⟨C,
      hlanguage,
      hlength.trans hbc⟩

/-- Every explicit certified output proves existence of a finite certified
canonical search. -/
theorem hasCorrectedConcreteCertifiedCanonicalSearch_of_output
    {L : Set (Word α)}
    (C :
      CorrectedConcreteCertifiedWorkingGrammarHypothesis
        α M obs f)
    (hlanguage :
      C.output.grammar.StringLanguage = L) :
    HasCorrectedConcreteCertifiedCanonicalSearch
      (obs := obs)
      (f := f)
      L := by

  exact
    ⟨C.canonicalSearch.length,
      C,
      hlanguage,
      Nat.le_refl _⟩

/-- Least finite canonical-search-list length among exact certified outputs. -/
noncomputable def correctedConcreteCertifiedCanonicalSearchComplexity
    {L : Set (Word α)}
    (hL :
      HasCorrectedConcreteCertifiedCanonicalSearch
        (obs := obs)
        (f := f)
        L) :
    Nat :=
  Nat.find hL

namespace HasCorrectedConcreteCertifiedCanonicalSearch

variable {L : Set (Word α)}

/-- The minimum finite canonical-search budget is attained. -/
theorem complexity_spec
    (hL :
      HasCorrectedConcreteCertifiedCanonicalSearch
        (obs := obs)
        (f := f)
        L) :
    CorrectedConcreteCertifiedCanonicalSearchAtBudget
      (obs := obs)
      (f := f)
      L
      (correctedConcreteCertifiedCanonicalSearchComplexity
        hL) := by

  exact
    Nat.find_spec hL

/-- Minimality of the certified canonical-search complexity. -/
theorem complexity_le_of_atBudget
    (hL :
      HasCorrectedConcreteCertifiedCanonicalSearch
        (obs := obs)
        (f := f)
        L)
    {searchBudget : Nat}
    (hbudget :
      CorrectedConcreteCertifiedCanonicalSearchAtBudget
        (obs := obs)
        (f := f)
        L searchBudget) :
    correctedConcreteCertifiedCanonicalSearchComplexity
        hL <=
      searchBudget := by

  exact
    Nat.find_min' hL hbudget

/-- Having an exact certified output with search budget `q` is equivalent to
being above the minimum certified canonical-search complexity. -/
theorem atBudget_iff_complexity_le
    (hL :
      HasCorrectedConcreteCertifiedCanonicalSearch
        (obs := obs)
        (f := f)
        L)
    (searchBudget : Nat) :
    CorrectedConcreteCertifiedCanonicalSearchAtBudget
        (obs := obs)
        (f := f)
        L searchBudget ↔
      correctedConcreteCertifiedCanonicalSearchComplexity
          hL <=
        searchBudget := by

  constructor

  · exact
      hL.complexity_le_of_atBudget

  · intro hcomplexity

    exact
      correctedConcreteCertifiedCanonicalSearchAtBudget_mono
        hcomplexity
        hL.complexity_spec

/-- The minimum is attained by a certified output whose finite canonical-search
list length is exactly the complexity value. -/
theorem exists_output_exact_complexity
    (hL :
      HasCorrectedConcreteCertifiedCanonicalSearch
        (obs := obs)
        (f := f)
        L) :
    ∃
      C :
        CorrectedConcreteCertifiedWorkingGrammarHypothesis
          α M obs f,
      C.output.grammar.StringLanguage = L ∧
        C.canonicalSearch.length =
          correctedConcreteCertifiedCanonicalSearchComplexity
            hL := by

  rcases hL.complexity_spec with
    ⟨C, hlanguage, hlength⟩

  have hminimum :
      correctedConcreteCertifiedCanonicalSearchComplexity
          hL <=
        C.canonicalSearch.length := by

    apply hL.complexity_le_of_atBudget

    exact
      ⟨C,
        hlanguage,
        Nat.le_refl _⟩

  exact
    ⟨C,
      hlanguage,
      Nat.le_antisymm
        hlength
        hminimum⟩

/-- The minimum certified canonical-search complexity is no larger than the
search-list length of any exact certified output for the language. -/
theorem complexity_le_output_searchLength
    (hL :
      HasCorrectedConcreteCertifiedCanonicalSearch
        (obs := obs)
        (f := f)
        L)
    (C :
      CorrectedConcreteCertifiedWorkingGrammarHypothesis
        α M obs f)
    (hlanguage :
      C.output.grammar.StringLanguage = L) :
    correctedConcreteCertifiedCanonicalSearchComplexity
        hL <=
      C.canonicalSearch.length := by

  apply hL.complexity_le_of_atBudget

  exact
    ⟨C,
      hlanguage,
      Nat.le_refl _⟩

end HasCorrectedConcreteCertifiedCanonicalSearch

end GenericCertifiedCanonicalSearchComplexity


section StartRootedTargetCertifiedComplexities

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Every semantic start-rooted target has some finite exact certified bit
description. -/
theorem startRootedTarget_hasCertifiedBitDescription
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    HasCorrectedConcreteCertifiedBitDescription
      (obs := obs)
      (f := f)
      L := by

  let C :=
    startRootedTargetMinimalCharacteristicCertifiedOutput
      (v := w) hα obs f hL

  exact
    ⟨correctedConcreteCompiledGrammarPaperPowerBitBound
        (startRootedTargetCharacteristicRank
          (v := w) hα obs f hL)
        f,
      C,
      by
        simpa [C] using
          startRootedTargetMinimalCharacteristicCertifiedOutput_language_eq
            (v := w) hα obs f hL,
      by
        simpa [C] using
          startRootedTargetMinimalCharacteristicCertifiedOutput_bitLength_le_rank
            (v := w) hα obs f hL⟩

/-- Every semantic start-rooted target has some finite exact certified
canonical search. -/
theorem startRootedTarget_hasCertifiedCanonicalSearch
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    HasCorrectedConcreteCertifiedCanonicalSearch
      (obs := obs)
      (f := f)
      L := by

  let C :=
    startRootedTargetMinimalCharacteristicCertifiedOutput
      (v := w) hα obs f hL

  exact
    ⟨2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            (startRootedTargetCharacteristicRank
              (v := w) hα obs f hL)
            f +
          1),
      C,
      by
        simpa [C] using
          startRootedTargetMinimalCharacteristicCertifiedOutput_language_eq
            (v := w) hα obs f hL,
      by
        simpa [C] using
          startRootedTargetMinimalCharacteristicCertifiedOutput_searchLength_le_rank
            (v := w) hα obs f hL⟩

/-- Target-specific least checked bit length among all exact certified outputs. -/
noncomputable def startRootedTargetCertifiedBitDescriptionComplexity
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    Nat :=
  correctedConcreteCertifiedBitDescriptionComplexity
    (startRootedTarget_hasCertifiedBitDescription
      (v := w) hα obs f hL)

/-- Target-specific least canonical-search-list length among all exact certified
outputs. -/
noncomputable def startRootedTargetCertifiedCanonicalSearchComplexity
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    Nat :=
  correctedConcreteCertifiedCanonicalSearchComplexity
    (startRootedTarget_hasCertifiedCanonicalSearch
      (v := w) hα obs f hL)

/-- The target's minimum certified bit complexity is attained exactly. -/
theorem startRootedTarget_exists_exact_minimumCertifiedBitDescription
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    ∃
      C :
        CorrectedConcreteCertifiedWorkingGrammarHypothesis
          α M obs f,
      C.output.grammar.StringLanguage = L ∧
        C.bits.length =
          startRootedTargetCertifiedBitDescriptionComplexity
            (v := w) hα obs f hL := by

  exact
    (startRootedTarget_hasCertifiedBitDescription
      (v := w) hα obs f hL).exists_output_exact_complexity

/-- The target's minimum certified canonical-search complexity is attained
exactly. -/
theorem startRootedTarget_exists_exact_minimumCertifiedCanonicalSearch
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    ∃
      C :
        CorrectedConcreteCertifiedWorkingGrammarHypothesis
          α M obs f,
      C.output.grammar.StringLanguage = L ∧
        C.canonicalSearch.length =
          startRootedTargetCertifiedCanonicalSearchComplexity
            (v := w) hα obs f hL := by

  exact
    (startRootedTarget_hasCertifiedCanonicalSearch
      (v := w) hα obs f hL).exists_output_exact_complexity

/-- Characteristic rank upper-bounds the minimum certified bit-description
complexity through the final paper-power function. -/
theorem
    startRootedTargetCertifiedBitDescriptionComplexity_le_characteristicRankPower
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    startRootedTargetCertifiedBitDescriptionComplexity
        (v := w) hα obs f hL <=
      correctedConcreteCompiledGrammarPaperPowerBitBound
        (startRootedTargetCharacteristicRank
          (v := w) hα obs f hL)
        f := by

  unfold
    startRootedTargetCertifiedBitDescriptionComplexity

  apply
    (startRootedTarget_hasCertifiedBitDescription
      (v := w) hα obs f hL).complexity_le_of_atBudget

  let C :=
    startRootedTargetMinimalCharacteristicCertifiedOutput
      (v := w) hα obs f hL

  exact
    ⟨C,
      by
        simpa [C] using
          startRootedTargetMinimalCharacteristicCertifiedOutput_language_eq
            (v := w) hα obs f hL,
      by
        simpa [C] using
          startRootedTargetMinimalCharacteristicCertifiedOutput_bitLength_le_rank
            (v := w) hα obs f hL⟩

/-- Characteristic rank upper-bounds the minimum certified canonical-search
complexity through the finite code-universe estimate. -/
theorem
    startRootedTargetCertifiedCanonicalSearchComplexity_le_characteristicRankPower
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    startRootedTargetCertifiedCanonicalSearchComplexity
        (v := w) hα obs f hL <=
      2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            (startRootedTargetCharacteristicRank
              (v := w) hα obs f hL)
            f +
          1) := by

  unfold
    startRootedTargetCertifiedCanonicalSearchComplexity

  apply
    (startRootedTarget_hasCertifiedCanonicalSearch
      (v := w) hα obs f hL).complexity_le_of_atBudget

  let C :=
    startRootedTargetMinimalCharacteristicCertifiedOutput
      (v := w) hα obs f hL

  exact
    ⟨C,
      by
        simpa [C] using
          startRootedTargetMinimalCharacteristicCertifiedOutput_language_eq
            (v := w) hα obs f hL,
      by
        simpa [C] using
          startRootedTargetMinimalCharacteristicCertifiedOutput_searchLength_le_rank
            (v := w) hα obs f hL⟩

/-- The minimum bit complexity is no larger than the actual checked code length
of the selected minimum-characteristic output. -/
theorem
    startRootedTargetCertifiedBitDescriptionComplexity_le_minimalCharacteristicOutput
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    startRootedTargetCertifiedBitDescriptionComplexity
        (v := w) hα obs f hL <=
      (startRootedTargetMinimalCharacteristicCertifiedOutput
        (v := w) hα obs f hL).bits.length := by

  unfold
    startRootedTargetCertifiedBitDescriptionComplexity

  apply
    (startRootedTarget_hasCertifiedBitDescription
      (v := w) hα obs f hL).complexity_le_output_bitLength

  exact
    startRootedTargetMinimalCharacteristicCertifiedOutput_language_eq
      (v := w) hα obs f hL

/-- The minimum search complexity is no larger than the actual finite search of
the selected minimum-characteristic output. -/
theorem
    startRootedTargetCertifiedCanonicalSearchComplexity_le_minimalCharacteristicOutput
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    startRootedTargetCertifiedCanonicalSearchComplexity
        (v := w) hα obs f hL <=
      (startRootedTargetMinimalCharacteristicCertifiedOutput
        (v := w) hα obs f hL).canonicalSearch.length := by

  unfold
    startRootedTargetCertifiedCanonicalSearchComplexity

  apply
    (startRootedTarget_hasCertifiedCanonicalSearch
      (v := w) hα obs f hL).complexity_le_output_searchLength

  exact
    startRootedTargetMinimalCharacteristicCertifiedOutput_language_eq
      (v := w) hα obs f hL

/-- Compact target-specific certified complexity package. -/
theorem startRootedTargetCertifiedDescriptionComplexity_package
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) :
    (∃
      C :
        CorrectedConcreteCertifiedWorkingGrammarHypothesis
          α M obs f,
      C.output.grammar.StringLanguage = L ∧
        C.bits.length =
          startRootedTargetCertifiedBitDescriptionComplexity
            (v := w) hα obs f hL) ∧
      (startRootedTargetCertifiedBitDescriptionComplexity
          (v := w) hα obs f hL <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
          (startRootedTargetCharacteristicRank
            (v := w) hα obs f hL)
          f) ∧
      (∃
        C :
          CorrectedConcreteCertifiedWorkingGrammarHypothesis
            α M obs f,
        C.output.grammar.StringLanguage = L ∧
          C.canonicalSearch.length =
            startRootedTargetCertifiedCanonicalSearchComplexity
              (v := w) hα obs f hL) ∧
      (startRootedTargetCertifiedCanonicalSearchComplexity
          (v := w) hα obs f hL <=
        2 ^
          (correctedConcreteCompiledGrammarPaperPowerBitBound
              (startRootedTargetCharacteristicRank
                (v := w) hα obs f hL)
              f +
            1)) := by

  exact
    ⟨startRootedTarget_exists_exact_minimumCertifiedBitDescription
        (v := w) hα obs f hL,
      startRootedTargetCertifiedBitDescriptionComplexity_le_characteristicRankPower
        (v := w) hα obs f hL,
      startRootedTarget_exists_exact_minimumCertifiedCanonicalSearch
        (v := w) hα obs f hL,
      startRootedTargetCertifiedCanonicalSearchComplexity_le_characteristicRankPower
        (v := w) hα obs f hL⟩

end StartRootedTargetCertifiedComplexities


section CertifiedDescriptionComplexityClassPackage

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Final class-level identification and attained minimum certified-description
complexity theorem. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLearner_identification_descriptionComplexity_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (∀
        L : Set (Word α),
        ∀ hL :
          L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f,
        ∃
          C :
            CorrectedConcreteCertifiedWorkingGrammarHypothesis
              α M obs f,
          C.output.grammar.StringLanguage = L ∧
            C.bits.length =
              startRootedTargetCertifiedBitDescriptionComplexity
                (v := w) hα obs f hL) ∧
      (∀
        L : Set (Word α),
        ∀ hL :
          L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f,
        startRootedTargetCertifiedBitDescriptionComplexity
            (v := w) hα obs f hL <=
          correctedConcreteCompiledGrammarPaperPowerBitBound
            (startRootedTargetCharacteristicRank
              (v := w) hα obs f hL)
            f) ∧
      (∀
        L : Set (Word α),
        ∀ hL :
          L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f,
        ∃
          C :
            CorrectedConcreteCertifiedWorkingGrammarHypothesis
              α M obs f,
          C.output.grammar.StringLanguage = L ∧
            C.canonicalSearch.length =
              startRootedTargetCertifiedCanonicalSearchComplexity
                (v := w) hα obs f hL) ∧
      (∀
        L : Set (Word α),
        ∀ hL :
          L ∈
            StartRootedCorrectedConcreteTargetClass
              (v := w) α M obs f,
        startRootedTargetCertifiedCanonicalSearchComplexity
            (v := w) hα obs f hL <=
          2 ^
            (correctedConcreteCompiledGrammarPaperPowerBitBound
                (startRootedTargetCharacteristicRank
                  (v := w) hα obs f hL)
                f +
              1)) := by

  exact
    ⟨correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      fun L hL =>
        startRootedTarget_exists_exact_minimumCertifiedBitDescription
          (v := w) hα obs f hL,
      fun L hL =>
        startRootedTargetCertifiedBitDescriptionComplexity_le_characteristicRankPower
          (v := w) hα obs f hL,
      fun L hL =>
        startRootedTarget_exists_exact_minimumCertifiedCanonicalSearch
          (v := w) hα obs f hL,
      fun L hL =>
        startRootedTargetCertifiedCanonicalSearchComplexity_le_characteristicRankPower
          (v := w) hα obs f hL⟩

end CertifiedDescriptionComplexityClassPackage

end MCFG
