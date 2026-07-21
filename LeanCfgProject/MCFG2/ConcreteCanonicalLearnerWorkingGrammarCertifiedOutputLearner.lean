/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarCanonicalSearchSelector

/-!
# ConcreteCanonicalLearnerWorkingGrammarCertifiedOutputLearner.lean

The preceding files construct, for every finite positive sample `K`,

* an actual cut-compiled `WorkingMCFG` learner output;
* its complete tagged presentation;
* its checked logarithmic bit code;
* a finite canonical decoder/re-encoder search;
* an exact code-indexed selector;
* decoder and re-encoder equations; and
* explicit code-length and search-size bounds.

Until now these facts have been exposed as separate definitions and theorem
packages.  This file collects them into the output type of one certified
set-driven learner.

## Certified output hypothesis

```lean
CorrectedConcreteCertifiedWorkingGrammarHypothesis α M obs f
```

stores

```text
the original actual WorkingMCFG hypothesis,
a presentation type,
the selected complete presentation,
the selected Boolean code,
the checked decoder and re-encoder,
the finite canonical search,
the code-indexed selector result,
decode/re-encode proofs,
search membership,
selector exactness,
the paper-power code-length bound,
and the finite-search-size bound.
```

Its semantic language is simply the language of the stored original grammar.

## Certified learner

```lean
correctedConcreteCertifiedWorkingGrammarLearner hα obs f
```

takes exactly the same input as the original learner: the current finite
positive sample.  Its `output` projection is definitionally

```lean
correctedConcreteWorkingGrammarLearner hα obs f K.
```

No target language or target grammar is an input.

We prove that the certified learner

* has the same language as the original learner at every sample;
* is consistent;
* is language-monotone;
* identifies the same semantic start-rooted target class;
* returns a checked canonical code/presentation fixed point at every stage;
* returns an exact finite-selector result at every stage; and
* obeys the same single-power bit bound and finite-search bound.

After the ordinary characteristic-sample coverage stage, the grammar stored in
every later certified output has exactly the target language while all
certificate fields remain valid.

This is the first theorem in the chain whose learner output itself carries the
complete checked finite-description certificate rather than merely admitting
one externally.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w


section CertifiedWorkingGrammarHypothesis

variable (α : Type u)
variable (M : Type v)
variable [Monoid M]
variable (obs : α → M)
variable (f : Nat)

/-- Actual compiled working-grammar hypothesis together with its complete
checked canonical finite-description certificate. -/
structure CorrectedConcreteCertifiedWorkingGrammarHypothesis where

  /-- The original actual working-grammar learner output. -/
  output :
    CorrectedConcreteWorkingGrammarHypothesis
      α M obs f

  /-- Type of decoded complete presentations carried by this output. -/
  Presentation :
    Type (max u v)

  /-- Selected complete presentation. -/
  presentation :
    Presentation

  /-- Selected checked logarithmic Boolean code. -/
  bits :
    List Bool

  /-- Checked decoder for this output's presentation type. -/
  decode :
    List Bool → Option Presentation

  /-- Canonical re-encoder for this output's presentation type. -/
  reencode :
    Presentation → List Bool

  /-- Finite canonical decoder/re-encoder search. -/
  canonicalSearch :
    List (List Bool × Presentation)

  /-- Result of selecting by the stored checked code. -/
  selectorResult :
    Option (List Bool × Presentation)

  /-- The stored code decodes to the stored presentation. -/
  decode_bits :
    decode bits = some presentation

  /-- The stored presentation re-encodes to the stored code. -/
  reencode_presentation :
    reencode presentation = bits

  /-- The stored pair occurs in the finite canonical search. -/
  pair_mem_search :
    (bits, presentation) ∈ canonicalSearch

  /-- The stored code-indexed selector returns the stored pair exactly. -/
  selector_exact :
    selectorResult = some (bits, presentation)

  /-- Explicit checked code-length bound indexed by the stored sample. -/
  bitLength_le :
    bits.length <=
      correctedConcreteCompiledGrammarPaperPowerBitBound
        (sampleLengthBudget output.sample)
        f

  /-- Explicit finite canonical-search-size bound. -/
  searchLength_le :
    canonicalSearch.length <=
      2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            (sampleLengthBudget output.sample)
            f +
          1)

namespace CorrectedConcreteCertifiedWorkingGrammarHypothesis

/-- Semantic language of a certified output: the language of its actual stored
working grammar. -/
def Language
    (H :
      CorrectedConcreteCertifiedWorkingGrammarHypothesis
        α M obs f) :
    Set (Word α) :=
  H.output.Language

/-- The certified output's grammar language is the language interpretation. -/
@[simp] theorem language_eq_grammar
    (H :
      CorrectedConcreteCertifiedWorkingGrammarHypothesis
        α M obs f) :
    H.Language =
      H.output.grammar.StringLanguage := by

  rfl

/-- The certificate fields state a checked decoder/re-encoder fixed point. -/
theorem checked_fixedPoint
    (H :
      CorrectedConcreteCertifiedWorkingGrammarHypothesis
        α M obs f) :
    H.decode H.bits =
        some H.presentation ∧
      H.reencode H.presentation =
        H.bits := by

  exact
    ⟨H.decode_bits,
      H.reencode_presentation⟩

/-- The stored selector is exact and its selected pair belongs to the finite
canonical search. -/
theorem selected_pair_certificate
    (H :
      CorrectedConcreteCertifiedWorkingGrammarHypothesis
        α M obs f) :
    H.selectorResult =
        some (H.bits, H.presentation) ∧
      (H.bits, H.presentation) ∈
        H.canonicalSearch := by

  exact
    ⟨H.selector_exact,
      H.pair_mem_search⟩

/-- The selected code belongs to the finite code universe at the output's own
sample-length level. -/
theorem bits_mem_codeUniverse
    (H :
      CorrectedConcreteCertifiedWorkingGrammarHypothesis
        α M obs f) :
    H.bits ∈
      correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        (sampleLengthBudget H.output.sample)
        f := by

  exact
    (mem_correctedConcreteCompiledGrammarCheckedBitCodeUniverse_iff
      H.bits
      (sampleLengthBudget H.output.sample)
      f).mpr
      H.bitLength_le

/-- The certificate contains an accepted canonical pair in a finite explicitly
bounded search. -/
theorem finite_checked_search_certificate
    (H :
      CorrectedConcreteCertifiedWorkingGrammarHypothesis
        α M obs f) :
    (H.bits, H.presentation) ∈
        H.canonicalSearch ∧
      H.decode H.bits =
        some H.presentation ∧
      H.reencode H.presentation =
        H.bits ∧
      H.bits.length <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
          (sampleLengthBudget H.output.sample)
          f ∧
      H.canonicalSearch.length <=
        2 ^
          (correctedConcreteCompiledGrammarPaperPowerBitBound
              (sampleLengthBudget H.output.sample)
              f +
            1) := by

  exact
    ⟨H.pair_mem_search,
      H.decode_bits,
      H.reencode_presentation,
      H.bitLength_le,
      H.searchLength_le⟩

end CorrectedConcreteCertifiedWorkingGrammarHypothesis

end CertifiedWorkingGrammarHypothesis


section CertifiedWorkingGrammarLearnerDefinition

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- Canonical certified output on one finite positive sample. -/
noncomputable def correctedConcreteCertifiedWorkingGrammarHypothesis
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    CorrectedConcreteCertifiedWorkingGrammarHypothesis
      α M obs f := by

  let output :=
    correctedConcreteWorkingGrammarLearner
      hα obs f K

  let H :=
    correctedConcreteFiniteHypothesis
      K obs f

  let presentation :=
    correctedConcreteWorkingGrammarLearnerActualPresentation
      hα obs f K

  let bits :=
    correctedConcreteWorkingGrammarLearnerLogarithmicBitList
      hα obs f K

  let decode :=
    correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
      hα obs f K

  let reencode :=
    correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
      hα obs f K

  let search :=
    correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
      hα obs f K

  let selector :=
    correctedConcreteWorkingGrammarLearnerCanonicalPairSelectorResult
      hα obs f K

  exact
    { output :=
        output

      Presentation :=
        List
          (CorrectedConcreteCompiledGrammarPresentationEntry
            H)

      presentation :=
        presentation

      bits :=
        bits

      decode :=
        decode

      reencode :=
        reencode

      canonicalSearch :=
        search

      selectorResult :=
        selector

      decode_bits := by
        simpa [
          decode,
          bits,
          presentation
        ] using
          correctedConcreteWorkingGrammarLearner_selectedCanonicalPresentation_decode
            hα obs f K

      reencode_presentation := by
        simpa [
          reencode,
          bits,
          presentation
        ] using
          correctedConcreteWorkingGrammarLearner_selectedCanonicalPresentation_reencode
            hα obs f K

      pair_mem_search := by
        simpa [
          search,
          bits,
          presentation
        ] using
          correctedConcreteWorkingGrammarLearner_selectedCanonicalPair_mem_search
            hα obs f K

      selector_exact := by
        simpa [
          selector,
          bits,
          presentation
        ] using
          correctedConcreteWorkingGrammarLearnerCanonicalPairSelectorResult_eq
            hα obs f K

      bitLength_le := by
        simpa [
          output,
          bits
        ] using
          correctedConcreteWorkingGrammarLearner_selectedCanonicalCode_length_le
            hα obs f K

      searchLength_le := by
        simpa [
          output,
          search
        ] using
          correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_length_le
            hα obs f K }

/-- Set-driven learner whose output type itself carries the full checked
canonical finite-description certificate. -/
noncomputable def correctedConcreteCertifiedWorkingGrammarLearner
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat) :
    SetDrivenLearner
      α
      (CorrectedConcreteCertifiedWorkingGrammarHypothesis
        α M obs f) :=
  fun K =>
    correctedConcreteCertifiedWorkingGrammarHypothesis
      hα obs f K

/-- Language interpretation for certified learner outputs. -/
def correctedConcreteCertifiedWorkingGrammarHypLanguage
    (obs : α → M)
    (f : Nat) :
    HypLanguage
      α
      (CorrectedConcreteCertifiedWorkingGrammarHypothesis
        α M obs f) :=
  fun H =>
    H.Language

end CertifiedWorkingGrammarLearnerDefinition


section CertifiedLearnerProjectionTheorems

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- The underlying actual grammar hypothesis is definitionally the original
learner output. -/
@[simp] theorem correctedConcreteCertifiedWorkingGrammarLearner_output
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f K).output =
      correctedConcreteWorkingGrammarLearner
        hα obs f K := by

  rfl

/-- The certified output stores the original finite sample. -/
@[simp] theorem correctedConcreteCertifiedWorkingGrammarLearner_sample
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f K).output.sample =
      K := by

  rfl

/-- The certified output's actual grammar is the original actual learner
grammar. -/
@[simp] theorem correctedConcreteCertifiedWorkingGrammarLearner_grammar
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f K).output.grammar =
      (correctedConcreteWorkingGrammarLearner
        hα obs f K).grammar := by

  rfl

/-- The certified output stores the original complete presentation. -/
@[simp] theorem correctedConcreteCertifiedWorkingGrammarLearner_presentation
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f K).presentation =
      correctedConcreteWorkingGrammarLearnerActualPresentation
        hα obs f K := by

  rfl

/-- The certified output stores the original checked logarithmic code. -/
@[simp] theorem correctedConcreteCertifiedWorkingGrammarLearner_bits
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f K).bits =
      correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f K := by

  rfl

/-- The certified output stores the original canonical finite search. -/
@[simp] theorem correctedConcreteCertifiedWorkingGrammarLearner_canonicalSearch
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f K).canonicalSearch =
      correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
        hα obs f K := by

  rfl

/-- The certified output stores the original exact code-indexed selector
result. -/
@[simp] theorem correctedConcreteCertifiedWorkingGrammarLearner_selectorResult
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f K).selectorResult =
      correctedConcreteWorkingGrammarLearnerCanonicalPairSelectorResult
        hα obs f K := by

  rfl

/-- Certified and original learner languages agree definitionally at every
sample. -/
@[simp] theorem
    correctedConcreteCertifiedWorkingGrammarHypLanguage_eq_original
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs f
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K) =
      correctedConcreteWorkingGrammarHypLanguage
        obs f
        (correctedConcreteWorkingGrammarLearner
          hα obs f K) := by

  rfl

/-- Expanded language equality with the corrected concrete learner language. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLearner_language_eq_corrected
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs f
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K) =
      CorrectedConcreteCanonicalLearnerLanguage
        K obs f := by

  exact
    correctedConcreteWorkingGrammarLearner_stringLanguage_eq_corrected
      hα obs f K

end CertifiedLearnerProjectionTheorems


section CertifiedLearnerCertificateTheorems

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- Every certified learner output carries an exact checked decoder/re-encoder
fixed point. -/
theorem correctedConcreteCertifiedWorkingGrammarLearner_checked_fixedPoint
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f K).decode
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K).bits =
      some
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K).presentation ∧
      (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K).reencode
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).presentation =
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K).bits := by

  exact
    (correctedConcreteCertifiedWorkingGrammarLearner
      hα obs f K).checked_fixedPoint

/-- Every certified output's exact selected pair belongs to its finite canonical
search. -/
theorem correctedConcreteCertifiedWorkingGrammarLearner_selector_exact
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f K).selectorResult =
      some
        ((correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).bits,
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).presentation) ∧
      ((correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).bits,
        (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).presentation) ∈
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).canonicalSearch := by

  exact
    (correctedConcreteCertifiedWorkingGrammarLearner
      hα obs f K).selected_pair_certificate

/-- Every certified output's code satisfies the final single-power bit bound. -/
theorem correctedConcreteCertifiedWorkingGrammarLearner_bitLength_le
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f K).bits.length <=
      correctedConcreteCompiledGrammarPaperPowerBitBound
        (sampleLengthBudget K)
        f := by

  simpa using
    (correctedConcreteCertifiedWorkingGrammarLearner
      hα obs f K).bitLength_le

/-- Every certified output's canonical search satisfies the explicit finite
size bound. -/
theorem correctedConcreteCertifiedWorkingGrammarLearner_searchLength_le
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f K).canonicalSearch.length <=
      2 ^
        (correctedConcreteCompiledGrammarPaperPowerBitBound
            (sampleLengthBudget K)
            f +
          1) := by

  simpa using
    (correctedConcreteCertifiedWorkingGrammarLearner
      hα obs f K).searchLength_le

/-- The selected code belongs to the finite code universe at the sample's total
length. -/
theorem correctedConcreteCertifiedWorkingGrammarLearner_bits_mem_codeUniverse
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f K).bits ∈
      correctedConcreteCompiledGrammarCheckedBitCodeUniverse
        (sampleLengthBudget K)
        f := by

  simpa using
    (correctedConcreteCertifiedWorkingGrammarLearner
      hα obs f K).bits_mem_codeUniverse

/-- Compact self-contained certificate exposed directly by one learner output. -/
theorem correctedConcreteCertifiedWorkingGrammarLearner_outputCertificate
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    ((correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f K).selectorResult =
      some
        ((correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).bits,
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).presentation)) ∧
      ((correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K).decode
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).bits =
        some
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).presentation) ∧
      ((correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K).reencode
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).presentation =
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K).bits) ∧
      (((correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).bits,
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).presentation) ∈
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K).canonicalSearch) ∧
      ((correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K).bits.length <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
          (sampleLengthBudget K)
          f) ∧
      ((correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K).canonicalSearch.length <=
        2 ^
          (correctedConcreteCompiledGrammarPaperPowerBitBound
              (sampleLengthBudget K)
              f +
            1)) := by

  let C :=
    correctedConcreteCertifiedWorkingGrammarLearner
      hα obs f K

  exact
    ⟨C.selector_exact,
      C.decode_bits,
      C.reencode_presentation,
      C.pair_mem_search,
      by simpa [C] using C.bitLength_le,
      by simpa [C] using C.searchLength_le⟩

end CertifiedLearnerCertificateTheorems


section CertifiedLearnerSemanticProperties

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- The certified learner contains every observed positive sample. -/
theorem correctedConcreteCertifiedWorkingGrammarLearner_consistent
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (K : Set (Word α)) ⊆
      correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs f
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K) := by

  exact
    correctedConcreteWorkingGrammarLearner_consistent
      hα obs f K

/-- Certified learner languages are monotone under finite sample extension. -/
theorem correctedConcreteCertifiedWorkingGrammarLearner_language_mono
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    {S K : Finset (Word α)}
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α))) :
    correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs f
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f S) ⊆
      correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs f
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K) := by

  exact
    correctedConcreteWorkingGrammarLearner_language_mono
      hα obs f hSK

/-- The certified learner identifies the same semantic start-rooted target
class as the original actual working-grammar learner. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat) :
    IdentifiesClassFromPositiveData
      (correctedConcreteCertifiedWorkingGrammarHypLanguage
        obs f)
      (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f)
      (StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) := by

  intro L hL T

  rcases
      correctedConcreteWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f
        L hL T with
    ⟨n0, hcorrect⟩

  exact
    ⟨n0,
      by
        intro n hn

        exact
          hcorrect n hn⟩

/-- After the usual target-coverage stage, the grammar inside every later
certified output has exactly the target language. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLearner_correct_after_startRootedCoverageStage
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    {L : Set (Word α)}
    (hL :
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f)
    (T : TextFor L)
    {n : Nat}
    (hn :
      startRootedCorrectedConcreteTargetCoverageStage
          (v := w) obs f hL T <=
        n) :
    (correctedConcreteCertifiedWorkingGrammarLearner
        hα obs f
        (T.prefixSample n)).output.grammar.StringLanguage =
      L := by

  exact
    correctedConcreteWorkingGrammarLearner_correct_after_startRootedCoverageStage
      (v := w) hα obs f hL T hn

end CertifiedLearnerSemanticProperties


section CertifiedLearnerSelectedStagePackage

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- After one finite target-coverage stage, every later certified output is
semantically exact and still carries its complete checked bounded
code/search/selector certificate. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLearner_selectedStage_package :
    ∀ L : Set (Word α),
      L ∈
        StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f →
      ∀ T : TextFor L,
        ∃ n0 : Nat,
          ∀ n : Nat, n0 <= n →
            (correctedConcreteCertifiedWorkingGrammarLearner
                hα obs f
                (T.prefixSample n)).output.grammar.StringLanguage =
              L ∧
            (correctedConcreteCertifiedWorkingGrammarLearner
                hα obs f
                (T.prefixSample n)).selectorResult =
              some
                ((correctedConcreteCertifiedWorkingGrammarLearner
                    hα obs f
                    (T.prefixSample n)).bits,
                  (correctedConcreteCertifiedWorkingGrammarLearner
                    hα obs f
                    (T.prefixSample n)).presentation) ∧
            (correctedConcreteCertifiedWorkingGrammarLearner
                hα obs f
                (T.prefixSample n)).decode
                (correctedConcreteCertifiedWorkingGrammarLearner
                  hα obs f
                  (T.prefixSample n)).bits =
              some
                (correctedConcreteCertifiedWorkingGrammarLearner
                  hα obs f
                  (T.prefixSample n)).presentation ∧
            (correctedConcreteCertifiedWorkingGrammarLearner
                hα obs f
                (T.prefixSample n)).reencode
                (correctedConcreteCertifiedWorkingGrammarLearner
                  hα obs f
                  (T.prefixSample n)).presentation =
              (correctedConcreteCertifiedWorkingGrammarLearner
                hα obs f
                (T.prefixSample n)).bits ∧
            (correctedConcreteCertifiedWorkingGrammarLearner
                hα obs f
                (T.prefixSample n)).bits.length <=
              correctedConcreteCompiledGrammarPaperPowerBitBound
                (sampleLengthBudget
                  (T.prefixSample n))
                f ∧
            (correctedConcreteCertifiedWorkingGrammarLearner
                hα obs f
                (T.prefixSample n)).canonicalSearch.length <=
              2 ^
                (correctedConcreteCompiledGrammarPaperPowerBitBound
                    (sampleLengthBudget
                      (T.prefixSample n))
                    f +
                  1) := by

  intro L hL T

  refine
    ⟨startRootedCorrectedConcreteTargetCoverageStage
        (v := w) obs f hL T,
      ?_⟩

  intro n hn

  let C :=
    correctedConcreteCertifiedWorkingGrammarLearner
      hα obs f
      (T.prefixSample n)

  exact
    ⟨correctedConcreteCertifiedWorkingGrammarLearner_correct_after_startRootedCoverageStage
        (v := w) hα obs f hL T hn,
      C.selector_exact,
      C.decode_bits,
      C.reencode_presentation,
      by simpa [C] using C.bitLength_le,
      by simpa [C] using C.searchLength_le⟩

/-- Final class-level theorem for the learner whose outputs themselves contain
the checked finite-description certificates. -/
theorem
    correctedConcreteCertifiedWorkingGrammarLearner_identification_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (∀ K : Finset (Word α),
        (K : Set (Word α)) ⊆
          correctedConcreteCertifiedWorkingGrammarHypLanguage
            obs f
            (correctedConcreteCertifiedWorkingGrammarLearner
              hα obs f K)) ∧
      (∀ S K : Finset (Word α),
        (S : Set (Word α)) ⊆
            (K : Set (Word α)) →
        correctedConcreteCertifiedWorkingGrammarHypLanguage
            obs f
            (correctedConcreteCertifiedWorkingGrammarLearner
              hα obs f S) ⊆
          correctedConcreteCertifiedWorkingGrammarHypLanguage
            obs f
            (correctedConcreteCertifiedWorkingGrammarLearner
              hα obs f K)) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).selectorResult =
          some
            ((correctedConcreteCertifiedWorkingGrammarLearner
                hα obs f K).bits,
              (correctedConcreteCertifiedWorkingGrammarLearner
                hα obs f K).presentation)) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).decode
            (correctedConcreteCertifiedWorkingGrammarLearner
              hα obs f K).bits =
          some
            (correctedConcreteCertifiedWorkingGrammarLearner
              hα obs f K).presentation) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).reencode
            (correctedConcreteCertifiedWorkingGrammarLearner
              hα obs f K).presentation =
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).bits) ∧
      (∀ K : Finset (Word α),
        ((correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).bits,
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).presentation) ∈
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).canonicalSearch) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).bits.length <=
          correctedConcreteCompiledGrammarPaperPowerBitBound
            (sampleLengthBudget K)
            f) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteCertifiedWorkingGrammarLearner
            hα obs f K).canonicalSearch.length <=
          2 ^
            (correctedConcreteCompiledGrammarPaperPowerBitBound
                (sampleLengthBudget K)
                f +
              1)) := by

  exact
    ⟨correctedConcreteCertifiedWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      correctedConcreteCertifiedWorkingGrammarLearner_consistent
        hα obs f,
      fun S K hSK =>
        correctedConcreteCertifiedWorkingGrammarLearner_language_mono
          hα obs f hSK,
      fun K =>
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K).selector_exact,
      fun K =>
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K).decode_bits,
      fun K =>
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K).reencode_presentation,
      fun K =>
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα obs f K).pair_mem_search,
      correctedConcreteCertifiedWorkingGrammarLearner_bitLength_le
        hα obs f,
      correctedConcreteCertifiedWorkingGrammarLearner_searchLength_le
        hα obs f⟩

end CertifiedLearnerSelectedStagePackage

end MCFG
