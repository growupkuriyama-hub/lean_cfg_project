/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarCanonicalDecodedSearch

/-!
# ConcreteCanonicalLearnerWorkingGrammarCanonicalSearchSelector.lean

The preceding file constructs a finite canonical search containing exactly the
code/presentation pairs satisfying

```text
decode bits = some presentation
and
reencode presentation = bits.
```

The actual learner code and complete presentation occur in that search, and
one source code has at most one decoded presentation.

This file adds an explicit finite-list selector.

## Generic code-indexed selector

For a target Boolean code and a finite pair list, define

```lean
selectCanonicalPairByCode targetCode pairs
```

to return the first pair whose source-code component equals `targetCode`.

The selector is executable and independent of the grammar development.  We
prove

* soundness: every returned pair belongs to the finite list and has the
  requested code;
* completeness: if the list contains a pair with that code, the selector
  returns some pair;
* exactness under value uniqueness; and
* the corresponding value-only selector theorem.

## Budgeted canonical selector

Applying the selector to

```lean
checkedBitCanonicalDecodedCodeSearch encode decode n f
```

gives a finite-search extraction operation.  Every returned pair satisfies

```text
bits.length ≤ paperPowerBitBound n f,
decode bits = some value,
encode value = bits.
```

If one known canonical pair with the target code exists, decoder functionality
makes the selected value unique.

## Canonical learner selector

For a finite sample `K`, use the actual checked learner bit list as the search
key:

```lean
correctedConcreteWorkingGrammarLearnerCanonicalPairSelectorResult
  hα obs f K.
```

The selector returns exactly

```text
some
  (actual learner bit list,
   actual complete compiled presentation).
```

The value-only selector therefore returns exactly the actual presentation.
The selected pair is a member of the finite canonical search and inherits its
checked decoding, exact re-encoding, and paper-power length bound.

Along a positive text for a semantic start-rooted target, after the ordinary
coverage stage, every later prefix has

* exact target language;
* exact selected canonical presentation;
* checked decode/re-encode equations; and
* the same finite-search size bound.

This is an extraction theorem indexed by the already computed learner code.
It is not a new target-discovery criterion that operates without that code.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section GenericCodeIndexedSelector

variable {β : Type z}

/-- Select the first code/value pair whose source-code component equals the
requested target code. -/
def selectCanonicalPairByCode
    (targetCode : List Bool) :
    List (List Bool × β) →
      Option (List Bool × β)

  | [] =>
      none

  | pair :: pairs =>
      if pair.1 = targetCode then
        some pair
      else
        selectCanonicalPairByCode
          targetCode pairs

/-- Every returned pair belongs to the finite source list and has the requested
source code. -/
theorem selectCanonicalPairByCode_sound
    (targetCode : List Bool) :
    ∀
      {pairs : List (List Bool × β)}
      {pair : List Bool × β},
      selectCanonicalPairByCode
          targetCode pairs =
        some pair →
      pair ∈ pairs ∧
        pair.1 = targetCode

  | [], pair, hselect => by
      simp [selectCanonicalPairByCode] at hselect

  | head :: tail, pair, hselect => by
      by_cases hhead :
          head.1 = targetCode

      · have hpair :
            pair = head := by
          simpa [
            selectCanonicalPairByCode,
            hhead
          ] using hselect.symm

        subst pair

        exact
          ⟨by simp,
            hhead⟩

      · have htail :
            selectCanonicalPairByCode
                targetCode tail =
              some pair := by

          simpa [
            selectCanonicalPairByCode,
            hhead
          ] using hselect

        rcases
            selectCanonicalPairByCode_sound
              targetCode htail with
          ⟨hmem, hcode⟩

        exact
          ⟨List.mem_cons_of_mem
              head hmem,
            hcode⟩

/-- If the finite source list contains at least one pair with the requested
code, the selector returns some pair. -/
theorem selectCanonicalPairByCode_exists_of_exists_mem
    (targetCode : List Bool) :
    ∀
      {pairs : List (List Bool × β)},
      (∃ value : β,
        (targetCode, value) ∈ pairs) →
      ∃ pair : List Bool × β,
        selectCanonicalPairByCode
            targetCode pairs =
          some pair

  | [], hexists => by
      rcases hexists with
        ⟨value, hmem⟩

      simp at hmem

  | head :: tail, hexists => by
      by_cases hhead :
          head.1 = targetCode

      · exact
          ⟨head,
            by
              simp [
                selectCanonicalPairByCode,
                hhead
              ]⟩

      · rcases hexists with
          ⟨value, hmem⟩

        rcases List.mem_cons.mp hmem with
          hheadPair | htailPair

        · have hheadCode :
              head.1 = targetCode := by

            rw [← hheadPair]

          exact
            False.elim
              (hhead hheadCode)

        · rcases
              selectCanonicalPairByCode_exists_of_exists_mem
                targetCode
                ⟨value, htailPair⟩ with
            ⟨pair, hselect⟩

          exact
            ⟨pair,
              by
                simpa [
                  selectCanonicalPairByCode,
                  hhead
                ] using hselect⟩

/-- Exactness of the code-indexed selector when every pair carrying the target
code has one specified value. -/
theorem selectCanonicalPairByCode_eq_some_of_mem_of_value_unique
    (targetCode : List Bool)
    (pairs : List (List Bool × β))
    (value : β)
    (hmem :
      (targetCode, value) ∈ pairs)
    (hunique :
      ∀ candidate : β,
        (targetCode, candidate) ∈ pairs →
          candidate = value) :
    selectCanonicalPairByCode
        targetCode pairs =
      some (targetCode, value) := by

  rcases
      selectCanonicalPairByCode_exists_of_exists_mem
        targetCode
        (pairs := pairs)
        ⟨value, hmem⟩ with
    ⟨pair, hselect⟩

  rcases pair with
    ⟨bits, candidate⟩

  have hsound :
      (bits, candidate) ∈ pairs ∧
        bits = targetCode :=
    selectCanonicalPairByCode_sound
      targetCode hselect

  rcases hsound with
    ⟨hpair, hbits⟩

  subst bits

  have hcandidate :
      candidate = value :=
    hunique candidate hpair

  subst candidate

  exact hselect

/-- The selector returns `none` exactly when no pair has the requested code. -/
theorem selectCanonicalPairByCode_eq_none_iff
    (targetCode : List Bool)
    (pairs : List (List Bool × β)) :
    selectCanonicalPairByCode
        targetCode pairs =
      none ↔
    ∀ value : β,
      (targetCode, value) ∉ pairs := by

  constructor

  · intro hnone value hmem

    rcases
        selectCanonicalPairByCode_exists_of_exists_mem
          targetCode
          (pairs := pairs)
          ⟨value, hmem⟩ with
      ⟨pair, hsome⟩

    rw [hnone] at hsome

    simp at hsome

  · intro hall

    cases hselect :
        selectCanonicalPairByCode
          targetCode pairs with

    | none =>
        rfl

    | some pair =>
        rcases pair with
          ⟨bits, value⟩

        have hsound :
            (bits, value) ∈ pairs ∧
              bits = targetCode :=
          selectCanonicalPairByCode_sound
            targetCode hselect

        rcases hsound with
          ⟨hmem, hbits⟩

        subst bits

        exact
          False.elim
            (hall value hmem)

/-- Select only the decoded value, forgetting the source-code component. -/
def selectCanonicalValueByCode
    (targetCode : List Bool)
    (pairs : List (List Bool × β)) :
    Option β :=
  match
    selectCanonicalPairByCode
      targetCode pairs with

  | none =>
      none

  | some pair =>
      some pair.2

/-- Exact value-only selection under code-level membership and value
uniqueness. -/
theorem selectCanonicalValueByCode_eq_some_of_mem_of_value_unique
    (targetCode : List Bool)
    (pairs : List (List Bool × β))
    (value : β)
    (hmem :
      (targetCode, value) ∈ pairs)
    (hunique :
      ∀ candidate : β,
        (targetCode, candidate) ∈ pairs →
          candidate = value) :
    selectCanonicalValueByCode
        targetCode pairs =
      some value := by

  rw [
    selectCanonicalPairByCode_eq_some_of_mem_of_value_unique
      targetCode pairs value hmem hunique
  ]

  rfl

/-- Every successfully selected value has a corresponding pair in the source
list with the requested code. -/
theorem selectCanonicalValueByCode_sound
    (targetCode : List Bool)
    (pairs : List (List Bool × β))
    {value : β}
    (hselect :
      selectCanonicalValueByCode
          targetCode pairs =
        some value) :
    (targetCode, value) ∈ pairs := by

  unfold
    selectCanonicalValueByCode at hselect

  cases hpair :
      selectCanonicalPairByCode
        targetCode pairs with

  | none =>
      simp [hpair] at hselect

  | some pair =>
      rcases pair with
        ⟨bits, candidate⟩

      simp [hpair] at hselect
      subst candidate

      have hsound :
          (bits, value) ∈ pairs ∧
            bits = targetCode :=
        selectCanonicalPairByCode_sound
          targetCode hpair

      rcases hsound with
        ⟨hmem, hbits⟩

      subst bits

      exact hmem

end GenericCodeIndexedSelector


section BudgetedCanonicalCodeSelector

variable {β : Type z}

/-- Select a canonical decoded pair at budget level `(n,f)` by its source code. -/
def checkedBitCanonicalPairSelectorByCode
    (targetCode : List Bool)
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (n f : Nat) :
    Option (List Bool × β) :=
  selectCanonicalPairByCode
    targetCode
    (checkedBitCanonicalDecodedCodeSearch
      encode decode n f)

/-- Select only the canonical decoded value at budget level `(n,f)`. -/
def checkedBitCanonicalValueSelectorByCode
    (targetCode : List Bool)
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (n f : Nat) :
    Option β :=
  selectCanonicalValueByCode
    targetCode
    (checkedBitCanonicalDecodedCodeSearch
      encode decode n f)

/-- Every budgeted selected pair is in the finite canonical search and carries
the requested source code. -/
theorem checkedBitCanonicalPairSelectorByCode_sound
    (targetCode : List Bool)
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (n f : Nat)
    {pair : List Bool × β}
    (hselect :
      checkedBitCanonicalPairSelectorByCode
          targetCode encode decode n f =
        some pair) :
    pair ∈
        checkedBitCanonicalDecodedCodeSearch
          encode decode n f ∧
      pair.1 = targetCode := by

  exact
    selectCanonicalPairByCode_sound
      targetCode hselect

/-- Every selected budgeted pair has a bounded source code, successful checked
decoding, and exact re-encoding. -/
theorem
    checkedBitCanonicalPairSelectorByCode_checked
    (targetCode : List Bool)
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (n f : Nat)
    {bits : List Bool}
    {value : β}
    (hselect :
      checkedBitCanonicalPairSelectorByCode
          targetCode encode decode n f =
        some (bits, value)) :
    bits = targetCode ∧
      bits.length <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
          n f ∧
      decode bits = some value ∧
      encode value = bits := by

  have hsound :
      (bits, value) ∈
          checkedBitCanonicalDecodedCodeSearch
            encode decode n f ∧
        bits = targetCode :=
    checkedBitCanonicalPairSelectorByCode_sound
      targetCode encode decode n f
      hselect

  rcases hsound with
    ⟨hpair, hbits⟩

  rcases
      (mem_checkedBitCanonicalDecodedCodeSearch_iff
        encode decode n f bits value).mp
        hpair with
    ⟨huniverse, hdecode, hencode⟩

  exact
    ⟨hbits,
      (mem_correctedConcreteCompiledGrammarCheckedBitCodeUniverse_iff
        bits n f).mp
        huniverse,
      hdecode,
      hencode⟩

/-- Exact budgeted pair selection when the target-code value is unique. -/
theorem
    checkedBitCanonicalPairSelectorByCode_eq_some_of_mem_of_value_unique
    (targetCode : List Bool)
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (n f : Nat)
    (value : β)
    (hmem :
      (targetCode, value) ∈
        checkedBitCanonicalDecodedCodeSearch
          encode decode n f)
    (hunique :
      ∀ candidate : β,
        (targetCode, candidate) ∈
            checkedBitCanonicalDecodedCodeSearch
              encode decode n f →
          candidate = value) :
    checkedBitCanonicalPairSelectorByCode
        targetCode encode decode n f =
      some (targetCode, value) := by

  exact
    selectCanonicalPairByCode_eq_some_of_mem_of_value_unique
      targetCode
      (checkedBitCanonicalDecodedCodeSearch
        encode decode n f)
      value
      hmem
      hunique

/-- Exact budgeted value-only selection when the target-code value is unique. -/
theorem
    checkedBitCanonicalValueSelectorByCode_eq_some_of_mem_of_value_unique
    (targetCode : List Bool)
    (encode : β → List Bool)
    (decode : List Bool → Option β)
    (n f : Nat)
    (value : β)
    (hmem :
      (targetCode, value) ∈
        checkedBitCanonicalDecodedCodeSearch
          encode decode n f)
    (hunique :
      ∀ candidate : β,
        (targetCode, candidate) ∈
            checkedBitCanonicalDecodedCodeSearch
              encode decode n f →
          candidate = value) :
    checkedBitCanonicalValueSelectorByCode
        targetCode encode decode n f =
      some value := by

  exact
    selectCanonicalValueByCode_eq_some_of_mem_of_value_unique
      targetCode
      (checkedBitCanonicalDecodedCodeSearch
        encode decode n f)
      value
      hmem
      hunique

end BudgetedCanonicalCodeSelector


section CanonicalLearnerSelectorDefinitions

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- The actual complete tagged presentation of one canonical learner output. -/
noncomputable def
    correctedConcreteWorkingGrammarLearnerActualPresentation
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    List
      (CorrectedConcreteCompiledGrammarPresentationEntry
        (correctedConcreteFiniteHypothesis K obs f)) :=
  (correctedConcreteFiniteHypothesis K obs f).
    compiledGrammarPresentationEntries
      (Classical.choice hα)

/-- Select from the finite canonical search by the actual checked learner code. -/
noncomputable def
    correctedConcreteWorkingGrammarLearnerCanonicalPairSelectorResult
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    Option
      (List Bool ×
        List
          (CorrectedConcreteCompiledGrammarPresentationEntry
            (correctedConcreteFiniteHypothesis K obs f))) :=
  checkedBitCanonicalPairSelectorByCode
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
      hα obs f K)
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
      hα obs f K)
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
      hα obs f K)
    (sampleLengthBudget K)
    f

/-- Value-only canonical selector indexed by the actual checked learner code. -/
noncomputable def
    correctedConcreteWorkingGrammarLearnerCanonicalPresentationSelectorResult
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    Option
      (List
        (CorrectedConcreteCompiledGrammarPresentationEntry
          (correctedConcreteFiniteHypothesis K obs f))) :=
  checkedBitCanonicalValueSelectorByCode
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
      hα obs f K)
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
      hα obs f K)
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
      hα obs f K)
    (sampleLengthBudget K)
    f

end CanonicalLearnerSelectorDefinitions


section CanonicalLearnerSelectorCorrectness

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]

/-- Every canonical-search pair carrying the actual learner code has the actual
complete learner presentation. -/
theorem
    correctedConcreteWorkingGrammarLearner_canonicalSearch_actualCode_value_unique
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α))
    (candidate :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry
          (correctedConcreteFiniteHypothesis K obs f)))
    (hcandidate :
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
          hα obs f K,
        candidate) ∈
        correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
          hα obs f K) :
    candidate =
      correctedConcreteWorkingGrammarLearnerActualPresentation
        hα obs f K := by

  exact
    correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_value_unique
      hα obs f K
      hcandidate
      (by
        simpa [
          correctedConcreteWorkingGrammarLearnerActualPresentation
        ] using
          correctedConcreteWorkingGrammarLearner_actualCodePresentation_mem_canonicalSearch
            hα obs f K)

/-- The code-indexed finite selector returns exactly the actual learner
code/presentation pair. -/
@[simp] theorem
    correctedConcreteWorkingGrammarLearnerCanonicalPairSelectorResult_eq
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteWorkingGrammarLearnerCanonicalPairSelectorResult
        hα obs f K =
      some
        (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
            hα obs f K,
          correctedConcreteWorkingGrammarLearnerActualPresentation
            hα obs f K) := by

  unfold
    correctedConcreteWorkingGrammarLearnerCanonicalPairSelectorResult

  apply
    checkedBitCanonicalPairSelectorByCode_eq_some_of_mem_of_value_unique

  · simpa [
      correctedConcreteWorkingGrammarLearnerActualPresentation
    ] using
      correctedConcreteWorkingGrammarLearner_actualCodePresentation_mem_canonicalSearch
        hα obs f K

  · intro candidate hcandidate

    exact
      correctedConcreteWorkingGrammarLearner_canonicalSearch_actualCode_value_unique
        hα obs f K candidate hcandidate

/-- The value-only finite selector returns exactly the actual complete learner
presentation. -/
@[simp] theorem
    correctedConcreteWorkingGrammarLearnerCanonicalPresentationSelectorResult_eq
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteWorkingGrammarLearnerCanonicalPresentationSelectorResult
        hα obs f K =
      some
        (correctedConcreteWorkingGrammarLearnerActualPresentation
          hα obs f K) := by

  unfold
    correctedConcreteWorkingGrammarLearnerCanonicalPresentationSelectorResult

  apply
    checkedBitCanonicalValueSelectorByCode_eq_some_of_mem_of_value_unique

  · simpa [
      correctedConcreteWorkingGrammarLearnerActualPresentation
    ] using
      correctedConcreteWorkingGrammarLearner_actualCodePresentation_mem_canonicalSearch
        hα obs f K

  · intro candidate hcandidate

    exact
      correctedConcreteWorkingGrammarLearner_canonicalSearch_actualCode_value_unique
        hα obs f K candidate hcandidate

/-- The selected pair is a member of the finite canonical search. -/
theorem
    correctedConcreteWorkingGrammarLearner_selectedCanonicalPair_mem_search
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f K,
      correctedConcreteWorkingGrammarLearnerActualPresentation
        hα obs f K) ∈
      correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
        hα obs f K := by

  simpa [
    correctedConcreteWorkingGrammarLearnerActualPresentation
  ] using
    correctedConcreteWorkingGrammarLearner_actualCodePresentation_mem_canonicalSearch
      hα obs f K

/-- The selected presentation is checked by decoding the selected source code. -/
theorem
    correctedConcreteWorkingGrammarLearner_selectedCanonicalPresentation_decode
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
        hα obs f K
        (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
          hα obs f K) =
      some
        (correctedConcreteWorkingGrammarLearnerActualPresentation
          hα obs f K) := by

  simpa [
    correctedConcreteWorkingGrammarLearnerActualPresentation
  ] using
    correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode_encode
      hα obs f K

/-- Re-encoding the selected presentation returns the selected source code. -/
theorem
    correctedConcreteWorkingGrammarLearner_selectedCanonicalPresentation_reencode
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
        hα obs f K
        (correctedConcreteWorkingGrammarLearnerActualPresentation
          hα obs f K) =
      correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f K := by

  simpa [
    correctedConcreteWorkingGrammarLearnerActualPresentation
  ] using
    correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode_actual
      hα obs f K

/-- The selected source code satisfies the final paper-power bit budget. -/
theorem
    correctedConcreteWorkingGrammarLearner_selectedCanonicalCode_length_le
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
        hα obs f K).length <=
      correctedConcreteCompiledGrammarPaperPowerBitBound
        (sampleLengthBudget K)
        f := by

  exact
    correctedConcreteWorkingGrammarLearnerLogarithmicBitList_length_le_paperPower
      hα obs f K

/-- Compact exact-selector package for one learner output. -/
theorem
    correctedConcreteWorkingGrammarLearner_canonicalSelector_package
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteWorkingGrammarLearnerCanonicalPairSelectorResult
        hα obs f K =
      some
        (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
            hα obs f K,
          correctedConcreteWorkingGrammarLearnerActualPresentation
            hα obs f K)) ∧
      (correctedConcreteWorkingGrammarLearnerCanonicalPresentationSelectorResult
          hα obs f K =
        some
          (correctedConcreteWorkingGrammarLearnerActualPresentation
            hα obs f K)) ∧
      ((correctedConcreteWorkingGrammarLearnerLogarithmicBitList
          hα obs f K,
        correctedConcreteWorkingGrammarLearnerActualPresentation
          hα obs f K) ∈
        correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
          hα obs f K) ∧
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitDecode
          hα obs f K
          (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
            hα obs f K) =
        some
          (correctedConcreteWorkingGrammarLearnerActualPresentation
            hα obs f K)) ∧
      (correctedConcreteWorkingGrammarLearnerLogarithmicBitReencode
          hα obs f K
          (correctedConcreteWorkingGrammarLearnerActualPresentation
            hα obs f K) =
        correctedConcreteWorkingGrammarLearnerLogarithmicBitList
          hα obs f K) ∧
      ((correctedConcreteWorkingGrammarLearnerLogarithmicBitList
          hα obs f K).length <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
          (sampleLengthBudget K)
          f) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearnerCanonicalPairSelectorResult_eq
        hα obs f K,
      correctedConcreteWorkingGrammarLearnerCanonicalPresentationSelectorResult_eq
        hα obs f K,
      correctedConcreteWorkingGrammarLearner_selectedCanonicalPair_mem_search
        hα obs f K,
      correctedConcreteWorkingGrammarLearner_selectedCanonicalPresentation_decode
        hα obs f K,
      correctedConcreteWorkingGrammarLearner_selectedCanonicalPresentation_reencode
        hα obs f K,
      correctedConcreteWorkingGrammarLearner_selectedCanonicalCode_length_le
        hα obs f K⟩

end CanonicalLearnerSelectorCorrectness


section EventualCanonicalSelectorPackage

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- After the standard coverage stage, every later actual output has exact
target language and its finite canonical selector returns exactly the complete
actual presentation. -/
theorem
    correctedConcreteWorkingGrammarLearner_selectedStage_canonicalSelector_package :
    ∀ L : Set (Word α),
      L ∈ StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f →
      ∀ T : TextFor L,
        ∃ n0 : Nat,
          ∀ n : Nat, n0 <= n →
            (correctedConcreteWorkingGrammarLearner
                hα obs f
                (T.prefixSample n)).grammar.StringLanguage =
              L ∧
            correctedConcreteWorkingGrammarLearnerCanonicalPairSelectorResult
                hα obs f
                (T.prefixSample n) =
              some
                (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
                    hα obs f
                    (T.prefixSample n),
                  correctedConcreteWorkingGrammarLearnerActualPresentation
                    hα obs f
                    (T.prefixSample n)) ∧
            correctedConcreteWorkingGrammarLearnerCanonicalPresentationSelectorResult
                hα obs f
                (T.prefixSample n) =
              some
                (correctedConcreteWorkingGrammarLearnerActualPresentation
                  hα obs f
                  (T.prefixSample n)) ∧
            (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
                hα obs f
                (T.prefixSample n)).length <=
              correctedConcreteCompiledGrammarPaperPowerBitBound
                (sampleLengthBudget
                  (T.prefixSample n))
                f := by

  intro L hL T

  refine
    ⟨startRootedCorrectedConcreteTargetCoverageStage
        (v := w) obs f hL T,
      ?_⟩

  intro n hn

  exact
    ⟨correctedConcreteWorkingGrammarLearner_correct_after_startRootedCoverageStage
        (v := w) hα obs f hL T hn,
      correctedConcreteWorkingGrammarLearnerCanonicalPairSelectorResult_eq
        hα obs f
        (T.prefixSample n),
      correctedConcreteWorkingGrammarLearnerCanonicalPresentationSelectorResult_eq
        hα obs f
        (T.prefixSample n),
      correctedConcreteWorkingGrammarLearner_selectedCanonicalCode_length_le
        hα obs f
        (T.prefixSample n)⟩

/-- Final identification plus exact finite canonical-selector package. -/
theorem
    correctedConcreteWorkingGrammarLearner_identification_canonicalSelector_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (∀ K : Finset (Word α),
        correctedConcreteWorkingGrammarLearnerCanonicalPairSelectorResult
            hα obs f K =
          some
            (correctedConcreteWorkingGrammarLearnerLogarithmicBitList
                hα obs f K,
              correctedConcreteWorkingGrammarLearnerActualPresentation
                hα obs f K)) ∧
      (∀ K : Finset (Word α),
        correctedConcreteWorkingGrammarLearnerCanonicalPresentationSelectorResult
            hα obs f K =
          some
            (correctedConcreteWorkingGrammarLearnerActualPresentation
              hα obs f K)) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
            hα obs f K).length <=
          2 ^
            (correctedConcreteCompiledGrammarPaperPowerBitBound
                (sampleLengthBudget K)
                f +
              1)) ∧
      (∀ L : Set (Word α),
        L ∈ StartRootedCorrectedConcreteTargetClass
            (v := w) α M obs f →
        ∀ T : TextFor L,
          ∃ n0 : Nat,
            ∀ n : Nat, n0 <= n →
              (correctedConcreteWorkingGrammarLearner
                  hα obs f
                  (T.prefixSample n)).grammar.StringLanguage =
                L ∧
              correctedConcreteWorkingGrammarLearnerCanonicalPresentationSelectorResult
                  hα obs f
                  (T.prefixSample n) =
                some
                  (correctedConcreteWorkingGrammarLearnerActualPresentation
                    hα obs f
                    (T.prefixSample n))) := by

  refine
    ⟨correctedConcreteWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      correctedConcreteWorkingGrammarLearnerCanonicalPairSelectorResult_eq
        hα obs f,
      correctedConcreteWorkingGrammarLearnerCanonicalPresentationSelectorResult_eq
        hα obs f,
      correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch_length_le
        hα obs f,
      ?_⟩

  intro L hL T

  rcases
      correctedConcreteWorkingGrammarLearner_selectedStage_canonicalSelector_package
        (v := w) hα obs f L hL T with
    ⟨n0, hstage⟩

  exact
    ⟨n0,
      by
        intro n hn

        rcases hstage n hn with
          ⟨hlanguage,
            hpairSelector,
            hpresentationSelector,
            hlength⟩

        exact
          ⟨hlanguage,
            hpresentationSelector⟩⟩

end EventualCanonicalSelectorPackage

end MCFG
