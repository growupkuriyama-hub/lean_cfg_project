/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarDenseEncoding

/-!
# ConcreteCanonicalLearnerWorkingGrammarTaggedDenseEncoding.lean

The preceding dense encoding assigned short position codes separately inside
four presentation sections:

* nonterminals;
* start rules;
* terminal rules;
* binary rules.

That convention is sufficient when the section tag is carried externally, but
raw natural-number codes may then be reused between different sections.  This
file makes the tag explicit in the encoded object and concatenates the four
finite sections into one global presentation list.

The first-occurrence position in that global tagged list gives one canonical
code space.  We prove:

```lean
entry ∈ H.compiledGrammarPresentationEntries dummy
  -> H.compiledGrammarGlobalDenseCode dummy entry
       < H.compiledGrammarPresentationItemCount
```

and, more importantly, injectivity on all actually stored tagged entries:

```lean
code entry₁ = code entry₂ -> entry₁ = entry₂.
```

Thus entries from different rule categories cannot collide.  The resulting
natural encoding still fits in the binary length of the complete presentation
item count, so it inherits the item-count-times-logarithmic-width description
bound from the preceding files.

This is an injective encoding of the finite top-level presentation entries
relative to their explicit global list.  It still does not claim that internal
terminal words and dependent templates have been serialized independently of
that list; that is a later structural-serialization layer.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section FirstOccurrenceInjectivity

/-- On elements that really occur in a list, the first-occurrence position is
injective.  Duplicate copies of one value do not cause a problem: all copies
have the same first position, while distinct values have distinct first
positions. -/
theorem listFirstIndex_injective_on_mem
    {β : Type u}
    [DecidableEq β] :
    ∀ (xs : List β) {x y : β},
      x ∈ xs →
      y ∈ xs →
      listFirstIndex x xs = listFirstIndex y xs →
      x = y

  | [], x, y, hx, _, _ => by
      simp at hx

  | z :: zs, x, y, hx, hy, hindex => by
      by_cases hxz : x = z

      · subst x

        by_cases hyz : y = z

        · exact hyz.symm

        · have himpossible :
              0 = listFirstIndex y zs + 1 := by
            simpa [listFirstIndex, hyz] using hindex

          omega

      · by_cases hyz : y = z

        · subst y

          have himpossible :
              listFirstIndex x zs + 1 = 0 := by
            simpa [listFirstIndex, hxz] using hindex

          omega

        · have hxTail : x ∈ zs := by
            simpa [hxz] using hx

          have hyTail : y ∈ zs := by
            simpa [hyz] using hy

          have hTailIndex :
              listFirstIndex x zs =
                listFirstIndex y zs := by
            simpa [listFirstIndex, hxz, hyz] using hindex

          exact
            listFirstIndex_injective_on_mem
              zs hxTail hyTail hTailIndex

end FirstOccurrenceInjectivity


section TaggedPresentationEntries

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- One tagged top-level entry of the actual cut-compiled grammar
presentation.  The constructors make the four sections disjoint even when
their local position codes happen to coincide. -/
inductive CorrectedConcreteCompiledGrammarPresentationEntry
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) where

  | nonterminal
      (A : CorrectedConcreteCutGrammarNonterminal H)

  | startRule
      (ρ : StartRule
        (CorrectedConcreteCutGrammarNonterminal H))

  | terminalRule
      (ρ : TerminalRule
        (CorrectedConcreteCutGrammarNonterminal H)
        α)

  | binaryRule
      (ρ : BinaryRule
        (CorrectedConcreteCutGrammarNonterminal H)
        α
        (correctedConcreteCutGrammarArity H))

/-- The complete tagged presentation list, in the canonical section order
nonterminals, start rules, terminal rules, binary rules. -/
noncomputable def
    CorrectedConcreteFiniteHypothesis.compiledGrammarPresentationEntries
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    List
      (CorrectedConcreteCompiledGrammarPresentationEntry H) :=
  H.compiledGrammarNonterminals.map
      CorrectedConcreteCompiledGrammarPresentationEntry.nonterminal ++
    (H.toCutWorkingMCFG dummy).startRules.map
      CorrectedConcreteCompiledGrammarPresentationEntry.startRule ++
    (H.toCutWorkingMCFG dummy).terminalRules.map
      CorrectedConcreteCompiledGrammarPresentationEntry.terminalRule ++
    (H.toCutWorkingMCFG dummy).binaryRules.map
      CorrectedConcreteCompiledGrammarPresentationEntry.binaryRule

namespace CorrectedConcreteFiniteHypothesis

variable
  (H :
    CorrectedConcreteFiniteHypothesis
      K obs f)

/-- The global tagged list has exactly the previously verified complete
presentation item count. -/
@[simp] theorem compiledGrammarPresentationEntries_length
    (dummy : α) :
    (H.compiledGrammarPresentationEntries dummy).length =
      H.compiledGrammarPresentationItemCount := by

  rw [← H.toCutWorkingMCFGPresentationItemCount_eq dummy]

  simp [
    CorrectedConcreteFiniteHypothesis.compiledGrammarPresentationEntries,
    CorrectedConcreteFiniteHypothesis.toCutWorkingMCFGPresentationItemCount,
    Nat.add_assoc
  ]

/-- Every stored nonterminal gives a member of the tagged global list. -/
theorem nonterminal_mem_compiledGrammarPresentationEntries
    (dummy : α)
    (A : CorrectedConcreteCutGrammarNonterminal H)
    (hA : A ∈ H.compiledGrammarNonterminals) :
    CorrectedConcreteCompiledGrammarPresentationEntry.nonterminal A ∈
      H.compiledGrammarPresentationEntries dummy := by

  simp [
    CorrectedConcreteFiniteHypothesis.compiledGrammarPresentationEntries,
    hA
  ]

/-- Every stored start rule gives a member of the tagged global list. -/
theorem startRule_mem_compiledGrammarPresentationEntries
    (dummy : α)
    (ρ : StartRule
      (CorrectedConcreteCutGrammarNonterminal H))
    (hρ : ρ ∈ (H.toCutWorkingMCFG dummy).startRules) :
    CorrectedConcreteCompiledGrammarPresentationEntry.startRule ρ ∈
      H.compiledGrammarPresentationEntries dummy := by

  simp [
    CorrectedConcreteFiniteHypothesis.compiledGrammarPresentationEntries,
    hρ
  ]

/-- Every stored terminal rule gives a member of the tagged global list. -/
theorem terminalRule_mem_compiledGrammarPresentationEntries
    (dummy : α)
    (ρ : TerminalRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α)
    (hρ : ρ ∈ (H.toCutWorkingMCFG dummy).terminalRules) :
    CorrectedConcreteCompiledGrammarPresentationEntry.terminalRule ρ ∈
      H.compiledGrammarPresentationEntries dummy := by

  simp [
    CorrectedConcreteFiniteHypothesis.compiledGrammarPresentationEntries,
    hρ
  ]

/-- Every stored binary rule gives a member of the tagged global list. -/
theorem binaryRule_mem_compiledGrammarPresentationEntries
    (dummy : α)
    (ρ : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hρ : ρ ∈ (H.toCutWorkingMCFG dummy).binaryRules) :
    CorrectedConcreteCompiledGrammarPresentationEntry.binaryRule ρ ∈
      H.compiledGrammarPresentationEntries dummy := by

  simp [
    CorrectedConcreteFiniteHypothesis.compiledGrammarPresentationEntries,
    hρ
  ]

/-- First-occurrence position of one tagged entry in the complete global
presentation list. -/
noncomputable def compiledGrammarGlobalDenseCode
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H) :
    Nat := by

  classical

  exact
    listFirstIndex entry
      (H.compiledGrammarPresentationEntries dummy)

/-- Every actually stored tagged entry receives a code strictly below the
complete presentation item count. -/
theorem compiledGrammarGlobalDenseCode_lt_presentationItemCount
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hentry :
      entry ∈ H.compiledGrammarPresentationEntries dummy) :
    H.compiledGrammarGlobalDenseCode dummy entry <
      H.compiledGrammarPresentationItemCount := by

  classical

  unfold compiledGrammarGlobalDenseCode

  simpa using
    (listFirstIndex_lt_length_of_mem
      entry
      (H.compiledGrammarPresentationEntries dummy)
      hentry)

/-- The global dense code is injective on all entries stored in the tagged
presentation list. -/
theorem compiledGrammarGlobalDenseCode_injective_on_storedEntries
    (dummy : α)
    {entry₁ entry₂ :
      CorrectedConcreteCompiledGrammarPresentationEntry H}
    (hentry₁ :
      entry₁ ∈ H.compiledGrammarPresentationEntries dummy)
    (hentry₂ :
      entry₂ ∈ H.compiledGrammarPresentationEntries dummy)
    (hcode :
      H.compiledGrammarGlobalDenseCode dummy entry₁ =
        H.compiledGrammarGlobalDenseCode dummy entry₂) :
    entry₁ = entry₂ := by

  classical

  unfold compiledGrammarGlobalDenseCode at hcode

  exact
    listFirstIndex_injective_on_mem
      (H.compiledGrammarPresentationEntries dummy)
      hentry₁ hentry₂ hcode

/-- The global tagged code yields an ordinary four-field natural encoding by
inserting the appropriate constructor before taking the global position. -/
noncomputable def taggedDenseNaturalEncoding
    (dummy : α) :
    CorrectedConcreteCompiledGrammarNaturalEncoding H where

  nonterminal := fun A =>
    H.compiledGrammarGlobalDenseCode dummy
      (.nonterminal A)

  startRule := fun ρ =>
    H.compiledGrammarGlobalDenseCode dummy
      (.startRule ρ)

  terminalRule := fun ρ =>
    H.compiledGrammarGlobalDenseCode dummy
      (.terminalRule ρ)

  binaryRule := fun ρ =>
    H.compiledGrammarGlobalDenseCode dummy
      (.binaryRule ρ)

/-- Every code used by the tagged dense natural encoding is below the complete
presentation item count. -/
theorem taggedDenseNaturalEncoding_codesBelow_presentationItemCount
    (dummy : α) :
    (H.taggedDenseNaturalEncoding dummy).CodesBelow
      dummy H.compiledGrammarPresentationItemCount := by

  classical

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro A hA

    exact
      H.compiledGrammarGlobalDenseCode_lt_presentationItemCount
        dummy
        (.nonterminal A)
        (H.nonterminal_mem_compiledGrammarPresentationEntries
          dummy A hA)

  · intro ρ hρ

    exact
      H.compiledGrammarGlobalDenseCode_lt_presentationItemCount
        dummy
        (.startRule ρ)
        (H.startRule_mem_compiledGrammarPresentationEntries
          dummy ρ hρ)

  · intro ρ hρ

    exact
      H.compiledGrammarGlobalDenseCode_lt_presentationItemCount
        dummy
        (.terminalRule ρ)
        (H.terminalRule_mem_compiledGrammarPresentationEntries
          dummy ρ hρ)

  · intro ρ hρ

    exact
      H.compiledGrammarGlobalDenseCode_lt_presentationItemCount
        dummy
        (.binaryRule ρ)
        (H.binaryRule_mem_compiledGrammarPresentationEntries
          dummy ρ hρ)

/-- All tagged dense codes fit in the binary length of the complete
presentation item count. -/
theorem taggedDenseNaturalEncoding_codesFitInBits_presentationItemCount
    (dummy : α) :
    (H.taggedDenseNaturalEncoding dummy).CodesFitInBits
      dummy
      (binaryNatCodeLength
        H.compiledGrammarPresentationItemCount) := by

  rcases
    H.taggedDenseNaturalEncoding_codesBelow_presentationItemCount dummy with
    ⟨hN, hS, hT, hB⟩

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro A hA
    exact
      (hN A hA).trans
        (natCode_lt_two_pow_binaryNatCodeLength
          H.compiledGrammarPresentationItemCount)

  · intro ρ hρ
    exact
      (hS ρ hρ).trans
        (natCode_lt_two_pow_binaryNatCodeLength
          H.compiledGrammarPresentationItemCount)

  · intro ρ hρ
    exact
      (hT ρ hρ).trans
        (natCode_lt_two_pow_binaryNatCodeLength
          H.compiledGrammarPresentationItemCount)

  · intro ρ hρ
    exact
      (hB ρ hρ).trans
        (natCode_lt_two_pow_binaryNatCodeLength
          H.compiledGrammarPresentationItemCount)

/-- The automatic width of the globally tagged encoding is no larger than the
binary length of the presentation item count. -/
theorem taggedDenseNaturalEncoding_automaticBitWidth_le_presentationItemLength
    (dummy : α) :
    (H.taggedDenseNaturalEncoding dummy).automaticBitWidth dummy ≤
      binaryNatCodeLength
        H.compiledGrammarPresentationItemCount := by

  apply
    (H.taggedDenseNaturalEncoding dummy).
      automaticBitWidth_le_of_codesFitInBits
        dummy
        (binaryNatCodeLength
          H.compiledGrammarPresentationItemCount)

  · simp [binaryNatCodeLength]

  · exact
      H.taggedDenseNaturalEncoding_codesFitInBits_presentationItemCount
        dummy

/-- The globally injective tagged encoding has the same optimal top-level
item-count-times-logarithmic-width payload estimate as the section-local dense
encoding. -/
theorem taggedDenseNaturalEncoding_binaryDescriptionSize_le_itemCount_mul_logWidth
    (dummy : α) :
    (H.taggedDenseNaturalEncoding dummy).binaryDescriptionSize dummy ≤
      H.compiledGrammarPresentationItemCount *
        binaryNatCodeLength
          H.compiledGrammarPresentationItemCount := by

  calc
    (H.taggedDenseNaturalEncoding dummy).binaryDescriptionSize dummy ≤
        H.compiledGrammarPresentationItemCount *
          (H.taggedDenseNaturalEncoding dummy).automaticBitWidth dummy :=
      (H.taggedDenseNaturalEncoding dummy).
        binaryDescriptionSize_le_presentationItemCount_mul_automaticBitWidth
          dummy

    _ ≤
        H.compiledGrammarPresentationItemCount *
          binaryNatCodeLength
            H.compiledGrammarPresentationItemCount :=
      Nat.mul_le_mul_left
        H.compiledGrammarPresentationItemCount
        (H.taggedDenseNaturalEncoding_automaticBitWidth_le_presentationItemLength
          dummy)

end CorrectedConcreteFiniteHypothesis

end TaggedPresentationEntries


section PaperFacingTaggedDenseBound

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Paper-facing tagged dense payload bound obtained by using the already
verified presentation-item bound as both the item bound and the source of the
common logarithmic code width. -/
theorem correctedConcreteFiniteHypothesis_taggedDenseBinaryDescriptionSize_le_paperBound
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    let H :=
      correctedConcreteFiniteHypothesis K obs f
    let B :=
      correctedConcreteCompiledGrammarPresentationItemBound
        (sampleLengthBudget K) f
    (H.taggedDenseNaturalEncoding dummy).binaryDescriptionSize dummy ≤
      B * binaryNatCodeLength B := by

  dsimp

  let H :=
    correctedConcreteFiniteHypothesis K obs f

  let B :=
    correctedConcreteCompiledGrammarPresentationItemBound
      (sampleLengthBudget K) f

  have hitems :
      H.compiledGrammarPresentationItemCount ≤ B := by
    exact
      correctedConcreteFiniteHypothesis_presentationItemCount_le_paperBound
        K obs f

  have hfit :
      (H.taggedDenseNaturalEncoding dummy).CodesFitInBits
        dummy (binaryNatCodeLength B) := by

    rcases
      H.taggedDenseNaturalEncoding_codesBelow_presentationItemCount dummy with
      ⟨hN, hS, hT, hBinary⟩

    refine ⟨?_, ?_, ?_, ?_⟩

    · intro A hA
      exact
        ((hN A hA).trans_le hitems).trans
          (natCode_lt_two_pow_binaryNatCodeLength B)

    · intro ρ hρ
      exact
        ((hS ρ hρ).trans_le hitems).trans
          (natCode_lt_two_pow_binaryNatCodeLength B)

    · intro ρ hρ
      exact
        ((hT ρ hρ).trans_le hitems).trans
          (natCode_lt_two_pow_binaryNatCodeLength B)

    · intro ρ hρ
      exact
        ((hBinary ρ hρ).trans_le hitems).trans
          (natCode_lt_two_pow_binaryNatCodeLength B)

  have hwidth :
      (H.taggedDenseNaturalEncoding dummy).automaticBitWidth dummy ≤
        binaryNatCodeLength B := by

    apply
      (H.taggedDenseNaturalEncoding dummy).
        automaticBitWidth_le_of_codesFitInBits
          dummy (binaryNatCodeLength B)

    · simp [binaryNatCodeLength]

    · exact hfit

  calc
    (H.taggedDenseNaturalEncoding dummy).binaryDescriptionSize dummy ≤
        H.compiledGrammarPresentationItemCount *
          (H.taggedDenseNaturalEncoding dummy).automaticBitWidth dummy :=
      (H.taggedDenseNaturalEncoding dummy).
        binaryDescriptionSize_le_presentationItemCount_mul_automaticBitWidth
          dummy

    _ ≤
        H.compiledGrammarPresentationItemCount *
          binaryNatCodeLength B :=
      Nat.mul_le_mul_left
        H.compiledGrammarPresentationItemCount hwidth

    _ ≤
        B * binaryNatCodeLength B :=
      Nat.mul_le_mul_right
        (binaryNatCodeLength B) hitems

end PaperFacingTaggedDenseBound

end MCFG
