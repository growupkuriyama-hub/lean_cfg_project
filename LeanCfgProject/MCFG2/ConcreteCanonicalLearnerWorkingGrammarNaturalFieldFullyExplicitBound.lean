/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarBinaryRuleTokenPayloadBounds

/-!
# ConcreteCanonicalLearnerWorkingGrammarNaturalFieldFullyExplicitBound.lean

The preceding file eliminates the last token-local maximum from every binary
rule actually stored in the cut-compiled grammar.  This file transports that
fully explicit rule bound back through

* top-level presentation entries;
* the complete entry list;
* the complete pure-natural grammar serialization; and
* the logarithmic self-delimiting bit codec.

For a binary-rule presentation entry, replace the former opaque payload bound

```lean
H.compiledBinaryRuleNaturalValueBound dummy rho
```

by the fully explicit structural quantity

```lean
H.compiledBinaryRuleFullyExplicitNaturalValueBound dummy rho.
```

The other three top-level entry forms already have explicit bounds in terms of

* the complete presentation-item count; and
* the augmented terminal-alphabet cardinality.

Taking the maximum over all actually stored entries gives

```lean
H.compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound dummy.
```

The final natural-field bound of this layer is

```text
max naturalFieldCount
  (max presentationItemCount
    maximumEntryFullyExplicitNaturalValueBound).
```

We prove that every field in the complete natural serialization is below this
quantity and, in particular,

```lean
H.compiledWorkingGrammarNaturalFieldValueBound dummy
  ≤
H.compiledWorkingGrammarFullyExplicitNaturalFieldBound dummy.
```

Its standard binary payload length is therefore a valid common width for the
complete natural stream.  The complete checked grammar bit serialization
satisfies the unconditional estimate

```text
grammarBitCount
  ≤
(naturalFieldCount + 1) *
  (2 * binaryNatCodeLength(fullyExplicitNaturalFieldBound) + 1).
```

No binary-rule local maximum, token maximum, terminal maximum, or variable-index
maximum remains in this theorem.  The remaining quantities are structural
cardinalities and per-rule body sizes.  The next layer can compress the maximum
over stored entries to a maximum stored body-token count and then bound that
quantity from the three compiler rule families.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section FullyExplicitPresentationEntryBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Fully explicit natural-value bound for one top-level presentation entry.

The binary-rule case uses the fully explicit stored-rule bound from the
preceding file. -/
noncomputable def
    compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
    (dummy : α) :
    CorrectedConcreteCompiledGrammarPresentationEntry H →
      Nat

  | .nonterminal _ =>
      max 2
        H.compiledGrammarPresentationItemCount

  | .startRule _ =>
      max 2
        H.compiledGrammarPresentationItemCount

  | .terminalRule _ =>
      max 3
        (max
          H.compiledGrammarPresentationItemCount
          (compiledTerminalAlphabet K dummy).card)

  | .binaryRule rho =>
      max
        (H.compiledGrammarPresentationEntryNaturalFieldCount
          dummy (.binaryRule rho))
        (max 3
          (H.compiledBinaryRuleFullyExplicitNaturalValueBound
            dummy rho))

/-- The previous explicit top-level entry bound is below the fully explicit
entry bound for every actually stored presentation entry. -/
theorem
    compiledGrammarPresentationEntryExplicitNaturalValueBound_le_fullyExplicit_of_mem
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hentry :
      entry ∈ H.compiledGrammarPresentationEntries dummy) :
    H.compiledGrammarPresentationEntryExplicitNaturalValueBound
        dummy entry <=
      H.compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
        dummy entry := by

  cases entry with

  | nonterminal A =>
      rfl

  | startRule rho =>
      rfl

  | terminalRule rho =>
      rfl

  | binaryRule rho =>
      have hrho :
          rho ∈
            (H.toCutWorkingMCFG dummy).binaryRules := by

        simpa [
          CorrectedConcreteFiniteHypothesis.compiledGrammarPresentationEntries
        ] using hentry

      unfold
        compiledGrammarPresentationEntryExplicitNaturalValueBound
        compiledGrammarPresentationEntryFullyExplicitNaturalValueBound

      apply max_le

      · exact
          Nat.le_max_left
            (H.compiledGrammarPresentationEntryNaturalFieldCount
              dummy (.binaryRule rho))
            (max 3
              (H.compiledBinaryRuleFullyExplicitNaturalValueBound
                dummy rho))

      · apply max_le

        · exact
            (Nat.le_max_left
                3
                (H.compiledBinaryRuleFullyExplicitNaturalValueBound
                  dummy rho)).trans
              (Nat.le_max_right
                (H.compiledGrammarPresentationEntryNaturalFieldCount
                  dummy (.binaryRule rho))
                (max 3
                  (H.compiledBinaryRuleFullyExplicitNaturalValueBound
                    dummy rho)))

        · exact
            (H.compiledBinaryRuleNaturalValueBound_le_fullyExplicit_of_mem
                dummy rho hrho).trans
              ((Nat.le_max_right
                  3
                  (H.compiledBinaryRuleFullyExplicitNaturalValueBound
                    dummy rho)).trans
                (Nat.le_max_right
                  (H.compiledGrammarPresentationEntryNaturalFieldCount
                    dummy (.binaryRule rho))
                  (max 3
                    (H.compiledBinaryRuleFullyExplicitNaturalValueBound
                      dummy rho))))

/-- The encoded entry length is below the fully explicit entry bound. -/
theorem
    compiledGrammarPresentationEntryNaturalFieldCount_le_fullyExplicitBound
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H) :
    H.compiledGrammarPresentationEntryNaturalFieldCount
        dummy entry <=
      H.compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
        dummy entry := by

  cases entry with

  | nonterminal A =>
      simp [
        compiledGrammarPresentationEntryNaturalFieldCount,
        compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
      ]

  | startRule rho =>
      simp [
        compiledGrammarPresentationEntryNaturalFieldCount,
        compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
      ]

  | terminalRule rho =>
      simp [
        compiledGrammarPresentationEntryNaturalFieldCount,
        compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
      ]

  | binaryRule rho =>
      exact
        Nat.le_max_left
          (H.compiledGrammarPresentationEntryNaturalFieldCount
            dummy (.binaryRule rho))
          (max 3
            (H.compiledBinaryRuleFullyExplicitNaturalValueBound
              dummy rho))

/-- Every natural field of an actually stored presentation entry is below its
fully explicit entry bound. -/
theorem
    compiledGrammarPresentationEntryNaturalField_le_fullyExplicitBound_of_mem
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hentry :
      entry ∈ H.compiledGrammarPresentationEntries dummy)
    {n : Nat}
    (hn :
      n ∈
        H.encodeCompiledGrammarPresentationEntryNaturalList
          dummy entry) :
    n <=
      H.compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
        dummy entry := by

  exact
    (H.compiledGrammarPresentationEntryNaturalField_le_explicitBound_of_mem
        dummy entry hentry hn).trans
      (H.compiledGrammarPresentationEntryExplicitNaturalValueBound_le_fullyExplicit_of_mem
        dummy entry hentry)

/-- The previous entry-local natural value bound is below the fully explicit
entry bound. -/
theorem
    compiledGrammarPresentationEntryNaturalValueBound_le_fullyExplicit_of_mem
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hentry :
      entry ∈ H.compiledGrammarPresentationEntries dummy) :
    H.compiledGrammarPresentationEntryNaturalValueBound
        dummy entry <=
      H.compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
        dummy entry := by

  exact
    (H.compiledGrammarPresentationEntryNaturalValueBound_le_explicitBound_of_mem
        dummy entry hentry).trans
      (H.compiledGrammarPresentationEntryExplicitNaturalValueBound_le_fullyExplicit_of_mem
        dummy entry hentry)

/-- Compact fully explicit entry-level package. -/
theorem
    compiledGrammarPresentationEntryFullyExplicitNaturalValueBound_package
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hentry :
      entry ∈ H.compiledGrammarPresentationEntries dummy) :
    (H.compiledGrammarPresentationEntryNaturalFieldCount
        dummy entry <=
      H.compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
        dummy entry) ∧
      (∀ n ∈
          H.encodeCompiledGrammarPresentationEntryNaturalList
            dummy entry,
        n <=
          H.compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
            dummy entry) ∧
      (H.compiledGrammarPresentationEntryNaturalValueBound
          dummy entry <=
        H.compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
          dummy entry) := by

  exact
    ⟨H.compiledGrammarPresentationEntryNaturalFieldCount_le_fullyExplicitBound
        dummy entry,
      by
        intro n hn
        exact
          H.compiledGrammarPresentationEntryNaturalField_le_fullyExplicitBound_of_mem
            dummy entry hentry hn,
      H.compiledGrammarPresentationEntryNaturalValueBound_le_fullyExplicit_of_mem
        dummy entry hentry⟩

end CorrectedConcreteFiniteHypothesis

end FullyExplicitPresentationEntryBound


section MaximumFullyExplicitPresentationEntryBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Maximum fully explicit entry-local bound over a finite list of presentation
entries. -/
noncomputable def
    maximumCompiledGrammarPresentationEntryFullyExplicitNaturalValueBound
    (dummy : α)
    (entries :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry H)) :
    Nat :=
  maximumNaturalFieldValue
    (entries.map
      (fun entry =>
        H.compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
          dummy entry))

/-- Every entry's fully explicit bound is below the maximum over its containing
entry list. -/
theorem
    compiledGrammarPresentationEntryFullyExplicitNaturalValueBound_le_maximum_of_mem
    (dummy : α)
    (entries :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry H))
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hentry :
      entry ∈ entries) :
    H.compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
        dummy entry <=
      H.maximumCompiledGrammarPresentationEntryFullyExplicitNaturalValueBound
        dummy entries := by

  unfold
    maximumCompiledGrammarPresentationEntryFullyExplicitNaturalValueBound

  apply
    nat_le_maximumNaturalFieldValue_of_mem

  exact
    List.mem_map.mpr
      ⟨entry, hentry, rfl⟩

/-- Maximum fully explicit entry bound over the actual complete compiled
presentation. -/
noncomputable def
    compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound
    (dummy : α) :
    Nat :=
  H.maximumCompiledGrammarPresentationEntryFullyExplicitNaturalValueBound
    dummy
    (H.compiledGrammarPresentationEntries dummy)

/-- The previous maximum explicit entry bound is below the new maximum fully
explicit entry bound. -/
theorem
    compiledWorkingGrammarMaximumEntryExplicitNaturalValueBound_le_fullyExplicit
    (dummy : α) :
    H.compiledWorkingGrammarMaximumEntryExplicitNaturalValueBound dummy <=
      H.compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound
        dummy := by

  unfold
    compiledWorkingGrammarMaximumEntryExplicitNaturalValueBound
    maximumCompiledGrammarPresentationEntryExplicitNaturalValueBound

  apply
    maximumNaturalFieldValue_le_of_forall_mem

  intro oldBound holdBound

  rcases List.mem_map.mp holdBound with
    ⟨entry, hentry, rfl⟩

  exact
    (H.compiledGrammarPresentationEntryExplicitNaturalValueBound_le_fullyExplicit_of_mem
        dummy entry hentry).trans
      (H.compiledGrammarPresentationEntryFullyExplicitNaturalValueBound_le_maximum_of_mem
        dummy
        (H.compiledGrammarPresentationEntries dummy)
        entry hentry)

/-- The earlier maximum entry-local natural value is below the maximum fully
explicit entry bound. -/
theorem
    compiledWorkingGrammarMaximumEntryNaturalValueBound_le_fullyExplicit
    (dummy : α) :
    H.compiledWorkingGrammarMaximumEntryNaturalValueBound dummy <=
      H.compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound
        dummy := by

  exact
    (H.compiledWorkingGrammarMaximumEntryNaturalValueBound_le_explicit
        dummy).trans
      (H.compiledWorkingGrammarMaximumEntryExplicitNaturalValueBound_le_fullyExplicit
        dummy)

end CorrectedConcreteFiniteHypothesis

end MaximumFullyExplicitPresentationEntryBound


section CompleteGrammarFullyExplicitNaturalFieldBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Complete fully explicit natural-field bound for the actual compiled grammar.

All top-level and binary-token-local maxima have been evaluated. -/
noncomputable def compiledWorkingGrammarFullyExplicitNaturalFieldBound
    (dummy : α) :
    Nat :=
  max
    (H.compiledWorkingGrammarNaturalFieldCount dummy)
    (max
      H.compiledGrammarPresentationItemCount
      (H.compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound
        dummy))

/-- The complete natural-field count is below the fully explicit global bound. -/
theorem
    compiledWorkingGrammarNaturalFieldCount_le_fullyExplicitBound
    (dummy : α) :
    H.compiledWorkingGrammarNaturalFieldCount dummy <=
      H.compiledWorkingGrammarFullyExplicitNaturalFieldBound
        dummy := by

  exact
    Nat.le_max_left
      (H.compiledWorkingGrammarNaturalFieldCount dummy)
      (max
        H.compiledGrammarPresentationItemCount
        (H.compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound
          dummy))

/-- The presentation-item count is below the fully explicit global bound. -/
theorem
    compiledGrammarPresentationItemCount_le_fullyExplicitBound
    (dummy : α) :
    H.compiledGrammarPresentationItemCount <=
      H.compiledWorkingGrammarFullyExplicitNaturalFieldBound
        dummy := by

  exact
    (Nat.le_max_left
        H.compiledGrammarPresentationItemCount
        (H.compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound
          dummy)).trans
      (Nat.le_max_right
        (H.compiledWorkingGrammarNaturalFieldCount dummy)
        (max
          H.compiledGrammarPresentationItemCount
          (H.compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound
            dummy)))

/-- The maximum fully explicit entry bound is below the complete global bound. -/
theorem
    compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound_le_global
    (dummy : α) :
    H.compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound
        dummy <=
      H.compiledWorkingGrammarFullyExplicitNaturalFieldBound
        dummy := by

  exact
    (Nat.le_max_right
        H.compiledGrammarPresentationItemCount
        (H.compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound
          dummy)).trans
      (Nat.le_max_right
        (H.compiledWorkingGrammarNaturalFieldCount dummy)
        (max
          H.compiledGrammarPresentationItemCount
          (H.compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound
            dummy)))

/-- The preceding entry-explicit global bound is below the fully explicit
global bound. -/
theorem
    compiledWorkingGrammarEntryExplicitNaturalFieldBound_le_fullyExplicit
    (dummy : α) :
    H.compiledWorkingGrammarEntryExplicitNaturalFieldBound dummy <=
      H.compiledWorkingGrammarFullyExplicitNaturalFieldBound
        dummy := by

  unfold
    compiledWorkingGrammarEntryExplicitNaturalFieldBound
    compiledWorkingGrammarFullyExplicitNaturalFieldBound

  apply max_le

  · exact
      Nat.le_max_left
        (H.compiledWorkingGrammarNaturalFieldCount dummy)
        (max
          H.compiledGrammarPresentationItemCount
          (H.compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound
            dummy))

  · apply max_le

    · exact
        (Nat.le_max_left
            H.compiledGrammarPresentationItemCount
            (H.compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound
              dummy)).trans
          (Nat.le_max_right
            (H.compiledWorkingGrammarNaturalFieldCount dummy)
            (max
              H.compiledGrammarPresentationItemCount
              (H.compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound
                dummy)))

    · exact
        (H.compiledWorkingGrammarMaximumEntryExplicitNaturalValueBound_le_fullyExplicit
            dummy).trans
          (H.compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound_le_global
            dummy)

/-- The original complete natural-field value bound is below the fully explicit
global structural bound. -/
theorem
    compiledWorkingGrammarNaturalFieldValueBound_le_fullyExplicitBound
    (dummy : α) :
    H.compiledWorkingGrammarNaturalFieldValueBound dummy <=
      H.compiledWorkingGrammarFullyExplicitNaturalFieldBound
        dummy := by

  exact
    (H.compiledWorkingGrammarNaturalFieldValueBound_le_entryExplicitBound
        dummy).trans
      (H.compiledWorkingGrammarEntryExplicitNaturalFieldBound_le_fullyExplicit
        dummy)

/-- Every natural field in the complete grammar serialization is below the fully
explicit global structural bound. -/
theorem
    compiledWorkingGrammarNaturalField_le_fullyExplicitBound_of_mem
    (dummy : α)
    {n : Nat}
    (hn :
      n ∈ H.encodeCompiledWorkingGrammarNaturalList dummy) :
    n <=
      H.compiledWorkingGrammarFullyExplicitNaturalFieldBound
        dummy := by

  exact
    (H.compiledWorkingGrammarNaturalField_le_valueBound_of_mem
        dummy hn).trans
      (H.compiledWorkingGrammarNaturalFieldValueBound_le_fullyExplicitBound
        dummy)

/-- The standard binary length of the fully explicit global field bound. -/
noncomputable def
    compiledWorkingGrammarFullyExplicitNaturalFieldBitWidth
    (dummy : α) :
    Nat :=
  binaryNatCodeLength
    (H.compiledWorkingGrammarFullyExplicitNaturalFieldBound
      dummy)

/-- The complete natural grammar serialization fits the fully explicit common
bit width. -/
theorem
    compiledWorkingGrammarNaturalFieldsFitInBits_fullyExplicit
    (dummy : α) :
    H.compiledWorkingGrammarNaturalFieldsFitInBits
        dummy
        (H.compiledWorkingGrammarFullyExplicitNaturalFieldBitWidth
          dummy) := by

  refine
    ⟨binaryNatCodeLength_pos
        (H.compiledWorkingGrammarFullyExplicitNaturalFieldBound
          dummy),
      ?_,
      ?_⟩

  · rw [
      H.encodeCompiledWorkingGrammarNaturalList_length
        dummy
    ]

    exact
      (H.compiledWorkingGrammarNaturalFieldCount_le_fullyExplicitBound
          dummy).trans_lt
        (natCode_lt_two_pow_binaryNatCodeLength
          (H.compiledWorkingGrammarFullyExplicitNaturalFieldBound
            dummy))

  · intro n hn

    exact
      (H.compiledWorkingGrammarNaturalField_le_fullyExplicitBound_of_mem
          dummy hn).trans_lt
        (natCode_lt_two_pow_binaryNatCodeLength
          (H.compiledWorkingGrammarFullyExplicitNaturalFieldBound
            dummy))

/-- The automatically selected least fitting width is below the fully explicit
structural width. -/
theorem
    compiledWorkingGrammarAutomaticNaturalFieldBitWidth_le_fullyExplicit
    (dummy : α) :
    H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth dummy <=
      H.compiledWorkingGrammarFullyExplicitNaturalFieldBitWidth
        dummy := by

  exact
    H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth_le_of_fits
      dummy
      (H.compiledWorkingGrammarNaturalFieldsFitInBits_fullyExplicit
        dummy)

/-- Unconditional complete-grammar logarithmic bit-size bound using only the
fully explicit structural natural-field bound. -/
theorem
    compiledWorkingGrammarLogarithmicBitCount_le_fullyExplicit
    (dummy : α) :
    H.compiledWorkingGrammarLogarithmicBitCount dummy <=
      (H.compiledWorkingGrammarNaturalFieldCount dummy + 1) *
        (2 *
            binaryNatCodeLength
              (H.compiledWorkingGrammarFullyExplicitNaturalFieldBound
                dummy) +
          1) := by

  exact
    H.compiledWorkingGrammarLogarithmicBitCount_le_of_naturalFieldsFitInBits
      dummy
      (H.compiledWorkingGrammarNaturalFieldsFitInBits_fullyExplicit
        dummy)

/-- Compact final endpoint of the fully explicit natural-field layer. -/
theorem
    compiledWorkingGrammarFullyExplicitNaturalFieldBound_package
    (dummy : α) :
    (H.compiledWorkingGrammarNaturalFieldValueBound dummy <=
      H.compiledWorkingGrammarFullyExplicitNaturalFieldBound
        dummy) ∧
      (∀ n ∈
          H.encodeCompiledWorkingGrammarNaturalList dummy,
        n <=
          H.compiledWorkingGrammarFullyExplicitNaturalFieldBound
            dummy) ∧
      H.compiledWorkingGrammarNaturalFieldsFitInBits
        dummy
        (H.compiledWorkingGrammarFullyExplicitNaturalFieldBitWidth
          dummy) ∧
      (H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth dummy <=
        H.compiledWorkingGrammarFullyExplicitNaturalFieldBitWidth
          dummy) ∧
      (H.compiledWorkingGrammarLogarithmicBitCount dummy <=
        (H.compiledWorkingGrammarNaturalFieldCount dummy + 1) *
          (2 *
              binaryNatCodeLength
                (H.compiledWorkingGrammarFullyExplicitNaturalFieldBound
                  dummy) +
            1)) := by

  exact
    ⟨H.compiledWorkingGrammarNaturalFieldValueBound_le_fullyExplicitBound
        dummy,
      by
        intro n hn
        exact
          H.compiledWorkingGrammarNaturalField_le_fullyExplicitBound_of_mem
            dummy hn,
      H.compiledWorkingGrammarNaturalFieldsFitInBits_fullyExplicit
        dummy,
      H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth_le_fullyExplicit
        dummy,
      H.compiledWorkingGrammarLogarithmicBitCount_le_fullyExplicit
        dummy⟩

end CorrectedConcreteFiniteHypothesis

end CompleteGrammarFullyExplicitNaturalFieldBound

end MCFG
