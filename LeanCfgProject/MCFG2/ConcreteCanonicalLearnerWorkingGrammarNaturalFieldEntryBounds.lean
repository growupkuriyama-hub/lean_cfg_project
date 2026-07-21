/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarNaturalFieldClassification

/-!
# ConcreteCanonicalLearnerWorkingGrammarNaturalFieldEntryBounds.lean

The preceding file classifies every natural field in the complete compiled
grammar serialization and reduces the global maximum to entry-local bounds.

This file evaluates those top-level entry bounds.

For a stored presentation entry, all nonterminal references use the global
dense code and are therefore strictly below

```lean
H.compiledGrammarPresentationItemCount.
```

Every stored terminal rule uses a terminal in

```lean
compiledTerminalAlphabet K dummy,
```

so its dense terminal code is strictly below the cardinality of that finite
alphabet.

The only remaining opaque local quantity is the natural value bound of the
already verified complete binary-rule payload:

```lean
compiledBinaryRuleNaturalValueBound.
```

Accordingly, the explicit entry bounds are

```text
nonterminal:
  max 2 presentationItemCount

start rule:
  max 2 presentationItemCount

terminal rule:
  max 3 (max presentationItemCount terminalAlphabetCard)

binary rule:
  max entryFieldCount
      (max 3 binaryRuleNaturalValueBound).
```

The first argument also bounds the local payload length; the remaining
arguments bound every natural field value.

We prove that every actually stored entry's previous local
`naturalFieldValueBound` is below this explicit structural bound.  Taking the
maximum over all stored entries then yields a new complete-grammar bound whose
only unresolved component is the maximum natural value bound of a stored
binary-rule payload.

Thus the next layer can work entirely inside the binary-rule serialization:
three dense nonterminal codes, a body-token count, token tags, component
lengths, terminal codes, and child-variable indices.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section BinaryRuleNaturalValueBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Local natural-value bound of the complete pure-natural serialization of one
compiled binary rule. -/
noncomputable def compiledBinaryRuleNaturalValueBound
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    Nat :=
  naturalFieldValueBound
    (H.encodeCompiledBinaryRuleNaturalList dummy rho)

/-- The number of natural fields in a binary-rule payload is below its local
natural-value bound. -/
theorem compiledBinaryRuleNaturalFieldCount_le_valueBound
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    (H.encodeCompiledBinaryRuleNaturalList dummy rho).length <=
      H.compiledBinaryRuleNaturalValueBound dummy rho := by

  exact
    fieldCount_le_naturalFieldValueBound
      (H.encodeCompiledBinaryRuleNaturalList dummy rho)

/-- Every natural field in a binary-rule payload is below its local
natural-value bound. -/
theorem compiledBinaryRuleNaturalField_le_valueBound_of_mem
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    {n : Nat}
    (hn :
      n ∈ H.encodeCompiledBinaryRuleNaturalList dummy rho) :
    n <= H.compiledBinaryRuleNaturalValueBound dummy rho := by

  exact
    field_le_naturalFieldValueBound_of_mem
      (H.encodeCompiledBinaryRuleNaturalList dummy rho)
      hn

end CorrectedConcreteFiniteHypothesis

end BinaryRuleNaturalValueBound


section DenseReferenceBounds

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Every compiled nonterminal reference has global dense code strictly below
the complete presentation-item count. -/
theorem compiledNonterminalGlobalDenseCode_lt_presentationItemCount
    (dummy : α)
    (A : CorrectedConcreteCutGrammarNonterminal H) :
    H.compiledGrammarGlobalDenseCode dummy
        (.nonterminal A) <
      H.compiledGrammarPresentationItemCount := by

  exact
    H.compiledGrammarGlobalDenseCode_lt_presentationItemCount
      dummy
      (.nonterminal A)
      (H.nonterminal_mem_compiledGrammarPresentationEntries
        dummy A
        (H.mem_compiledGrammarNonterminals A))

/-- Nonterminal dense codes are bounded non-strictly by the complete
presentation-item count. -/
theorem compiledNonterminalGlobalDenseCode_le_presentationItemCount
    (dummy : α)
    (A : CorrectedConcreteCutGrammarNonterminal H) :
    H.compiledGrammarGlobalDenseCode dummy
        (.nonterminal A) <=
      H.compiledGrammarPresentationItemCount := by

  exact
    Nat.le_of_lt
      (H.compiledNonterminalGlobalDenseCode_lt_presentationItemCount
        dummy A)

end CorrectedConcreteFiniteHypothesis

end DenseReferenceBounds


section ExplicitEntryNaturalBounds

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Explicit top-level natural-value bound for one presentation entry.

Only the binary-rule case retains a local binary-payload bound for the next
serialization layer. -/
noncomputable def compiledGrammarPresentationEntryExplicitNaturalValueBound
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
          (H.compiledBinaryRuleNaturalValueBound
            dummy rho))

/-- The encoded entry length is below the explicit entry bound. -/
theorem
    compiledGrammarPresentationEntryNaturalFieldCount_le_explicitBound
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H) :
    H.compiledGrammarPresentationEntryNaturalFieldCount
        dummy entry <=
      H.compiledGrammarPresentationEntryExplicitNaturalValueBound
        dummy entry := by

  cases entry with

  | nonterminal A =>
      simp [
        compiledGrammarPresentationEntryNaturalFieldCount,
        compiledGrammarPresentationEntryExplicitNaturalValueBound
      ]

  | startRule rho =>
      simp [
        compiledGrammarPresentationEntryNaturalFieldCount,
        compiledGrammarPresentationEntryExplicitNaturalValueBound
      ]

  | terminalRule rho =>
      simp [
        compiledGrammarPresentationEntryNaturalFieldCount,
        compiledGrammarPresentationEntryExplicitNaturalValueBound
      ]

  | binaryRule rho =>
      exact
        Nat.le_max_left
          (H.compiledGrammarPresentationEntryNaturalFieldCount
            dummy (.binaryRule rho))
          (max 3
            (H.compiledBinaryRuleNaturalValueBound
              dummy rho))

/-- Every natural field of an actually stored entry is below the explicit
entry-local bound. -/
theorem
    compiledGrammarPresentationEntryNaturalField_le_explicitBound_of_mem
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
      H.compiledGrammarPresentationEntryExplicitNaturalValueBound
        dummy entry := by

  have hclass :
      H.CompiledGrammarPresentationEntryNaturalFieldClass
        dummy entry n :=
    (H.compiledGrammarPresentationEntryNaturalFieldClass_iff_mem
      dummy entry n).mpr hn

  cases entry with

  | nonterminal A =>
      rcases hclass with htag | hcode

      · subst n

        exact
          Nat.zero_le
            (H.compiledGrammarPresentationEntryExplicitNaturalValueBound
              dummy (.nonterminal A))

      · subst n

        exact
          (H.compiledNonterminalGlobalDenseCode_le_presentationItemCount
              dummy A).trans
            (Nat.le_max_right
              2
              H.compiledGrammarPresentationItemCount)

  | startRule rho =>
      rcases hclass with htag | hcode

      · subst n

        exact
          (show
            1 <=
              max 2
                H.compiledGrammarPresentationItemCount by
              omega)

      · subst n

        exact
          (H.compiledNonterminalGlobalDenseCode_le_presentationItemCount
              dummy rho.child).trans
            (Nat.le_max_right
              2
              H.compiledGrammarPresentationItemCount)

  | terminalRule rho =>
      have hrho :
          rho ∈
            (H.toCutWorkingMCFG dummy).terminalRules := by

        simpa [
          CorrectedConcreteFiniteHypothesis.compiledGrammarPresentationEntries
        ] using hentry

      have hterminal :
          rho.terminal ∈
            compiledTerminalAlphabet K dummy :=
        H.terminalRule_terminal_mem_compiledTerminalAlphabet_of_mem
          dummy rho hrho

      rcases hclass with
        htag | hcode | hterminalCode

      · subst n

        exact
          Nat.le_max_left
            3
            (max
              H.compiledGrammarPresentationItemCount
              (compiledTerminalAlphabet K dummy).card)

      · subst n

        exact
          (H.compiledNonterminalGlobalDenseCode_le_presentationItemCount
              dummy rho.lhs).trans
            ((Nat.le_max_left
                H.compiledGrammarPresentationItemCount
                (compiledTerminalAlphabet K dummy).card).trans
              (Nat.le_max_right
                3
                (max
                  H.compiledGrammarPresentationItemCount
                  (compiledTerminalAlphabet K dummy).card)))

      · subst n

        exact
          (Nat.le_of_lt
              (compiledTerminalDenseCode_lt_card
                K dummy rho.terminal hterminal)).trans
            ((Nat.le_max_right
                H.compiledGrammarPresentationItemCount
                (compiledTerminalAlphabet K dummy).card).trans
              (Nat.le_max_right
                3
                (max
                  H.compiledGrammarPresentationItemCount
                  (compiledTerminalAlphabet K dummy).card)))

  | binaryRule rho =>
      rcases hclass with
        htag | hpayloadLength | hpayloadField

      · subst n

        exact
          (Nat.le_max_left
              3
              (H.compiledBinaryRuleNaturalValueBound
                dummy rho)).trans
            (Nat.le_max_right
              (H.compiledGrammarPresentationEntryNaturalFieldCount
                dummy (.binaryRule rho))
              (max 3
                (H.compiledBinaryRuleNaturalValueBound
                  dummy rho)))

      · subst n

        have hpayload :
            (H.encodeCompiledBinaryRuleNaturalList
                dummy rho).length <=
              H.compiledBinaryRuleNaturalValueBound
                dummy rho :=
          H.compiledBinaryRuleNaturalFieldCount_le_valueBound
            dummy rho

        exact
          hpayload.trans
            ((Nat.le_max_right
                3
                (H.compiledBinaryRuleNaturalValueBound
                  dummy rho)).trans
              (Nat.le_max_right
                (H.compiledGrammarPresentationEntryNaturalFieldCount
                  dummy (.binaryRule rho))
                (max 3
                  (H.compiledBinaryRuleNaturalValueBound
                    dummy rho))))

      · have hpayload :
            n <=
              H.compiledBinaryRuleNaturalValueBound
                dummy rho :=
          H.compiledBinaryRuleNaturalField_le_valueBound_of_mem
            dummy rho hpayloadField

        exact
          hpayload.trans
            ((Nat.le_max_right
                3
                (H.compiledBinaryRuleNaturalValueBound
                  dummy rho)).trans
              (Nat.le_max_right
                (H.compiledGrammarPresentationEntryNaturalFieldCount
                  dummy (.binaryRule rho))
                (max 3
                  (H.compiledBinaryRuleNaturalValueBound
                    dummy rho))))

/-- The previous entry-local `naturalFieldValueBound` is below the explicit
structural entry bound for every actually stored entry. -/
theorem
    compiledGrammarPresentationEntryNaturalValueBound_le_explicitBound_of_mem
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hentry :
      entry ∈ H.compiledGrammarPresentationEntries dummy) :
    H.compiledGrammarPresentationEntryNaturalValueBound
        dummy entry <=
      H.compiledGrammarPresentationEntryExplicitNaturalValueBound
        dummy entry := by

  unfold
    compiledGrammarPresentationEntryNaturalValueBound

  apply
    naturalFieldValueBound_le_of_count_le_of_all_le

  · rw [
      H.encodeCompiledGrammarPresentationEntryNaturalList_length
        dummy entry
    ]

    exact
      H.compiledGrammarPresentationEntryNaturalFieldCount_le_explicitBound
        dummy entry

  · intro n hn

    exact
      H.compiledGrammarPresentationEntryNaturalField_le_explicitBound_of_mem
        dummy entry hentry hn

/-- Compact stored-entry natural-value-bound package. -/
theorem
    compiledGrammarPresentationEntryExplicitNaturalValueBound_package
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hentry :
      entry ∈ H.compiledGrammarPresentationEntries dummy) :
    (H.compiledGrammarPresentationEntryNaturalFieldCount
        dummy entry <=
      H.compiledGrammarPresentationEntryExplicitNaturalValueBound
        dummy entry) ∧
      (∀ n ∈
          H.encodeCompiledGrammarPresentationEntryNaturalList
            dummy entry,
        n <=
          H.compiledGrammarPresentationEntryExplicitNaturalValueBound
            dummy entry) ∧
      (H.compiledGrammarPresentationEntryNaturalValueBound
          dummy entry <=
        H.compiledGrammarPresentationEntryExplicitNaturalValueBound
          dummy entry) := by

  exact
    ⟨H.compiledGrammarPresentationEntryNaturalFieldCount_le_explicitBound
        dummy entry,
      by
        intro n hn
        exact
          H.compiledGrammarPresentationEntryNaturalField_le_explicitBound_of_mem
            dummy entry hentry hn,
      H.compiledGrammarPresentationEntryNaturalValueBound_le_explicitBound_of_mem
        dummy entry hentry⟩

end CorrectedConcreteFiniteHypothesis

end ExplicitEntryNaturalBounds


section AggregatedExplicitEntryBounds

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Maximum explicit natural-value bound over a finite presentation-entry list. -/
noncomputable def
    maximumCompiledGrammarPresentationEntryExplicitNaturalValueBound
    (dummy : α)
    (entries :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry H)) :
    Nat :=
  maximumNaturalFieldValue
    (entries.map
      (fun entry =>
        H.compiledGrammarPresentationEntryExplicitNaturalValueBound
          dummy entry))

/-- Every entry's explicit bound lies below the maximum explicit bound over the
entry list. -/
theorem
    compiledGrammarPresentationEntryExplicitNaturalValueBound_le_maximum_of_mem
    (dummy : α)
    (entries :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry H))
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hentry :
      entry ∈ entries) :
    H.compiledGrammarPresentationEntryExplicitNaturalValueBound
        dummy entry <=
      H.maximumCompiledGrammarPresentationEntryExplicitNaturalValueBound
        dummy entries := by

  unfold
    maximumCompiledGrammarPresentationEntryExplicitNaturalValueBound

  apply
    nat_le_maximumNaturalFieldValue_of_mem

  exact
    List.mem_map.mpr
      ⟨entry, hentry, rfl⟩

/-- Maximum explicit entry-local bound over the actual complete compiled
presentation. -/
noncomputable def
    compiledWorkingGrammarMaximumEntryExplicitNaturalValueBound
    (dummy : α) :
    Nat :=
  H.maximumCompiledGrammarPresentationEntryExplicitNaturalValueBound
    dummy
    (H.compiledGrammarPresentationEntries dummy)

/-- The previous maximum of entry-local bounds is below the maximum of explicit
entry-local structural bounds. -/
theorem
    compiledWorkingGrammarMaximumEntryNaturalValueBound_le_explicit
    (dummy : α) :
    H.compiledWorkingGrammarMaximumEntryNaturalValueBound dummy <=
      H.compiledWorkingGrammarMaximumEntryExplicitNaturalValueBound
        dummy := by

  unfold
    compiledWorkingGrammarMaximumEntryNaturalValueBound
    maximumCompiledGrammarPresentationEntryNaturalValueBound

  apply
    maximumNaturalFieldValue_le_of_forall_mem

  intro localBound hlocalBound

  rcases List.mem_map.mp hlocalBound with
    ⟨entry, hentry, rfl⟩

  exact
    (H.compiledGrammarPresentationEntryNaturalValueBound_le_explicitBound_of_mem
        dummy entry hentry).trans
      (H.compiledGrammarPresentationEntryExplicitNaturalValueBound_le_maximum_of_mem
        dummy
        (H.compiledGrammarPresentationEntries dummy)
        entry hentry)

/-- Complete grammar natural-field bound after evaluating the top-level entry
constructors.

The only remaining non-cardinality component is the maximum explicit binary-rule
payload bound contained inside the entry maximum. -/
noncomputable def compiledWorkingGrammarEntryExplicitNaturalFieldBound
    (dummy : α) :
    Nat :=
  max
    H.compiledWorkingGrammarNaturalFieldCount
    (max
      H.compiledGrammarPresentationItemCount
      (H.compiledWorkingGrammarMaximumEntryExplicitNaturalValueBound
        dummy))

/-- The earlier classification-based global bound is below the new explicit
entry-level bound. -/
theorem
    compiledWorkingGrammarClassifiedNaturalFieldBound_le_entryExplicitBound
    (dummy : α) :
    H.compiledWorkingGrammarClassifiedNaturalFieldBound dummy <=
      H.compiledWorkingGrammarEntryExplicitNaturalFieldBound
        dummy := by

  unfold
    compiledWorkingGrammarClassifiedNaturalFieldBound
    compiledWorkingGrammarEntryExplicitNaturalFieldBound

  apply max_le

  · exact
      Nat.le_max_left
        H.compiledWorkingGrammarNaturalFieldCount
        (max
          H.compiledGrammarPresentationItemCount
          (H.compiledWorkingGrammarMaximumEntryExplicitNaturalValueBound
            dummy))

  · apply max_le

    · exact
        (Nat.le_max_left
          H.compiledGrammarPresentationItemCount
          (H.compiledWorkingGrammarMaximumEntryExplicitNaturalValueBound
            dummy)).trans
          (Nat.le_max_right
            H.compiledWorkingGrammarNaturalFieldCount
            (max
              H.compiledGrammarPresentationItemCount
              (H.compiledWorkingGrammarMaximumEntryExplicitNaturalValueBound
                dummy)))

    · exact
        (H.compiledWorkingGrammarMaximumEntryNaturalValueBound_le_explicit
            dummy).trans
          ((Nat.le_max_right
              H.compiledGrammarPresentationItemCount
              (H.compiledWorkingGrammarMaximumEntryExplicitNaturalValueBound
                dummy)).trans
            (Nat.le_max_right
              H.compiledWorkingGrammarNaturalFieldCount
              (max
                H.compiledGrammarPresentationItemCount
                (H.compiledWorkingGrammarMaximumEntryExplicitNaturalValueBound
                  dummy))))

/-- The original complete natural-field value bound is below the explicit
entry-level structural bound. -/
theorem
    compiledWorkingGrammarNaturalFieldValueBound_le_entryExplicitBound
    (dummy : α) :
    H.compiledWorkingGrammarNaturalFieldValueBound dummy <=
      H.compiledWorkingGrammarEntryExplicitNaturalFieldBound
        dummy := by

  exact
    (H.compiledWorkingGrammarNaturalFieldValueBound_le_classifiedBound
        dummy).trans
      (H.compiledWorkingGrammarClassifiedNaturalFieldBound_le_entryExplicitBound
        dummy)

/-- Every complete-grammar natural field is below the explicit entry-level
structural bound. -/
theorem
    compiledWorkingGrammarNaturalField_le_entryExplicitBound_of_mem
    (dummy : α)
    {n : Nat}
    (hn :
      n ∈ H.encodeCompiledWorkingGrammarNaturalList dummy) :
    n <=
      H.compiledWorkingGrammarEntryExplicitNaturalFieldBound
        dummy := by

  exact
    (H.compiledWorkingGrammarNaturalField_le_valueBound_of_mem
        dummy hn).trans
      (H.compiledWorkingGrammarNaturalFieldValueBound_le_entryExplicitBound
        dummy)

/-- Compact final package for the explicit top-level entry-bound layer. -/
theorem
    compiledWorkingGrammarNaturalFieldEntryBounds_package
    (dummy : α) :
    (H.compiledWorkingGrammarMaximumEntryNaturalValueBound dummy <=
      H.compiledWorkingGrammarMaximumEntryExplicitNaturalValueBound
        dummy) ∧
      (H.compiledWorkingGrammarClassifiedNaturalFieldBound dummy <=
        H.compiledWorkingGrammarEntryExplicitNaturalFieldBound
          dummy) ∧
      (H.compiledWorkingGrammarNaturalFieldValueBound dummy <=
        H.compiledWorkingGrammarEntryExplicitNaturalFieldBound
          dummy) ∧
      (∀ n ∈
          H.encodeCompiledWorkingGrammarNaturalList dummy,
        n <=
          H.compiledWorkingGrammarEntryExplicitNaturalFieldBound
            dummy) := by

  exact
    ⟨H.compiledWorkingGrammarMaximumEntryNaturalValueBound_le_explicit
        dummy,
      H.compiledWorkingGrammarClassifiedNaturalFieldBound_le_entryExplicitBound
        dummy,
      H.compiledWorkingGrammarNaturalFieldValueBound_le_entryExplicitBound
        dummy,
      by
        intro n hn
        exact
          H.compiledWorkingGrammarNaturalField_le_entryExplicitBound_of_mem
            dummy hn⟩

end CorrectedConcreteFiniteHypothesis

end AggregatedExplicitEntryBounds

end MCFG
