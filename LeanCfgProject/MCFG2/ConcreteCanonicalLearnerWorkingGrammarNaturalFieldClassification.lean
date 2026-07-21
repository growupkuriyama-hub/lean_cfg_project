/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarNaturalFieldMaximum

/-!
# ConcreteCanonicalLearnerWorkingGrammarNaturalFieldClassification.lean

The preceding file reduces the complete logarithmic bit-size analysis to one
natural quantity:

```lean
H.compiledWorkingGrammarNaturalFieldValueBound dummy.
```

This file classifies every natural field that occurs in the complete checked
serialization and reduces the global maximum to entry-local maxima.

For one top-level presentation entry, the possible natural fields are exactly:

* the entry tag `0`, `1`, `2`, or `3`;
* a global dense nonterminal code;
* a dense terminal code;
* a binary-payload length; or
* a field of the complete binary-rule natural payload.

For the framed presentation stream, every field is exactly either

* the natural length of one encoded entry; or
* a field belonging to that encoded entry.

For the complete grammar stream, every field is exactly either

* the complete presentation-item count; or
* one of the framed-stream fields above.

The classification is proved in both directions, so it is not merely a sound
over-approximation.

We then define the entry-local bound

```lean
compiledGrammarPresentationEntryNaturalValueBound
```

as the `naturalFieldValueBound` of the entry's own natural payload, and aggregate
those bounds over all stored entries.  The resulting structural bound is

```text
max naturalFieldCount
  (max presentationItemCount maximumEntryValueBound).
```

The complete grammar's previous `naturalFieldValueBound` is proved below this
structural quantity.  Hence the remaining quantitative analysis may work
entry-by-entry and then combine the resulting bounds mechanically.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section EntryNaturalFieldClassification

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Exact structural classification of a natural field inside one encoded
top-level presentation entry. -/
noncomputable def CompiledGrammarPresentationEntryNaturalFieldClass
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (n : Nat) :
    Prop :=

  match entry with

  | .nonterminal A =>
      n = 0 ∨
        n =
          H.compiledGrammarGlobalDenseCode dummy
            (.nonterminal A)

  | .startRule rho =>
      n = 1 ∨
        n =
          H.compiledGrammarGlobalDenseCode dummy
            (.nonterminal rho.child)

  | .terminalRule rho =>
      n = 2 ∨
        n =
          H.compiledGrammarGlobalDenseCode dummy
            (.nonterminal rho.lhs) ∨
        n =
          compiledTerminalDenseCode
            K dummy rho.terminal

  | .binaryRule rho =>
      n = 3 ∨
        n =
          (H.encodeCompiledBinaryRuleNaturalList
            dummy rho).length ∨
        n ∈
          H.encodeCompiledBinaryRuleNaturalList
            dummy rho

/-- Entry-local classification is exact: it is equivalent to membership in the
entry's natural payload. -/
@[simp] theorem
    compiledGrammarPresentationEntryNaturalFieldClass_iff_mem
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (n : Nat) :
    H.CompiledGrammarPresentationEntryNaturalFieldClass
        dummy entry n ↔
      n ∈
        H.encodeCompiledGrammarPresentationEntryNaturalList
          dummy entry := by

  classical

  cases entry with

  | nonterminal A =>
      simp [
        CompiledGrammarPresentationEntryNaturalFieldClass,
        encodeCompiledGrammarPresentationEntryNaturalList
      ]

  | startRule rho =>
      simp [
        CompiledGrammarPresentationEntryNaturalFieldClass,
        encodeCompiledGrammarPresentationEntryNaturalList
      ]

  | terminalRule rho =>
      simp [
        CompiledGrammarPresentationEntryNaturalFieldClass,
        encodeCompiledGrammarPresentationEntryNaturalList,
        or_assoc
      ]

  | binaryRule rho =>
      simp [
        CompiledGrammarPresentationEntryNaturalFieldClass,
        encodeCompiledGrammarPresentationEntryNaturalList,
        or_assoc
      ]

/-- The local natural-value bound of one encoded presentation entry.  It
simultaneously bounds the entry payload length and every field value occurring
inside that payload. -/
noncomputable def compiledGrammarPresentationEntryNaturalValueBound
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H) :
    Nat :=
  naturalFieldValueBound
    (H.encodeCompiledGrammarPresentationEntryNaturalList
      dummy entry)

/-- The natural length of an encoded entry is bounded by its local value bound. -/
theorem
    compiledGrammarPresentationEntryNaturalFieldCount_le_valueBound
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H) :
    H.compiledGrammarPresentationEntryNaturalFieldCount
        dummy entry <=
      H.compiledGrammarPresentationEntryNaturalValueBound
        dummy entry := by

  simpa [
    compiledGrammarPresentationEntryNaturalValueBound
  ] using
    fieldCount_le_naturalFieldValueBound
      (H.encodeCompiledGrammarPresentationEntryNaturalList
        dummy entry)

/-- Every classified field of one entry is bounded by that entry's local value
bound. -/
theorem
    compiledGrammarPresentationEntryNaturalField_le_valueBound
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    {n : Nat}
    (hclass :
      H.CompiledGrammarPresentationEntryNaturalFieldClass
        dummy entry n) :
    n <=
      H.compiledGrammarPresentationEntryNaturalValueBound
        dummy entry := by

  apply
    field_le_naturalFieldValueBound_of_mem
      (H.encodeCompiledGrammarPresentationEntryNaturalList
        dummy entry)

  exact
    (H.compiledGrammarPresentationEntryNaturalFieldClass_iff_mem
      dummy entry n).mp hclass

/-- Compact exact entry-local classification and bound package. -/
theorem
    compiledGrammarPresentationEntryNaturalFieldClassification_package
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (n : Nat) :
    (H.CompiledGrammarPresentationEntryNaturalFieldClass
        dummy entry n ↔
      n ∈
        H.encodeCompiledGrammarPresentationEntryNaturalList
          dummy entry) ∧
      (H.CompiledGrammarPresentationEntryNaturalFieldClass
          dummy entry n →
        n <=
          H.compiledGrammarPresentationEntryNaturalValueBound
            dummy entry) ∧
      (H.compiledGrammarPresentationEntryNaturalFieldCount
          dummy entry <=
        H.compiledGrammarPresentationEntryNaturalValueBound
          dummy entry) := by

  exact
    ⟨H.compiledGrammarPresentationEntryNaturalFieldClass_iff_mem
        dummy entry n,
      H.compiledGrammarPresentationEntryNaturalField_le_valueBound
        dummy entry,
      H.compiledGrammarPresentationEntryNaturalFieldCount_le_valueBound
        dummy entry⟩

end CorrectedConcreteFiniteHypothesis

end EntryNaturalFieldClassification


section PresentationStreamNaturalFieldClassification

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Exact source classification of a natural field in a framed stream of
presentation entries. -/
noncomputable def CompiledGrammarPresentationEntryStreamNaturalFieldClass
    (dummy : α)
    (entries :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry H))
    (n : Nat) :
    Prop :=
  ∃ entry,
    entry ∈ entries ∧
      (n =
          H.compiledGrammarPresentationEntryNaturalFieldCount
            dummy entry ∨
        H.CompiledGrammarPresentationEntryNaturalFieldClass
          dummy entry n)

/-- Every classified framed-stream field occurs in the encoded stream. -/
theorem
    mem_encodeCompiledGrammarPresentationEntryStream_of_class
    (dummy : α) :
    ∀
      (entries :
        List
          (CorrectedConcreteCompiledGrammarPresentationEntry H))
      (n : Nat),
      H.CompiledGrammarPresentationEntryStreamNaturalFieldClass
          dummy entries n →
        n ∈
          H.encodeCompiledGrammarPresentationEntryStream
            dummy entries

  | [], n, hclass => by
      simp [
        CompiledGrammarPresentationEntryStreamNaturalFieldClass
      ] at hclass

  | entry :: entries, n, hclass => by
      rcases hclass with
        ⟨source, hsource, hframe | hentryField⟩

      rcases List.mem_cons.mp hsource with
        rfl | hsourceTail

      · unfold
          encodeCompiledGrammarPresentationEntryStream

        dsimp

        apply List.mem_cons.mpr
        left

        simpa using hframe

      · have htailClass :
            H.CompiledGrammarPresentationEntryStreamNaturalFieldClass
              dummy entries n :=
          ⟨source, hsourceTail, Or.inl hframe⟩

        have htailMem :
            n ∈
              H.encodeCompiledGrammarPresentationEntryStream
                dummy entries :=
          H.mem_encodeCompiledGrammarPresentationEntryStream_of_class
            dummy entries n htailClass

        unfold
          encodeCompiledGrammarPresentationEntryStream

        dsimp

        apply List.mem_cons.mpr
        right

        apply List.mem_append.mpr
        right

        exact htailMem

      · unfold
          encodeCompiledGrammarPresentationEntryStream

        dsimp

        apply List.mem_cons.mpr
        right

        apply List.mem_append.mpr
        left

        exact
          (H.compiledGrammarPresentationEntryNaturalFieldClass_iff_mem
            dummy entry n).mp hentryField

      · have htailClass :
            H.CompiledGrammarPresentationEntryStreamNaturalFieldClass
              dummy entries n :=
          ⟨source, hsourceTail, Or.inr hentryField⟩

        have htailMem :
            n ∈
              H.encodeCompiledGrammarPresentationEntryStream
                dummy entries :=
          H.mem_encodeCompiledGrammarPresentationEntryStream_of_class
            dummy entries n htailClass

        unfold
          encodeCompiledGrammarPresentationEntryStream

        dsimp

        apply List.mem_cons.mpr
        right

        apply List.mem_append.mpr
        right

        exact htailMem

/-- Every natural field occurring in a framed presentation stream has one of
the classified entry-local sources. -/
theorem
    class_of_mem_encodeCompiledGrammarPresentationEntryStream
    (dummy : α) :
    ∀
      (entries :
        List
          (CorrectedConcreteCompiledGrammarPresentationEntry H))
      (n : Nat),
      n ∈
          H.encodeCompiledGrammarPresentationEntryStream
            dummy entries →
        H.CompiledGrammarPresentationEntryStreamNaturalFieldClass
          dummy entries n

  | [], n, hmem => by
      simp [
        encodeCompiledGrammarPresentationEntryStream
      ] at hmem

  | entry :: entries, n, hmem => by
      unfold
        encodeCompiledGrammarPresentationEntryStream
        at hmem

      dsimp at hmem

      rcases List.mem_cons.mp hmem with
        hframe | hrest

      · exact
          ⟨entry,
            by simp,
            Or.inl
              (by simpa using hframe)⟩

      · rcases List.mem_append.mp hrest with
          hentry | htail

        · exact
            ⟨entry,
              by simp,
              Or.inr
                ((H.compiledGrammarPresentationEntryNaturalFieldClass_iff_mem
                    dummy entry n).mpr hentry)⟩

        · rcases
            H.class_of_mem_encodeCompiledGrammarPresentationEntryStream
              dummy entries n htail with
          ⟨source, hsource, hkind⟩

          exact
            ⟨source,
              by simp [hsource],
              hkind⟩

/-- Framed-stream classification is exact. -/
@[simp] theorem
    compiledGrammarPresentationEntryStreamNaturalFieldClass_iff_mem
    (dummy : α)
    (entries :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry H))
    (n : Nat) :
    H.CompiledGrammarPresentationEntryStreamNaturalFieldClass
        dummy entries n ↔
      n ∈
        H.encodeCompiledGrammarPresentationEntryStream
          dummy entries := by

  constructor

  · exact
      H.mem_encodeCompiledGrammarPresentationEntryStream_of_class
        dummy entries n

  · exact
      H.class_of_mem_encodeCompiledGrammarPresentationEntryStream
        dummy entries n

end CorrectedConcreteFiniteHypothesis

end PresentationStreamNaturalFieldClassification


section CompleteGrammarNaturalFieldClassification

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Exact source classification of a natural field in the complete pure-natural
compiled-grammar serialization. -/
noncomputable def CompiledWorkingGrammarNaturalFieldClass
    (dummy : α)
    (n : Nat) :
    Prop :=
  n = H.compiledGrammarPresentationItemCount ∨
    H.CompiledGrammarPresentationEntryStreamNaturalFieldClass
      dummy
      (H.compiledGrammarPresentationEntries dummy)
      n

/-- Complete-grammar field classification is exact. -/
@[simp] theorem compiledWorkingGrammarNaturalFieldClass_iff_mem
    (dummy : α)
    (n : Nat) :
    H.CompiledWorkingGrammarNaturalFieldClass dummy n ↔
      n ∈
        H.encodeCompiledWorkingGrammarNaturalList dummy := by

  classical

  constructor

  · intro hclass

    rcases hclass with
      hcount | hstream

    · unfold
        encodeCompiledWorkingGrammarNaturalList

      dsimp

      apply List.mem_cons.mpr
      left

      simpa using hcount

    · unfold
        encodeCompiledWorkingGrammarNaturalList

      dsimp

      apply List.mem_cons.mpr
      right

      exact
        (H.compiledGrammarPresentationEntryStreamNaturalFieldClass_iff_mem
          dummy
          (H.compiledGrammarPresentationEntries dummy)
          n).mp hstream

  · intro hmem

    unfold
      encodeCompiledWorkingGrammarNaturalList
      at hmem

    dsimp at hmem

    rcases List.mem_cons.mp hmem with
      hcount | hstream

    · left

      simpa using hcount

    · right

      exact
        (H.compiledGrammarPresentationEntryStreamNaturalFieldClass_iff_mem
          dummy
          (H.compiledGrammarPresentationEntries dummy)
          n).mpr hstream

/-- Expanded exact source form for every complete-grammar natural field. -/
theorem compiledWorkingGrammarNaturalField_classification
    (dummy : α)
    {n : Nat}
    (hmem :
      n ∈
        H.encodeCompiledWorkingGrammarNaturalList dummy) :
    n = H.compiledGrammarPresentationItemCount ∨
      ∃ entry,
        entry ∈
          H.compiledGrammarPresentationEntries dummy ∧
          (n =
              H.compiledGrammarPresentationEntryNaturalFieldCount
                dummy entry ∨
            H.CompiledGrammarPresentationEntryNaturalFieldClass
              dummy entry n) := by

  exact
    (H.compiledWorkingGrammarNaturalFieldClass_iff_mem
      dummy n).mpr hmem

end CorrectedConcreteFiniteHypothesis

end CompleteGrammarNaturalFieldClassification


section AggregatedEntryNaturalFieldBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Maximum entry-local natural-value bound among a finite list of presentation
entries. -/
noncomputable def maximumCompiledGrammarPresentationEntryNaturalValueBound
    (dummy : α)
    (entries :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry H)) :
    Nat :=
  maximumNaturalFieldValue
    (entries.map
      (fun entry =>
        H.compiledGrammarPresentationEntryNaturalValueBound
          dummy entry))

/-- Every stored entry-local bound is below the maximum over the entry list. -/
theorem
    compiledGrammarPresentationEntryNaturalValueBound_le_maximum_of_mem
    (dummy : α)
    (entries :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry H))
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hentry :
      entry ∈ entries) :
    H.compiledGrammarPresentationEntryNaturalValueBound
        dummy entry <=
      H.maximumCompiledGrammarPresentationEntryNaturalValueBound
        dummy entries := by

  unfold
    maximumCompiledGrammarPresentationEntryNaturalValueBound

  apply
    nat_le_maximumNaturalFieldValue_of_mem

  exact
    List.mem_map.mpr
      ⟨entry, hentry, rfl⟩

/-- Maximum entry-local natural value over the actual compiled presentation. -/
noncomputable def compiledWorkingGrammarMaximumEntryNaturalValueBound
    (dummy : α) :
    Nat :=
  H.maximumCompiledGrammarPresentationEntryNaturalValueBound
    dummy
    (H.compiledGrammarPresentationEntries dummy)

/-- Structural natural-field bound obtained after classification.

It includes

* the complete natural-field count;
* the presentation-item count stored as the first natural field; and
* the maximum local bound of every encoded top-level entry.
-/
noncomputable def compiledWorkingGrammarClassifiedNaturalFieldBound
    (dummy : α) :
    Nat :=
  max
    H.compiledWorkingGrammarNaturalFieldCount
    (max
      H.compiledGrammarPresentationItemCount
      (H.compiledWorkingGrammarMaximumEntryNaturalValueBound
        dummy))

/-- The complete natural-field count is below the classified structural bound. -/
theorem
    compiledWorkingGrammarNaturalFieldCount_le_classifiedBound
    (dummy : α) :
    H.compiledWorkingGrammarNaturalFieldCount <=
      H.compiledWorkingGrammarClassifiedNaturalFieldBound
        dummy := by

  exact
    Nat.le_max_left
      H.compiledWorkingGrammarNaturalFieldCount
      (max
        H.compiledGrammarPresentationItemCount
        (H.compiledWorkingGrammarMaximumEntryNaturalValueBound
          dummy))

/-- The stored presentation-item count is below the classified structural
bound. -/
theorem
    compiledGrammarPresentationItemCount_le_classifiedBound
    (dummy : α) :
    H.compiledGrammarPresentationItemCount <=
      H.compiledWorkingGrammarClassifiedNaturalFieldBound
        dummy := by

  exact
    (Nat.le_max_left
      H.compiledGrammarPresentationItemCount
      (H.compiledWorkingGrammarMaximumEntryNaturalValueBound
        dummy)).trans
      (Nat.le_max_right
        H.compiledWorkingGrammarNaturalFieldCount
        (max
          H.compiledGrammarPresentationItemCount
          (H.compiledWorkingGrammarMaximumEntryNaturalValueBound
            dummy)))

/-- The maximum local entry bound is below the complete classified structural
bound. -/
theorem
    compiledWorkingGrammarMaximumEntryNaturalValueBound_le_classifiedBound
    (dummy : α) :
    H.compiledWorkingGrammarMaximumEntryNaturalValueBound dummy <=
      H.compiledWorkingGrammarClassifiedNaturalFieldBound
        dummy := by

  exact
    (Nat.le_max_right
      H.compiledGrammarPresentationItemCount
      (H.compiledWorkingGrammarMaximumEntryNaturalValueBound
        dummy)).trans
      (Nat.le_max_right
        H.compiledWorkingGrammarNaturalFieldCount
        (max
          H.compiledGrammarPresentationItemCount
          (H.compiledWorkingGrammarMaximumEntryNaturalValueBound
            dummy)))

/-- Every complete-grammar natural field is below the classified structural
bound. -/
theorem
    compiledWorkingGrammarNaturalField_le_classifiedBound_of_mem
    (dummy : α)
    {n : Nat}
    (hmem :
      n ∈
        H.encodeCompiledWorkingGrammarNaturalList dummy) :
    n <=
      H.compiledWorkingGrammarClassifiedNaturalFieldBound
        dummy := by

  rcases
      H.compiledWorkingGrammarNaturalField_classification
        dummy hmem with
    hcount | ⟨entry, hentry, hframe | hentryField⟩

  · subst n

    exact
      H.compiledGrammarPresentationItemCount_le_classifiedBound
        dummy

  · have hlocal :
        n <=
          H.compiledGrammarPresentationEntryNaturalValueBound
            dummy entry := by

      calc
        n =
            H.compiledGrammarPresentationEntryNaturalFieldCount
              dummy entry := hframe
        _ <=
            H.compiledGrammarPresentationEntryNaturalValueBound
              dummy entry :=
          H.compiledGrammarPresentationEntryNaturalFieldCount_le_valueBound
            dummy entry

    exact
      hlocal.trans
        ((H.compiledGrammarPresentationEntryNaturalValueBound_le_maximum_of_mem
            dummy
            (H.compiledGrammarPresentationEntries dummy)
            entry
            hentry).trans
          (H.compiledWorkingGrammarMaximumEntryNaturalValueBound_le_classifiedBound
            dummy))

  · have hlocal :
        n <=
          H.compiledGrammarPresentationEntryNaturalValueBound
            dummy entry :=
      H.compiledGrammarPresentationEntryNaturalField_le_valueBound
        dummy entry hentryField

    exact
      hlocal.trans
        ((H.compiledGrammarPresentationEntryNaturalValueBound_le_maximum_of_mem
            dummy
            (H.compiledGrammarPresentationEntries dummy)
            entry
            hentry).trans
          (H.compiledWorkingGrammarMaximumEntryNaturalValueBound_le_classifiedBound
            dummy))

/-- The previous complete-grammar natural-field value bound is below the new
classification-based structural bound. -/
theorem
    compiledWorkingGrammarNaturalFieldValueBound_le_classifiedBound
    (dummy : α) :
    H.compiledWorkingGrammarNaturalFieldValueBound dummy <=
      H.compiledWorkingGrammarClassifiedNaturalFieldBound
        dummy := by

  unfold
    compiledWorkingGrammarNaturalFieldValueBound

  apply
    naturalFieldValueBound_le_of_count_le_of_all_le

  · rw [
      H.encodeCompiledWorkingGrammarNaturalList_length
        dummy
    ]

    exact
      H.compiledWorkingGrammarNaturalFieldCount_le_classifiedBound
        dummy

  · intro n hmem

    exact
      H.compiledWorkingGrammarNaturalField_le_classifiedBound_of_mem
        dummy hmem

/-- Compact final package for this classification layer. -/
theorem
    compiledWorkingGrammarNaturalFieldClassification_package
    (dummy : α) :
    (∀ n : Nat,
      H.CompiledWorkingGrammarNaturalFieldClass dummy n ↔
        n ∈
          H.encodeCompiledWorkingGrammarNaturalList dummy) ∧
      (∀ n ∈
          H.encodeCompiledWorkingGrammarNaturalList dummy,
        n <=
          H.compiledWorkingGrammarClassifiedNaturalFieldBound
            dummy) ∧
      (H.compiledWorkingGrammarNaturalFieldValueBound dummy <=
        H.compiledWorkingGrammarClassifiedNaturalFieldBound
          dummy) := by

  exact
    ⟨by
        intro n
        exact
          H.compiledWorkingGrammarNaturalFieldClass_iff_mem
            dummy n,
      by
        intro n hmem
        exact
          H.compiledWorkingGrammarNaturalField_le_classifiedBound_of_mem
            dummy hmem,
      H.compiledWorkingGrammarNaturalFieldValueBound_le_classifiedBound
        dummy⟩

end CorrectedConcreteFiniteHypothesis

end AggregatedEntryNaturalFieldBound

end MCFG
