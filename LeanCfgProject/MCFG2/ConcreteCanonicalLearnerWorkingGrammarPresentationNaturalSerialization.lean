/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarBinaryRuleTerminalClosure

/-!
# ConcreteCanonicalLearnerWorkingGrammarPresentationNaturalSerialization.lean

The preceding development gives a pure-`Nat` list codec for every binary rule
actually stored in the cut-compiled grammar.  This file extends that codec to
the complete finite grammar presentation.

Each top-level presentation entry is encoded by a tagged natural list:

```text
[0, nonterminalCode]

[1, childCode]

[2, lhsCode, terminalCode]

[3, binaryPayloadLength] ++ binaryPayload.
```

The four cases represent, respectively,

* a nonterminal declaration;
* a start rule;
* a terminal rule;
* a binary rule.

Nonterminal references use the global tagged dense code from the earlier
presentation codec.  Terminals use the dense code in

```text
insert dummy (sampleAlphabet K).
```

Binary payloads use the complete checked pure-natural codec already constructed.

The complete presentation is then serialized as one natural list.  Every entry
payload receives its own length prefix, and the entire stream receives an
initial entry count:

```text
[entryCount,
 entryLength_1, entryPayload_1,
 ...
 entryLength_n, entryPayload_n].
```

The decoder checks all entry lengths, all tags, all finite references, all
terminal codes, all dependent binary-rule data, the declared entry count, and
the absence of trailing fields.

The main endpoint is the exact whole-presentation round trip:

```lean
H.decodeCompiledWorkingGrammarNaturalList dummy
    (H.encodeCompiledWorkingGrammarNaturalList dummy)
  =
some (H.compiledGrammarPresentationEntries dummy).
```

An exact formula for the number of natural fields in the serialization is also
proved.  Bit widths and bit-level concatenation remain separate later layers.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section PresentationEntryNaturalCodec

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Encode one tagged top-level presentation entry as a self-contained natural
list. -/
noncomputable def encodeCompiledGrammarPresentationEntryNaturalList
    (dummy : α) :
    CorrectedConcreteCompiledGrammarPresentationEntry H →
      List Nat

  | .nonterminal A =>
      [0,
        H.compiledGrammarGlobalDenseCode dummy
          (.nonterminal A)]

  | .startRule rho =>
      [1,
        H.compiledGrammarGlobalDenseCode dummy
          (.nonterminal rho.child)]

  | .terminalRule rho =>
      [2,
        H.compiledGrammarGlobalDenseCode dummy
          (.nonterminal rho.lhs),
        compiledTerminalDenseCode
          K dummy rho.terminal]

  | .binaryRule rho =>
      let payload :=
        H.encodeCompiledBinaryRuleNaturalList
          dummy rho
      3 :: payload.length :: payload

/-- Checked reconstruction of one tagged top-level presentation entry from a
self-contained natural list. -/
noncomputable def decodeCompiledGrammarPresentationEntryNaturalList
    (dummy : α) :
    List Nat →
      Option
        (CorrectedConcreteCompiledGrammarPresentationEntry H)

  | 0 :: code :: [] =>
      match
          H.decodeCompiledNonterminalCode
            dummy code with

      | none =>
          none

      | some A =>
          some (.nonterminal A)

  | 1 :: childCode :: [] =>
      match
          H.decodeCompiledNonterminalCode
            dummy childCode with

      | none =>
          none

      | some child =>
          some
            (.startRule
              { child := child })

  | 2 :: lhsCode :: terminalCode :: [] =>
      match
          H.decodeCompiledNonterminalCode
            dummy lhsCode with

      | none =>
          none

      | some lhs =>
          match
              compiledTerminalDenseDecode
                K dummy terminalCode with

          | none =>
              none

          | some terminal =>
              some
                (.terminalRule
                  { lhs := lhs
                    terminal := terminal })

  | 3 :: payloadLength :: payload =>
      if hlength :
          payload.length = payloadLength then

        match
            H.decodeCompiledBinaryRuleNaturalList
              dummy payload with

        | none =>
            none

        | some rho =>
            some (.binaryRule rho)

      else
        none

  | _ =>
      none

/-- Nonterminal declarations survive the structural natural-list codec. -/
@[simp] theorem
    decodeCompiledGrammarPresentationEntryNaturalList_encode_nonterminal
    (dummy : α)
    (A : CorrectedConcreteCutGrammarNonterminal H) :
    H.decodeCompiledGrammarPresentationEntryNaturalList dummy
        (H.encodeCompiledGrammarPresentationEntryNaturalList
          dummy (.nonterminal A)) =
      some (.nonterminal A) := by

  classical

  simp [
    encodeCompiledGrammarPresentationEntryNaturalList,
    decodeCompiledGrammarPresentationEntryNaturalList
  ]

/-- Start rules survive the structural natural-list codec. -/
@[simp] theorem
    decodeCompiledGrammarPresentationEntryNaturalList_encode_startRule
    (dummy : α)
    (rho : StartRule
      (CorrectedConcreteCutGrammarNonterminal H)) :
    H.decodeCompiledGrammarPresentationEntryNaturalList dummy
        (H.encodeCompiledGrammarPresentationEntryNaturalList
          dummy (.startRule rho)) =
      some (.startRule rho) := by

  classical

  rcases rho with ⟨child⟩

  simp [
    encodeCompiledGrammarPresentationEntryNaturalList,
    decodeCompiledGrammarPresentationEntryNaturalList
  ]

/-- Terminal rules survive the structural natural-list codec whenever their
literal terminal lies in the augmented finite compiled alphabet. -/
@[simp] theorem
    decodeCompiledGrammarPresentationEntryNaturalList_encode_terminalRule
    (dummy : α)
    (rho : TerminalRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α)
    (hterminal :
      rho.terminal ∈
        compiledTerminalAlphabet K dummy) :
    H.decodeCompiledGrammarPresentationEntryNaturalList dummy
        (H.encodeCompiledGrammarPresentationEntryNaturalList
          dummy (.terminalRule rho)) =
      some (.terminalRule rho) := by

  classical

  rcases rho with ⟨lhs, terminal⟩

  simp [
    encodeCompiledGrammarPresentationEntryNaturalList,
    decodeCompiledGrammarPresentationEntryNaturalList,
    compiledTerminalDenseDecode_encode_of_mem
      K dummy terminal hterminal
  ]

/-- Binary rules actually stored in the compiled grammar survive the complete
structural natural-list codec with no additional terminal-support premise. -/
@[simp] theorem
    decodeCompiledGrammarPresentationEntryNaturalList_encode_binaryRule_of_mem
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈
        (H.toCutWorkingMCFG dummy).binaryRules) :
    H.decodeCompiledGrammarPresentationEntryNaturalList dummy
        (H.encodeCompiledGrammarPresentationEntryNaturalList
          dummy (.binaryRule rho)) =
      some (.binaryRule rho) := by

  classical

  simp [
    encodeCompiledGrammarPresentationEntryNaturalList,
    decodeCompiledGrammarPresentationEntryNaturalList,
    H.decodeCompiledBinaryRuleNaturalList_encode_of_mem
      dummy rho hrho
  ]

/-- Every stored terminal rule is the dummy seed rule, hence its literal
terminal lies in the augmented finite compiled alphabet. -/
theorem terminalRule_terminal_mem_compiledTerminalAlphabet_of_mem
    (dummy : α)
    (rho : TerminalRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α)
    (hrho :
      rho ∈
        (H.toCutWorkingMCFG dummy).terminalRules) :
    rho.terminal ∈
      compiledTerminalAlphabet K dummy := by

  have hrhoEq :
      rho =
        correctedConcreteCutSeedRule
          H dummy := by

    simpa [
      CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG
    ] using hrho

  subst rho

  exact
    dummy_mem_compiledTerminalAlphabet
      K dummy

/-- Every actually stored tagged presentation entry survives the complete
entry-level natural-list codec. -/
@[simp] theorem
    decodeCompiledGrammarPresentationEntryNaturalList_encode_of_mem
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hentry :
      entry ∈
        H.compiledGrammarPresentationEntries dummy) :
    H.decodeCompiledGrammarPresentationEntryNaturalList dummy
        (H.encodeCompiledGrammarPresentationEntryNaturalList
          dummy entry) =
      some entry := by

  classical

  cases entry with

  | nonterminal A =>
      exact
        H.decodeCompiledGrammarPresentationEntryNaturalList_encode_nonterminal
          dummy A

  | startRule rho =>
      exact
        H.decodeCompiledGrammarPresentationEntryNaturalList_encode_startRule
          dummy rho

  | terminalRule rho =>
      have hrho :
          rho ∈
            (H.toCutWorkingMCFG dummy).terminalRules := by

        simpa [
          CorrectedConcreteFiniteHypothesis.compiledGrammarPresentationEntries
        ] using hentry

      exact
        H.decodeCompiledGrammarPresentationEntryNaturalList_encode_terminalRule
          dummy rho
          (H.terminalRule_terminal_mem_compiledTerminalAlphabet_of_mem
            dummy rho hrho)

  | binaryRule rho =>
      have hrho :
          rho ∈
            (H.toCutWorkingMCFG dummy).binaryRules := by

        simpa [
          CorrectedConcreteFiniteHypothesis.compiledGrammarPresentationEntries
        ] using hentry

      exact
        H.decodeCompiledGrammarPresentationEntryNaturalList_encode_binaryRule_of_mem
          dummy rho hrho

/-- Exact natural-field count of one structurally encoded top-level entry. -/
def compiledGrammarPresentationEntryNaturalFieldCount
    (dummy : α) :
    CorrectedConcreteCompiledGrammarPresentationEntry H →
      Nat

  | .nonterminal _ =>
      2

  | .startRule _ =>
      2

  | .terminalRule _ =>
      3

  | .binaryRule rho =>
      2 +
        (H.encodeCompiledBinaryRuleNaturalList
          dummy rho).length

/-- The entry field-count definition is exactly the length of the structural
natural serialization. -/
@[simp] theorem
    encodeCompiledGrammarPresentationEntryNaturalList_length
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H) :
    (H.encodeCompiledGrammarPresentationEntryNaturalList
        dummy entry).length =
      H.compiledGrammarPresentationEntryNaturalFieldCount
        dummy entry := by

  cases entry with

  | nonterminal A =>
      rfl

  | startRule rho =>
      rfl

  | terminalRule rho =>
      rfl

  | binaryRule rho =>
      simp [
        encodeCompiledGrammarPresentationEntryNaturalList,
        compiledGrammarPresentationEntryNaturalFieldCount,
        Nat.add_comm
      ]

/-- Expanded exact field count for a binary-rule presentation entry. -/
@[simp] theorem
    compiledGrammarPresentationEntryNaturalFieldCount_binaryRule
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H)) :
    H.compiledGrammarPresentationEntryNaturalFieldCount
        dummy (.binaryRule rho) =
      6 +
        2 *
          (correctedConcreteCutGrammarArity H rho.lhs +
            ((List.ofFn rho.body).map List.length).sum) := by

  simp [
    compiledGrammarPresentationEntryNaturalFieldCount,
    Nat.add_assoc
  ]

/-- Compact entry-level codec endpoint for any actually stored presentation
entry. -/
theorem compiledGrammarPresentationEntryNaturalCodec_of_mem_package
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hentry :
      entry ∈
        H.compiledGrammarPresentationEntries dummy) :
    (H.decodeCompiledGrammarPresentationEntryNaturalList dummy
        (H.encodeCompiledGrammarPresentationEntryNaturalList
          dummy entry) =
      some entry) ∧
      ((H.encodeCompiledGrammarPresentationEntryNaturalList
          dummy entry).length =
        H.compiledGrammarPresentationEntryNaturalFieldCount
          dummy entry) := by

  constructor

  · exact
      H.decodeCompiledGrammarPresentationEntryNaturalList_encode_of_mem
        dummy entry hentry

  · exact
      H.encodeCompiledGrammarPresentationEntryNaturalList_length
        dummy entry

end CorrectedConcreteFiniteHypothesis

end PresentationEntryNaturalCodec


section FramedPresentationStream

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Concatenate an ordered list of encoded presentation entries, placing the
length of each entry payload immediately before that payload. -/
noncomputable def encodeCompiledGrammarPresentationEntryStream
    (dummy : α) :
    List
        (CorrectedConcreteCompiledGrammarPresentationEntry H) →
      List Nat

  | [] =>
      []

  | entry :: entries =>
      let payload :=
        H.encodeCompiledGrammarPresentationEntryNaturalList
          dummy entry
      payload.length ::
        (payload ++
          H.encodeCompiledGrammarPresentationEntryStream
            dummy entries)

/-- Parse exactly the prescribed number of length-framed presentation entries,
retaining the unconsumed natural suffix. -/
noncomputable def decodeCompiledGrammarPresentationEntryStreamAux
    (dummy : α) :
    Nat → List Nat →
      Option
        (List
            (CorrectedConcreteCompiledGrammarPresentationEntry H) ×
          List Nat)

  | 0, codes =>
      some ([], codes)

  | Nat.succ _, [] =>
      none

  | Nat.succ entryCount,
      payloadLength :: rest =>
      match
          takeExactly payloadLength rest with

      | none =>
          none

      | some (payload, suffix) =>
          match
              H.decodeCompiledGrammarPresentationEntryNaturalList
                dummy payload with

          | none =>
              none

          | some entry =>
              match
                  H.decodeCompiledGrammarPresentationEntryStreamAux
                    dummy entryCount suffix with

              | none =>
                  none

              | some (entries, finalSuffix) =>
                  some
                    (entry :: entries,
                      finalSuffix)

/-- Exact stream decoder: the prescribed number of entry frames must consume
the complete natural stream. -/
noncomputable def decodeCompiledGrammarPresentationEntryStreamExact
    (dummy : α)
    (entryCount : Nat)
    (codes : List Nat) :
    Option
      (List
        (CorrectedConcreteCompiledGrammarPresentationEntry H)) :=

  match
      H.decodeCompiledGrammarPresentationEntryStreamAux
        dummy entryCount codes with

  | some (entries, []) =>
      some entries

  | _ =>
      none

/-- Decoding a framed stream of stored entries consumes exactly that stream and
leaves an arbitrary supplied suffix untouched. -/
theorem
    decodeCompiledGrammarPresentationEntryStreamAux_encode_append
    (dummy : α) :
    ∀
      (entries :
        List
          (CorrectedConcreteCompiledGrammarPresentationEntry H))
      (suffix : List Nat),
      (∀ entry ∈ entries,
        entry ∈
          H.compiledGrammarPresentationEntries dummy) →
      H.decodeCompiledGrammarPresentationEntryStreamAux
          dummy entries.length
          (H.encodeCompiledGrammarPresentationEntryStream
              dummy entries ++
            suffix) =
        some (entries, suffix)

  | [], suffix, _ => by
      rfl

  | entry :: entries, suffix, hstored => by
      have hentry :
          entry ∈
            H.compiledGrammarPresentationEntries dummy :=
        hstored entry (by simp)

      have hrest :
          ∀ next ∈ entries,
            next ∈
              H.compiledGrammarPresentationEntries dummy := by

        intro next hnext
        exact
          hstored next
            (by simp [hnext])

      have hdecodeEntry :
          H.decodeCompiledGrammarPresentationEntryNaturalList dummy
              (H.encodeCompiledGrammarPresentationEntryNaturalList
                dummy entry) =
            some entry :=
        H.decodeCompiledGrammarPresentationEntryNaturalList_encode_of_mem
          dummy entry hentry

      have hdecodeRest :
          H.decodeCompiledGrammarPresentationEntryStreamAux
              dummy entries.length
              (H.encodeCompiledGrammarPresentationEntryStream
                  dummy entries ++
                suffix) =
            some (entries, suffix) :=
        H.decodeCompiledGrammarPresentationEntryStreamAux_encode_append
          dummy entries suffix hrest

      simp [
        encodeCompiledGrammarPresentationEntryStream,
        decodeCompiledGrammarPresentationEntryStreamAux,
        takeExactly_length_append,
        hdecodeEntry,
        hdecodeRest,
        List.append_assoc
      ]

/-- Exact framed-stream decoding is the identity on every list of stored
presentation entries. -/
@[simp] theorem
    decodeCompiledGrammarPresentationEntryStreamExact_encode
    (dummy : α)
    (entries :
      List
        (CorrectedConcreteCompiledGrammarPresentationEntry H))
    (hstored :
      ∀ entry ∈ entries,
        entry ∈
          H.compiledGrammarPresentationEntries dummy) :
    H.decodeCompiledGrammarPresentationEntryStreamExact
        dummy entries.length
        (H.encodeCompiledGrammarPresentationEntryStream
          dummy entries) =
      some entries := by

  unfold
    decodeCompiledGrammarPresentationEntryStreamExact

  rw [
    show
      H.encodeCompiledGrammarPresentationEntryStream
          dummy entries =
        H.encodeCompiledGrammarPresentationEntryStream
            dummy entries ++ [] by
        simp
  ]

  rw [
    H.decodeCompiledGrammarPresentationEntryStreamAux_encode_append
      dummy entries [] hstored
  ]

/-- Exact length of a framed stream: each entry contributes one frame-length
field plus the fields of its entry payload. -/
@[simp] theorem
    encodeCompiledGrammarPresentationEntryStream_length
    (dummy : α) :
    ∀
      (entries :
        List
          (CorrectedConcreteCompiledGrammarPresentationEntry H)),
      (H.encodeCompiledGrammarPresentationEntryStream
          dummy entries).length =
        (entries.map
          (fun entry =>
            1 +
              H.compiledGrammarPresentationEntryNaturalFieldCount
                dummy entry)).sum

  | [] => by
      rfl

  | entry :: entries => by
      simp [
        encodeCompiledGrammarPresentationEntryStream,
        H.encodeCompiledGrammarPresentationEntryNaturalList_length,
        H.encodeCompiledGrammarPresentationEntryStream_length
          dummy entries,
        Nat.add_assoc,
        Nat.add_comm,
        Nat.add_left_comm
      ]

end CorrectedConcreteFiniteHypothesis

end FramedPresentationStream


section CompleteWorkingGrammarNaturalCodec

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Complete pure-natural serialization of the actual cut-compiled grammar.
The first field is the number of following length-framed presentation entries. -/
noncomputable def encodeCompiledWorkingGrammarNaturalList
    (dummy : α) :
    List Nat :=

  let entries :=
    H.compiledGrammarPresentationEntries dummy

  entries.length ::
    H.encodeCompiledGrammarPresentationEntryStream
      dummy entries

/-- Complete checked decoder for the pure-natural cut-compiled grammar
serialization. -/
noncomputable def decodeCompiledWorkingGrammarNaturalList
    (dummy : α) :
    List Nat →
      Option
        (List
          (CorrectedConcreteCompiledGrammarPresentationEntry H))

  | [] =>
      none

  | entryCount :: payload =>
      H.decodeCompiledGrammarPresentationEntryStreamExact
        dummy entryCount payload

/-- Exact natural-field count of the complete compiled grammar serialization. -/
noncomputable def compiledWorkingGrammarNaturalFieldCount
    (dummy : α) :
    Nat :=
  1 +
    ((H.compiledGrammarPresentationEntries dummy).map
      (fun entry =>
        1 +
          H.compiledGrammarPresentationEntryNaturalFieldCount
            dummy entry)).sum

/-- Whole-presentation pure-natural round trip. -/
@[simp] theorem decodeCompiledWorkingGrammarNaturalList_encode
    (dummy : α) :
    H.decodeCompiledWorkingGrammarNaturalList dummy
        (H.encodeCompiledWorkingGrammarNaturalList dummy) =
      some
        (H.compiledGrammarPresentationEntries dummy) := by

  classical

  unfold
    encodeCompiledWorkingGrammarNaturalList
    decodeCompiledWorkingGrammarNaturalList

  exact
    H.decodeCompiledGrammarPresentationEntryStreamExact_encode
      dummy
      (H.compiledGrammarPresentationEntries dummy)
      (by
        intro entry hentry
        exact hentry)

/-- The complete natural-field count is exactly the length of the complete
pure-natural serialization. -/
@[simp] theorem encodeCompiledWorkingGrammarNaturalList_length
    (dummy : α) :
    (H.encodeCompiledWorkingGrammarNaturalList dummy).length =
      H.compiledWorkingGrammarNaturalFieldCount dummy := by

  classical

  simp [
    encodeCompiledWorkingGrammarNaturalList,
    compiledWorkingGrammarNaturalFieldCount,
    Nat.add_comm
  ]

/-- The entry count stored in the complete natural serialization is exactly the
previously verified complete presentation item count. -/
@[simp] theorem encodeCompiledWorkingGrammarNaturalList_head
    (dummy : α) :
    (H.encodeCompiledWorkingGrammarNaturalList dummy).head? =
      some H.compiledGrammarPresentationItemCount := by

  classical

  simp [
    encodeCompiledWorkingGrammarNaturalList
  ]

/-- Compact whole-grammar codec endpoint: exact round trip, exact natural-field
count, and the verified top-level entry count. -/
theorem compiledWorkingGrammarNaturalCodec_package
    (dummy : α) :
    (H.decodeCompiledWorkingGrammarNaturalList dummy
        (H.encodeCompiledWorkingGrammarNaturalList dummy) =
      some
        (H.compiledGrammarPresentationEntries dummy)) ∧
      ((H.encodeCompiledWorkingGrammarNaturalList dummy).length =
        H.compiledWorkingGrammarNaturalFieldCount dummy) ∧
      ((H.encodeCompiledWorkingGrammarNaturalList dummy).head? =
        some H.compiledGrammarPresentationItemCount) := by

  exact
    ⟨H.decodeCompiledWorkingGrammarNaturalList_encode dummy,
      H.encodeCompiledWorkingGrammarNaturalList_length dummy,
      H.encodeCompiledWorkingGrammarNaturalList_head dummy⟩

end CorrectedConcreteFiniteHypothesis

end CompleteWorkingGrammarNaturalCodec

end MCFG
