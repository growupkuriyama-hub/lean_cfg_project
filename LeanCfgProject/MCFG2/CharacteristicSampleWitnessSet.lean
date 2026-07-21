/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleFromTrimmedPresentation

/-!
# CharacteristicSampleWitnessSet.lean

Forty-seventh clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleFromTrimmedPresentation.lean` packaged a finite set
containing the presentation-relative characteristic witness words as

```lean
TrimmedPresentationCharacteristicSample
```

This file defines the corresponding witness-word set directly:

```lean
TrimmedPresentationWitnessWordSet D
```

It contains exactly the kinds of words required by the trimmed-presentation
route:

* anchor witness words;
* terminal-rule witness words;
* binary-rule witness words;
* start-rule witness words;
* the distinguished start word.

Then we prove that any positive finite sample containing this witness-word set
yields a `TrimmedPresentationCharacteristicSample`, and therefore the stable
trimmed-presentation final theorem.

This is still not the concrete enumeration of `CS(G̃₀)`, but it reduces that
future task to a clean finite-set inclusion statement.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section WitnessWordSet

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- The set of all witness words required by a trimmed-presentation pre-core.

A future concrete characteristic-sample construction should build a finite
sample containing this set. -/
def TrimmedPresentationWitnessWordSet
    (D : TrimmedPresentationPreCoreData T f) : Set (Word α) :=
  fun word =>
    (∃ A : N, word = D.anchorWitnessWord A) ∨
    (∃ ρ : TerminalRule N α,
      ρ ∈ G.terminalRules ∧
        ∃ hwt : G.arity ρ.lhs = 1,
          word = D.terminalWitnessWord ρ hwt) ∨
    (∃ ρ : BinaryRule N α G.arity,
      ρ ∈ G.binaryRules ∧
        word = D.binaryWitnessWord ρ) ∨
    (∃ ρ : StartRule N,
      ρ ∈ G.startRules ∧
        ∃ hwt : G.arity ρ.child = G.arity G.start,
          word = D.startWitnessWord ρ hwt) ∨
    word = D.startWord

namespace TrimmedPresentationWitnessWordSet

variable {D : TrimmedPresentationPreCoreData T f}

/-- Anchor witness words belong to the witness-word set. -/
theorem anchor_mem
    (A : N) :
    D.anchorWitnessWord A ∈ TrimmedPresentationWitnessWordSet D := by
  left
  exact ⟨A, rfl⟩

/-- Terminal witness words belong to the witness-word set. -/
theorem terminal_mem
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    D.terminalWitnessWord ρ hwt ∈
      TrimmedPresentationWitnessWordSet D := by
  right
  left
  exact ⟨ρ, hρ, ⟨hwt, rfl⟩⟩

/-- Binary witness words belong to the witness-word set. -/
theorem binary_mem
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈
      TrimmedPresentationWitnessWordSet D := by
  right
  right
  left
  exact ⟨ρ, hρ, rfl⟩

/-- Start-rule witness words belong to the witness-word set. -/
theorem start_mem
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    D.startWitnessWord ρ hwt ∈
      TrimmedPresentationWitnessWordSet D := by
  right
  right
  right
  left
  exact ⟨ρ, hρ, ⟨hwt, rfl⟩⟩

/-- The distinguished start word belongs to the witness-word set. -/
theorem startWord_mem :
    D.startWord ∈ TrimmedPresentationWitnessWordSet D := by
  right
  right
  right
  right
  rfl

end TrimmedPresentationWitnessWordSet

end WitnessWordSet


section WitnessSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

/-- A positive finite sample containing all words in the trimmed-presentation
witness-word set. -/
structure TrimmedPresentationWitnessSample
    (D : TrimmedPresentationPreCoreData T f)
    (S : Finset (Word α)) where
  sample_positive : (S : Set (Word α)) ⊆ G.StringLanguage
  contains_witnesses :
    TrimmedPresentationWitnessWordSet D ⊆ (S : Set (Word α))

namespace TrimmedPresentationWitnessSample

/-- A witness-sample package supplies trimmed-presentation sample data. -/
def toSampleData
    (H : TrimmedPresentationWitnessSample D S) :
    TrimmedPresentationSampleData D S where
  sample_positive := H.sample_positive
  anchor_mem := by
    intro A
    exact H.contains_witnesses
      (TrimmedPresentationWitnessWordSet.anchor_mem (D := D) A)
  terminal_mem := by
    intro ρ hρ hwt
    exact H.contains_witnesses
      (TrimmedPresentationWitnessWordSet.terminal_mem
        (D := D) ρ hρ hwt)
  binary_mem := by
    intro ρ hρ
    exact H.contains_witnesses
      (TrimmedPresentationWitnessWordSet.binary_mem
        (D := D) ρ hρ)
  start_mem := by
    intro ρ hρ hwt
    exact H.contains_witnesses
      (TrimmedPresentationWitnessWordSet.start_mem
        (D := D) ρ hρ hwt)
  startWord_mem :=
    H.contains_witnesses
      (TrimmedPresentationWitnessWordSet.startWord_mem (D := D))

/-- A witness-sample package supplies a characteristic-sample object. -/
def toCharacteristicSample
    (H : TrimmedPresentationWitnessSample D S) :
    TrimmedPresentationCharacteristicSample D :=
  TrimmedPresentationCharacteristicSample.ofSampleData H.toSampleData

@[simp] theorem toCharacteristicSample_sample
    (H : TrimmedPresentationWitnessSample D S) :
    H.toCharacteristicSample.sample = S :=
  rfl

/-- Convert directly to trimmed final data after adding the remaining splicing
constructor and global assumptions. -/
def toFinalData
    (H : TrimmedPresentationWitnessSample D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationFinalData D S :=
  TrimmedPresentationFinalData.mk H.toSampleData U hfan hL

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (H : TrimmedPresentationWitnessSample D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G S obs f :=
  (H.toFinalData U hfan hL).toFinalReachableData

/-- Exact reconstruction for every positive finite superset of a witness
sample. -/
theorem exact_for_positive_superset
    (H : TrimmedPresentationWitnessSample D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  (H.toFinalData U hfan hL).exact_for_positive_superset hSK hKpos

/-- Eventual prefix-exact reconstruction from a witness sample. -/
theorem prefix_exact_eventually
    (H : TrimmedPresentationWitnessSample D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (H.toFinalData U hfan hL).prefix_exact_eventually

/-- Reachable Gold identification from a witness sample. -/
theorem identifies_from_positive_text
    (H : TrimmedPresentationWitnessSample D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (H.toFinalData U hfan hL).identifies_from_positive_text

end TrimmedPresentationWitnessSample

end WitnessSample


section CharacteristicSampleContainsWitnesses

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

namespace TrimmedPresentationCharacteristicSample

/-- A characteristic-sample object contains the whole witness-word set. -/
theorem contains_witness_word_set
    (C : TrimmedPresentationCharacteristicSample D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) := by
  intro word hword
  rcases hword with hAnchor | hRest
  · rcases hAnchor with ⟨A, rfl⟩
    exact C.anchor_mem A
  rcases hRest with hTerminal | hRest
  · rcases hTerminal with ⟨ρ, hρ, hwt, rfl⟩
    exact C.terminal_mem ρ hρ hwt
  rcases hRest with hBinary | hRest
  · rcases hBinary with ⟨ρ, hρ, rfl⟩
    exact C.binary_mem ρ hρ
  rcases hRest with hStart | hStartWord
  · rcases hStart with ⟨ρ, hρ, hwt, rfl⟩
    exact C.start_mem ρ hρ hwt
  · rw [hStartWord]
    exact C.startWord_mem

/-- Any characteristic-sample object is a witness-sample package. -/
def toWitnessSample
    (C : TrimmedPresentationCharacteristicSample D) :
    TrimmedPresentationWitnessSample D C.sample where
  sample_positive := C.sample_positive
  contains_witnesses := C.contains_witness_word_set

end TrimmedPresentationCharacteristicSample

end CharacteristicSampleContainsWitnesses


section MainTheoremsFromWitnessSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

/-- Stable top-level identification theorem from a positive finite sample that
contains the trimmed-presentation witness-word set. -/
theorem trimmed_witness_sample_reachable_identification
    (H : TrimmedPresentationWitnessSample D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  H.identifies_from_positive_text U hfan hL

/-- Stable top-level prefix-exact theorem from a positive finite sample that
contains the trimmed-presentation witness-word set. -/
theorem trimmed_witness_sample_reachable_prefix_exact
    (H : TrimmedPresentationWitnessSample D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  H.prefix_exact_eventually U hfan hL

end MainTheoremsFromWitnessSample

end MCFG
