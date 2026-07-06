/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.TrimmedPresentationFinalTheorem

/-!
# CharacteristicSampleFromTrimmedPresentation.lean

Forty-sixth clean Lean experiment for the fixed-observation MCFG project.

`TrimmedPresentationSample.lean` identified the witness words that a
presentation-relative characteristic sample must contain:

* anchor witness words;
* terminal-rule witness words;
* binary-rule witness words;
* start-rule witness words;
* the distinguished start word.

This file packages a finite set containing those words as a single object:

```lean
TrimmedPresentationCharacteristicSample
```

and proves that it supplies `TrimmedPresentationSampleData`, hence the stable
trimmed-presentation final theorem.

This is still not the concrete enumeration of `CS(G̃₀)`.  Rather, it is the
finite-set interface that a future enumeration file should construct.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section CharacteristicSampleObject

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- A finite characteristic sample associated with trimmed-presentation
pre-core data.

The record stores a finite set of words and the proof that it contains every
witness word required by `TrimmedPresentationSampleData`. -/
structure TrimmedPresentationCharacteristicSample
    (D : TrimmedPresentationPreCoreData T f) where
  sample : Finset (Word α)

  sample_positive : (sample : Set (Word α)) ⊆ G.StringLanguage

  anchor_mem :
    ∀ A : N,
      D.anchorWitnessWord A ∈ sample

  terminal_mem :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        D.terminalWitnessWord ρ hwt ∈ sample

  binary_mem :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        D.binaryWitnessWord ρ ∈ sample

  start_mem :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        D.startWitnessWord ρ hwt ∈ sample

  startWord_mem :
    D.startWord ∈ sample

namespace TrimmedPresentationCharacteristicSample

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert a characteristic sample object into the trimmed sample-data package
used by the final theorem. -/
def toSampleData
    (C : TrimmedPresentationCharacteristicSample D) :
    TrimmedPresentationSampleData D C.sample where
  sample_positive := C.sample_positive
  anchor_mem := C.anchor_mem
  terminal_mem := C.terminal_mem
  binary_mem := C.binary_mem
  start_mem := C.start_mem
  startWord_mem := C.startWord_mem

/-- Build the object from an existing trimmed sample-data package. -/
def ofSampleData
    {S : Finset (Word α)}
    (H : TrimmedPresentationSampleData D S) :
    TrimmedPresentationCharacteristicSample D where
  sample := S
  sample_positive := H.sample_positive
  anchor_mem := H.anchor_mem
  terminal_mem := H.terminal_mem
  binary_mem := H.binary_mem
  start_mem := H.start_mem
  startWord_mem := H.startWord_mem

@[simp] theorem ofSampleData_sample
    {S : Finset (Word α)}
    (H : TrimmedPresentationSampleData D S) :
    (ofSampleData H).sample = S :=
  rfl

/-- The sample is positive for the target grammar language. -/
theorem sample_subset_target
    (C : TrimmedPresentationCharacteristicSample D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.sample_positive

/-- Anchor witness words are in the target language. -/
theorem anchor_mem_target
    (C : TrimmedPresentationCharacteristicSample D)
    (A : N) :
    D.anchorWitnessWord A ∈ G.StringLanguage :=
  C.sample_positive (C.anchor_mem A)

/-- Terminal witness words are in the target language. -/
theorem terminal_mem_target
    (C : TrimmedPresentationCharacteristicSample D)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    D.terminalWitnessWord ρ hwt ∈ G.StringLanguage :=
  C.sample_positive (C.terminal_mem ρ hρ hwt)

/-- Binary witness words are in the target language. -/
theorem binary_mem_target
    (C : TrimmedPresentationCharacteristicSample D)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈ G.StringLanguage :=
  C.sample_positive (C.binary_mem ρ hρ)

/-- Start witness words are in the target language. -/
theorem start_mem_target
    (C : TrimmedPresentationCharacteristicSample D)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    D.startWitnessWord ρ hwt ∈ G.StringLanguage :=
  C.sample_positive (C.start_mem ρ hρ hwt)

/-- The distinguished start word is in the target language. -/
theorem startWord_mem_target
    (C : TrimmedPresentationCharacteristicSample D) :
    D.startWord ∈ G.StringLanguage :=
  C.sample_positive C.startWord_mem

/-- Extend a characteristic sample object to a larger positive finite sample. -/
def extend
    (C : TrimmedPresentationCharacteristicSample D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    TrimmedPresentationCharacteristicSample D where
  sample := K
  sample_positive := hKpos
  anchor_mem := by
    intro A
    exact hCK (C.anchor_mem A)
  terminal_mem := by
    intro ρ hρ hwt
    exact hCK (C.terminal_mem ρ hρ hwt)
  binary_mem := by
    intro ρ hρ
    exact hCK (C.binary_mem ρ hρ)
  start_mem := by
    intro ρ hρ hwt
    exact hCK (C.start_mem ρ hρ hwt)
  startWord_mem := hCK C.startWord_mem

@[simp] theorem extend_sample
    (C : TrimmedPresentationCharacteristicSample D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (C.extend hCK hKpos).sample = K :=
  rfl

/-- Extension agrees with monotonicity of the underlying trimmed sample-data
package. -/
theorem toSampleData_extend
    (C : TrimmedPresentationCharacteristicSample D)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (C.extend hCK hKpos).toSampleData =
      C.toSampleData.mono hCK hKpos := by
  rfl

/-- Convert the characteristic sample object to the trimmed final-data package
after adding the remaining splicing constructor and global assumptions. -/
def toFinalData
    (C : TrimmedPresentationCharacteristicSample D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationFinalData D C.sample where
  sampleData := C.toSampleData
  splicingConstructor := U
  fanout := hfan
  promise := hL

/-- Convert directly to the final reachable-data package. -/
def toFinalReachableData
    (C : TrimmedPresentationCharacteristicSample D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G C.sample obs f :=
  (C.toFinalData U hfan hL).toFinalReachableData

/-- The finite characteristic sample object gives a characteristic sample for
the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationCharacteristicSample D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  (C.toFinalData U hfan hL).characteristic_sample

/-- Exact reconstruction for any positive finite superset of the characteristic
sample object. -/
theorem exact_for_positive_superset
    (C : TrimmedPresentationCharacteristicSample D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  (C.toFinalData U hfan hL).exact_for_positive_superset hCK hKpos

/-- Eventual prefix-exact reconstruction from the characteristic sample object. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationCharacteristicSample D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (C.toFinalData U hfan hL).prefix_exact_eventually

/-- Reachable Gold identification from the characteristic sample object. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationCharacteristicSample D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (C.toFinalData U hfan hL).identifies_from_positive_text

end TrimmedPresentationCharacteristicSample

end CharacteristicSampleObject


section MainTheoremsFromCharacteristicSampleObject

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level identification theorem from a trimmed-presentation
characteristic sample object. -/
theorem trimmed_characteristic_sample_reachable_identification
    (C : TrimmedPresentationCharacteristicSample D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text U hfan hL

/-- Stable top-level prefix-exact theorem from a trimmed-presentation
characteristic sample object. -/
theorem trimmed_characteristic_sample_reachable_prefix_exact
    (C : TrimmedPresentationCharacteristicSample D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually U hfan hL

end MainTheoremsFromCharacteristicSampleObject

end MCFG
