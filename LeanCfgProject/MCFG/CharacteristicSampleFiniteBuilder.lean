/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleWitnessSetMonotone

/-!
# CharacteristicSampleFiniteBuilder.lean

Forty-ninth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleWitnessSet.lean` reduced the future construction of
`CS(G̃₀)` to a clean set-inclusion statement:

```lean
TrimmedPresentationWitnessWordSet D ⊆ (S : Set (Word α))
```

`CharacteristicSampleWitnessSetMonotone.lean` then proved the monotonicity and
identification consequences for such finite samples.

This file introduces a small finite-builder interface:

```lean
TrimmedPresentationFiniteSampleBuilder D
```

It packages just:

* a finite set of words;
* proof that it contains the witness-word set.

The positivity proof is supplied separately.  This separation matches the
future construction plan:

1. explicitly enumerate a finite candidate `CS(G̃₀)`;
2. prove it contains the required witness words;
3. prove it is positive, using presentation soundness / grammar membership;
4. invoke the already verified reachable-identification route.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section FiniteSampleBuilder

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- A finite builder for the presentation-relative characteristic sample.

This record deliberately contains only finite coverage of the required witness
set.  Positivity is supplied separately, because in a future concrete
construction it should follow from presentation/grammar soundness. -/
structure TrimmedPresentationFiniteSampleBuilder
    (D : TrimmedPresentationPreCoreData T f) where
  sample : Finset (Word α)
  contains_witnesses :
    TrimmedPresentationWitnessWordSet D ⊆ (sample : Set (Word α))

namespace TrimmedPresentationFiniteSampleBuilder

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert a finite builder to a witness-sample package after adding positivity. -/
def toWitnessSample
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (hpos : (B.sample : Set (Word α)) ⊆ G.StringLanguage) :
    TrimmedPresentationWitnessSample D B.sample where
  sample_positive := hpos
  contains_witnesses := B.contains_witnesses

/-- Convert a finite builder to trimmed sample data after adding positivity. -/
def toSampleData
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (hpos : (B.sample : Set (Word α)) ⊆ G.StringLanguage) :
    TrimmedPresentationSampleData D B.sample :=
  (B.toWitnessSample hpos).toSampleData

/-- Convert a finite builder to a characteristic-sample object after adding
positivity. -/
def toCharacteristicSample
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (hpos : (B.sample : Set (Word α)) ⊆ G.StringLanguage) :
    TrimmedPresentationCharacteristicSample D :=
  (B.toWitnessSample hpos).toCharacteristicSample

@[simp] theorem toCharacteristicSample_sample
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (hpos : (B.sample : Set (Word α)) ⊆ G.StringLanguage) :
    (B.toCharacteristicSample hpos).sample = B.sample :=
  rfl

/-- Convert a finite builder to trimmed final data after adding positivity,
a splicing constructor, and the global assumptions. -/
def toFinalData
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (hpos : (B.sample : Set (Word α)) ⊆ G.StringLanguage)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationFinalData D B.sample :=
  (B.toWitnessSample hpos).toFinalData U hfan hL

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (hpos : (B.sample : Set (Word α)) ⊆ G.StringLanguage)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G B.sample obs f :=
  (B.toFinalData hpos U hfan hL).toFinalReachableData

/-- The builder sample contains all required witness words. -/
theorem witness_set_subset_sample
    (B : TrimmedPresentationFiniteSampleBuilder D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (B.sample : Set (Word α)) :=
  B.contains_witnesses

/-- Anchor witness words are contained in the builder sample. -/
theorem anchor_mem
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (A : N) :
    D.anchorWitnessWord A ∈ B.sample :=
  B.contains_witnesses
    (TrimmedPresentationWitnessWordSet.anchor_mem (D := D) A)

/-- Terminal witness words are contained in the builder sample. -/
theorem terminal_mem
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    D.terminalWitnessWord ρ hwt ∈ B.sample :=
  B.contains_witnesses
    (TrimmedPresentationWitnessWordSet.terminal_mem
      (D := D) ρ hρ hwt)

/-- Binary witness words are contained in the builder sample. -/
theorem binary_mem
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈ B.sample :=
  B.contains_witnesses
    (TrimmedPresentationWitnessWordSet.binary_mem
      (D := D) ρ hρ)

/-- Start witness words are contained in the builder sample. -/
theorem start_mem
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    D.startWitnessWord ρ hwt ∈ B.sample :=
  B.contains_witnesses
    (TrimmedPresentationWitnessWordSet.start_mem
      (D := D) ρ hρ hwt)

/-- The distinguished start word is contained in the builder sample. -/
theorem startWord_mem
    (B : TrimmedPresentationFiniteSampleBuilder D) :
    D.startWord ∈ B.sample :=
  B.contains_witnesses
    (TrimmedPresentationWitnessWordSet.startWord_mem (D := D))

/-- Extend a builder to a larger finite set. -/
def extend
    (B : TrimmedPresentationFiniteSampleBuilder D)
    {K : Finset (Word α)}
    (hBK : (B.sample : Set (Word α)) ⊆ (K : Set (Word α))) :
    TrimmedPresentationFiniteSampleBuilder D where
  sample := K
  contains_witnesses := by
    intro word hword
    exact hBK (B.contains_witnesses hword)

@[simp] theorem extend_sample
    (B : TrimmedPresentationFiniteSampleBuilder D)
    {K : Finset (Word α)}
    (hBK : (B.sample : Set (Word α)) ⊆ (K : Set (Word α))) :
    (B.extend hBK).sample = K :=
  rfl

/-- Extending a builder and then adding positivity agrees with monotonicity of
the witness-sample package. -/
theorem toWitnessSample_extend
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (hpos : (B.sample : Set (Word α)) ⊆ G.StringLanguage)
    {K : Finset (Word α)}
    (hBK : (B.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (B.extend hBK).toWitnessSample hKpos =
      (B.toWitnessSample hpos).mono hBK hKpos := by
  rfl

/-- Exact reconstruction for every positive finite superset of the builder
sample. -/
theorem exact_for_positive_superset
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (hpos : (B.sample : Set (Word α)) ⊆ G.StringLanguage)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hBK : (B.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  (B.toWitnessSample hpos).exact_after_mono
    U hfan hL hBK hKpos

/-- Eventual prefix-exact reconstruction from a finite builder. -/
theorem prefix_exact_eventually
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (hpos : (B.sample : Set (Word α)) ⊆ G.StringLanguage)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (B.toWitnessSample hpos).prefix_exact_via_mono
    U hfan hL

/-- Reachable Gold identification from a finite builder. -/
theorem identifies_from_positive_text
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (hpos : (B.sample : Set (Word α)) ⊆ G.StringLanguage)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (B.toWitnessSample hpos).identifies_via_mono
    U hfan hL

end TrimmedPresentationFiniteSampleBuilder

end FiniteSampleBuilder


section MainTheoremsFromFiniteSampleBuilder

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from the finite builder
interface. -/
theorem trimmed_finite_builder_reachable_identification
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (hpos : (B.sample : Set (Word α)) ⊆ G.StringLanguage)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  B.identifies_from_positive_text hpos U hfan hL

/-- Stable top-level prefix-exact theorem from the finite builder interface. -/
theorem trimmed_finite_builder_reachable_prefix_exact
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (hpos : (B.sample : Set (Word α)) ⊆ G.StringLanguage)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  B.prefix_exact_eventually hpos U hfan hL

end MainTheoremsFromFiniteSampleBuilder

end MCFG
