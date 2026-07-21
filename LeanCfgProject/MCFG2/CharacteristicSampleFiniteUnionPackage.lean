/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleFiniteUnionBuilder

/-!
# CharacteristicSampleFiniteUnionPackage.lean

Fifty-first clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleFiniteUnionBuilder.lean` split the future characteristic
sample into finite parts:

* `anchorSample`
* `terminalSample`
* `binarySample`
* `startSample`
* `{startWord}`

and separately introduced positivity for those parts.

This file packages the union builder and its positivity proof together as a
single object:

```lean
TrimmedPresentationPositiveFiniteUnionBuilder D
```

This is a convenience layer for future concrete enumeration files.  Once an
enumeration supplies the four finite parts and positivity for each part, this
package exposes the already verified route to:

* a finite sample builder;
* a witness sample;
* a characteristic-sample object;
* final reachable data;
* reachable Gold identification;
* eventual prefix-exact reconstruction.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PositiveFiniteUnionPackage

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- A finite union builder together with positivity of all its finite parts.

This is the convenient package expected from a future concrete enumeration of
the presentation-relative characteristic sample. -/
structure TrimmedPresentationPositiveFiniteUnionBuilder
    (D : TrimmedPresentationPreCoreData T f) where
  builder : TrimmedPresentationFiniteUnionBuilder D
  positive : TrimmedPresentationFiniteUnionBuilder.Positive builder

namespace TrimmedPresentationPositiveFiniteUnionBuilder

variable {D : TrimmedPresentationPreCoreData T f}

/-- The finite characteristic sample produced by the positive finite-union
builder. -/
def sample
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D) :
    Finset (Word α) :=
  C.builder.sample

/-- The finite sample is positive for the target grammar language. -/
theorem sample_positive
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D) :
    (C.sample : Set (Word α)) ⊆ G.StringLanguage :=
  C.positive.sample_positive

/-- The sample contains the full trimmed-presentation witness-word set. -/
theorem contains_witnesses
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (C.sample : Set (Word α)) :=
  C.builder.contains_witnesses

/-- Convert to the abstract finite-sample builder. -/
def toFiniteSampleBuilder
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D) :
    TrimmedPresentationFiniteSampleBuilder D :=
  C.builder.toFiniteSampleBuilder

@[simp] theorem toFiniteSampleBuilder_sample
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D) :
    C.toFiniteSampleBuilder.sample = C.sample :=
  rfl

/-- Convert to the witness-sample package. -/
def toWitnessSample
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D) :
    TrimmedPresentationWitnessSample D C.sample :=
  C.positive.toWitnessSample

/-- Convert to trimmed sample data. -/
def toSampleData
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D) :
    TrimmedPresentationSampleData D C.sample :=
  C.positive.toSampleData

/-- Convert to a characteristic-sample object. -/
def toCharacteristicSample
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D) :
    TrimmedPresentationCharacteristicSample D :=
  C.positive.toCharacteristicSample

@[simp] theorem toCharacteristicSample_sample
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D) :
    C.toCharacteristicSample.sample = C.sample :=
  rfl

/-- Convert to trimmed final data after adding the remaining splicing
constructor and global assumptions. -/
def toFinalData
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationFinalData D C.sample :=
  C.positive.toFinalData U hfan hL

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G C.sample obs f :=
  (C.toFinalData U hfan hL).toFinalReachableData

/-- Anchor witness words are in the produced sample. -/
theorem anchor_mem
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D)
    (A : N) :
    D.anchorWitnessWord A ∈ C.sample :=
  C.builder.anchor_mem_sample A

/-- Terminal witness words are in the produced sample. -/
theorem terminal_mem
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    D.terminalWitnessWord ρ hwt ∈ C.sample :=
  C.builder.terminal_mem_sample ρ hρ hwt

/-- Binary witness words are in the produced sample. -/
theorem binary_mem
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈ C.sample :=
  C.builder.binary_mem_sample ρ hρ

/-- Start-rule witness words are in the produced sample. -/
theorem start_mem
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    D.startWitnessWord ρ hwt ∈ C.sample :=
  C.builder.start_mem_sample ρ hρ hwt

/-- The distinguished start word is in the produced sample. -/
theorem startWord_mem
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D) :
    D.startWord ∈ C.sample :=
  C.builder.startWord_mem_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hCK : (C.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  C.toFiniteSampleBuilder.exact_for_positive_superset
    C.sample_positive U hfan hL hCK hKpos

/-- Exact reconstruction at a positive-text prefix containing the produced
sample. -/
theorem exact_at_seen_prefix
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (C.sample : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  C.toWitnessSample.exact_at_prefix_via_mono
    U hfan hL Ttxt hseen

/-- Eventual prefix-exact reconstruction from a positive finite-union builder. -/
theorem prefix_exact_eventually
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.positive.prefix_exact_eventually U hfan hL

/-- Reachable Gold identification from a positive finite-union builder. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.positive.identifies_from_positive_text U hfan hL

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      C.sample
      G.StringLanguage :=
  C.toFinalData U hfan hL |>.characteristic_sample

end TrimmedPresentationPositiveFiniteUnionBuilder

end PositiveFiniteUnionPackage


section MainTheoremsFromPositiveFiniteUnionPackage

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from the positive
finite-union package. -/
theorem trimmed_positive_finite_union_reachable_identification
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.identifies_from_positive_text U hfan hL

/-- Stable top-level prefix-exact theorem from the positive finite-union
package. -/
theorem trimmed_positive_finite_union_reachable_prefix_exact
    (C : TrimmedPresentationPositiveFiniteUnionBuilder D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.prefix_exact_eventually U hfan hL

end MainTheoremsFromPositiveFiniteUnionPackage

end MCFG
