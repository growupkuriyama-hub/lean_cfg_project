/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleComponentPackage

/-!
# CharacteristicSampleComponentEnumeration.lean

Fifty-third clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleComponentPackage.lean` split the future characteristic
sample into four positive finite components:

* anchor witnesses;
* terminal witnesses;
* binary witnesses;
* start-rule witnesses.

This file adds one more construction layer.  Each component may now be produced
from an explicit finite index set by taking a `Finset.image`.

This is still a skeleton: the finite index sets and their coverage proofs are
supplied as data.  The point is to expose the exact shape of the future concrete
enumeration of `CS(G̃₀)`:

```text
finite indices
→ witness word function
→ image finite set
→ component package
→ reachable identification.
```

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section IndexedComponents

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- An indexed finite enumeration of all anchor witness words. -/
structure AnchorWitnessEnumeration
    (D : TrimmedPresentationPreCoreData T f) where
  Index : Type (max u v w)
  indices : Finset Index
  word : Index → Word α
  word_positive :
    ∀ i : Index, i ∈ indices → word i ∈ G.StringLanguage
  covers :
    ∀ A : N, ∃ i : Index, i ∈ indices ∧
      word i = D.anchorWitnessWord A

/-- An indexed finite enumeration of all terminal-rule witness words. -/
structure TerminalWitnessEnumeration
    (D : TrimmedPresentationPreCoreData T f) where
  Index : Type (max u v w)
  indices : Finset Index
  word : Index → Word α
  word_positive :
    ∀ i : Index, i ∈ indices → word i ∈ G.StringLanguage
  covers :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        ∃ i : Index, i ∈ indices ∧
          word i = D.terminalWitnessWord ρ hwt

/-- An indexed finite enumeration of all binary-rule witness words. -/
structure BinaryWitnessEnumeration
    (D : TrimmedPresentationPreCoreData T f) where
  Index : Type (max u v w)
  indices : Finset Index
  word : Index → Word α
  word_positive :
    ∀ i : Index, i ∈ indices → word i ∈ G.StringLanguage
  covers :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        ∃ i : Index, i ∈ indices ∧
          word i = D.binaryWitnessWord ρ

/-- An indexed finite enumeration of all start-rule witness words. -/
structure StartWitnessEnumeration
    (D : TrimmedPresentationPreCoreData T f) where
  Index : Type (max u v w)
  indices : Finset Index
  word : Index → Word α
  word_positive :
    ∀ i : Index, i ∈ indices → word i ∈ G.StringLanguage
  covers :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        ∃ i : Index, i ∈ indices ∧
          word i = D.startWitnessWord ρ hwt

namespace AnchorWitnessEnumeration

variable {D : TrimmedPresentationPreCoreData T f}

/-- The finite set produced by the anchor enumeration. -/
def sample
    (E : AnchorWitnessEnumeration D) : Finset (Word α) :=
  E.indices.image E.word

/-- The produced anchor sample is positive. -/
theorem sample_positive
    (E : AnchorWitnessEnumeration D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage := by
  intro word hword
  rcases Finset.mem_image.mp hword with ⟨i, hi, hEq⟩
  rw [← hEq]
  exact E.word_positive i hi

/-- The produced anchor sample covers every anchor witness word. -/
theorem covers_sample
    (E : AnchorWitnessEnumeration D)
    (A : N) :
    D.anchorWitnessWord A ∈ E.sample := by
  rcases E.covers A with ⟨i, hi, hEq⟩
  exact Finset.mem_image.mpr ⟨i, hi, hEq⟩

/-- Convert an anchor enumeration to an anchor witness component. -/
def toComponent
    (E : AnchorWitnessEnumeration D) :
    AnchorWitnessComponent D where
  sample := E.sample
  covers := E.covers_sample
  positive := E.sample_positive

end AnchorWitnessEnumeration

namespace TerminalWitnessEnumeration

variable {D : TrimmedPresentationPreCoreData T f}

/-- The finite set produced by the terminal enumeration. -/
def sample
    (E : TerminalWitnessEnumeration D) : Finset (Word α) :=
  E.indices.image E.word

/-- The produced terminal sample is positive. -/
theorem sample_positive
    (E : TerminalWitnessEnumeration D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage := by
  intro word hword
  rcases Finset.mem_image.mp hword with ⟨i, hi, hEq⟩
  rw [← hEq]
  exact E.word_positive i hi

/-- The produced terminal sample covers every terminal-rule witness word. -/
theorem covers_sample
    (E : TerminalWitnessEnumeration D)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    D.terminalWitnessWord ρ hwt ∈ E.sample := by
  rcases E.covers ρ hρ hwt with ⟨i, hi, hEq⟩
  exact Finset.mem_image.mpr ⟨i, hi, hEq⟩

/-- Convert a terminal enumeration to a terminal witness component. -/
def toComponent
    (E : TerminalWitnessEnumeration D) :
    TerminalWitnessComponent D where
  sample := E.sample
  covers := E.covers_sample
  positive := E.sample_positive

end TerminalWitnessEnumeration

namespace BinaryWitnessEnumeration

variable {D : TrimmedPresentationPreCoreData T f}

/-- The finite set produced by the binary enumeration. -/
def sample
    (E : BinaryWitnessEnumeration D) : Finset (Word α) :=
  E.indices.image E.word

/-- The produced binary sample is positive. -/
theorem sample_positive
    (E : BinaryWitnessEnumeration D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage := by
  intro word hword
  rcases Finset.mem_image.mp hword with ⟨i, hi, hEq⟩
  rw [← hEq]
  exact E.word_positive i hi

/-- The produced binary sample covers every binary-rule witness word. -/
theorem covers_sample
    (E : BinaryWitnessEnumeration D)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈ E.sample := by
  rcases E.covers ρ hρ with ⟨i, hi, hEq⟩
  exact Finset.mem_image.mpr ⟨i, hi, hEq⟩

/-- Convert a binary enumeration to a binary witness component. -/
def toComponent
    (E : BinaryWitnessEnumeration D) :
    BinaryWitnessComponent D where
  sample := E.sample
  covers := E.covers_sample
  positive := E.sample_positive

end BinaryWitnessEnumeration

namespace StartWitnessEnumeration

variable {D : TrimmedPresentationPreCoreData T f}

/-- The finite set produced by the start-rule enumeration. -/
def sample
    (E : StartWitnessEnumeration D) : Finset (Word α) :=
  E.indices.image E.word

/-- The produced start-rule sample is positive. -/
theorem sample_positive
    (E : StartWitnessEnumeration D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage := by
  intro word hword
  rcases Finset.mem_image.mp hword with ⟨i, hi, hEq⟩
  rw [← hEq]
  exact E.word_positive i hi

/-- The produced start-rule sample covers every start-rule witness word. -/
theorem covers_sample
    (E : StartWitnessEnumeration D)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    D.startWitnessWord ρ hwt ∈ E.sample := by
  rcases E.covers ρ hρ hwt with ⟨i, hi, hEq⟩
  exact Finset.mem_image.mpr ⟨i, hi, hEq⟩

/-- Convert a start-rule enumeration to a start witness component. -/
def toComponent
    (E : StartWitnessEnumeration D) :
    StartWitnessComponent D where
  sample := E.sample
  covers := E.covers_sample
  positive := E.sample_positive

end StartWitnessEnumeration

end IndexedComponents


section EnumerationPackage

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Componentwise indexed enumeration package for the future `CS(G̃₀)`
construction. -/
structure TrimmedPresentationComponentEnumeration
    (D : TrimmedPresentationPreCoreData T f) where
  anchor : AnchorWitnessEnumeration D
  terminal : TerminalWitnessEnumeration D
  binary : BinaryWitnessEnumeration D
  start : StartWitnessEnumeration D
  startWord_positive :
    D.startWord ∈ G.StringLanguage

namespace TrimmedPresentationComponentEnumeration

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert indexed enumerations to componentwise finite characteristic-sample
data. -/
def toComponentPackage
    (E : TrimmedPresentationComponentEnumeration D) :
    TrimmedPresentationComponentPackage D where
  anchor := E.anchor.toComponent
  terminal := E.terminal.toComponent
  binary := E.binary.toComponent
  start := E.start.toComponent
  startWord_positive := E.startWord_positive

/-- The finite sample produced by the indexed enumeration package. -/
def sample
    (E : TrimmedPresentationComponentEnumeration D) :
    Finset (Word α) :=
  E.toComponentPackage.sample

/-- The produced sample is positive. -/
theorem sample_positive
    (E : TrimmedPresentationComponentEnumeration D) :
    (E.sample : Set (Word α)) ⊆ G.StringLanguage :=
  E.toComponentPackage.sample_positive

/-- The produced sample contains all required witness words. -/
theorem contains_witnesses
    (E : TrimmedPresentationComponentEnumeration D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (E.sample : Set (Word α)) :=
  E.toComponentPackage.contains_witnesses

/-- Convert to the abstract finite-sample builder. -/
def toFiniteSampleBuilder
    (E : TrimmedPresentationComponentEnumeration D) :
    TrimmedPresentationFiniteSampleBuilder D :=
  E.toComponentPackage.toFiniteSampleBuilder

/-- Convert to a witness-sample package. -/
def toWitnessSample
    (E : TrimmedPresentationComponentEnumeration D) :
    TrimmedPresentationWitnessSample D E.sample :=
  E.toComponentPackage.toWitnessSample

/-- Convert to a characteristic-sample object. -/
def toCharacteristicSample
    (E : TrimmedPresentationComponentEnumeration D) :
    TrimmedPresentationCharacteristicSample D :=
  E.toComponentPackage.toCharacteristicSample

/-- Convert to final reachable data after adding the remaining splicing
constructor and global assumptions. -/
def toFinalReachableData
    (E : TrimmedPresentationComponentEnumeration D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G E.sample obs f :=
  E.toComponentPackage.toFinalReachableData U hfan hL

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (E : TrimmedPresentationComponentEnumeration D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      E.sample
      G.StringLanguage :=
  E.toComponentPackage.characteristic_sample U hfan hL

/-- Eventual prefix-exact reconstruction from indexed component enumerations. -/
theorem prefix_exact_eventually
    (E : TrimmedPresentationComponentEnumeration D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.toComponentPackage.prefix_exact_eventually U hfan hL

/-- Reachable Gold identification from indexed component enumerations. -/
theorem identifies_from_positive_text
    (E : TrimmedPresentationComponentEnumeration D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.toComponentPackage.identifies_from_positive_text U hfan hL

end TrimmedPresentationComponentEnumeration

end EnumerationPackage


section MainTheoremsFromComponentEnumeration

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from indexed component
enumerations. -/
theorem trimmed_component_enumeration_reachable_identification
    (E : TrimmedPresentationComponentEnumeration D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  E.identifies_from_positive_text U hfan hL

/-- Stable top-level prefix-exact theorem from indexed component enumerations. -/
theorem trimmed_component_enumeration_reachable_prefix_exact
    (E : TrimmedPresentationComponentEnumeration D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  E.prefix_exact_eventually U hfan hL

end MainTheoremsFromComponentEnumeration

end MCFG
