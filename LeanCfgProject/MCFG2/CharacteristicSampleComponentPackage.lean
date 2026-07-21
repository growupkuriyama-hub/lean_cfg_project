/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleFiniteUnionPackage

/-!
# CharacteristicSampleComponentPackage.lean

Fifty-second clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleFiniteUnionBuilder.lean` represented the future
presentation-relative characteristic sample as a union of four finite parts:

* anchor witnesses;
* terminal witnesses;
* binary witnesses;
* start-rule witnesses;

plus the distinguished start word.

`CharacteristicSampleFiniteUnionPackage.lean` then bundled the finite union
builder with positivity of the parts.

This file splits those finite parts into independent component packages.  This
is useful for the next concrete-enumeration stage: one can build and prove
positivity of the anchor component, terminal component, binary component, and
start component separately, and then combine them into the already verified
finite-union route.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ComponentPackages

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Finite component containing all anchor witness words. -/
structure AnchorWitnessComponent
    (D : TrimmedPresentationPreCoreData T f) where
  sample : Finset (Word α)
  covers :
    ∀ A : N,
      D.anchorWitnessWord A ∈ sample
  positive :
    (sample : Set (Word α)) ⊆ G.StringLanguage

/-- Finite component containing all terminal-rule witness words. -/
structure TerminalWitnessComponent
    (D : TrimmedPresentationPreCoreData T f) where
  sample : Finset (Word α)
  covers :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        D.terminalWitnessWord ρ hwt ∈ sample
  positive :
    (sample : Set (Word α)) ⊆ G.StringLanguage

/-- Finite component containing all binary-rule witness words. -/
structure BinaryWitnessComponent
    (D : TrimmedPresentationPreCoreData T f) where
  sample : Finset (Word α)
  covers :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        D.binaryWitnessWord ρ ∈ sample
  positive :
    (sample : Set (Word α)) ⊆ G.StringLanguage

/-- Finite component containing all start-rule witness words. -/
structure StartWitnessComponent
    (D : TrimmedPresentationPreCoreData T f) where
  sample : Finset (Word α)
  covers :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        D.startWitnessWord ρ hwt ∈ sample
  positive :
    (sample : Set (Word α)) ⊆ G.StringLanguage

namespace AnchorWitnessComponent

variable {D : TrimmedPresentationPreCoreData T f}

/-- Anchor component membership in the target language. -/
theorem mem_target
    (C : AnchorWitnessComponent D)
    {word : Word α}
    (hword : word ∈ C.sample) :
    word ∈ G.StringLanguage :=
  C.positive hword

/-- Every anchor witness word is target-positive. -/
theorem witness_mem_target
    (C : AnchorWitnessComponent D)
    (A : N) :
    D.anchorWitnessWord A ∈ G.StringLanguage :=
  C.positive (C.covers A)

end AnchorWitnessComponent

namespace TerminalWitnessComponent

variable {D : TrimmedPresentationPreCoreData T f}

/-- Terminal component membership in the target language. -/
theorem mem_target
    (C : TerminalWitnessComponent D)
    {word : Word α}
    (hword : word ∈ C.sample) :
    word ∈ G.StringLanguage :=
  C.positive hword

/-- Every terminal witness word is target-positive. -/
theorem witness_mem_target
    (C : TerminalWitnessComponent D)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    D.terminalWitnessWord ρ hwt ∈ G.StringLanguage :=
  C.positive (C.covers ρ hρ hwt)

end TerminalWitnessComponent

namespace BinaryWitnessComponent

variable {D : TrimmedPresentationPreCoreData T f}

/-- Binary component membership in the target language. -/
theorem mem_target
    (C : BinaryWitnessComponent D)
    {word : Word α}
    (hword : word ∈ C.sample) :
    word ∈ G.StringLanguage :=
  C.positive hword

/-- Every binary witness word is target-positive. -/
theorem witness_mem_target
    (C : BinaryWitnessComponent D)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈ G.StringLanguage :=
  C.positive (C.covers ρ hρ)

end BinaryWitnessComponent

namespace StartWitnessComponent

variable {D : TrimmedPresentationPreCoreData T f}

/-- Start component membership in the target language. -/
theorem mem_target
    (C : StartWitnessComponent D)
    {word : Word α}
    (hword : word ∈ C.sample) :
    word ∈ G.StringLanguage :=
  C.positive hword

/-- Every start-rule witness word is target-positive. -/
theorem witness_mem_target
    (C : StartWitnessComponent D)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    D.startWitnessWord ρ hwt ∈ G.StringLanguage :=
  C.positive (C.covers ρ hρ hwt)

end StartWitnessComponent

end ComponentPackages


section ComponentPackageAssembly

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Componentwise package for constructing the presentation-relative
characteristic sample.

The distinguished start word is not a finite component by itself; it is added
as a singleton by `TrimmedPresentationFiniteUnionBuilder.sample`, so we only
store its positivity here. -/
structure TrimmedPresentationComponentPackage
    (D : TrimmedPresentationPreCoreData T f) where
  anchor : AnchorWitnessComponent D
  terminal : TerminalWitnessComponent D
  binary : BinaryWitnessComponent D
  start : StartWitnessComponent D
  startWord_positive :
    D.startWord ∈ G.StringLanguage

namespace TrimmedPresentationComponentPackage

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert componentwise data to the finite-union builder. -/
def toFiniteUnionBuilder
    (P : TrimmedPresentationComponentPackage D) :
    TrimmedPresentationFiniteUnionBuilder D where
  anchorSample := P.anchor.sample
  terminalSample := P.terminal.sample
  binarySample := P.binary.sample
  startSample := P.start.sample
  anchor_mem := P.anchor.covers
  terminal_mem := P.terminal.covers
  binary_mem := P.binary.covers
  start_mem := P.start.covers

/-- Positivity of the finite-union builder obtained from componentwise
positivity. -/
def toFiniteUnionPositive
    (P : TrimmedPresentationComponentPackage D) :
    TrimmedPresentationFiniteUnionBuilder.Positive P.toFiniteUnionBuilder where
  anchor_positive := P.anchor.positive
  terminal_positive := P.terminal.positive
  binary_positive := P.binary.positive
  start_positive := P.start.positive
  startWord_positive := P.startWord_positive

/-- Convert componentwise data to the positive finite-union package. -/
def toPositiveFiniteUnionBuilder
    (P : TrimmedPresentationComponentPackage D) :
    TrimmedPresentationPositiveFiniteUnionBuilder D where
  builder := P.toFiniteUnionBuilder
  positive := P.toFiniteUnionPositive

/-- The finite sample produced by the component package. -/
def sample
    (P : TrimmedPresentationComponentPackage D) :
    Finset (Word α) :=
  P.toPositiveFiniteUnionBuilder.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (P : TrimmedPresentationComponentPackage D) :
    (P.sample : Set (Word α)) ⊆ G.StringLanguage :=
  P.toPositiveFiniteUnionBuilder.sample_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (P : TrimmedPresentationComponentPackage D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (P.sample : Set (Word α)) :=
  P.toPositiveFiniteUnionBuilder.contains_witnesses

/-- Convert to the abstract finite-sample builder. -/
def toFiniteSampleBuilder
    (P : TrimmedPresentationComponentPackage D) :
    TrimmedPresentationFiniteSampleBuilder D :=
  P.toPositiveFiniteUnionBuilder.toFiniteSampleBuilder

/-- Convert to a witness-sample package. -/
def toWitnessSample
    (P : TrimmedPresentationComponentPackage D) :
    TrimmedPresentationWitnessSample D P.sample :=
  P.toPositiveFiniteUnionBuilder.toWitnessSample

/-- Convert to trimmed sample data. -/
def toSampleData
    (P : TrimmedPresentationComponentPackage D) :
    TrimmedPresentationSampleData D P.sample :=
  P.toPositiveFiniteUnionBuilder.toSampleData

/-- Convert to a characteristic-sample object. -/
def toCharacteristicSample
    (P : TrimmedPresentationComponentPackage D) :
    TrimmedPresentationCharacteristicSample D :=
  P.toPositiveFiniteUnionBuilder.toCharacteristicSample

/-- Convert to final reachable data after adding the remaining splicing
constructor and global assumptions. -/
def toFinalReachableData
    (P : TrimmedPresentationComponentPackage D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G P.sample obs f :=
  P.toPositiveFiniteUnionBuilder.toFinalReachableData U hfan hL

/-- Eventual prefix-exact reconstruction from componentwise characteristic
sample data. -/
theorem prefix_exact_eventually
    (P : TrimmedPresentationComponentPackage D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.toPositiveFiniteUnionBuilder.prefix_exact_eventually U hfan hL

/-- Reachable Gold identification from componentwise characteristic sample
data. -/
theorem identifies_from_positive_text
    (P : TrimmedPresentationComponentPackage D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  P.toPositiveFiniteUnionBuilder.identifies_from_positive_text U hfan hL

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (P : TrimmedPresentationComponentPackage D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      P.sample
      G.StringLanguage :=
  P.toPositiveFiniteUnionBuilder.characteristic_sample U hfan hL

end TrimmedPresentationComponentPackage

end ComponentPackageAssembly


section MainTheoremsFromComponentPackage

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from componentwise
characteristic sample data. -/
theorem trimmed_component_package_reachable_identification
    (P : TrimmedPresentationComponentPackage D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  P.identifies_from_positive_text U hfan hL

/-- Stable top-level prefix-exact theorem from componentwise characteristic
sample data. -/
theorem trimmed_component_package_reachable_prefix_exact
    (P : TrimmedPresentationComponentPackage D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually U hfan hL

end MainTheoremsFromComponentPackage

end MCFG
