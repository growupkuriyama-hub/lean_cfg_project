/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleBuilderSkeleton

/-!
# BlueprintFiniteSample.lean

Twenty-fifth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleBuilderSkeleton.lean` introduced the flat record

```lean
ReachableCharacteristicBlueprint
```

as the target for the future construction from `CS(G̃₀)`.

This file factors that blueprint into two parts:

* `ReachableBlueprintCore`: the sample-independent mathematical choices
  such as anchors, exposing contexts, output-type equalities, filling
  identities, and the start anchor;
* `ReachableBlueprintFiniteSample`: the finite-sample membership facts saying
  that the words required by the core are actually present in a finite sample
  `S`, and that `S` is positive for the target language.

Together they reconstruct `ReachableCharacteristicBlueprint`, and hence all
reachable exact-reconstruction and Gold-identification theorems already proved.

This is a small interface layer, but it is useful for the next construction
phase: `CS(G̃₀)` should eventually be represented by building a core and then
showing that its required witness words are included in the finite sample.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section CoreAndFiniteSample

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Sample-independent core data for constructing a reachable characteristic
blueprint.

This record contains all choices and semantic equalities, but no finite-sample
membership assertions. -/
structure ReachableBlueprintCore
    (G : WorkingMCFG N α)
    (obs : α → M) (f : Nat) where
  anchor : ∀ A : N, Tuple α (G.arity A)
  expose : ∀ A : N, NamedSentenceContext α (G.arity A)

  terminal_type_eq :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        tupleType obs (anchor ρ.lhs) =
          tupleType obs (castTuple hwt.symm ρ.outputTuple)

  binary_type_eq :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        tupleType obs (anchor ρ.lhs) =
          tupleType obs (ρ.apply (anchor ρ.left) (anchor ρ.right))

  binary_leftIdentity :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        LeftFillingIdentity namedFill (expose ρ.lhs) ρ.body (anchor ρ.right)

  binary_rightIdentity :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        ∀ u : Tuple α (G.arity ρ.left),
          RightFillingIdentity namedFill (expose ρ.lhs) ρ.body u

  start_type_eq :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        tupleType obs (anchor G.start) =
          tupleType obs (castTuple hwt (anchor ρ.child))

  startWord : Word α
  start_arity : 1 = G.arity G.start
  start_anchor_eq :
    anchor G.start =
      castTuple start_arity (singletonTuple startWord)

/-- Finite-sample membership data for a fixed blueprint core.

This record says that the words required by the core are present in the finite
sample `S`, and that `S` itself is a positive sample for the target language. -/
structure ReachableBlueprintFiniteSample
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (C : ReachableBlueprintCore G obs f) where
  sample_positive : (S : Set (Word α)) ⊆ G.StringLanguage

  anchor_mem :
    ∀ A : N,
      namedFill (G.arity A) (C.expose A) (C.anchor A) ∈ S

  terminal_mem :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        namedFill (G.arity ρ.lhs) (C.expose ρ.lhs)
          (castTuple hwt.symm ρ.outputTuple) ∈ S

  binary_mem :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        namedFill (G.arity ρ.lhs) (C.expose ρ.lhs)
          (ρ.apply (C.anchor ρ.left) (C.anchor ρ.right)) ∈ S

  start_mem :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        namedFill (G.arity G.start) (C.expose G.start)
          (castTuple hwt (C.anchor ρ.child)) ∈ S

  startWord_mem : C.startWord ∈ S

namespace ReachableBlueprintFiniteSample

variable {G : WorkingMCFG N α}
variable {S : Finset (Word α)} {obs : α → M} {f : Nat}
variable {C : ReachableBlueprintCore G obs f}

/-- Combine a sample-independent core and finite membership facts into the flat
reachable characteristic blueprint used by the main theorem. -/
def toBlueprint
    (H : ReachableBlueprintFiniteSample G S obs f C) :
    ReachableCharacteristicBlueprint G S obs f where
  sample_positive := H.sample_positive
  anchor := C.anchor
  expose := C.expose
  anchor_mem := H.anchor_mem
  terminal_mem := H.terminal_mem
  terminal_type_eq := C.terminal_type_eq
  binary_mem := H.binary_mem
  binary_type_eq := C.binary_type_eq
  binary_leftIdentity := C.binary_leftIdentity
  binary_rightIdentity := C.binary_rightIdentity
  start_mem := H.start_mem
  start_type_eq := C.start_type_eq
  startWord := C.startWord
  startWord_mem := H.startWord_mem
  start_arity := C.start_arity
  start_anchor_eq := C.start_anchor_eq

/-- Convert finite-sample facts into a reachable characteristic package. -/
def toPackage
    (H : ReachableBlueprintFiniteSample G S obs f C) :
    ReachableCharacteristicPackage G S obs f :=
  H.toBlueprint.toPackage

/-- Convert finite-sample facts into full reachable main data after adding the
global target assumptions. -/
def toMainData
    (H : ReachableBlueprintFiniteSample G S obs f C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ReachableMainData G S obs f :=
  H.toBlueprint.toMainData hfan hL

/-- Finite-sample data is monotone in the sample: if all words of `S` occur in
`K`, then the same core is valid over `K`. -/
def mono
    {K : Finset (Word α)}
    (H : ReachableBlueprintFiniteSample G S obs f C)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableBlueprintFiniteSample G K obs f C where
  sample_positive := hKpos
  anchor_mem := by
    intro A
    exact hSK (H.anchor_mem A)
  terminal_mem := by
    intro ρ hρ hwt
    exact hSK (H.terminal_mem ρ hρ hwt)
  binary_mem := by
    intro ρ hρ
    exact hSK (H.binary_mem ρ hρ)
  start_mem := by
    intro ρ hρ hwt
    exact hSK (H.start_mem ρ hρ hwt)
  startWord_mem := hSK H.startWord_mem

/-- The reachable learner has the target language at any positive finite
superset of the blueprint finite sample. -/
theorem exact_for_positive_superset
    {K : Finset (Word α)}
    (H : ReachableBlueprintFiniteSample G S obs f C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  H.toBlueprint.exact_for_positive_superset hfan hL hSK hKpos

/-- At any text prefix where `S` has appeared, reachable exact reconstruction
holds for that prefix. -/
theorem exact_at_seen_prefix
    (H : ReachableBlueprintFiniteSample G S obs f C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (T : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (S : Set (Word α)) ⊆
      (T.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (T.prefixSample n) obs f =
      G.StringLanguage :=
  H.toBlueprint.exact_at_seen_prefix hfan hL T hseen

/-- The finite-sample data gives a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (H : ReachableBlueprintFiniteSample G S obs f C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      S
      G.StringLanguage :=
  H.toBlueprint.characteristic_sample hfan hL

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (H : ReachableBlueprintFiniteSample G S obs f C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  H.toBlueprint.prefix_exact_eventually hfan hL

/-- Gold identification for the reachable learner from finite-sample blueprint
membership data. -/
theorem identifies_from_positive_text
    (H : ReachableBlueprintFiniteSample G S obs f C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  H.toBlueprint.identifies_from_positive_text hfan hL

end ReachableBlueprintFiniteSample

end CoreAndFiniteSample


section MainTheoremsFromFiniteSampleBlueprint

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Main reachable identification theorem stated from a blueprint core plus
finite-sample membership facts. -/
theorem main_reachable_identification_from_finite_sample_blueprint
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (C : ReachableBlueprintCore G obs f)
    (H : ReachableBlueprintFiniteSample G S obs f C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  H.identifies_from_positive_text hfan hL

/-- Main reachable prefix-exact theorem stated from a blueprint core plus
finite-sample membership facts. -/
theorem main_reachable_prefix_exact_from_finite_sample_blueprint
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (C : ReachableBlueprintCore G obs f)
    (H : ReachableBlueprintFiniteSample G S obs f C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  H.prefix_exact_eventually hfan hL

end MainTheoremsFromFiniteSampleBlueprint

end MCFG
