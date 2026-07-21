/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.SplicingCharacteristicPackage

/-!
# SplicingBlueprint.lean

Thirty-third clean Lean experiment for the fixed-observation MCFG project.

`SplicingCharacteristicPackage.lean` introduced the current finite construction
target

```lean
ReachableSplicingPackage
```

which separates:

* `ReachableBlueprintPreCore`;
* `ReachablePreCoreFiniteSample`;
* `NamedContextSplicingConstructor`.

For actual construction from `CS(G̃₀)`, it is often more convenient to fill one
flat record.  This file introduces such a record:

```lean
ReachableSplicingBlueprint
```

It contains all pre-core fields, all finite-sample membership fields, and the
universal named-context splicing constructor.  From it we build the package and
therefore recover all reachable exact-reconstruction and Gold-identification
theorems.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section FlatSplicingBlueprint

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- A flat construction target for the splicing-based reachable theorem.

This is now the most direct target for a future construction from the actual
characteristic sample `CS(G̃₀)`: it lists anchors, exposing contexts, type
equalities, finite sample membership facts, the start anchor, and the universal
named-context splicing constructor in one record. -/
structure ReachableSplicingBlueprint
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat) where
  sample_positive : (S : Set (Word α)) ⊆ G.StringLanguage

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

  anchor_mem :
    ∀ A : N,
      namedFill (G.arity A) (expose A) (anchor A) ∈ S

  terminal_mem :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        namedFill (G.arity ρ.lhs) (expose ρ.lhs)
          (castTuple hwt.symm ρ.outputTuple) ∈ S

  binary_mem :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        namedFill (G.arity ρ.lhs) (expose ρ.lhs)
          (ρ.apply (anchor ρ.left) (anchor ρ.right)) ∈ S

  start_mem :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        namedFill (G.arity G.start) (expose G.start)
          (castTuple hwt (anchor ρ.child)) ∈ S

  startWord_mem : startWord ∈ S

  splicingConstructor : NamedContextSplicingConstructor α

namespace ReachableSplicingBlueprint

variable {G : WorkingMCFG N α}
variable {S : Finset (Word α)} {obs : α → M} {f : Nat}

/-- Extract the sample-independent pre-core from the flat blueprint. -/
def toPreCore
    (B : ReachableSplicingBlueprint G S obs f) :
    ReachableBlueprintPreCore G obs f where
  anchor := B.anchor
  expose := B.expose
  terminal_type_eq := B.terminal_type_eq
  binary_type_eq := B.binary_type_eq
  start_type_eq := B.start_type_eq
  startWord := B.startWord
  start_arity := B.start_arity
  start_anchor_eq := B.start_anchor_eq

/-- Extract finite-sample membership data from the flat blueprint. -/
def toFiniteSample
    (B : ReachableSplicingBlueprint G S obs f) :
    ReachablePreCoreFiniteSample G S obs f B.toPreCore where
  sample_positive := B.sample_positive
  anchor_mem := by
    intro A
    exact B.anchor_mem A
  terminal_mem := by
    intro ρ hρ hwt
    exact B.terminal_mem ρ hρ hwt
  binary_mem := by
    intro ρ hρ
    exact B.binary_mem ρ hρ
  start_mem := by
    intro ρ hρ hwt
    exact B.start_mem ρ hρ hwt
  startWord_mem := B.startWord_mem

/-- Convert the flat blueprint into the finite splicing package. -/
def toPackage
    (B : ReachableSplicingBlueprint G S obs f) :
    ReachableSplicingPackage G S obs f where
  preCore := B.toPreCore
  finiteSample := B.toFiniteSample
  splicingConstructor := B.splicingConstructor

/-- Convert the flat blueprint into the full main-data package after adding the
global target assumptions. -/
def toMainData
    (B : ReachableSplicingBlueprint G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ReachableSplicingMainData G S obs f :=
  B.toPackage.toMainData hfan hL

/-- The flat blueprint is monotone in the finite sample. -/
def mono
    {K : Finset (Word α)}
    (B : ReachableSplicingBlueprint G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSplicingBlueprint G K obs f where
  sample_positive := hKpos
  anchor := B.anchor
  expose := B.expose
  terminal_type_eq := B.terminal_type_eq
  binary_type_eq := B.binary_type_eq
  start_type_eq := B.start_type_eq
  startWord := B.startWord
  start_arity := B.start_arity
  start_anchor_eq := B.start_anchor_eq
  anchor_mem := by
    intro A
    exact hSK (B.anchor_mem A)
  terminal_mem := by
    intro ρ hρ hwt
    exact hSK (B.terminal_mem ρ hρ hwt)
  binary_mem := by
    intro ρ hρ
    exact hSK (B.binary_mem ρ hρ)
  start_mem := by
    intro ρ hρ hwt
    exact hSK (B.start_mem ρ hρ hwt)
  startWord_mem := hSK B.startWord_mem
  splicingConstructor := B.splicingConstructor

@[simp] theorem mono_toPreCore
    {K : Finset (Word α)}
    (B : ReachableSplicingBlueprint G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (B.mono hSK hKpos).toPreCore = B.toPreCore :=
  rfl

@[simp] theorem mono_splicingConstructor
    {K : Finset (Word α)}
    (B : ReachableSplicingBlueprint G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (B.mono hSK hKpos).splicingConstructor = B.splicingConstructor :=
  rfl

/-- The flat blueprint gives a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (B : ReachableSplicingBlueprint G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      S
      G.StringLanguage :=
  B.toPackage.characteristic_sample hfan hL

/-- Exact reconstruction for any positive finite superset. -/
theorem exact_for_positive_superset
    {K : Finset (Word α)}
    (B : ReachableSplicingBlueprint G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  B.toPackage.exact_for_positive_superset hfan hL hSK hKpos

/-- Exact reconstruction at any text prefix where the finite sample has
appeared. -/
theorem exact_at_seen_prefix
    (B : ReachableSplicingBlueprint G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (T : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (S : Set (Word α)) ⊆
      (T.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (T.prefixSample n) obs f =
      G.StringLanguage :=
  B.toPackage.exact_at_seen_prefix hfan hL T hseen

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (B : ReachableSplicingBlueprint G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  B.toPackage.prefix_exact_eventually hfan hL

/-- Gold identification for the reachable learner on every positive text. -/
theorem identifies_from_positive_text
    (B : ReachableSplicingBlueprint G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  B.toPackage.identifies_from_positive_text hfan hL

end ReachableSplicingBlueprint

end FlatSplicingBlueprint


section MainTheoremsFromSplicingBlueprint

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Main reachable identification theorem from the flat splicing blueprint. -/
theorem main_reachable_identification_from_splicing_blueprint
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (B : ReachableSplicingBlueprint G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  B.identifies_from_positive_text hfan hL

/-- Main reachable prefix-exact theorem from the flat splicing blueprint. -/
theorem main_reachable_prefix_exact_from_splicing_blueprint
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (B : ReachableSplicingBlueprint G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  B.prefix_exact_eventually hfan hL

end MainTheoremsFromSplicingBlueprint

end MCFG
