/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSamplePackage

/-!
# CharacteristicSampleBuilderSkeleton.lean

Twenty-fourth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSamplePackage.lean` introduced the package needed by the
reachable main theorem:

```lean
ReachableCharacteristicPackage
```

However, constructing that package directly is slightly awkward because the
start-anchor witness depends on the already-built `CharacteristicSampleData`.

This file introduces a construction-friendly blueprint.  It lists all finite
characteristic-sample fields in one flat record, including the start word and
start-anchor equality.  From such a blueprint we build:

* `CharacteristicSampleData`;
* `StartAnchorCanonical`;
* `ReachableCharacteristicPackage`;
* hence the reachable main theorem.

This is still a skeleton: later files should construct this blueprint from the
actual output-type-refined grammar and its characteristic sample `CS(G̃₀)`.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section Blueprint

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Flat construction data for a reachable characteristic sample.

This record is intentionally close to the paper's characteristic-sample
construction: choose anchors, exposing contexts, rule-witness sample words, and
a sample start word.  It is then converted into the more structured package
used by the main theorem. -/
structure ReachableCharacteristicBlueprint
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat) where
  sample_positive : (S : Set (Word α)) ⊆ G.StringLanguage

  anchor : ∀ A : N, Tuple α (G.arity A)
  expose : ∀ A : N, NamedSentenceContext α (G.arity A)

  anchor_mem :
    ∀ A : N,
      namedFill (G.arity A) (expose A) (anchor A) ∈ S

  terminal_mem :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        namedFill (G.arity ρ.lhs) (expose ρ.lhs)
          (castTuple hwt.symm ρ.outputTuple) ∈ S

  terminal_type_eq :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        tupleType obs (anchor ρ.lhs) =
          tupleType obs (castTuple hwt.symm ρ.outputTuple)

  binary_mem :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        namedFill (G.arity ρ.lhs) (expose ρ.lhs)
          (ρ.apply (anchor ρ.left) (anchor ρ.right)) ∈ S

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

  start_mem :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        namedFill (G.arity G.start) (expose G.start)
          (castTuple hwt (anchor ρ.child)) ∈ S

  start_type_eq :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        tupleType obs (anchor G.start) =
          tupleType obs (castTuple hwt (anchor ρ.child))

  startWord : Word α
  startWord_mem : startWord ∈ S
  start_arity : 1 = G.arity G.start
  start_anchor_eq :
    anchor G.start =
      castTuple start_arity (singletonTuple startWord)

namespace ReachableCharacteristicBlueprint

variable {G : WorkingMCFG N α}
variable {S : Finset (Word α)} {obs : α → M} {f : Nat}

/-- Build `CharacteristicSampleData` from the flat blueprint. -/
def toData
    (B : ReachableCharacteristicBlueprint G S obs f) :
    CharacteristicSampleData G S obs f where
  anchor := B.anchor
  expose := B.expose
  anchor_mem := B.anchor_mem
  terminal_mem := B.terminal_mem
  terminal_type_eq := B.terminal_type_eq
  binary_mem := B.binary_mem
  binary_type_eq := B.binary_type_eq
  binary_leftIdentity := B.binary_leftIdentity
  binary_rightIdentity := B.binary_rightIdentity
  start_mem := B.start_mem
  start_type_eq := B.start_type_eq

/-- Build the construction-friendly start-anchor witness from the blueprint. -/
def toStartAnchorCanonical
    (B : ReachableCharacteristicBlueprint G S obs f) :
    StartAnchorCanonical B.toData where
  startWord := B.startWord
  start_mem := B.startWord_mem
  start_arity := B.start_arity
  anchor_eq := by
    exact B.start_anchor_eq

/-- Build the finite reachable characteristic package from the blueprint. -/
def toPackage
    (B : ReachableCharacteristicBlueprint G S obs f) :
    ReachableCharacteristicPackage G S obs f where
  sample_positive := B.sample_positive
  data := B.toData
  startAnchor := B.toStartAnchorCanonical

@[simp] theorem toPackage_data
    (B : ReachableCharacteristicBlueprint G S obs f) :
    B.toPackage.data = B.toData :=
  rfl

/-- Build the full reachable main-data record from the blueprint after adding
the global target assumptions. -/
def toMainData
    (B : ReachableCharacteristicBlueprint G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ReachableMainData G S obs f :=
  B.toPackage.toMainData hfan hL

/-- Exact reconstruction at any prefix where the blueprint sample has appeared. -/
theorem exact_at_seen_prefix
    (B : ReachableCharacteristicBlueprint G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (T : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (S : Set (Word α)) ⊆
      (T.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (T.prefixSample n) obs f =
      G.StringLanguage :=
  B.toPackage.exact_at_seen_prefix hfan hL T hseen

/-- Eventual prefix-exact reconstruction from the blueprint. -/
theorem prefix_exact_eventually
    (B : ReachableCharacteristicBlueprint G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  B.toPackage.prefix_exact_eventually hfan hL

/-- Gold identification from the blueprint. -/
theorem identifies_from_positive_text
    (B : ReachableCharacteristicBlueprint G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  B.toPackage.identifies_from_positive_text hfan hL

/-- Characteristic-sample conclusion for the reachable learner from the
blueprint. -/
theorem characteristic_sample
    (B : ReachableCharacteristicBlueprint G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      S
      G.StringLanguage :=
  B.toPackage.characteristic_sample hfan hL

/-- Exact reconstruction for any positive finite superset of the blueprint
sample. -/
theorem exact_for_positive_superset
    {K : Finset (Word α)}
    (B : ReachableCharacteristicBlueprint G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  B.toPackage.exact_for_positive_superset hfan hL hSK hKpos

end ReachableCharacteristicBlueprint

end Blueprint


section MainTheoremsFromBlueprint

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Main reachable identification theorem stated from the flat characteristic
blueprint. -/
theorem main_reachable_identification_from_blueprint
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (B : ReachableCharacteristicBlueprint G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  B.identifies_from_positive_text hfan hL

/-- Main reachable prefix-exact theorem stated from the flat characteristic
blueprint. -/
theorem main_reachable_prefix_exact_from_blueprint
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (B : ReachableCharacteristicBlueprint G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  B.prefix_exact_eventually hfan hL

end MainTheoremsFromBlueprint

end MCFG
