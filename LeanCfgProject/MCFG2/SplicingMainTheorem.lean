/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.NamedContextSplicingConstructor

/-!
# SplicingMainTheorem.lean

Thirtieth clean Lean experiment for the fixed-observation MCFG project.

This file packages the current theorem in terms of a universal named-context
splicing constructor.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section SplicingMainData

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Main theorem data after reducing binary filling identities to a universal
named-context splicing constructor. -/
structure ReachableSplicingMainData
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat) where
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage
  preCore : ReachableBlueprintPreCore G obs f
  finiteSample : ReachablePreCoreFiniteSample G S obs f preCore
  splicingConstructor : NamedContextSplicingConstructor α

namespace ReachableSplicingMainData

variable {G : WorkingMCFG N α}
variable {S : Finset (Word α)} {obs : α → M} {f : Nat}

/-- The local binary-rule splicing provider induced by the universal
constructor. -/
def ruleSplicingProvider
    (A : ReachableSplicingMainData G S obs f) :
    BinaryRuleSplicingProvider G A.preCore :=
  A.splicingConstructor.toRuleSplicingProvider G A.preCore

/-- The global named-splicing family induced by the universal constructor. -/
def namedSplicingFamily
    (A : ReachableSplicingMainData G S obs f) :
    BinaryNamedSplicingFamily G A.preCore :=
  A.splicingConstructor.toNamedSplicingFamily G A.preCore

/-- The abstract filling-witness family induced by the universal constructor. -/
def fillingWitnessFamily
    (A : ReachableSplicingMainData G S obs f) :
    BinaryFillingWitnessFamily G A.preCore :=
  A.splicingConstructor.toFillingWitnessFamily G A.preCore

/-- The full blueprint core induced by the universal splicing constructor. -/
def blueprintCore
    (A : ReachableSplicingMainData G S obs f) :
    ReachableBlueprintCore G obs f :=
  A.splicingConstructor.toBlueprintCore G A.preCore

/-- Convert the finite pre-core sample data into finite-sample blueprint data. -/
def finiteBlueprintSample
    (A : ReachableSplicingMainData G S obs f) :
    ReachableBlueprintFiniteSample G S obs f A.blueprintCore :=
  A.ruleSplicingProvider.toFiniteSample A.finiteSample

/-- Convert the current package into a reachable characteristic blueprint. -/
def toBlueprint
    (A : ReachableSplicingMainData G S obs f) :
    ReachableCharacteristicBlueprint G S obs f :=
  A.ruleSplicingProvider.toBlueprint A.finiteSample

/-- Convert the current package into a reachable characteristic package. -/
def toPackage
    (A : ReachableSplicingMainData G S obs f) :
    ReachableCharacteristicPackage G S obs f :=
  A.toBlueprint.toPackage

/-- Convert the current package into the previously verified main-data record. -/
def toMainData
    (A : ReachableSplicingMainData G S obs f) :
    ReachableMainData G S obs f :=
  A.toBlueprint.toMainData A.fanout A.promise

/-- Exact reconstruction for any positive finite superset of the finite sample. -/
theorem exact_for_positive_superset
    (A : ReachableSplicingMainData G S obs f)
    {K : Finset (Word α)}
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  NamedContextSplicingConstructor.exact_for_positive_superset
    A.splicingConstructor G A.preCore A.finiteSample
    A.fanout A.promise hSK hKpos

/-- At any text prefix where the finite sample has appeared, reachable exact
reconstruction holds for that prefix. -/
theorem exact_at_seen_prefix
    (A : ReachableSplicingMainData G S obs f)
    (T : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (S : Set (Word α)) ⊆
      (T.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (T.prefixSample n) obs f =
      G.StringLanguage := by
  have hKpos : (T.prefixSample n : Set (Word α)) ⊆ G.StringLanguage := by
    intro word hword
    exact T.prefixSample_subset n hword
  exact A.exact_for_positive_superset hseen hKpos

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (A : ReachableSplicingMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  NamedContextSplicingConstructor.prefix_exact_eventually
    A.splicingConstructor G A.preCore A.finiteSample
    A.fanout A.promise

/-- The reachable learner is eventually correct on every positive text. -/
theorem identifies_from_positive_text
    (A : ReachableSplicingMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  NamedContextSplicingConstructor.identifies_from_positive_text
    A.splicingConstructor G A.preCore A.finiteSample
    A.fanout A.promise

/-- Characteristic-sample conclusion for the reachable learner. -/
theorem characteristic_sample
    (A : ReachableSplicingMainData G S obs f) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      S
      G.StringLanguage :=
  A.toBlueprint.characteristic_sample A.fanout A.promise

/-- Same eventual correctness theorem through `ReachableMainData`. -/
theorem identifies_from_positive_text_via_main_data
    (A : ReachableSplicingMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  A.toMainData.identifies_from_positive_text

end ReachableSplicingMainData

end SplicingMainData


section MainTheoremsFromSplicingData

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Main reachable identification theorem from the splicing-constructor
assumption package. -/
theorem main_reachable_identification_from_splicing_data
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (A : ReachableSplicingMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  A.identifies_from_positive_text

/-- Main reachable prefix-exact theorem from the splicing-constructor
assumption package. -/
theorem main_reachable_prefix_exact_from_splicing_data
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (A : ReachableSplicingMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  A.prefix_exact_eventually

end MainTheoremsFromSplicingData

end MCFG
