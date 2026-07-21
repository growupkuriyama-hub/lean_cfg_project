/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.SplicingMainDataMonotone

/-!
# SplicingCharacteristicPackage.lean

Thirty-second clean Lean experiment for the fixed-observation MCFG project.

`SplicingMainTheorem.lean` introduced `ReachableSplicingMainData`, which contains

* global target assumptions: fanout and fixed-observation promise;
* finite characteristic construction data: pre-core, finite-sample membership,
  and a universal named-context splicing constructor.

This file separates the finite construction package from the global target
assumptions.

The resulting record

```lean
ReachableSplicingPackage
```

is the current construction target for future files.  Once the global target
assumptions are supplied, it converts to `ReachableSplicingMainData`, and hence
all reachable exact-reconstruction and Gold-identification theorems follow.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section SplicingPackage

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Finite construction package for the splicing-based reachable theorem.

This contains no global target assumptions.  It is the data that should
eventually be constructed from the trimmed output-type refinement and the
finite characteristic sample. -/
structure ReachableSplicingPackage
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat) where
  preCore : ReachableBlueprintPreCore G obs f
  finiteSample : ReachablePreCoreFiniteSample G S obs f preCore
  splicingConstructor : NamedContextSplicingConstructor α

namespace ReachableSplicingPackage

variable {G : WorkingMCFG N α}
variable {S : Finset (Word α)} {obs : α → M} {f : Nat}

/-- Add global target assumptions to a finite splicing package. -/
def toMainData
    (P : ReachableSplicingPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ReachableSplicingMainData G S obs f where
  fanout := hfan
  promise := hL
  preCore := P.preCore
  finiteSample := P.finiteSample
  splicingConstructor := P.splicingConstructor

/-- The package induces a rule-splicing provider. -/
def ruleSplicingProvider
    (P : ReachableSplicingPackage G S obs f) :
    BinaryRuleSplicingProvider G P.preCore :=
  P.splicingConstructor.toRuleSplicingProvider G P.preCore

/-- The package induces a named-splicing family. -/
def namedSplicingFamily
    (P : ReachableSplicingPackage G S obs f) :
    BinaryNamedSplicingFamily G P.preCore :=
  P.splicingConstructor.toNamedSplicingFamily G P.preCore

/-- The package induces an abstract filling-witness family. -/
def fillingWitnessFamily
    (P : ReachableSplicingPackage G S obs f) :
    BinaryFillingWitnessFamily G P.preCore :=
  P.splicingConstructor.toFillingWitnessFamily G P.preCore

/-- The package induces a full reachable blueprint core. -/
def blueprintCore
    (P : ReachableSplicingPackage G S obs f) :
    ReachableBlueprintCore G obs f :=
  P.splicingConstructor.toBlueprintCore G P.preCore

/-- The package induces finite-sample blueprint data. -/
def finiteBlueprintSample
    (P : ReachableSplicingPackage G S obs f) :
    ReachableBlueprintFiniteSample G S obs f P.blueprintCore :=
  P.ruleSplicingProvider.toFiniteSample P.finiteSample

/-- The package induces a reachable characteristic blueprint. -/
def toBlueprint
    (P : ReachableSplicingPackage G S obs f) :
    ReachableCharacteristicBlueprint G S obs f :=
  P.ruleSplicingProvider.toBlueprint P.finiteSample

/-- The package induces the previous reachable characteristic package. -/
def toCharacteristicPackage
    (P : ReachableSplicingPackage G S obs f) :
    ReachableCharacteristicPackage G S obs f :=
  P.toBlueprint.toPackage

/-- The finite package is monotone in the sample, provided the larger sample is
positive for the target language. -/
def mono
    {K : Finset (Word α)}
    (P : ReachableSplicingPackage G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSplicingPackage G K obs f where
  preCore := P.preCore
  finiteSample := P.finiteSample.mono hSK hKpos
  splicingConstructor := P.splicingConstructor

@[simp] theorem mono_preCore
    {K : Finset (Word α)}
    (P : ReachableSplicingPackage G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (P.mono hSK hKpos).preCore = P.preCore :=
  rfl

@[simp] theorem mono_splicingConstructor
    {K : Finset (Word α)}
    (P : ReachableSplicingPackage G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (P.mono hSK hKpos).splicingConstructor = P.splicingConstructor :=
  rfl

/-- The package gives a characteristic sample for the reachable learner after
adding the global assumptions. -/
theorem characteristic_sample
    (P : ReachableSplicingPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      S
      G.StringLanguage :=
  (P.toMainData hfan hL).characteristic_sample

/-- Exact reconstruction for any positive finite superset. -/
theorem exact_for_positive_superset
    {K : Finset (Word α)}
    (P : ReachableSplicingPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  (P.toMainData hfan hL).exact_for_positive_superset hSK hKpos

/-- Exact reconstruction at any text prefix where the package sample has
appeared. -/
theorem exact_at_seen_prefix
    (P : ReachableSplicingPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (T : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (S : Set (Word α)) ⊆
      (T.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (T.prefixSample n) obs f =
      G.StringLanguage :=
  (P.toMainData hfan hL).exact_at_seen_prefix T hseen

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (P : ReachableSplicingPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  (P.toMainData hfan hL).prefix_exact_eventually

/-- Gold identification for the reachable learner on every positive text. -/
theorem identifies_from_positive_text
    (P : ReachableSplicingPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  (P.toMainData hfan hL).identifies_from_positive_text

/-- Monotone package exactness for a larger positive finite sample. -/
theorem exact_after_mono
    {K : Finset (Word α)}
    (P : ReachableSplicingPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  ((P.mono hSK hKpos).toMainData hfan hL).exact_for_positive_superset
    (fun word hword => hword) hKpos

end ReachableSplicingPackage

end SplicingPackage


section MainTheoremsFromSplicingPackage

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Main reachable identification theorem from the finite splicing package. -/
theorem main_reachable_identification_from_splicing_package
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (P : ReachableSplicingPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  P.identifies_from_positive_text hfan hL

/-- Main reachable prefix-exact theorem from the finite splicing package. -/
theorem main_reachable_prefix_exact_from_splicing_package
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (P : ReachableSplicingPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually hfan hL

end MainTheoremsFromSplicingPackage

end MCFG
