/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.SplicingBlueprint

/-!
# SplicingBlueprintMainData.lean

Thirty-fourth clean Lean experiment for the fixed-observation MCFG project.

`SplicingBlueprint.lean` introduced the current flat construction target:

```lean
ReachableSplicingBlueprint
```

This file packages the flat blueprint together with the global target
assumptions:

* fanout bound;
* fixed-observation substitutability promise.

The resulting record is a convenient final interface for the current reachable
main theorem.  Future construction files can aim to produce a
`ReachableSplicingBlueprint`; theorem users can then add the two global
assumptions and immediately obtain reachable exact reconstruction and Gold
identification.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section BlueprintMainData

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Main theorem data using the flat splicing blueprint.

This is currently the most direct package for the reachable-model theorem:
`blueprint` is the finite characteristic construction target, while `fanout`
and `promise` are global assumptions on the target grammar/language. -/
structure ReachableSplicingBlueprintMainData
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat) where
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage
  blueprint : ReachableSplicingBlueprint G S obs f

namespace ReachableSplicingBlueprintMainData

variable {G : WorkingMCFG N α}
variable {S : Finset (Word α)} {obs : α → M} {f : Nat}

/-- Convert to the finite splicing package. -/
def toPackage
    (A : ReachableSplicingBlueprintMainData G S obs f) :
    ReachableSplicingPackage G S obs f :=
  A.blueprint.toPackage

/-- Convert to splicing-main data. -/
def toSplicingMainData
    (A : ReachableSplicingBlueprintMainData G S obs f) :
    ReachableSplicingMainData G S obs f :=
  A.blueprint.toMainData A.fanout A.promise

/-- Convert to the older reachable main-data package. -/
def toReachableMainData
    (A : ReachableSplicingBlueprintMainData G S obs f) :
    ReachableMainData G S obs f :=
  A.toSplicingMainData.toMainData

/-- The induced reachable characteristic blueprint is exactly the stored one. -/
@[simp] theorem toSplicingMainData_toBlueprint
    (A : ReachableSplicingBlueprintMainData G S obs f) :
    A.toSplicingMainData.toBlueprint = A.blueprint.toPackage.toBlueprint :=
  rfl

/-- The finite sample `S` is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (A : ReachableSplicingBlueprintMainData G S obs f) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      S
      G.StringLanguage :=
  A.blueprint.characteristic_sample A.fanout A.promise

/-- Exact reconstruction for any positive finite superset of the finite
blueprint sample. -/
theorem exact_for_positive_superset
    (A : ReachableSplicingBlueprintMainData G S obs f)
    {K : Finset (Word α)}
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  A.blueprint.exact_for_positive_superset A.fanout A.promise hSK hKpos

/-- Exact reconstruction at any positive-text prefix where the finite blueprint
sample has appeared. -/
theorem exact_at_seen_prefix
    (A : ReachableSplicingBlueprintMainData G S obs f)
    (T : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (S : Set (Word α)) ⊆
      (T.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (T.prefixSample n) obs f =
      G.StringLanguage :=
  A.blueprint.exact_at_seen_prefix A.fanout A.promise T hseen

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (A : ReachableSplicingBlueprintMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  A.blueprint.prefix_exact_eventually A.fanout A.promise

/-- Gold identification for the reachable learner on every positive text. -/
theorem identifies_from_positive_text
    (A : ReachableSplicingBlueprintMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  A.blueprint.identifies_from_positive_text A.fanout A.promise

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (A : ReachableSplicingBlueprintMainData G S obs f)
    (T : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      T :=
  A.identifies_from_positive_text T

/-- The theorem can also be recovered through the splicing-main package. -/
theorem identifies_from_positive_text_via_splicing_main
    (A : ReachableSplicingBlueprintMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  A.toSplicingMainData.identifies_from_positive_text

/-- The theorem can also be recovered through the older reachable-main package. -/
theorem identifies_from_positive_text_via_reachable_main
    (A : ReachableSplicingBlueprintMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  A.toReachableMainData.identifies_from_positive_text

end ReachableSplicingBlueprintMainData

end BlueprintMainData


section MainTheoremsFromBlueprintMainData

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Main reachable identification theorem from flat blueprint main data. -/
theorem main_reachable_identification_from_splicing_blueprint_data
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (A : ReachableSplicingBlueprintMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  A.identifies_from_positive_text

/-- Main reachable prefix-exact theorem from flat blueprint main data. -/
theorem main_reachable_prefix_exact_from_splicing_blueprint_data
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (A : ReachableSplicingBlueprintMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  A.prefix_exact_eventually

end MainTheoremsFromBlueprintMainData

end MCFG
