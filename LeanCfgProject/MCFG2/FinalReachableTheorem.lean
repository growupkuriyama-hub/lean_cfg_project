/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.SplicingBlueprintMainDataMonotone

/-!
# FinalReachableTheorem.lean

Thirty-sixth clean Lean experiment for the fixed-observation MCFG project.

This file fixes the current reachable-model theorem under stable final names.

Mathematically, it adds no new construction.  Its purpose is to expose the
current endpoint in a compact interface:

* a finite flat splicing blueprint;
* a fanout bound;
* the fixed-observation substitutability promise.

From these assumptions, the reachable learner identifies the target language
from every positive text, and every sufficiently late prefix sample reconstructs
the target exactly.

The theorem is still for `ReachableSampleStringLanguage`, not yet for the fully
enumerated concrete canonical learner.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section FinalReachableData

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Final assumption package for the currently verified reachable theorem.

This is a thin wrapper around `ReachableSplicingBlueprintMainData`, chosen to
give the current endpoint stable names. -/
structure FinalReachableData
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat) where
  data : ReachableSplicingBlueprintMainData G S obs f

namespace FinalReachableData

variable {G : WorkingMCFG N α}
variable {S : Finset (Word α)} {obs : α → M} {f : Nat}

/-- The underlying flat splicing blueprint. -/
def blueprint
    (A : FinalReachableData G S obs f) :
    ReachableSplicingBlueprint G S obs f :=
  A.data.blueprint

/-- The fanout bound. -/
def fanout
    (A : FinalReachableData G S obs f) :
    G.FanoutAtMost f :=
  A.data.fanout

/-- The fixed-observation substitutability promise. -/
def promise
    (A : FinalReachableData G S obs f) :
    FixedNamedTupleSubstitutable f obs G.StringLanguage :=
  A.data.promise

/-- Convert back to the previous final interface. -/
def toBlueprintMainData
    (A : FinalReachableData G S obs f) :
    ReachableSplicingBlueprintMainData G S obs f :=
  A.data

/-- Convert to the splicing-main-data interface. -/
def toSplicingMainData
    (A : FinalReachableData G S obs f) :
    ReachableSplicingMainData G S obs f :=
  A.data.toSplicingMainData

/-- Convert to the older reachable-main-data interface. -/
def toReachableMainData
    (A : FinalReachableData G S obs f) :
    ReachableMainData G S obs f :=
  A.data.toReachableMainData

/-- The finite sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (A : FinalReachableData G S obs f) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      S
      G.StringLanguage :=
  A.data.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the finite
characteristic sample. -/
theorem exact_for_positive_superset
    (A : FinalReachableData G S obs f)
    {K : Finset (Word α)}
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  A.data.exact_for_positive_superset hSK hKpos

/-- Exact reconstruction at any positive-text prefix where the finite sample has
appeared. -/
theorem exact_at_seen_prefix
    (A : FinalReachableData G S obs f)
    (T : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (S : Set (Word α)) ⊆
      (T.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (T.prefixSample n) obs f =
      G.StringLanguage :=
  A.data.exact_at_seen_prefix T hseen

/-- Eventual exact reconstruction along every positive text. -/
theorem prefix_exact_eventually
    (A : FinalReachableData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  A.data.prefix_exact_eventually_via_mono

/-- Gold identification of the target by the reachable learner. -/
theorem identifies_from_positive_text
    (A : FinalReachableData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  A.data.identifies_from_positive_text_via_mono

/-- Pointwise version for one positive text. -/
theorem eventually_correct_on_text
    (A : FinalReachableData G S obs f)
    (T : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      T :=
  A.identifies_from_positive_text T

/-- Monotonicity of the final data in the finite sample. -/
def mono
    (A : FinalReachableData G S obs f)
    {K : Finset (Word α)}
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    FinalReachableData G K obs f where
  data := A.data.mono hSK hKpos

/-- The monotone final data reconstructs the target exactly on the larger
positive finite sample. -/
theorem exact_after_mono
    (A : FinalReachableData G S obs f)
    {K : Finset (Word α)}
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  A.data.exact_after_mono hSK hKpos

end FinalReachableData

end FinalReachableData


section FinalReachableTheorems

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Final reachable identification theorem.

This is the compact statement of the strongest theorem currently verified in
this development. -/
theorem final_reachable_identification
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (A : FinalReachableData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  A.identifies_from_positive_text

/-- Final reachable prefix-exact theorem.

After a finite stage, every later prefix sample reconstructs the target language
exactly in the reachable sample-language model. -/
theorem final_reachable_prefix_exact
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (A : FinalReachableData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  A.prefix_exact_eventually

/-- Final reachable finite-superset exactness theorem. -/
theorem final_reachable_exact_for_positive_superset
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (A : FinalReachableData G S obs f)
    {K : Finset (Word α)}
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  A.exact_for_positive_superset hSK hKpos

end FinalReachableTheorems

end MCFG
