/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.SplicingBlueprintMainData

/-!
# SplicingBlueprintMainDataMonotone.lean

Thirty-fifth clean Lean experiment for the fixed-observation MCFG project.

`SplicingBlueprintMainData.lean` gave the current final interface:

```lean
ReachableSplicingBlueprintMainData
```

This file adds monotonicity for that final interface.

If the flat blueprint is valid over a finite sample `S`, then the same anchors,
contexts, start data, and splicing constructor are valid over any larger
positive finite sample `K`.  Only the finite sample membership proofs are
transported along `S ⊆ K`.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section BlueprintMainDataMonotone

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α}
variable {S K : Finset (Word α)}
variable {obs : α → M} {f : Nat}

namespace ReachableSplicingBlueprintMainData

/-- Flat blueprint main data is monotone in the finite sample. -/
def mono
    (A : ReachableSplicingBlueprintMainData G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSplicingBlueprintMainData G K obs f where
  fanout := A.fanout
  promise := A.promise
  blueprint := A.blueprint.mono hSK hKpos

@[simp] theorem mono_blueprint_toPreCore
    (A : ReachableSplicingBlueprintMainData G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (A.mono hSK hKpos).blueprint.toPreCore = A.blueprint.toPreCore :=
  rfl

@[simp] theorem mono_fanout
    (A : ReachableSplicingBlueprintMainData G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (A.mono hSK hKpos).fanout = A.fanout :=
  rfl

@[simp] theorem mono_promise
    (A : ReachableSplicingBlueprintMainData G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (A.mono hSK hKpos).promise = A.promise :=
  rfl

/-- The monotone main-data package reconstructs the target exactly on the
larger positive sample. -/
theorem exact_after_mono
    (A : ReachableSplicingBlueprintMainData G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  (A.mono hSK hKpos).exact_for_positive_superset
    (fun word hword => hword) hKpos

/-- The larger sample is also a characteristic sample for the reachable learner. -/
theorem characteristic_sample_after_mono
    (A : ReachableSplicingBlueprintMainData G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      K
      G.StringLanguage :=
  (A.mono hSK hKpos).characteristic_sample

/-- At a text prefix containing `S`, the monotone blueprint main data over that
prefix gives exact reconstruction. -/
theorem exact_at_prefix_via_mono
    (A : ReachableSplicingBlueprintMainData G S obs f)
    (T : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (S : Set (Word α)) ⊆
      (T.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (T.prefixSample n) obs f =
      G.StringLanguage := by
  have hKpos :
      (T.prefixSample n : Set (Word α)) ⊆ G.StringLanguage := by
    intro word hword
    exact T.prefixSample_subset n hword
  exact A.exact_after_mono hseen hKpos

/-- Eventual prefix-exact reconstruction derived directly from monotonicity of
the final blueprint-main-data interface. -/
theorem prefix_exact_eventually_via_mono
    (A : ReachableSplicingBlueprintMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage := by
  intro T
  rcases T.eventuallyContains_of_subset S
      A.blueprint.sample_positive with ⟨n0, hcontains⟩
  refine ⟨n0, ?_⟩
  intro n hn
  exact A.exact_at_prefix_via_mono T (hcontains n hn)

/-- Eventual correctness of the reachable learner, derived from monotonicity of
the final blueprint-main-data interface. -/
theorem identifies_from_positive_text_via_mono
    (A : ReachableSplicingBlueprintMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T := by
  intro T
  rcases A.prefix_exact_eventually_via_mono T with ⟨n0, hcorr⟩
  refine ⟨n0, ?_⟩
  intro n hn
  simpa [reachableHypLanguage, reachableSampleLearner] using hcorr n hn

end ReachableSplicingBlueprintMainData

end BlueprintMainDataMonotone


section MainTheoremsFromMonotoneBlueprintMainData

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Main reachable prefix-exact theorem using monotonicity of the flat
blueprint-main-data interface. -/
theorem main_reachable_prefix_exact_from_splicing_blueprint_data_mono
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (A : ReachableSplicingBlueprintMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  A.prefix_exact_eventually_via_mono

/-- Main reachable identification theorem using monotonicity of the flat
blueprint-main-data interface. -/
theorem main_reachable_identification_from_splicing_blueprint_data_mono
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (A : ReachableSplicingBlueprintMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  A.identifies_from_positive_text_via_mono

end MainTheoremsFromMonotoneBlueprintMainData

end MCFG
