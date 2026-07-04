/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ReachableStartBridge

/-!
# ReachableGoldTheorem.lean

Eighteenth clean Lean experiment for the fixed-observation MCFG project.

This file connects the reachable exact-reconstruction theorem with the
Gold-identification skeleton.

The concrete canonical learner is still represented by the reachable
sample-language model:

```lean
K ↦ ReachableSampleStringLanguage K obs f
```

The main theorem says:

If a finite sample `S` is positive for the target and every positive finite
`K` containing `S` supplies the characteristic-sample data plus the start-anchor
bridge, then `S` is a characteristic sample for the reachable learner.  By
finite text coverage, the reachable learner identifies the target on every
positive text.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ReachableLearner

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]

/-- The reachable learner's hypothesis type is just the finite sample itself. -/
abbrev ReachableSampleHyp (α : Type u) := Finset (Word α)

/-- The reachable sample learner is set-driven: it stores the finite sample. -/
def reachableSampleLearner : SetDrivenLearner α (ReachableSampleHyp α) :=
  fun K => K

/-- Interpret a finite sample hypothesis by the reachable sample string
language generated from that sample. -/
def reachableHypLanguage (obs : α → M) (f : Nat) :
    HypLanguage α (ReachableSampleHyp α) :=
  fun K => ReachableSampleStringLanguage K obs f

end ReachableLearner


section CharacteristicSampleFromReachableReconstruction

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- A compact condition saying that every positive finite superset of `S`
contains enough characteristic evidence to reconstruct the target language in
the reachable sample model. -/
def ReachableCharacteristicCondition
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat) : Prop :=
  ∀ K : Finset (Word α),
    (S : Set (Word α)) ⊆ (K : Set (Word α)) →
    (K : Set (Word α)) ⊆ G.StringLanguage →
      ∃ D : CharacteristicSampleData G K obs f,
        StartAnchorAsSampleWord D

/-- If a finite sample `S` gives characteristic data for every positive
finite superset `K`, then `S` is a characteristic sample for the reachable
sample learner. -/
theorem reachable_characteristicSample
    (G : WorkingMCFG N α)
    {obs : α → M} {f : Nat}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (S : Finset (Word α))
    (hSpos : (S : Set (Word α)) ⊆ G.StringLanguage)
    (hCond : ReachableCharacteristicCondition G S obs f) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      S
      G.StringLanguage := by
  refine ⟨hSpos, ?_⟩
  intro K hSK hKG
  rcases hCond K hSK hKG with ⟨D, B⟩
  have hKpos : PositiveSample G K := by
    intro word hword
    exact hKG hword
  simpa [reachableHypLanguage, reachableSampleLearner]
    using StartAnchorAsSampleWord.exact_reconstruction_reachable
      D B hfan hL hKpos

/-- Gold-style identification theorem for the reachable sample learner.

Once `S` satisfies the reachable characteristic condition, every positive text
for the target eventually yields the target language as the learner hypothesis. -/
theorem reachable_identifies_from_positive_text
    (G : WorkingMCFG N α)
    {obs : α → M} {f : Nat}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (S : Finset (Word α))
    (hSpos : (S : Set (Word α)) ⊆ G.StringLanguage)
    (hCond : ReachableCharacteristicCondition G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T := by
  exact finiteCharacteristicSample_identifies_target
    (reachableHypLanguage obs f)
    (reachableSampleLearner (α := α))
    S
    (reachable_characteristicSample G hfan hL S hSpos hCond)

/-- Same theorem, unpacked as an eventual-stage statement. -/
theorem reachable_identifies_after_some_stage
    (G : WorkingMCFG N α)
    {obs : α → M} {f : Nat}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (S : Finset (Word α))
    (hSpos : (S : Set (Word α)) ⊆ G.StringLanguage)
    (hCond : ReachableCharacteristicCondition G S obs f)
    (T : TextFor G.StringLanguage) :
    ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
      reachableHypLanguage obs f
        (reachableSampleLearner (α := α) (T.prefixSample n)) =
          G.StringLanguage := by
  exact reachable_identifies_from_positive_text
    G hfan hL S hSpos hCond T

end CharacteristicSampleFromReachableReconstruction

end MCFG
