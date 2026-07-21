/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.StartAnchorCanonical

/-!
# PrefixExactReconstruction.lean

Twenty-first clean Lean experiment for the fixed-observation MCFG project.

This file states the reachable exact-reconstruction theorem directly for
prefix samples of a positive text.

If a finite characteristic sample `S` has already appeared in the prefix sample
`T.prefixSample n`, then the characteristic data over `S` transports to that
prefix sample, and reachable exact reconstruction holds at stage `n`.

Thus, once the characteristic sample has appeared, every later hypothesis of
the reachable learner is exactly the target language.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PrefixExact

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- If the finite characteristic sample `S` is contained in a prefix sample of a
positive text, then reachable exact reconstruction holds for that prefix. -/
theorem exact_reconstruction_at_prefix_after_seen
    (G : WorkingMCFG N α)
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (D : CharacteristicSampleData G S obs f)
    (C : StartAnchorCanonical D)
    (T : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (S : Set (Word α)) ⊆
      (T.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (T.prefixSample n) obs f =
      G.StringLanguage := by
  have hK : PositiveSample G (T.prefixSample n) := by
    intro word hword
    exact T.prefixSample_subset n hword
  exact StartAnchorCanonical.exact_reconstruction_reachable
    (D.mono hseen) (C.mono hseen) hfan hL hK

/-- Once a finite characteristic sample is positive for the target, every text
for the target reaches a stage after which all prefix hypotheses are exactly
the target language. -/
theorem eventually_exact_reconstruction_at_prefixes
    (G : WorkingMCFG N α)
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSpos : (S : Set (Word α)) ⊆ G.StringLanguage)
    (D : CharacteristicSampleData G S obs f)
    (C : StartAnchorCanonical D)
    (T : TextFor G.StringLanguage) :
    ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
      ReachableSampleStringLanguage (T.prefixSample n) obs f =
        G.StringLanguage := by
  rcases T.eventuallyContains_of_subset S hSpos with ⟨n0, hcontains⟩
  refine ⟨n0, ?_⟩
  intro n hn
  exact exact_reconstruction_at_prefix_after_seen
    G hfan hL D C T (hcontains n hn)

/-- The same result phrased using the reachable learner/hypothesis-language
interface. -/
theorem eventually_reachable_hypothesis_correct_at_prefixes
    (G : WorkingMCFG N α)
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSpos : (S : Set (Word α)) ⊆ G.StringLanguage)
    (D : CharacteristicSampleData G S obs f)
    (C : StartAnchorCanonical D)
    (T : TextFor G.StringLanguage) :
    ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
      reachableHypLanguage obs f
        (reachableSampleLearner (α := α) (T.prefixSample n)) =
          G.StringLanguage := by
  simpa [reachableHypLanguage, reachableSampleLearner]
    using eventually_exact_reconstruction_at_prefixes
      G hfan hL hSpos D C T

/-- Pointwise form: at any stage where `S` has appeared, the reachable learner's
hypothesis is exactly the target. -/
theorem reachable_hypothesis_correct_after_seen
    (G : WorkingMCFG N α)
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (D : CharacteristicSampleData G S obs f)
    (C : StartAnchorCanonical D)
    (T : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (S : Set (Word α)) ⊆
      (T.prefixSample n : Set (Word α))) :
    reachableHypLanguage obs f
      (reachableSampleLearner (α := α) (T.prefixSample n)) =
        G.StringLanguage := by
  simpa [reachableHypLanguage, reachableSampleLearner]
    using exact_reconstruction_at_prefix_after_seen
      G hfan hL D C T hseen

end PrefixExact

end MCFG
