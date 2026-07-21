/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.PrefixExactReconstruction

/-!
# MainReachableTheorem.lean

Twenty-second clean Lean experiment for the fixed-observation MCFG project.

This file packages the current verified development into a single reachable
main theorem.

The theorem is still for the reachable sample-language model, not yet for the
fully enumerated concrete canonical learner.  The remaining concrete work is
to construct `CharacteristicSampleData` and `StartAnchorCanonical` from the
actual characteristic sample `CS(G̃₀)` and to connect the reachable model to the
finite canonical grammar produced by the algorithm.

Nevertheless, under the current characteristic-data assumptions, this file gives
the clean final shape:

* after the finite characteristic sample has appeared in a positive text,
  every later prefix sample reconstructs the target exactly;
* equivalently, the reachable learner identifies the target in the limit from
  positive data.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section MainReachableData

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- The current package of assumptions needed for the reachable main theorem.

This is deliberately explicit: it separates the already-verified formal
machinery from the remaining construction problem.

Later files should aim to construct this record from the actual
output-type-refined grammar and its characteristic sample. -/
structure ReachableMainData
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat) where
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage
  sample_positive : (S : Set (Word α)) ⊆ G.StringLanguage
  characteristicData : CharacteristicSampleData G S obs f
  startAnchor : StartAnchorCanonical characteristicData

namespace ReachableMainData

variable {G : WorkingMCFG N α}
variable {S : Finset (Word α)} {obs : α → M} {f : Nat}

/-- At any text stage where the finite characteristic sample has appeared, the
reachable learner reconstructs the target language exactly. -/
theorem exact_at_seen_prefix
    (A : ReachableMainData G S obs f)
    (T : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (S : Set (Word α)) ⊆
      (T.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (T.prefixSample n) obs f =
      G.StringLanguage :=
  exact_reconstruction_at_prefix_after_seen
    G A.fanout A.promise A.characteristicData A.startAnchor T hseen

/-- Eventual exact reconstruction along every positive text. -/
theorem eventually_exact_at_prefixes
    (A : ReachableMainData G S obs f)
    (T : TextFor G.StringLanguage) :
    ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
      ReachableSampleStringLanguage (T.prefixSample n) obs f =
        G.StringLanguage :=
  eventually_exact_reconstruction_at_prefixes
    G A.fanout A.promise A.sample_positive
    A.characteristicData A.startAnchor T

/-- Same result through the reachable learner/hypothesis-language interface. -/
theorem eventually_hypothesis_correct_at_prefixes
    (A : ReachableMainData G S obs f)
    (T : TextFor G.StringLanguage) :
    ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
      reachableHypLanguage obs f
        (reachableSampleLearner (α := α) (T.prefixSample n)) =
          G.StringLanguage :=
  eventually_reachable_hypothesis_correct_at_prefixes
    G A.fanout A.promise A.sample_positive
    A.characteristicData A.startAnchor T

/-- The reachable learner is eventually correct on every positive text. -/
theorem eventually_correct_on_text
    (A : ReachableMainData G S obs f)
    (T : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      T :=
  reachable_identifies_from_canonical_characteristic_data
    G A.fanout A.promise A.sample_positive
    A.characteristicData A.startAnchor T

/-- The finite sample `S` is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (A : ReachableMainData G S obs f) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      S
      G.StringLanguage :=
  reachable_characteristicSample_of_canonical_data
    G A.fanout A.promise A.sample_positive
    A.characteristicData A.startAnchor

/-- One-line reachable main theorem: the reachable learner identifies the target
from every positive text. -/
theorem identifies_from_positive_text
    (A : ReachableMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T := by
  intro T
  exact A.eventually_correct_on_text T

/-- One-line prefix form: after some finite stage, every later prefix sample
reconstructs the target language exactly. -/
theorem prefix_exact_eventually
    (A : ReachableMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage := by
  intro T
  exact A.eventually_exact_at_prefixes T

end ReachableMainData

end MainReachableData


section MainReachableTheorem

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Main reachable identification theorem, stated without opening the
assumption package.

This is the cleanest current Lean version of the paper's positive-data
identification theorem, with the concrete characteristic-sample construction
represented by `CharacteristicSampleData` and `StartAnchorCanonical`. -/
theorem main_reachable_identification
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (A : ReachableMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  A.identifies_from_positive_text

/-- Main reachable prefix-exact theorem, stated without opening the assumption
package. -/
theorem main_reachable_prefix_exact
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (A : ReachableMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  A.prefix_exact_eventually

end MainReachableTheorem

end MCFG
