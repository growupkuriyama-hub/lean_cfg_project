/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.MainReachableTheorem

/-!
# CharacteristicSamplePackage.lean

Twenty-third clean Lean experiment for the fixed-observation MCFG project.

`MainReachableTheorem.lean` packaged the reachable main theorem in
`ReachableMainData`.  That record contains both global assumptions
(`fanout`, fixed-observation promise) and finite characteristic-sample data.

This file separates the finite characteristic-sample package itself:

* positivity of the finite sample `S`;
* `CharacteristicSampleData` over `S`;
* the canonical start-anchor witness.

The package can be converted into `ReachableMainData` once the global target
assumptions are supplied.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section Package

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Finite characteristic-sample package for the reachable theorem.

This is the data that should eventually be constructed from the actual
characteristic sample `CS(G̃₀)`.  It deliberately does not include the global
target assumptions `G.FanoutAtMost f` and
`FixedNamedTupleSubstitutable f obs G.StringLanguage`; those belong to the
ambient theorem rather than to the finite sample itself. -/
structure ReachableCharacteristicPackage
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat) where
  sample_positive : (S : Set (Word α)) ⊆ G.StringLanguage
  data : CharacteristicSampleData G S obs f
  startAnchor : StartAnchorCanonical data

namespace ReachableCharacteristicPackage

variable {G : WorkingMCFG N α}
variable {S : Finset (Word α)} {obs : α → M} {f : Nat}

/-- Convert the finite characteristic package into the full reachable main-data
record after adding the global assumptions. -/
def toMainData
    (P : ReachableCharacteristicPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ReachableMainData G S obs f where
  fanout := hfan
  promise := hL
  sample_positive := P.sample_positive
  characteristicData := P.data
  startAnchor := P.startAnchor

/-- Characteristic-sample conclusion for the reachable learner. -/
theorem characteristic_sample
    (P : ReachableCharacteristicPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      S
      G.StringLanguage :=
  (P.toMainData hfan hL).characteristic_sample

/-- Eventual correctness on a fixed positive text. -/
theorem eventually_correct_on_text
    (P : ReachableCharacteristicPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (T : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      T :=
  (P.toMainData hfan hL).eventually_correct_on_text T

/-- Identification from every positive text. -/
theorem identifies_from_positive_text
    (P : ReachableCharacteristicPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  (P.toMainData hfan hL).identifies_from_positive_text

/-- Prefix-exact reconstruction after the finite characteristic sample has
appeared in the current prefix. -/
theorem exact_at_seen_prefix
    (P : ReachableCharacteristicPackage G S obs f)
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
    (P : ReachableCharacteristicPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  (P.toMainData hfan hL).prefix_exact_eventually

/-- The finite package is monotone in the sample, provided the larger sample is
positive for the target. -/
def mono
    {K : Finset (Word α)}
    (P : ReachableCharacteristicPackage G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableCharacteristicPackage G K obs f where
  sample_positive := hKpos
  data := P.data.mono hSK
  startAnchor := P.startAnchor.mono hSK

@[simp] theorem mono_data
    {K : Finset (Word α)}
    (P : ReachableCharacteristicPackage G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (P.mono hSK hKpos).data = P.data.mono hSK :=
  rfl

/-- Monotonicity plus exact reconstruction for any positive finite superset. -/
theorem exact_for_positive_superset
    {K : Finset (Word α)}
    (P : ReachableCharacteristicPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage := by
  have hK : PositiveSample G K := by
    intro word hword
    exact hKpos hword
  exact StartAnchorCanonical.exact_reconstruction_reachable
    (P.data.mono hSK) (P.startAnchor.mono hSK) hfan hL hK

/-- The package gives the condition used in `ReachableGoldTheorem.lean`. -/
theorem toReachableCharacteristicCondition
    (P : ReachableCharacteristicPackage G S obs f) :
    ReachableCharacteristicCondition G S obs f :=
  reachableCharacteristicCondition_of_data
    G P.data P.startAnchor.toStartAnchorAsSampleWord

end ReachableCharacteristicPackage

end Package


section MainTheoremsFromPackage

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Main reachable identification theorem stated using the finite characteristic
package. -/
theorem main_reachable_identification_from_package
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (P : ReachableCharacteristicPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  P.identifies_from_positive_text hfan hL

/-- Main reachable prefix-exact theorem stated using the finite characteristic
package. -/
theorem main_reachable_prefix_exact_from_package
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (P : ReachableCharacteristicPackage G S obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually hfan hL

end MainTheoremsFromPackage

end MCFG
