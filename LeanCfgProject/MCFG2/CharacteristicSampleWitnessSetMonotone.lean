/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleWitnessSet

/-!
# CharacteristicSampleWitnessSetMonotone.lean

Forty-eighth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleWitnessSet.lean` introduced the witness-set interface:

```lean
TrimmedPresentationWitnessWordSet D ⊆ S
```

for finite samples `S`.

This file proves monotonicity of the corresponding witness-sample package.
If `S` contains all required witness words and `S ⊆ K ⊆ G.StringLanguage`,
then `K` contains the same witness words.

Consequently, the stable reachable identification and prefix-exact
reconstruction theorems are available directly from the witness-set interface
after finite sample extension.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section WitnessSampleMonotone

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S K : Finset (Word α)}

namespace TrimmedPresentationWitnessSample

/-- Witness-sample data is monotone in the finite sample. -/
def mono
    (H : TrimmedPresentationWitnessSample D S)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    TrimmedPresentationWitnessSample D K where
  sample_positive := hKpos
  contains_witnesses := by
    intro word hword
    exact hSK (H.contains_witnesses hword)

@[simp] theorem mono_sample_positive
    (H : TrimmedPresentationWitnessSample D S)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (H.mono hSK hKpos).sample_positive = hKpos :=
  rfl

/-- Monotonicity agrees with conversion to trimmed sample data. -/
theorem toSampleData_mono
    (H : TrimmedPresentationWitnessSample D S)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (H.mono hSK hKpos).toSampleData =
      H.toSampleData.mono hSK hKpos := by
  rfl

/-- Monotonicity agrees with conversion to characteristic-sample objects. -/
theorem toCharacteristicSample_mono
    (H : TrimmedPresentationWitnessSample D S)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (H.mono hSK hKpos).toCharacteristicSample =
      H.toCharacteristicSample.extend hSK hKpos := by
  rfl

/-- The monotone witness sample gives exact reconstruction on the larger
positive finite sample. -/
theorem exact_after_mono
    (H : TrimmedPresentationWitnessSample D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  (H.mono hSK hKpos).exact_for_positive_superset
    U hfan hL (fun word hword => hword) hKpos

/-- At a positive-text prefix containing the witness sample, monotonicity
transports the witness-sample package to that prefix and yields exact
reconstruction. -/
theorem exact_at_prefix_via_mono
    (H : TrimmedPresentationWitnessSample D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (S : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage := by
  have hKpos :
      (Ttxt.prefixSample n : Set (Word α)) ⊆ G.StringLanguage := by
    intro word hword
    exact Ttxt.prefixSample_subset n hword
  exact H.exact_after_mono U hfan hL hseen hKpos

/-- Eventual prefix-exact reconstruction from witness-sample monotonicity. -/
theorem prefix_exact_via_mono
    (H : TrimmedPresentationWitnessSample D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage := by
  intro Ttxt
  rcases Ttxt.eventuallyContains_of_subset S
      H.sample_positive with ⟨n0, hcontains⟩
  refine ⟨n0, ?_⟩
  intro n hn
  exact H.exact_at_prefix_via_mono U hfan hL Ttxt (hcontains n hn)

/-- Reachable Gold identification from witness-sample monotonicity. -/
theorem identifies_via_mono
    (H : TrimmedPresentationWitnessSample D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt := by
  intro Ttxt
  rcases H.prefix_exact_via_mono U hfan hL Ttxt with ⟨n0, hcorr⟩
  refine ⟨n0, ?_⟩
  intro n hn
  simpa [reachableHypLanguage, reachableSampleLearner] using hcorr n hn

end TrimmedPresentationWitnessSample

end WitnessSampleMonotone


section MainTheoremsFromWitnessSampleMonotone

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

/-- Main reachable identification theorem from the monotone witness-sample
interface. -/
theorem main_reachable_identification_from_witness_sample_mono
    (H : TrimmedPresentationWitnessSample D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  H.identifies_via_mono U hfan hL

/-- Main reachable prefix-exact theorem from the monotone witness-sample
interface. -/
theorem main_reachable_prefix_exact_from_witness_sample_mono
    (H : TrimmedPresentationWitnessSample D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  H.prefix_exact_via_mono U hfan hL

end MainTheoremsFromWitnessSampleMonotone

end MCFG
