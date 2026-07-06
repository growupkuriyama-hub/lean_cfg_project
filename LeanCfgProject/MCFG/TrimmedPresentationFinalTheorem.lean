/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.TrimmedPresentationSampleMonotone

/-!
# TrimmedPresentationFinalTheorem.lean

Forty-fifth clean Lean experiment for the fixed-observation MCFG project.

`TrimmedPresentationSample.lean` and
`TrimmedPresentationSampleMonotone.lean` connected trimmed-presentation sample
data to the final reachable theorem.

This file gives that route stable names.

The final data package here starts from:

* a trimmed-presentation pre-core `D`;
* finite sample membership data for the witness words required by `D`;
* a universal named-context splicing constructor;
* the global fanout and fixed-observation substitutability assumptions.

From this, it exposes the same final conclusions:

* reachable Gold identification;
* eventual prefix-exact reconstruction;
* exact reconstruction for every positive finite superset.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section TrimmedFinalData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Final theorem data for the trimmed-presentation route.

This is the current most convenient endpoint for the route

```text
trimmed typed presentation
⇒ base representatives / pre-core
⇒ finite witness sample
⇒ final reachable theorem.
``` -/
structure TrimmedPresentationFinalData
    (D : TrimmedPresentationPreCoreData T f)
    (S : Finset (Word α)) where
  sampleData : TrimmedPresentationSampleData D S
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationFinalData

variable {S K : Finset (Word α)}

/-- The reachable pre-core induced by the trimmed-presentation data. -/
def toReachablePreCore
    (A : TrimmedPresentationFinalData D S) :
    ReachableBlueprintPreCore G obs f :=
  D.toReachablePreCore

/-- The reachable finite-sample package induced by the trimmed sample data. -/
def toReachablePreCoreFiniteSample
    (A : TrimmedPresentationFinalData D S) :
    ReachablePreCoreFiniteSample G S obs f A.toReachablePreCore :=
  A.sampleData.toReachablePreCoreFiniteSample

/-- The finite splicing package induced by the trimmed final data. -/
def toSplicingPackage
    (A : TrimmedPresentationFinalData D S) :
    ReachableSplicingPackage G S obs f :=
  A.sampleData.toSplicingPackage A.splicingConstructor

/-- The flat splicing blueprint induced by the trimmed final data. -/
def toSplicingBlueprint
    (A : TrimmedPresentationFinalData D S) :
    ReachableSplicingBlueprint G S obs f :=
  A.sampleData.toSplicingBlueprint A.splicingConstructor

/-- The flat splicing blueprint main-data package induced by the trimmed final
data. -/
def toSplicingBlueprintMainData
    (A : TrimmedPresentationFinalData D S) :
    ReachableSplicingBlueprintMainData G S obs f :=
  A.sampleData.toSplicingBlueprintMainData
    A.splicingConstructor A.fanout A.promise

/-- The final reachable-data package induced by the trimmed final data. -/
def toFinalReachableData
    (A : TrimmedPresentationFinalData D S) :
    FinalReachableData G S obs f :=
  A.sampleData.toFinalReachableData
    A.splicingConstructor A.fanout A.promise

/-- Monotonicity of trimmed final data under positive finite sample extension. -/
def mono
    (A : TrimmedPresentationFinalData D S)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    TrimmedPresentationFinalData D K where
  sampleData := A.sampleData.mono hSK hKpos
  splicingConstructor := A.splicingConstructor
  fanout := A.fanout
  promise := A.promise

@[simp] theorem mono_splicingConstructor
    (A : TrimmedPresentationFinalData D S)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (A.mono hSK hKpos).splicingConstructor =
      A.splicingConstructor :=
  rfl

@[simp] theorem mono_fanout
    (A : TrimmedPresentationFinalData D S)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (A.mono hSK hKpos).fanout = A.fanout :=
  rfl

@[simp] theorem mono_promise
    (A : TrimmedPresentationFinalData D S)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (A.mono hSK hKpos).promise = A.promise :=
  rfl

/-- Exact reconstruction for every positive finite superset of the trimmed
witness sample. -/
theorem exact_for_positive_superset
    (A : TrimmedPresentationFinalData D S)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  A.sampleData.exact_after_mono
    A.splicingConstructor A.fanout A.promise hSK hKpos

/-- Exact reconstruction at every positive-text prefix containing the trimmed
witness sample. -/
theorem exact_at_seen_prefix
    (A : TrimmedPresentationFinalData D S)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (S : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  A.sampleData.exact_at_prefix_via_mono
    A.splicingConstructor A.fanout A.promise Ttxt hseen

/-- Eventual prefix-exact reconstruction from trimmed-presentation final data. -/
theorem prefix_exact_eventually
    (A : TrimmedPresentationFinalData D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  A.sampleData.prefix_exact_via_mono
    A.splicingConstructor A.fanout A.promise

/-- Reachable Gold identification from trimmed-presentation final data. -/
theorem identifies_from_positive_text
    (A : TrimmedPresentationFinalData D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  A.sampleData.identifies_via_mono
    A.splicingConstructor A.fanout A.promise

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (A : TrimmedPresentationFinalData D S)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  A.identifies_from_positive_text Ttxt

/-- Characteristic-sample conclusion for the reachable learner. -/
theorem characteristic_sample
    (A : TrimmedPresentationFinalData D S) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      S
      G.StringLanguage :=
  A.toFinalReachableData.characteristic_sample

/-- Exactness of the monotone final data on the larger positive sample. -/
theorem exact_after_mono
    (A : TrimmedPresentationFinalData D S)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  (A.mono hSK hKpos).toFinalReachableData.exact_for_positive_superset
    (fun word hword => hword) hKpos

end TrimmedPresentationFinalData

end TrimmedFinalData


section MainTheoremsFromTrimmedPresentation

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S K : Finset (Word α)}

/-- Stable top-level reachable identification theorem for the
trimmed-presentation route. -/
theorem trimmed_presentation_reachable_identification
    (A : TrimmedPresentationFinalData D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  A.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem for the trimmed-presentation route. -/
theorem trimmed_presentation_reachable_prefix_exact
    (A : TrimmedPresentationFinalData D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  A.prefix_exact_eventually

/-- Stable top-level finite-superset exactness theorem for the
trimmed-presentation route. -/
theorem trimmed_presentation_exact_for_positive_superset
    (A : TrimmedPresentationFinalData D S)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  A.exact_for_positive_superset hSK hKpos

/-- Direct theorem from the raw trimmed sample-data fields, without explicitly
building the final-data wrapper. -/
theorem trimmed_sample_reachable_identification
    (H : TrimmedPresentationSampleData D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (TrimmedPresentationFinalData.mk H U hfan hL).identifies_from_positive_text

/-- Direct prefix-exact theorem from the raw trimmed sample-data fields. -/
theorem trimmed_sample_reachable_prefix_exact
    (H : TrimmedPresentationSampleData D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (TrimmedPresentationFinalData.mk H U hfan hL).prefix_exact_eventually

end MainTheoremsFromTrimmedPresentation

end MCFG
