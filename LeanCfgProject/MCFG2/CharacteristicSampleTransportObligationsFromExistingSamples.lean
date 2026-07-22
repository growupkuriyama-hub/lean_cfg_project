/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleTransportObligationsFromSample

/-!
# CharacteristicSampleTransportObligationsFromExistingSamples.lean

Seventy-third clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleTransportObligationsFromSample.lean` allowed the
start-word evidence required by transport obligations to be extracted from an
auxiliary positive finite sample containing the distinguished start word.

This file connects that interface to the characteristic-sample packages already
constructed earlier:

* `TrimmedPresentationWitnessSample`;
* `TrimmedPresentationCharacteristicSample`.

Thus, once we have either of those sample packages, we can build the exposing
or common-context transport obligation packages without separately supplying
`TrimmedPresentationStartWordEvidence`.

No new semantic principle is introduced here.  This is interface plumbing that
keeps the future `CS(G̃₀)` route short.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ExposingTransportFromWitnessSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

/-- Exposing-context transport obligations whose start-word evidence is
extracted from an existing witness-sample package. -/
structure TrimmedPresentationExposingTransportFromWitnessSample
    (D : TrimmedPresentationPreCoreData T f)
    (S : Finset (Word α)) where
  witnessSample : TrimmedPresentationWitnessSample D S

  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  exposingTransport : TrimmedPresentationExposingContextTransport D

  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationExposingTransportFromWitnessSample

/-- Start-word sample evidence extracted from the witness-sample package. -/
def toStartWordSampleEvidence
    (O : TrimmedPresentationExposingTransportFromWitnessSample D S) :
    TrimmedPresentationStartWordSampleEvidence D S :=
  O.witnessSample.toStartWordSampleEvidence

/-- Compact start-word evidence extracted from the witness-sample package. -/
def toStartWordEvidence
    (O : TrimmedPresentationExposingTransportFromWitnessSample D S) :
    TrimmedPresentationStartWordEvidence D :=
  O.witnessSample.toStartWordEvidence

/-- Convert to the from-sample exposing-transport obligation package. -/
def toObligationsFromSample
    (O : TrimmedPresentationExposingTransportFromWitnessSample D S) :
    TrimmedPresentationExposingTransportObligationsFromSample D S where
  baseNonterminals := O.baseNonterminals
  base_covers := O.base_covers
  arities := O.arities
  exposingTransport := O.exposingTransport
  startSampleEvidence := O.toStartWordSampleEvidence
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the compact exposing-transport obligation package. -/
def toObligations
    (O : TrimmedPresentationExposingTransportFromWitnessSample D S) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toObligationsFromSample.toExposingTransportObligations

/-- The finite sample produced by the resulting obligation package. -/
noncomputable def sample
    (O : TrimmedPresentationExposingTransportFromWitnessSample D S) :
    Finset (Word α) :=
  O.toObligations.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationExposingTransportFromWitnessSample D S) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toObligations.sample_positive

/-- The original witness sample supplies the distinguished start-word
positivity. -/
theorem startWord_positive
    (O : TrimmedPresentationExposingTransportFromWitnessSample D S) :
    D.startWord ∈ G.StringLanguage :=
  O.toStartWordSampleEvidence.startWord_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationExposingTransportFromWitnessSample D S) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toObligations.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (O : TrimmedPresentationExposingTransportFromWitnessSample D S) :
    FinalReachableData G O.sample obs f :=
  O.toObligations.toFinalReachableData

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationExposingTransportFromWitnessSample D S) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toObligations.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (O : TrimmedPresentationExposingTransportFromWitnessSample D S)
    {K : Finset (Word α)}
    (hOK : (O.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  O.toObligations.exact_for_positive_superset hOK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationExposingTransportFromWitnessSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toObligations.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationExposingTransportFromWitnessSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toObligations.identifies_from_positive_text

end TrimmedPresentationExposingTransportFromWitnessSample

end ExposingTransportFromWitnessSample


section CommonContextFromWitnessSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

/-- Common-context transport obligations whose start-word evidence is extracted
from an existing witness-sample package. -/
structure TrimmedPresentationCommonContextFromWitnessSample
    (D : TrimmedPresentationPreCoreData T f)
    (S : Finset (Word α)) where
  witnessSample : TrimmedPresentationWitnessSample D S
  commonData : TrimmedPresentationAnchorCommonContextCoreData D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationCommonContextFromWitnessSample

/-- Start-word sample evidence extracted from the witness-sample package. -/
def toStartWordSampleEvidence
    (O : TrimmedPresentationCommonContextFromWitnessSample D S) :
    TrimmedPresentationStartWordSampleEvidence D S :=
  O.witnessSample.toStartWordSampleEvidence

/-- Compact start-word evidence extracted from the witness-sample package. -/
def toStartWordEvidence
    (O : TrimmedPresentationCommonContextFromWitnessSample D S) :
    TrimmedPresentationStartWordEvidence D :=
  O.witnessSample.toStartWordEvidence

/-- Convert to the from-sample common-context obligation package. -/
def toObligationsFromSample
    (O : TrimmedPresentationCommonContextFromWitnessSample D S) :
    TrimmedPresentationCommonContextTransportObligationsFromSample D S where
  commonData := O.commonData
  startSampleEvidence := O.toStartWordSampleEvidence
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the compact common-context obligation package. -/
def toObligations
    (O : TrimmedPresentationCommonContextFromWitnessSample D S) :
    TrimmedPresentationCommonContextTransportObligations D :=
  O.toObligationsFromSample.toCommonContextTransportObligations

/-- Convert to exposing-transport obligations through the common-context route. -/
def toExposingTransportObligations
    (O : TrimmedPresentationCommonContextFromWitnessSample D S) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toObligations.toExposingTransportObligations

/-- The finite sample produced by the resulting obligation package. -/
noncomputable def sample
    (O : TrimmedPresentationCommonContextFromWitnessSample D S) :
    Finset (Word α) :=
  O.toObligations.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationCommonContextFromWitnessSample D S) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toObligations.sample_positive

/-- The original witness sample supplies distinguished start-word positivity. -/
theorem startWord_positive
    (O : TrimmedPresentationCommonContextFromWitnessSample D S) :
    D.startWord ∈ G.StringLanguage :=
  O.toStartWordSampleEvidence.startWord_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationCommonContextFromWitnessSample D S) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toObligations.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (O : TrimmedPresentationCommonContextFromWitnessSample D S) :
    FinalReachableData G O.sample obs f :=
  O.toObligations.toFinalReachableData

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationCommonContextFromWitnessSample D S) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toObligations.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (O : TrimmedPresentationCommonContextFromWitnessSample D S)
    {K : Finset (Word α)}
    (hOK : (O.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  O.toObligations.exact_for_positive_superset hOK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationCommonContextFromWitnessSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toObligations.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationCommonContextFromWitnessSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toObligations.identifies_from_positive_text

end TrimmedPresentationCommonContextFromWitnessSample

end CommonContextFromWitnessSample


section ExposingTransportFromCharacteristicSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Exposing-context transport obligations whose start-word evidence is
extracted from an existing characteristic-sample object. -/
structure TrimmedPresentationExposingTransportFromCharacteristicSample
    (D : TrimmedPresentationPreCoreData T f) where
  characteristicSample : TrimmedPresentationCharacteristicSample D

  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  exposingTransport : TrimmedPresentationExposingContextTransport D

  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationExposingTransportFromCharacteristicSample

variable {D : TrimmedPresentationPreCoreData T f}

/-- Start-word sample evidence extracted from the characteristic sample. -/
def toStartWordSampleEvidence
    (O : TrimmedPresentationExposingTransportFromCharacteristicSample D) :
    TrimmedPresentationStartWordSampleEvidence D
      O.characteristicSample.sample :=
  O.characteristicSample.toStartWordSampleEvidence

/-- Compact start-word evidence extracted from the characteristic sample. -/
def toStartWordEvidence
    (O : TrimmedPresentationExposingTransportFromCharacteristicSample D) :
    TrimmedPresentationStartWordEvidence D :=
  O.characteristicSample.toStartWordEvidence

/-- Convert to the from-sample exposing-transport obligation package. -/
def toObligationsFromSample
    (O : TrimmedPresentationExposingTransportFromCharacteristicSample D) :
    TrimmedPresentationExposingTransportObligationsFromSample D
      O.characteristicSample.sample where
  baseNonterminals := O.baseNonterminals
  base_covers := O.base_covers
  arities := O.arities
  exposingTransport := O.exposingTransport
  startSampleEvidence := O.toStartWordSampleEvidence
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the compact exposing-transport obligation package. -/
def toObligations
    (O : TrimmedPresentationExposingTransportFromCharacteristicSample D) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toObligationsFromSample.toExposingTransportObligations

/-- The finite sample produced by the resulting obligation package. -/
noncomputable def sample
    (O : TrimmedPresentationExposingTransportFromCharacteristicSample D) :
    Finset (Word α) :=
  O.toObligations.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationExposingTransportFromCharacteristicSample D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toObligations.sample_positive

/-- The characteristic sample supplies distinguished start-word positivity. -/
theorem startWord_positive
    (O : TrimmedPresentationExposingTransportFromCharacteristicSample D) :
    D.startWord ∈ G.StringLanguage :=
  O.toStartWordSampleEvidence.startWord_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationExposingTransportFromCharacteristicSample D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toObligations.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (O : TrimmedPresentationExposingTransportFromCharacteristicSample D) :
    FinalReachableData G O.sample obs f :=
  O.toObligations.toFinalReachableData

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationExposingTransportFromCharacteristicSample D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toObligations.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationExposingTransportFromCharacteristicSample D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toObligations.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationExposingTransportFromCharacteristicSample D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toObligations.identifies_from_positive_text

end TrimmedPresentationExposingTransportFromCharacteristicSample

end ExposingTransportFromCharacteristicSample


section CommonContextFromCharacteristicSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Common-context transport obligations whose start-word evidence is extracted
from an existing characteristic-sample object. -/
structure TrimmedPresentationCommonContextFromCharacteristicSample
    (D : TrimmedPresentationPreCoreData T f) where
  characteristicSample : TrimmedPresentationCharacteristicSample D
  commonData : TrimmedPresentationAnchorCommonContextCoreData D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationCommonContextFromCharacteristicSample

variable {D : TrimmedPresentationPreCoreData T f}

/-- Start-word sample evidence extracted from the characteristic sample. -/
def toStartWordSampleEvidence
    (O : TrimmedPresentationCommonContextFromCharacteristicSample D) :
    TrimmedPresentationStartWordSampleEvidence D
      O.characteristicSample.sample :=
  O.characteristicSample.toStartWordSampleEvidence

/-- Compact start-word evidence extracted from the characteristic sample. -/
def toStartWordEvidence
    (O : TrimmedPresentationCommonContextFromCharacteristicSample D) :
    TrimmedPresentationStartWordEvidence D :=
  O.characteristicSample.toStartWordEvidence

/-- Convert to the from-sample common-context obligation package. -/
def toObligationsFromSample
    (O : TrimmedPresentationCommonContextFromCharacteristicSample D) :
    TrimmedPresentationCommonContextTransportObligationsFromSample D
      O.characteristicSample.sample where
  commonData := O.commonData
  startSampleEvidence := O.toStartWordSampleEvidence
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the compact common-context obligation package. -/
def toObligations
    (O : TrimmedPresentationCommonContextFromCharacteristicSample D) :
    TrimmedPresentationCommonContextTransportObligations D :=
  O.toObligationsFromSample.toCommonContextTransportObligations

/-- Convert to exposing-transport obligations through the common-context route. -/
def toExposingTransportObligations
    (O : TrimmedPresentationCommonContextFromCharacteristicSample D) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toObligations.toExposingTransportObligations

/-- The finite sample produced by the resulting obligation package. -/
noncomputable def sample
    (O : TrimmedPresentationCommonContextFromCharacteristicSample D) :
    Finset (Word α) :=
  O.toObligations.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationCommonContextFromCharacteristicSample D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toObligations.sample_positive

/-- The characteristic sample supplies distinguished start-word positivity. -/
theorem startWord_positive
    (O : TrimmedPresentationCommonContextFromCharacteristicSample D) :
    D.startWord ∈ G.StringLanguage :=
  O.toStartWordSampleEvidence.startWord_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationCommonContextFromCharacteristicSample D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toObligations.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (O : TrimmedPresentationCommonContextFromCharacteristicSample D) :
    FinalReachableData G O.sample obs f :=
  O.toObligations.toFinalReachableData

/-- The produced finite sample is a characteristic sample for the reachable
learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationCommonContextFromCharacteristicSample D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toObligations.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationCommonContextFromCharacteristicSample D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toObligations.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationCommonContextFromCharacteristicSample D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toObligations.identifies_from_positive_text

end TrimmedPresentationCommonContextFromCharacteristicSample

end CommonContextFromCharacteristicSample


section MainTheoremsFromExistingSampleTransportObligations

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

/-- Stable top-level reachable identification theorem from exposing transport
and an existing witness-sample package. -/
theorem trimmed_exposing_transport_from_witness_sample_reachable_identification
    (O : TrimmedPresentationExposingTransportFromWitnessSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from exposing transport and an
existing witness-sample package. -/
theorem trimmed_exposing_transport_from_witness_sample_prefix_exact
    (O : TrimmedPresentationExposingTransportFromWitnessSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from common-context
transport and an existing witness-sample package. -/
theorem trimmed_common_context_from_witness_sample_reachable_identification
    (O : TrimmedPresentationCommonContextFromWitnessSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from common-context transport and an
existing witness-sample package. -/
theorem trimmed_common_context_from_witness_sample_prefix_exact
    (O : TrimmedPresentationCommonContextFromWitnessSample D S) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from exposing transport
and an existing characteristic-sample object. -/
theorem trimmed_exposing_transport_from_characteristic_sample_reachable_identification
    (O : TrimmedPresentationExposingTransportFromCharacteristicSample D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from exposing transport and an
existing characteristic-sample object. -/
theorem trimmed_exposing_transport_from_characteristic_sample_prefix_exact
    (O : TrimmedPresentationExposingTransportFromCharacteristicSample D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from common-context
transport and an existing characteristic-sample object. -/
theorem trimmed_common_context_from_characteristic_sample_reachable_identification
    (O : TrimmedPresentationCommonContextFromCharacteristicSample D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from common-context transport and an
existing characteristic-sample object. -/
theorem trimmed_common_context_from_characteristic_sample_prefix_exact
    (O : TrimmedPresentationCommonContextFromCharacteristicSample D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

end MainTheoremsFromExistingSampleTransportObligations

end MCFG
