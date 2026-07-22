/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleTransportObligationsFromExistingSamples

/-!
# CharacteristicSampleTransportObligationsFromBuilders.lean

Seventy-fourth clean Lean experiment for the fixed-observation MCFG project.

The preceding file connected transport obligations to existing witness-sample
and characteristic-sample packages.  This file moves one step closer to the
future concrete `CS(G̃₀)` construction by connecting transport obligations to
the finite-builder interfaces:

* `TrimmedPresentationFiniteSampleBuilder`;
* `TrimmedPresentationPositiveFiniteUnionBuilder`.

A finite builder plus positivity gives a witness sample.  A positive finite
union builder already gives a witness sample.  Therefore both can supply the
start-word evidence required by the transport-obligation routes.

No new semantic principle is introduced here.  This is another interface layer:
it lets future concrete enumeration files enter the final theorem through the
builder objects directly.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ExposingTransportFromFiniteBuilder

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Exposing-context transport obligations whose start-word evidence is
extracted from a positive finite sample builder. -/
structure TrimmedPresentationExposingTransportFromFiniteBuilder
    (D : TrimmedPresentationPreCoreData T f) where
  builder : TrimmedPresentationFiniteSampleBuilder D
  positive : (builder.sample : Set (Word α)) ⊆ G.StringLanguage

  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  exposingTransport : TrimmedPresentationExposingContextTransport D

  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationExposingTransportFromFiniteBuilder

variable {D : TrimmedPresentationPreCoreData T f}

/-- The witness sample obtained from the finite builder and positivity. -/
def toWitnessSample
    (O : TrimmedPresentationExposingTransportFromFiniteBuilder D) :
    TrimmedPresentationWitnessSample D O.builder.sample :=
  O.builder.toWitnessSample O.positive

/-- The characteristic-sample object obtained from the finite builder and
positivity. -/
def toCharacteristicSample
    (O : TrimmedPresentationExposingTransportFromFiniteBuilder D) :
    TrimmedPresentationCharacteristicSample D :=
  O.builder.toCharacteristicSample O.positive

/-- Convert to the existing witness-sample transport route. -/
def toTransportFromWitnessSample
    (O : TrimmedPresentationExposingTransportFromFiniteBuilder D) :
    TrimmedPresentationExposingTransportFromWitnessSample
      D O.builder.sample where
  witnessSample := O.toWitnessSample
  baseNonterminals := O.baseNonterminals
  base_covers := O.base_covers
  arities := O.arities
  exposingTransport := O.exposingTransport
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the from-sample exposing-transport obligation package. -/
def toObligationsFromSample
    (O : TrimmedPresentationExposingTransportFromFiniteBuilder D) :
    TrimmedPresentationExposingTransportObligationsFromSample
      D O.builder.sample :=
  O.toTransportFromWitnessSample.toObligationsFromSample

/-- Convert to the compact exposing-transport obligation package. -/
def toObligations
    (O : TrimmedPresentationExposingTransportFromFiniteBuilder D) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toTransportFromWitnessSample.toObligations

/-- The finite sample produced by the resulting obligation package. -/
noncomputable def sample
    (O : TrimmedPresentationExposingTransportFromFiniteBuilder D) :
    Finset (Word α) :=
  O.toTransportFromWitnessSample.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationExposingTransportFromFiniteBuilder D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toTransportFromWitnessSample.sample_positive

/-- The builder positivity supplies distinguished start-word positivity. -/
theorem startWord_positive
    (O : TrimmedPresentationExposingTransportFromFiniteBuilder D) :
    D.startWord ∈ G.StringLanguage :=
  O.toTransportFromWitnessSample.startWord_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationExposingTransportFromFiniteBuilder D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toTransportFromWitnessSample.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (O : TrimmedPresentationExposingTransportFromFiniteBuilder D) :
    FinalReachableData G O.sample obs f :=
  O.toTransportFromWitnessSample.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationExposingTransportFromFiniteBuilder D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toTransportFromWitnessSample.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (O : TrimmedPresentationExposingTransportFromFiniteBuilder D)
    {K : Finset (Word α)}
    (hOK : (O.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  O.toTransportFromWitnessSample.exact_for_positive_superset hOK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationExposingTransportFromFiniteBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toTransportFromWitnessSample.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationExposingTransportFromFiniteBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toTransportFromWitnessSample.identifies_from_positive_text

end TrimmedPresentationExposingTransportFromFiniteBuilder

end ExposingTransportFromFiniteBuilder


section CommonContextFromFiniteBuilder

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Common-context transport obligations whose start-word evidence is extracted
from a positive finite sample builder. -/
structure TrimmedPresentationCommonContextFromFiniteBuilder
    (D : TrimmedPresentationPreCoreData T f) where
  builder : TrimmedPresentationFiniteSampleBuilder D
  positive : (builder.sample : Set (Word α)) ⊆ G.StringLanguage

  commonData : TrimmedPresentationAnchorCommonContextCoreData D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationCommonContextFromFiniteBuilder

variable {D : TrimmedPresentationPreCoreData T f}

/-- The witness sample obtained from the finite builder and positivity. -/
def toWitnessSample
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D) :
    TrimmedPresentationWitnessSample D O.builder.sample :=
  O.builder.toWitnessSample O.positive

/-- The characteristic-sample object obtained from the finite builder and
positivity. -/
def toCharacteristicSample
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D) :
    TrimmedPresentationCharacteristicSample D :=
  O.builder.toCharacteristicSample O.positive

/-- Convert to the existing witness-sample common-context route. -/
def toTransportFromWitnessSample
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D) :
    TrimmedPresentationCommonContextFromWitnessSample
      D O.builder.sample where
  witnessSample := O.toWitnessSample
  commonData := O.commonData
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert to the from-sample common-context obligation package. -/
def toObligationsFromSample
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D) :
    TrimmedPresentationCommonContextTransportObligationsFromSample
      D O.builder.sample :=
  O.toTransportFromWitnessSample.toObligationsFromSample

/-- Convert to the compact common-context obligation package. -/
def toObligations
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D) :
    TrimmedPresentationCommonContextTransportObligations D :=
  O.toTransportFromWitnessSample.toObligations

/-- Convert to exposing-transport obligations through the common-context route. -/
def toExposingTransportObligations
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toTransportFromWitnessSample.toExposingTransportObligations

/-- The finite sample produced by the resulting obligation package. -/
noncomputable def sample
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D) :
    Finset (Word α) :=
  O.toTransportFromWitnessSample.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toTransportFromWitnessSample.sample_positive

/-- The builder positivity supplies distinguished start-word positivity. -/
theorem startWord_positive
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D) :
    D.startWord ∈ G.StringLanguage :=
  O.toTransportFromWitnessSample.startWord_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toTransportFromWitnessSample.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D) :
    FinalReachableData G O.sample obs f :=
  O.toTransportFromWitnessSample.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toTransportFromWitnessSample.characteristic_sample

/-- Exact reconstruction for every positive finite superset of the produced
sample. -/
theorem exact_for_positive_superset
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D)
    {K : Finset (Word α)}
    (hOK : (O.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  O.toTransportFromWitnessSample.exact_for_positive_superset hOK hKpos

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toTransportFromWitnessSample.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toTransportFromWitnessSample.identifies_from_positive_text

end TrimmedPresentationCommonContextFromFiniteBuilder

end CommonContextFromFiniteBuilder


section ExposingTransportFromPositiveFiniteUnionBuilder

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Exposing-context transport obligations whose start-word evidence is
extracted from a positive finite-union builder. -/
structure TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder
    (D : TrimmedPresentationPreCoreData T f) where
  unionBuilder : TrimmedPresentationPositiveFiniteUnionBuilder D

  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  exposingTransport : TrimmedPresentationExposingContextTransport D

  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder

variable {D : TrimmedPresentationPreCoreData T f}

/-- The finite sample builder underlying the positive union builder. -/
def toFiniteSampleBuilder
    (O : TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder D) :
    TrimmedPresentationFiniteSampleBuilder D :=
  O.unionBuilder.toFiniteSampleBuilder

/-- Convert to the finite-builder transport route. -/
def toTransportFromFiniteBuilder
    (O : TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder D) :
    TrimmedPresentationExposingTransportFromFiniteBuilder D where
  builder := O.toFiniteSampleBuilder
  positive := by
    simpa [toFiniteSampleBuilder,
      TrimmedPresentationPositiveFiniteUnionBuilder.toFiniteSampleBuilder_sample]
      using O.unionBuilder.sample_positive
  baseNonterminals := O.baseNonterminals
  base_covers := O.base_covers
  arities := O.arities
  exposingTransport := O.exposingTransport
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert directly to the witness-sample transport route. -/
def toTransportFromWitnessSample
    (O : TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder D) :
    TrimmedPresentationExposingTransportFromWitnessSample
      D O.toFiniteSampleBuilder.sample :=
  O.toTransportFromFiniteBuilder.toTransportFromWitnessSample

/-- The finite sample produced by the resulting obligation package. -/
noncomputable def sample
    (O : TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder D) :
    Finset (Word α) :=
  O.toTransportFromFiniteBuilder.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toTransportFromFiniteBuilder.sample_positive

/-- The union builder supplies distinguished start-word positivity. -/
theorem startWord_positive
    (O : TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder D) :
    D.startWord ∈ G.StringLanguage :=
  O.toTransportFromFiniteBuilder.startWord_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toTransportFromFiniteBuilder.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (O : TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder D) :
    FinalReachableData G O.sample obs f :=
  O.toTransportFromFiniteBuilder.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toTransportFromFiniteBuilder.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toTransportFromFiniteBuilder.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toTransportFromFiniteBuilder.identifies_from_positive_text

end TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder

end ExposingTransportFromPositiveFiniteUnionBuilder


section CommonContextFromPositiveFiniteUnionBuilder

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Common-context transport obligations whose start-word evidence is extracted
from a positive finite-union builder. -/
structure TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder
    (D : TrimmedPresentationPreCoreData T f) where
  unionBuilder : TrimmedPresentationPositiveFiniteUnionBuilder D

  commonData : TrimmedPresentationAnchorCommonContextCoreData D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder

variable {D : TrimmedPresentationPreCoreData T f}

/-- The finite sample builder underlying the positive union builder. -/
def toFiniteSampleBuilder
    (O : TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder D) :
    TrimmedPresentationFiniteSampleBuilder D :=
  O.unionBuilder.toFiniteSampleBuilder

/-- Convert to the finite-builder common-context route. -/
def toTransportFromFiniteBuilder
    (O : TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder D) :
    TrimmedPresentationCommonContextFromFiniteBuilder D where
  builder := O.toFiniteSampleBuilder
  positive := by
    simpa [toFiniteSampleBuilder,
      TrimmedPresentationPositiveFiniteUnionBuilder.toFiniteSampleBuilder_sample]
      using O.unionBuilder.sample_positive
  commonData := O.commonData
  splicingConstructor := O.splicingConstructor
  fanout := O.fanout
  promise := O.promise

/-- Convert directly to the witness-sample common-context route. -/
def toTransportFromWitnessSample
    (O : TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder D) :
    TrimmedPresentationCommonContextFromWitnessSample
      D O.toFiniteSampleBuilder.sample :=
  O.toTransportFromFiniteBuilder.toTransportFromWitnessSample

/-- Convert to exposing-transport obligations through the common-context route. -/
def toExposingTransportObligations
    (O : TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder D) :
    TrimmedPresentationExposingTransportObligations D :=
  O.toTransportFromFiniteBuilder.toExposingTransportObligations

/-- The finite sample produced by the resulting obligation package. -/
noncomputable def sample
    (O : TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder D) :
    Finset (Word α) :=
  O.toTransportFromFiniteBuilder.sample

/-- The produced finite sample is positive. -/
theorem sample_positive
    (O : TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder D) :
    (O.sample : Set (Word α)) ⊆ G.StringLanguage :=
  O.toTransportFromFiniteBuilder.sample_positive

/-- The union builder supplies distinguished start-word positivity. -/
theorem startWord_positive
    (O : TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder D) :
    D.startWord ∈ G.StringLanguage :=
  O.toTransportFromFiniteBuilder.startWord_positive

/-- The produced finite sample contains all required witness words. -/
theorem contains_witnesses
    (O : TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (O.sample : Set (Word α)) :=
  O.toTransportFromFiniteBuilder.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (O : TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder D) :
    FinalReachableData G O.sample obs f :=
  O.toTransportFromFiniteBuilder.toFinalReachableData

/-- The produced sample is a characteristic sample for the reachable learner. -/
theorem characteristic_sample
    (O : TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      O.sample
      G.StringLanguage :=
  O.toTransportFromFiniteBuilder.characteristic_sample

/-- Eventual prefix-exact reconstruction. -/
theorem prefix_exact_eventually
    (O : TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.toTransportFromFiniteBuilder.prefix_exact_eventually

/-- Reachable Gold identification. -/
theorem identifies_from_positive_text
    (O : TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.toTransportFromFiniteBuilder.identifies_from_positive_text

end TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder

end CommonContextFromPositiveFiniteUnionBuilder


section MainTheoremsFromBuilderTransportObligations

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from exposing transport
and a positive finite sample builder. -/
theorem trimmed_exposing_transport_from_finite_builder_reachable_identification
    (O : TrimmedPresentationExposingTransportFromFiniteBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from exposing transport and a
positive finite sample builder. -/
theorem trimmed_exposing_transport_from_finite_builder_prefix_exact
    (O : TrimmedPresentationExposingTransportFromFiniteBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from common-context
transport and a positive finite sample builder. -/
theorem trimmed_common_context_from_finite_builder_reachable_identification
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from common-context transport and a
positive finite sample builder. -/
theorem trimmed_common_context_from_finite_builder_prefix_exact
    (O : TrimmedPresentationCommonContextFromFiniteBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from exposing transport
and a positive finite-union builder. -/
theorem trimmed_exposing_transport_from_positive_union_reachable_identification
    (O : TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from exposing transport and a positive
finite-union builder. -/
theorem trimmed_exposing_transport_from_positive_union_prefix_exact
    (O : TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

/-- Stable top-level reachable identification theorem from common-context
transport and a positive finite-union builder. -/
theorem trimmed_common_context_from_positive_union_reachable_identification
    (O : TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  O.identifies_from_positive_text

/-- Stable top-level prefix-exact theorem from common-context transport and a
positive finite-union builder. -/
theorem trimmed_common_context_from_positive_union_prefix_exact
    (O : TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  O.prefix_exact_eventually

end MainTheoremsFromBuilderTransportObligations

end MCFG
