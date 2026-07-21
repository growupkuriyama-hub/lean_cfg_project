/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleExactOnceMinimalPaperRoute
import LeanCfgProject.MCFG2.CharacteristicSampleExposingTransport

/-!
# CharacteristicSampleExactOnceExposingTransportRoute.lean

Connect the existing exposing-context transport route to the concrete
exact-once named-context splicing construction.

Unlike `PaperExactOnceMinimalPieces`, this route does not assume a fully built
positive grammar-rule sample.  Positivity of terminal, binary, and start-rule
witness words is obtained from
`TrimmedPresentationExposingContextTransport`; the resulting finite witness
sample is then sent through the concrete exact-once splicing construction.

Thus the route is

```text
trimmed pre-core
+ finite base-nonterminal cover
+ rule arity selectors
+ exposing-context transport
+ positive distinguished start word
+ exact-once binary rules
+ fanout / substitutability
=> finite positive characteristic sample
=> prefix exactness
=> Gold identification.
```

No theorem in this file uses the false unrestricted
`NamedContextSplicingConstructor` premise.
-/

namespace MCFG

universe u v w

section ExactOnceExposingTransport

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

namespace TrimmedPresentationExposingTransportData

/-- The sample data constructed from exposing-context transport.  Terminal,
binary, and start witness positivity are supplied by the transport theorem,
not assumed through a pre-built `TrimmedPresentationGrammarRuleBuilder`. -/
def exactSampleData
    (P : TrimmedPresentationExposingTransportData D) :
    TrimmedPresentationSampleData D P.sample :=
  P.toGrammarRuleTransportData.toWitnessSample.toSampleData

/-- Concrete exact-once splicing turns exposing-transport sample data into the
reachable characteristic blueprint. -/
def toExactReachableBlueprint
    (P : TrimmedPresentationExposingTransportData D)
    (hexact : G.BinaryRulesExactlyOnce) :
    ReachableCharacteristicBlueprint G P.sample obs f :=
  P.exactSampleData.toExactReachableBlueprint hexact

/-- The exposing-transport sample is characteristic for the reachable learner
once the listed binary rules are exact-once. -/
theorem exact_characteristic_sample
    (P : TrimmedPresentationExposingTransportData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      P.sample
      G.StringLanguage :=
  P.exactSampleData.exact_characteristic_sample hexact hfan hL

/-- Exact reconstruction holds for every positive finite superset of the
sample generated from exposing-context transport. -/
theorem exact_for_positive_superset
    (P : TrimmedPresentationExposingTransportData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hPK : (P.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  P.exactSampleData.exact_reconstruction_for_positive_superset
    hexact hfan hL hPK hKpos

/-- Eventual prefix-exact reconstruction from exposing-context transport and
concrete exact-once splicing. -/
theorem exact_prefix_reconstruction
    (P : TrimmedPresentationExposingTransportData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.exactSampleData.exact_prefix_reconstruction hexact hfan hL

/-- Gold identification from exposing-context transport and concrete
exact-once splicing. -/
theorem exact_identifies_from_positive_text
    (P : TrimmedPresentationExposingTransportData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  P.exactSampleData.exact_identifies_from_positive_text hexact hfan hL

/-- Paper-facing finite positive characteristic-sample conclusion. -/
theorem exact_paper_characteristic_sample_theorem
    (P : TrimmedPresentationExposingTransportData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveCharacteristicSampleConclusion G obs := by
  show ExistsBoundedPositiveCharacteristicSample G obs
  exact ⟨f, P.sample, P.sample_positive,
    P.exact_characteristic_sample hexact hfan hL⟩

/-- Paper-facing eventual prefix-exact conclusion. -/
theorem exact_paper_prefix_exact_theorem
    (P : TrimmedPresentationExposingTransportData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructivePrefixExactConclusion G obs := by
  show ExistsBoundedPrefixExactIdentification G obs
  exact ⟨f, P.exact_prefix_reconstruction hexact hfan hL⟩

/-- Corrected paper-facing identification theorem from exposing-context
transport.  The unrestricted splicing constructor is not an assumption. -/
theorem exact_paper_main_theorem
    (P : TrimmedPresentationExposingTransportData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs := by
  show ExistsBoundedReachableIdentification G obs
  exact ⟨f, P.exact_identifies_from_positive_text hexact hfan hL⟩

/-- Complete corrected paper-facing conclusion package. -/
theorem exact_paper_conclusion_package
    (P : TrimmedPresentationExposingTransportData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  ⟨P.exact_paper_characteristic_sample_theorem hexact hfan hL,
    P.exact_paper_prefix_exact_theorem hexact hfan hL,
    P.exact_paper_main_theorem hexact hfan hL⟩

/-- Version phrased with the paper's exact working-condition package. -/
theorem exact_working_paper_main_theorem
    (P : TrimmedPresentationExposingTransportData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  P.exact_paper_main_theorem hworking.2 hfan hL

/-- Full conclusion package phrased with exact working conditions. -/
theorem exact_working_paper_conclusion_package
    (P : TrimmedPresentationExposingTransportData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  P.exact_paper_conclusion_package hworking.2 hfan hL

end TrimmedPresentationExposingTransportData

end ExactOnceExposingTransport


section ExactOnceExposingTransportTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable exact-once endpoint from exposing-context transport. -/
theorem trimmed_exposing_transport_exact_once_main_theorem
    (P : TrimmedPresentationExposingTransportData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  P.exact_paper_main_theorem hexact hfan hL

/-- Stable full conclusion package from exposing-context transport. -/
theorem trimmed_exposing_transport_exact_once_conclusion_package
    (P : TrimmedPresentationExposingTransportData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  P.exact_paper_conclusion_package hexact hfan hL

/-- Stable endpoint using exact working conditions. -/
theorem trimmed_exposing_transport_exact_working_main_theorem
    (P : TrimmedPresentationExposingTransportData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  P.exact_working_paper_main_theorem hworking hfan hL

/-- Stable full conclusion package using exact working conditions. -/
theorem trimmed_exposing_transport_exact_working_conclusion_package
    (P : TrimmedPresentationExposingTransportData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  P.exact_working_paper_conclusion_package hworking hfan hL

end ExactOnceExposingTransportTopLevel

end MCFG
