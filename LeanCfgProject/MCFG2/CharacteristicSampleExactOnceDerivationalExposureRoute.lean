/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleExactOnceExposingTransportRoute
import LeanCfgProject.MCFG2.CharacteristicSampleRuleWitnessTransport

/-!
# CharacteristicSampleExactOnceDerivationalExposureRoute.lean

Replace the overly strong unconditional exposing-transport premise by the
semantic property used in the paper:

* every chosen anchor is genuinely derivable from its base nonterminal;
* the chosen exposing context accepts every tuple genuinely derivable from that
  nonterminal.

These derivational facts directly imply positivity of the terminal, binary, and
start-rule witness words.  Consequently they produce the existing
`TrimmedPresentationRuleWitnessTransport` package, and the concrete exact-once
splicing construction then yields characteristic samples, prefix-exact
reconstruction, and Gold identification.

No use is made of the false unrestricted `NamedContextSplicingConstructor`.
No theorem in this file uses `sorry`.
-/

namespace MCFG

universe u v w

section DerivationalExposure

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- The semantic exposing-context property actually used by the paper.

The first field records that each selected anchor is a genuine tuple derived by
its base nonterminal.  The second field records that the selected exposing
context accepts every tuple genuinely derived by that nonterminal.

Unlike `TrimmedPresentationExposingContextTransport`, this record makes no
claim about arbitrary non-derivable tuples having the same observation type as
an anchor. -/
structure TrimmedPresentationDerivationalExposure
    (D : TrimmedPresentationPreCoreData T f) where
  anchor_derives :
    ∀ A : N,
      DerivesTuple G A (D.anchor A)

  expose_accepts_derives :
    ∀ (A : N) {x : Tuple α (G.arity A)},
      DerivesTuple G A x →
        namedFill (G.arity A) (D.expose A) x ∈ G.StringLanguage

namespace TrimmedPresentationDerivationalExposure

variable {D : TrimmedPresentationPreCoreData T f}

/-- The anchor witness word is positive by derivability and universal exposure. -/
theorem anchorWitnessWord_positive
    (E : TrimmedPresentationDerivationalExposure D)
    (A : N) :
    D.anchorWitnessWord A ∈ G.StringLanguage := by
  exact E.expose_accepts_derives A (E.anchor_derives A)

/-- The distinguished start word is positive because the selected start anchor
is the singleton tuple of that word and is genuinely derivable. -/
theorem startWord_positive
    (E : TrimmedPresentationDerivationalExposure D) :
    D.startWord ∈ G.StringLanguage := by
  apply mem_StringLanguage_of_start_derives G D.startWord D.start_arity
  rw [← D.start_anchor_eq]
  exact E.anchor_derives G.start

/-- A terminal-rule witness tuple is genuinely derivable. -/
theorem terminalWitnessTuple_derives
    (E : TrimmedPresentationDerivationalExposure D)
    (A : TrimmedPresentationRuleAritySelectors D)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules) :
    DerivesTuple G ρ.lhs
      (castTuple (A.terminal_arity ρ hρ).symm ρ.outputTuple) :=
  DerivesTuple.terminal hρ (A.terminal_arity ρ hρ)

/-- A binary-rule witness tuple is genuinely derivable because both selected
child anchors are genuinely derivable. -/
theorem binaryWitnessTuple_derives
    (E : TrimmedPresentationDerivationalExposure D)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    DerivesTuple G ρ.lhs
      (ρ.apply (D.anchor ρ.left) (D.anchor ρ.right)) :=
  DerivesTuple.binary hρ
    (E.anchor_derives ρ.left)
    (E.anchor_derives ρ.right)

/-- A start-rule witness tuple is genuinely derivable from the selected child
anchor. -/
theorem startWitnessTuple_derives
    (E : TrimmedPresentationDerivationalExposure D)
    (A : TrimmedPresentationRuleAritySelectors D)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules) :
    DerivesTuple G G.start
      (castTuple (A.start_arity ρ hρ) (D.anchor ρ.child)) :=
  DerivesTuple.start hρ
    (E.anchor_derives ρ.child)
    (A.start_arity ρ hρ)

/-- Derivational exposure directly supplies all remaining rule-witness
positivity facts.  No unconditional same-type transport is needed. -/
def toRuleWitnessTransport
    (E : TrimmedPresentationDerivationalExposure D)
    (A : TrimmedPresentationRuleAritySelectors D) :
    TrimmedPresentationRuleWitnessTransport D A where
  terminal_positive := by
    intro ρ hρ
    exact E.expose_accepts_derives ρ.lhs
      (E.terminalWitnessTuple_derives A ρ hρ)

  binary_positive := by
    intro ρ hρ
    exact E.expose_accepts_derives ρ.lhs
      (E.binaryWitnessTuple_derives ρ hρ)

  start_positive := by
    intro ρ hρ
    exact E.expose_accepts_derives G.start
      (E.startWitnessTuple_derives A ρ hρ)

  startWord_positive := E.startWord_positive

end TrimmedPresentationDerivationalExposure

end DerivationalExposure


section DerivationalExposureData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Finite grammar-rule data whose semantic positivity is generated from
actual tuple derivations and exposing-context acceptance. -/
structure TrimmedPresentationDerivationalExposureData
    (D : TrimmedPresentationPreCoreData T f) where
  baseNonterminals : Finset N
  base_covers :
    ∀ A : N, A ∈ baseNonterminals

  arities : TrimmedPresentationRuleAritySelectors D
  semantics : TrimmedPresentationDerivationalExposure D

namespace TrimmedPresentationDerivationalExposureData

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert derivational exposure data to the existing grammar-rule transport
package. -/
def toGrammarRuleTransportData
    (P : TrimmedPresentationDerivationalExposureData D) :
    TrimmedPresentationGrammarRuleTransportData D where
  baseNonterminals := P.baseNonterminals
  base_covers := P.base_covers
  arities := P.arities
  transport := P.semantics.toRuleWitnessTransport P.arities

/-- The finite witness sample generated from the grammar's finite rule lists. -/
def sample
    (P : TrimmedPresentationDerivationalExposureData D) :
    Finset (Word α) :=
  P.toGrammarRuleTransportData.sample

/-- The generated finite sample is positive. -/
theorem sample_positive
    (P : TrimmedPresentationDerivationalExposureData D) :
    (P.sample : Set (Word α)) ⊆ G.StringLanguage :=
  P.toGrammarRuleTransportData.sample_positive

/-- The generated sample contains all witness words required by the trimmed
pre-core. -/
theorem contains_witnesses
    (P : TrimmedPresentationDerivationalExposureData D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (P.sample : Set (Word α)) :=
  P.toGrammarRuleTransportData.contains_witnesses

/-- View the generated witness sample as the sample data consumed by the
concrete exact-once route. -/
def exactSampleData
    (P : TrimmedPresentationDerivationalExposureData D) :
    TrimmedPresentationSampleData D P.sample :=
  P.toGrammarRuleTransportData.toWitnessSample.toSampleData

/-- Concrete exact-once splicing produces the reachable characteristic
blueprint from derivational exposure data. -/
def toExactReachableBlueprint
    (P : TrimmedPresentationDerivationalExposureData D)
    (hexact : G.BinaryRulesExactlyOnce) :
    ReachableCharacteristicBlueprint G P.sample obs f :=
  P.exactSampleData.toExactReachableBlueprint hexact

/-- The generated finite positive sample is characteristic for the reachable
learner. -/
theorem exact_characteristic_sample
    (P : TrimmedPresentationDerivationalExposureData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      P.sample
      G.StringLanguage :=
  P.exactSampleData.exact_characteristic_sample hexact hfan hL

/-- Exact reconstruction on every positive finite superset of the generated
sample. -/
theorem exact_for_positive_superset
    (P : TrimmedPresentationDerivationalExposureData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hPK : (P.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  P.exactSampleData.exact_reconstruction_for_positive_superset
    hexact hfan hL hPK hKpos

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem exact_prefix_reconstruction
    (P : TrimmedPresentationDerivationalExposureData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.exactSampleData.exact_prefix_reconstruction hexact hfan hL

/-- Gold identification from derivational exposure and concrete exact-once
splicing. -/
theorem exact_identifies_from_positive_text
    (P : TrimmedPresentationDerivationalExposureData D)
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
    (P : TrimmedPresentationDerivationalExposureData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveCharacteristicSampleConclusion G obs := by
  show ExistsBoundedPositiveCharacteristicSample G obs
  exact ⟨f, P.sample, P.sample_positive,
    P.exact_characteristic_sample hexact hfan hL⟩

/-- Paper-facing eventual prefix-exact conclusion. -/
theorem exact_paper_prefix_exact_theorem
    (P : TrimmedPresentationDerivationalExposureData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructivePrefixExactConclusion G obs := by
  show ExistsBoundedPrefixExactIdentification G obs
  exact ⟨f, P.exact_prefix_reconstruction hexact hfan hL⟩

/-- Corrected paper-facing identification theorem from derivational exposure.
The false unrestricted splicing constructor and the overly strong unconditional
exposing-transport premise are absent. -/
theorem exact_paper_main_theorem
    (P : TrimmedPresentationDerivationalExposureData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs := by
  show ExistsBoundedReachableIdentification G obs
  exact ⟨f, P.exact_identifies_from_positive_text hexact hfan hL⟩

/-- Complete paper-facing learning conclusion package. -/
theorem exact_paper_conclusion_package
    (P : TrimmedPresentationDerivationalExposureData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  ⟨P.exact_paper_characteristic_sample_theorem hexact hfan hL,
    P.exact_paper_prefix_exact_theorem hexact hfan hL,
    P.exact_paper_main_theorem hexact hfan hL⟩

/-- Version using the paper's exact working-condition package. -/
theorem exact_working_paper_main_theorem
    (P : TrimmedPresentationDerivationalExposureData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  P.exact_paper_main_theorem hworking.2 hfan hL

/-- Full conclusion package using exact working conditions. -/
theorem exact_working_paper_conclusion_package
    (P : TrimmedPresentationDerivationalExposureData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  P.exact_paper_conclusion_package hworking.2 hfan hL

end TrimmedPresentationDerivationalExposureData

end DerivationalExposureData


section DerivationalExposureTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable corrected endpoint from the paper-faithful derivational exposure
property and exact-once binary rules. -/
theorem trimmed_derivational_exposure_exact_once_main_theorem
    (P : TrimmedPresentationDerivationalExposureData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  P.exact_paper_main_theorem hexact hfan hL

/-- Stable full conclusion package from derivational exposure. -/
theorem trimmed_derivational_exposure_exact_once_conclusion_package
    (P : TrimmedPresentationDerivationalExposureData D)
    (hexact : G.BinaryRulesExactlyOnce)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  P.exact_paper_conclusion_package hexact hfan hL

/-- Stable endpoint using exact working conditions. -/
theorem trimmed_derivational_exposure_exact_working_main_theorem
    (P : TrimmedPresentationDerivationalExposureData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  P.exact_working_paper_main_theorem hworking hfan hL

/-- Stable full conclusion package using exact working conditions. -/
theorem trimmed_derivational_exposure_exact_working_conclusion_package
    (P : TrimmedPresentationDerivationalExposureData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  P.exact_working_paper_conclusion_package hworking hfan hL

end DerivationalExposureTopLevel

end MCFG
