/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.OutputTypeTrimmedPresentationSuccessfulOccurrenceConstruction

/-!
# CharacteristicSampleExactOnceSuccessfulPresentationRoute.lean

The preceding file constructs all typed anchors and exposing contexts of a
`TrimmedOutputTypePresentation` from explicit successful derivation
occurrences.  The remaining characteristic-sample route, however, is indexed
by the original base nonterminals and expects a
`TrimmedPresentationPreCoreData`.

This file supplies that bridge.

For every base nonterminal, choose one present typed representative.  Its
successful-occurrence anchor and exposing context are transported along the
representative's base equality.  This constructs:

```lean
TrimmedBaseRepresentatives T
```

without separately assuming base-indexed anchors or exposure positivity.

The only rule-level information required is output-type compatibility of the
chosen representatives:

* a terminal lhs representative has the terminal output type;
* a binary lhs representative has the template-computed output type of the
  chosen child representatives;
* the chosen start representative and start-rule child representative have
  the same transported output type.

From these typed-output equations, the concrete anchor type equations required
by `TrimmedPresentationPreCoreData` are derived using
`BinaryRule.outputType_sound` and transport of `tupleType`.

The start word is extracted canonically from the selected start anchor using
the start-arity-one condition.  The successful typed occurrences are then
transported to base-indexed successful occurrences, producing the exact-once
finite characteristic sample and the paper-facing Gold-identification theorem.

No unrestricted named-context splicing constructor or unconditional exposing
transport is used.
-/

namespace MCFG

universe u v w

section TransportLemmas

variable {N : Type v} {α : Type u} {M : Type w}
variable [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Componentwise tuple observation commutes with transport of the tuple
arity. -/
theorem tupleType_castTuple_transport
    {d e : Nat}
    (h : d = e)
    (x : Tuple α d) :
    tupleType obs (castTuple h x) =
      castTuple h (tupleType obs x) := by
  cases h
  rfl

namespace ExactSuccessfulDerivationOccurrence

/-- Transport a successful occurrence along equality of its base
nonterminal. -/
def transportNonterminal
    {A B : N}
    (h : A = B)
    {x : Tuple α (G.arity A)}
    {c : NamedSentenceContext α (G.arity A)}
    (O : ExactSuccessfulDerivationOccurrence G A x c) :
    ExactSuccessfulDerivationOccurrence G B
      (castTuple (congrArg G.arity h) x)
      (transportNamedSentenceContext
        (congrArg G.arity h) c) := by
  cases h
  exact O

@[simp] theorem transportNonterminal_rfl
    {A : N}
    {x : Tuple α (G.arity A)}
    {c : NamedSentenceContext α (G.arity A)}
    (O : ExactSuccessfulDerivationOccurrence G A x c) :
    O.transportNonterminal (rfl : A = A) = O :=
  rfl

end ExactSuccessfulDerivationOccurrence

end TransportLemmas


section BaseRepresentativeSelection

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable
  (S : SuccessfulOccurrenceCompletePresentation G obs)

/-- One present typed representative for every base nonterminal.

The anchors and exposing contexts are not fields: they are obtained from the
successful occurrences already stored by `S`. -/
structure SuccessfulOccurrenceBaseRepresentativeSelection where
  rep :
    ∀ A : N,
      PresentTypedNonterminal
        S.completePresentation.presentation

  rep_base_eq :
    ∀ A : N,
      (rep A).node.base = A

namespace SuccessfulOccurrenceBaseRepresentativeSelection

variable {S : SuccessfulOccurrenceCompletePresentation G obs}

/-- Equality of the representative arity with its selected base arity. -/
def repArityEq
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (A : N) :
    G.arity (R.rep A).node.base = G.arity A :=
  congrArg G.arity (R.rep_base_eq A)

/-- The selected typed anchor before transport to the base index. -/
def typedAnchor
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (A : N) :
    Tuple α (G.arity (R.rep A).node.base) :=
  S.toTrimmedOutputTypePresentation.anchor (R.rep A)

/-- The selected typed exposing context before transport to the base index. -/
def typedExpose
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (A : N) :
    NamedSentenceContext α (G.arity (R.rep A).node.base) :=
  S.toTrimmedOutputTypePresentation.expose (R.rep A)

/-- The selected anchor transported to the original base nonterminal. -/
def anchor
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (A : N) :
    Tuple α (G.arity A) :=
  castTuple (R.repArityEq A) (R.typedAnchor A)

/-- The selected exposing context transported to the original base
nonterminal. -/
def expose
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (A : N) :
    NamedSentenceContext α (G.arity A) :=
  transportNamedSentenceContext
    (R.repArityEq A) (R.typedExpose A)

/-- The representative's stored output type transported to the selected base
arity. -/
def transportedOutput
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (A : N) :
    Tuple M (G.arity A) :=
  castTuple (R.repArityEq A) (R.rep A).node.out

/-- The transported base anchor has the transported output type of its selected
typed representative. -/
theorem anchor_tupleType
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (A : N) :
    tupleType obs (R.anchor A) =
      R.transportedOutput A := by
  unfold anchor transportedOutput typedAnchor
  rw [tupleType_castTuple_transport]
  exact congrArg (castTuple (R.repArityEq A))
    (S.completePresentation.withSuccessfulOccurrences_anchor_tupleType
      S.occurrences (R.rep A))

/-- The transported exposing context accepts the transported anchor. -/
theorem expose_accepts_anchor
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (A : N) :
    namedFill (G.arity A) (R.expose A) (R.anchor A) ∈
      G.StringLanguage := by
  unfold expose anchor
  rw [namedFill_transportNamedSentenceContext]
  exact (S.anchor_occurrence (R.rep A)).accepts

/-- Construct the base-indexed representatives used by the pre-core layer. -/
def toTrimmedBaseRepresentatives
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S) :
    TrimmedBaseRepresentatives
      S.toTrimmedOutputTypePresentation where
  rep := R.rep
  rep_base_eq := R.rep_base_eq
  anchor := R.anchor
  expose := R.expose
  anchor_matches_rep := R.anchor_tupleType
  expose_accepts := R.expose_accepts_anchor

/-- The selected successful typed occurrence transported to its base
nonterminal. -/
def baseOccurrence
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S)
    (A : N) :
    ExactSuccessfulDerivationOccurrence G A
      (R.anchor A) (R.expose A) :=
  (S.anchor_occurrence (R.rep A)).transportNonterminal
    (R.rep_base_eq A)

end SuccessfulOccurrenceBaseRepresentativeSelection

end BaseRepresentativeSelection


section RepresentativeOutputCompatibility

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {S : SuccessfulOccurrenceCompletePresentation G obs}

/-- Rule-level compatibility of a base representative selection.

These fields concern only the stored output types of selected typed
nonterminals.  The tuple-specific pre-core equations are derived later from
the successful-occurrence anchors. -/
structure SuccessfulOccurrenceRepresentativeOutputCompatibility
    (R : SuccessfulOccurrenceBaseRepresentativeSelection S) where

  terminal_output :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        R.transportedOutput ρ.lhs =
          tupleType obs
            (castTuple hwt.symm ρ.outputTuple)

  binary_output :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        R.transportedOutput ρ.lhs =
          BinaryRule.outputType obs ρ
            (R.transportedOutput ρ.left)
            (R.transportedOutput ρ.right)

  start_output :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        R.transportedOutput G.start =
          castTuple hwt
            (R.transportedOutput ρ.child)

end RepresentativeOutputCompatibility


section SuccessfulPresentationConstruction

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

/-- A complete output-type presentation with successful typed occurrences,
one selected typed representative for every base nonterminal, and rule-level
compatibility of the selected output types. -/
structure SuccessfulOccurrencePreCoreConstruction
    (G : WorkingMCFG N α)
    (obs : α → M) where

  presentation :
    SuccessfulOccurrenceCompletePresentation G obs

  representatives :
    SuccessfulOccurrenceBaseRepresentativeSelection presentation

  compatibility :
    SuccessfulOccurrenceRepresentativeOutputCompatibility representatives

namespace SuccessfulOccurrencePreCoreConstruction

/-- The witness-bearing trimmed presentation generated by successful typed
occurrences. -/
def trimmedPresentation
    (C : SuccessfulOccurrencePreCoreConstruction G obs) :
    TrimmedOutputTypePresentation G obs :=
  C.presentation.toTrimmedOutputTypePresentation

/-- The base-indexed representative object generated from the selected typed
representatives. -/
def baseRepresentatives
    (C : SuccessfulOccurrencePreCoreConstruction G obs) :
    TrimmedBaseRepresentatives C.trimmedPresentation :=
  C.representatives.toTrimmedBaseRepresentatives

/-- Canonical start word extracted from the selected start anchor. -/
def startWord
    (C : SuccessfulOccurrencePreCoreConstruction G obs)
    (hworking : G.BasicWorkingConditions) :
    Word α :=
  tupleWordOfArityOne hworking.1.symm
    (C.representatives.anchor G.start)

/-- Construct the full trimmed-presentation pre-core.

The terminal, binary, and start tuple-type equations are consequences of
representative output compatibility; they are not supplied as tuple-specific
fields. -/
def toPreCoreData
    (C : SuccessfulOccurrencePreCoreConstruction G obs)
    (hworking : G.BasicWorkingConditions) :
    TrimmedPresentationPreCoreData C.trimmedPresentation f where

  representatives := C.baseRepresentatives

  terminal_type_eq := by
    intro ρ hρ hwt
    calc
      tupleType obs (C.representatives.anchor ρ.lhs) =
          C.representatives.transportedOutput ρ.lhs :=
        C.representatives.anchor_tupleType ρ.lhs
      _ =
          tupleType obs
            (castTuple hwt.symm ρ.outputTuple) :=
        C.compatibility.terminal_output ρ hρ hwt

  binary_type_eq := by
    intro ρ hρ
    calc
      tupleType obs (C.representatives.anchor ρ.lhs) =
          C.representatives.transportedOutput ρ.lhs :=
        C.representatives.anchor_tupleType ρ.lhs
      _ =
          BinaryRule.outputType obs ρ
            (C.representatives.transportedOutput ρ.left)
            (C.representatives.transportedOutput ρ.right) :=
        C.compatibility.binary_output ρ hρ
      _ =
          tupleType obs
            (ρ.apply
              (C.representatives.anchor ρ.left)
              (C.representatives.anchor ρ.right)) :=
        (BinaryRule.outputType_sound obs ρ
          (C.representatives.anchor_tupleType ρ.left)
          (C.representatives.anchor_tupleType ρ.right)).symm

  start_type_eq := by
    intro ρ hρ hwt
    calc
      tupleType obs (C.representatives.anchor G.start) =
          C.representatives.transportedOutput G.start :=
        C.representatives.anchor_tupleType G.start
      _ =
          castTuple hwt
            (C.representatives.transportedOutput ρ.child) :=
        C.compatibility.start_output ρ hρ hwt
      _ =
          tupleType obs
            (castTuple hwt
              (C.representatives.anchor ρ.child)) := by
        rw [tupleType_castTuple_transport]
        rw [C.representatives.anchor_tupleType]

  startWord := C.startWord hworking
  start_arity := hworking.1.symm
  start_anchor_eq := by
    exact
      (castTuple_singleton_tupleWordOfArityOne
        hworking.1.symm
        (C.representatives.anchor G.start)).symm

/-- The base-indexed successful occurrence data belonging to the constructed
pre-core. -/
def toSuccessfulOccurrenceData
    (C : SuccessfulOccurrencePreCoreConstruction G obs)
    (hworking : G.BasicWorkingConditions) :
    TrimmedPresentationSuccessfulOccurrenceData
      (C.toPreCoreData (f := f) hworking) where
  occurrence := by
    intro A
    exact C.representatives.baseOccurrence A

/-- The constructed base anchors are genuinely derivable. -/
theorem anchor_derives
    (C : SuccessfulOccurrencePreCoreConstruction G obs)
    (hworking : G.BasicWorkingConditions)
    (A : N) :
    DerivesTuple G A
      ((C.toPreCoreData (f := f) hworking).anchor A) :=
  ((C.toSuccessfulOccurrenceData (f := f) hworking).occurrence A).derives

/-- The constructed base exposing context accepts every tuple derivable from
its selected base nonterminal. -/
theorem expose_accepts_derives
    (C : SuccessfulOccurrencePreCoreConstruction G obs)
    (hworking : G.BasicWorkingConditions)
    (A : N)
    {x : Tuple α (G.arity A)}
    (hx : DerivesTuple G A x) :
    namedFill (G.arity A)
        ((C.toPreCoreData (f := f) hworking).expose A)
        x ∈
      G.StringLanguage :=
  ((C.toSuccessfulOccurrenceData (f := f) hworking).occurrence A).
    spine.acceptsDerives hx

end SuccessfulOccurrencePreCoreConstruction

end SuccessfulPresentationConstruction


section FiniteSuccessfulPresentationRoute

variable {N : Type v} {α : Type u} {M : Type w}
variable [Finite N]
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

namespace SuccessfulOccurrencePreCoreConstruction

/-- The concrete finite characteristic-sample candidate generated from a
successful complete typed presentation and a compatible representative
selection. -/
noncomputable def finiteSample
    (C : SuccessfulOccurrencePreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions) :
    Finset (Word α) :=
  (C.toSuccessfulOccurrenceData (f := f) hworking.basic).
    finiteSample hworking.basic

/-- The generated sample is positive. -/
theorem finiteSample_positive
    (C : SuccessfulOccurrencePreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions) :
    (C.finiteSample (f := f) hworking : Set (Word α)) ⊆
      G.StringLanguage :=
  (C.toSuccessfulOccurrenceData (f := f) hworking.basic).
    finiteSample_positive hworking.basic

/-- Exact reconstruction on every positive finite superset of the generated
sample. -/
theorem exact_for_positive_superset
    (C : SuccessfulOccurrencePreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hCK :
      (C.finiteSample (f := f) hworking : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f =
      G.StringLanguage :=
  (C.toSuccessfulOccurrenceData (f := f) hworking.basic).
    exact_for_positive_superset hworking hfan hL hCK hKpos

/-- Eventual prefix-exact reconstruction from the successful presentation
construction. -/
theorem exact_prefix_reconstruction
    (C : SuccessfulOccurrencePreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (C.toSuccessfulOccurrenceData (f := f) hworking.basic).
    exact_prefix_reconstruction hworking hfan hL

/-- Gold identification from a successful complete typed presentation and a
compatible base-representative selection. -/
theorem identifies_from_positive_text
    (C : SuccessfulOccurrencePreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (C.toSuccessfulOccurrenceData (f := f) hworking.basic).
    identifies_from_positive_text hworking hfan hL

/-- Paper-facing identification theorem from the successful presentation
construction. -/
theorem exact_working_paper_main_theorem
    (C : SuccessfulOccurrencePreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  (C.toSuccessfulOccurrenceData (f := f) hworking.basic).
    exact_working_paper_main_theorem hworking hfan hL

/-- Full characteristic-sample, prefix-exact, and Gold-identification package
from the successful presentation construction. -/
theorem exact_working_paper_conclusion_package
    (C : SuccessfulOccurrencePreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  (C.toSuccessfulOccurrenceData (f := f) hworking.basic).
    exact_working_paper_conclusion_package hworking hfan hL

end SuccessfulOccurrencePreCoreConstruction

end FiniteSuccessfulPresentationRoute


section SuccessfulPresentationTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [Finite N]
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

/-- Stable paper-facing endpoint from a complete typed presentation equipped
with successful occurrences and a rule-compatible base representative
selection. -/
theorem trimmed_successful_presentation_exact_working_main_theorem
    (C : SuccessfulOccurrencePreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  C.exact_working_paper_main_theorem
    (f := f) hworking hfan hL

/-- Stable full conclusion package from the successful presentation
construction. -/
theorem trimmed_successful_presentation_exact_working_conclusion_package
    (C : SuccessfulOccurrencePreCoreConstruction G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  C.exact_working_paper_conclusion_package
    (f := f) hworking hfan hL

end SuccessfulPresentationTopLevel

end MCFG
