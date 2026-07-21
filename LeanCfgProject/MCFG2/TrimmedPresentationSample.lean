/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.TrimmedPresentationPreCore

/-!
# TrimmedPresentationSample.lean

Forty-third clean Lean experiment for the fixed-observation MCFG project.

`TrimmedPresentationPreCore.lean` converted base representatives from a trimmed
typed presentation into the `ReachableBlueprintPreCore` interface.

This file adds the finite sample layer.

Given a trimmed-presentation pre-core `D`, we package the assertion that a
finite sample `S` contains all words required by that pre-core:

* exposed anchor words for every base nonterminal;
* terminal witness words;
* binary witness words;
* start-rule witness words;
* the distinguished start word.

From this package we construct `ReachablePreCoreFiniteSample`, and therefore,
after adding a `NamedContextSplicingConstructor`, a `ReachableSplicingPackage`
or a full `ReachableSplicingBlueprint`.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section TrimmedSampleWords

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- The anchor/exposure word for a base nonterminal in a trimmed-presentation
pre-core. -/
def TrimmedPresentationPreCoreData.anchorWitnessWord
    (D : TrimmedPresentationPreCoreData T f)
    (A : N) : Word α :=
  namedFill (G.arity A) (D.expose A) (D.anchor A)

/-- The terminal-rule witness word required by a trimmed-presentation pre-core. -/
def TrimmedPresentationPreCoreData.terminalWitnessWord
    (D : TrimmedPresentationPreCoreData T f)
    (ρ : TerminalRule N α)
    (hwt : G.arity ρ.lhs = 1) : Word α :=
  namedFill (G.arity ρ.lhs) (D.expose ρ.lhs)
    (castTuple hwt.symm ρ.outputTuple)

/-- The binary-rule witness word required by a trimmed-presentation pre-core. -/
def TrimmedPresentationPreCoreData.binaryWitnessWord
    (D : TrimmedPresentationPreCoreData T f)
    (ρ : BinaryRule N α G.arity) : Word α :=
  namedFill (G.arity ρ.lhs) (D.expose ρ.lhs)
    (ρ.apply (D.anchor ρ.left) (D.anchor ρ.right))

/-- The start-rule witness word required by a trimmed-presentation pre-core. -/
def TrimmedPresentationPreCoreData.startWitnessWord
    (D : TrimmedPresentationPreCoreData T f)
    (ρ : StartRule N)
    (hwt : G.arity ρ.child = G.arity G.start) : Word α :=
  namedFill (G.arity G.start) (D.expose G.start)
    (castTuple hwt (D.anchor ρ.child))

namespace TrimmedPresentationPreCoreData

/-- The base exposed word agrees definitionally with the anchor witness word. -/
@[simp] theorem anchorWitnessWord_eq_exposedWord
    (D : TrimmedPresentationPreCoreData T f)
    (A : N) :
    D.anchorWitnessWord A = D.exposedWord A :=
  rfl

/-- Anchor witness words are accepted by the target grammar. -/
theorem anchorWitnessWord_mem_target
    (D : TrimmedPresentationPreCoreData T f)
    (A : N) :
    D.anchorWitnessWord A ∈ G.StringLanguage :=
  D.exposedWord_mem A

end TrimmedPresentationPreCoreData

end TrimmedSampleWords


section TrimmedSampleData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {S : Finset (Word α)}

/-- Finite sample membership data associated with a trimmed-presentation
pre-core. -/
structure TrimmedPresentationSampleData
    (D : TrimmedPresentationPreCoreData T f)
    (S : Finset (Word α)) where
  sample_positive : (S : Set (Word α)) ⊆ G.StringLanguage

  anchor_mem :
    ∀ A : N,
      D.anchorWitnessWord A ∈ S

  terminal_mem :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        D.terminalWitnessWord ρ hwt ∈ S

  binary_mem :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        D.binaryWitnessWord ρ ∈ S

  start_mem :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        D.startWitnessWord ρ hwt ∈ S

  startWord_mem :
    D.startWord ∈ S

namespace TrimmedPresentationSampleData

variable {D : TrimmedPresentationPreCoreData T f}

/-- Anchor witness words are positive, because the whole sample is positive. -/
theorem anchor_mem_target
    (H : TrimmedPresentationSampleData D S)
    (A : N) :
    D.anchorWitnessWord A ∈ G.StringLanguage :=
  H.sample_positive (H.anchor_mem A)

/-- Terminal witness words are positive. -/
theorem terminal_mem_target
    (H : TrimmedPresentationSampleData D S)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    D.terminalWitnessWord ρ hwt ∈ G.StringLanguage :=
  H.sample_positive (H.terminal_mem ρ hρ hwt)

/-- Binary witness words are positive. -/
theorem binary_mem_target
    (H : TrimmedPresentationSampleData D S)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈ G.StringLanguage :=
  H.sample_positive (H.binary_mem ρ hρ)

/-- Start witness words are positive. -/
theorem start_mem_target
    (H : TrimmedPresentationSampleData D S)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    D.startWitnessWord ρ hwt ∈ G.StringLanguage :=
  H.sample_positive (H.start_mem ρ hρ hwt)

/-- The distinguished start word is positive. -/
theorem startWord_mem_target
    (H : TrimmedPresentationSampleData D S) :
    D.startWord ∈ G.StringLanguage :=
  H.sample_positive H.startWord_mem

/-- Convert trimmed-presentation sample data to the reachable finite-sample
package used by the main theorem. -/
def toReachablePreCoreFiniteSample
    (H : TrimmedPresentationSampleData D S) :
    ReachablePreCoreFiniteSample G S obs f D.toReachablePreCore where
  sample_positive := H.sample_positive
  anchor_mem := by
    intro A
    exact H.anchor_mem A
  terminal_mem := by
    intro ρ hρ hwt
    exact H.terminal_mem ρ hρ hwt
  binary_mem := by
    intro ρ hρ
    exact H.binary_mem ρ hρ
  start_mem := by
    intro ρ hρ hwt
    exact H.start_mem ρ hρ hwt
  startWord_mem := H.startWord_mem

/-- Convert the trimmed pre-core and sample data, together with a universal
named-context splicing constructor, into the finite splicing package. -/
def toSplicingPackage
    (H : TrimmedPresentationSampleData D S)
    (U : NamedContextSplicingConstructor α) :
    ReachableSplicingPackage G S obs f where
  preCore := D.toReachablePreCore
  finiteSample := H.toReachablePreCoreFiniteSample
  splicingConstructor := U

/-- Convert directly to the flat splicing blueprint. -/
def toSplicingBlueprint
    (H : TrimmedPresentationSampleData D S)
    (U : NamedContextSplicingConstructor α) :
    ReachableSplicingBlueprint G S obs f where
  sample_positive := H.sample_positive
  anchor := D.anchor
  expose := D.expose
  terminal_type_eq := D.terminal_type_eq
  binary_type_eq := D.binary_type_eq
  start_type_eq := D.start_type_eq
  startWord := D.startWord
  start_arity := D.start_arity
  start_anchor_eq := D.start_anchor_eq
  anchor_mem := by
    intro A
    exact H.anchor_mem A
  terminal_mem := by
    intro ρ hρ hwt
    exact H.terminal_mem ρ hρ hwt
  binary_mem := by
    intro ρ hρ
    exact H.binary_mem ρ hρ
  start_mem := by
    intro ρ hρ hwt
    exact H.start_mem ρ hρ hwt
  startWord_mem := H.startWord_mem
  splicingConstructor := U

/-- Add global assumptions to obtain the blueprint-main-data package. -/
def toSplicingBlueprintMainData
    (H : TrimmedPresentationSampleData D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ReachableSplicingBlueprintMainData G S obs f where
  fanout := hfan
  promise := hL
  blueprint := H.toSplicingBlueprint U

/-- Add global assumptions to obtain the final reachable-data package. -/
def toFinalReachableData
    (H : TrimmedPresentationSampleData D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    FinalReachableData G S obs f where
  data := H.toSplicingBlueprintMainData U hfan hL

/-- Reachable identification from trimmed-presentation sample data plus the
remaining splicing constructor and global target assumptions. -/
theorem identifies_from_trimmed_sample
    (H : TrimmedPresentationSampleData D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (H.toFinalReachableData U hfan hL).identifies_from_positive_text

/-- Prefix-exact reconstruction from trimmed-presentation sample data plus the
remaining splicing constructor and global target assumptions. -/
theorem prefix_exact_from_trimmed_sample
    (H : TrimmedPresentationSampleData D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (H.toFinalReachableData U hfan hL).prefix_exact_eventually

end TrimmedPresentationSampleData

end TrimmedSampleData

end MCFG
