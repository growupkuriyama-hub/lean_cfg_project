/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleExactOnceSuccessfulDerivationSpineRoute

/-!
# CharacteristicSampleExactOnceSuccessfulOccurrenceRoute.lean

The previous file separated the remaining successful-occurrence information
into two fields:

```lean
anchor_derives
expose_spine
```

This file packages them into one inductively generated object.  An
`ExactSuccessfulDerivationOccurrence G A x c` records that the tuple `x`
occurs at nonterminal `A` inside a successful derivation to the start language,
and that the surrounding successful derivation induces the named context `c`.

The constructors mirror a path through an actual derivation:

* a derived start tuple occurs at the root under the transported identity
  context;
* a start-rule child occurs below a successful start occurrence;
* the left child of a binary rule occurs below a successful parent occurrence,
  with a genuinely derived right sibling;
* symmetrically for the right child.

Exact-once child contexts are the concrete contexts already proved correct in
`CharacteristicSampleNamedContextSplicingExactOnceConstruction.lean`.

A single occurrence witness therefore yields both:

```lean
DerivesTuple G A x
ExactSuccessfulDerivationSpine G A c
```

and hence the derivational-exposure invariant, the concrete finite
characteristic sample, exact reconstruction, and Gold identification.

No unrestricted splicing constructor or unconditional exposing transport is
used.
-/

namespace MCFG

universe u v w

section ExactSuccessfulOccurrences

variable {N : Type v} {α : Type u}

/-- A concrete occurrence of a tuple inside a successful exact-once
derivation.

The tuple and its surrounding named context are indices of the relation.  Thus
the constructors do not merely assert independent derivability and exposure:
they build both along one path from the grammar start to the selected
occurrence. -/
inductive ExactSuccessfulDerivationOccurrence
    (G : WorkingMCFG N α) :
    (A : N) →
      Tuple α (G.arity A) →
      NamedSentenceContext α (G.arity A) →
      Prop where

  /-- Any genuinely derived start tuple occurs at the root, surrounded by the
  transported one-hole identity context. -/
  | root
      (hstart : 1 = G.arity G.start)
      {x : Tuple α (G.arity G.start)}
      (hx : DerivesTuple G G.start x) :
      ExactSuccessfulDerivationOccurrence G G.start x
        (startIdentityNamedContext G hstart)

  /-- Descend through a start rule to its child occurrence. -/
  | throughStart
      {ρ : StartRule N}
      (hρ : ρ ∈ G.startRules)
      (hwt : ρ.WellTyped G)
      {x : Tuple α (G.arity ρ.child)}
      (hx : DerivesTuple G ρ.child x)
      {parent : NamedSentenceContext α (G.arity G.start)}
      (parentOccurrence :
        ExactSuccessfulDerivationOccurrence G G.start
          (castTuple hwt x) parent) :
      ExactSuccessfulDerivationOccurrence G ρ.child x
        (transportNamedSentenceContext hwt.symm parent)

  /-- Descend through an exact-once binary rule to its left child.  The right
  sibling is part of the same successful parent derivation. -/
  | throughLeft
      {ρ : BinaryRule N α G.arity}
      (hρ : ρ ∈ G.binaryRules)
      (hexact : ρ.ExactlyOnce)
      {x : Tuple α (G.arity ρ.left)}
      {y : Tuple α (G.arity ρ.right)}
      (hx : DerivesTuple G ρ.left x)
      (hy : DerivesTuple G ρ.right y)
      {parent : NamedSentenceContext α (G.arity ρ.lhs)}
      (parentOccurrence :
        ExactSuccessfulDerivationOccurrence G ρ.lhs
          (ρ.apply x y) parent) :
      ExactSuccessfulDerivationOccurrence G ρ.left x
        (ExactSplicing.leftContextNSC
          parent ρ.body hexact.2.1 y)

  /-- Descend through an exact-once binary rule to its right child.  The left
  sibling is part of the same successful parent derivation. -/
  | throughRight
      {ρ : BinaryRule N α G.arity}
      (hρ : ρ ∈ G.binaryRules)
      (hexact : ρ.ExactlyOnce)
      {x : Tuple α (G.arity ρ.left)}
      {y : Tuple α (G.arity ρ.right)}
      (hx : DerivesTuple G ρ.left x)
      (hy : DerivesTuple G ρ.right y)
      {parent : NamedSentenceContext α (G.arity ρ.lhs)}
      (parentOccurrence :
        ExactSuccessfulDerivationOccurrence G ρ.lhs
          (ρ.apply x y) parent) :
      ExactSuccessfulDerivationOccurrence G ρ.right y
        (ExactSplicing.rightContextNSC
          parent ρ.body hexact.2.2 x)

namespace ExactSuccessfulDerivationOccurrence

/-- The selected tuple in a successful occurrence is genuinely derivable. -/
def derives
    {G : WorkingMCFG N α}
    {A : N}
    {x : Tuple α (G.arity A)}
    {c : NamedSentenceContext α (G.arity A)}
    (O : ExactSuccessfulDerivationOccurrence G A x c) :
    DerivesTuple G A x :=
  match O with
  | .root _ hx =>
      hx
  | .throughStart _ _ hx _ =>
      hx
  | .throughLeft _ _ hx _ _ =>
      hx
  | .throughRight _ _ _ hy _ =>
      hy

/-- The surrounding context of a successful occurrence is an explicit
successful derivation spine. -/
def spine
    {G : WorkingMCFG N α}
    {A : N}
    {x : Tuple α (G.arity A)}
    {c : NamedSentenceContext α (G.arity A)}
    (O : ExactSuccessfulDerivationOccurrence G A x c) :
    ExactSuccessfulDerivationSpine G A c :=
  match O with
  | .root hstart _ =>
      .root hstart
  | .throughStart hρ hwt _ parentOccurrence =>
      .throughStart hρ hwt (spine parentOccurrence)
  | .throughLeft hρ hexact _ hy parentOccurrence =>
      .throughLeft hρ hexact hy (spine parentOccurrence)
  | .throughRight hρ hexact hx _ parentOccurrence =>
      .throughRight hρ hexact hx (spine parentOccurrence)
termination_by O

/-- A successful occurrence accepts its selected tuple. -/
theorem accepts
    {G : WorkingMCFG N α}
    {A : N}
    {x : Tuple α (G.arity A)}
    {c : NamedSentenceContext α (G.arity A)}
    (O : ExactSuccessfulDerivationOccurrence G A x c) :
    namedFill (G.arity A) c x ∈ G.StringLanguage :=
  O.spine.acceptsDerives O.derives

/-- A successful occurrence gives the grammar-level
`ExposedWithContext` witness. -/
theorem exposedWithContext
    {G : WorkingMCFG N α}
    {A : N}
    {x : Tuple α (G.arity A)}
    {c : NamedSentenceContext α (G.arity A)}
    (O : ExactSuccessfulDerivationOccurrence G A x c) :
    ExposedWithContext G A x c :=
  ⟨O.derives, O.accepts⟩

/-- Root occurrence obtained from exact working conditions and a derived start
tuple. -/
def rootOfExactWorking
    {G : WorkingMCFG N α}
    (hworking : G.ExactWorkingConditions)
    {x : Tuple α (G.arity G.start)}
    (hx : DerivesTuple G G.start x) :
    ExactSuccessfulDerivationOccurrence G G.start x
      (startIdentityNamedContext G hworking.basic.1.symm) :=
  .root hworking.basic.1.symm hx

/-- Start-child occurrence with well-typedness extracted from exact working
conditions. -/
def throughStartOfExactWorking
    {G : WorkingMCFG N α}
    (hworking : G.ExactWorkingConditions)
    {ρ : StartRule N}
    (hρ : ρ ∈ G.startRules)
    {x : Tuple α (G.arity ρ.child)}
    (hx : DerivesTuple G ρ.child x)
    {parent : NamedSentenceContext α (G.arity G.start)}
    (parentOccurrence :
      ExactSuccessfulDerivationOccurrence G G.start
        (castTuple (hworking.basic.2.1 ρ hρ) x) parent) :
    ExactSuccessfulDerivationOccurrence G ρ.child x
      (transportNamedSentenceContext
        (hworking.basic.2.1 ρ hρ).symm parent) :=
  .throughStart hρ (hworking.basic.2.1 ρ hρ)
    hx parentOccurrence

/-- Left-child occurrence with exact-once linearity extracted from exact
working conditions. -/
def throughLeftOfExactWorking
    {G : WorkingMCFG N α}
    (hworking : G.ExactWorkingConditions)
    {ρ : BinaryRule N α G.arity}
    (hρ : ρ ∈ G.binaryRules)
    {x : Tuple α (G.arity ρ.left)}
    {y : Tuple α (G.arity ρ.right)}
    (hx : DerivesTuple G ρ.left x)
    (hy : DerivesTuple G ρ.right y)
    {parent : NamedSentenceContext α (G.arity ρ.lhs)}
    (parentOccurrence :
      ExactSuccessfulDerivationOccurrence G ρ.lhs
        (ρ.apply x y) parent) :
    ExactSuccessfulDerivationOccurrence G ρ.left x
      (ExactSplicing.leftContextNSC
        parent ρ.body (hworking.2 ρ hρ).2.1 y) :=
  .throughLeft hρ (hworking.2 ρ hρ)
    hx hy parentOccurrence

/-- Right-child occurrence with exact-once linearity extracted from exact
working conditions. -/
def throughRightOfExactWorking
    {G : WorkingMCFG N α}
    (hworking : G.ExactWorkingConditions)
    {ρ : BinaryRule N α G.arity}
    (hρ : ρ ∈ G.binaryRules)
    {x : Tuple α (G.arity ρ.left)}
    {y : Tuple α (G.arity ρ.right)}
    (hx : DerivesTuple G ρ.left x)
    (hy : DerivesTuple G ρ.right y)
    {parent : NamedSentenceContext α (G.arity ρ.lhs)}
    (parentOccurrence :
      ExactSuccessfulDerivationOccurrence G ρ.lhs
        (ρ.apply x y) parent) :
    ExactSuccessfulDerivationOccurrence G ρ.right y
      (ExactSplicing.rightContextNSC
        parent ρ.body (hworking.2 ρ hρ).2.2 x) :=
  .throughRight hρ (hworking.2 ρ hρ)
    hx hy parentOccurrence

end ExactSuccessfulDerivationOccurrence

end ExactSuccessfulOccurrences


section SuccessfulOccurrenceData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- For each selected base representative, provide one concrete occurrence in
a successful exact-once derivation.

This single field simultaneously certifies that the chosen anchor is derived
and that the chosen exposing context is generated by the surrounding successful
derivation. -/
structure TrimmedPresentationSuccessfulOccurrenceData
    (D : TrimmedPresentationPreCoreData T f) where
  occurrence :
    ∀ A : N,
      ExactSuccessfulDerivationOccurrence G A
        (D.anchor A) (D.expose A)

namespace TrimmedPresentationSuccessfulOccurrenceData

/-- Concrete successful occurrences produce the previously verified successful
spine data. -/
def toSuccessfulSpineData
    (C : TrimmedPresentationSuccessfulOccurrenceData D) :
    TrimmedPresentationSuccessfulSpineData D where
  anchor_derives := fun A =>
    (C.occurrence A).derives
  expose_spine := fun A =>
    (C.occurrence A).spine

/-- Concrete successful occurrences produce the paper-faithful derivational
exposure invariant. -/
def toDerivationalExposure
    (C : TrimmedPresentationSuccessfulOccurrenceData D) :
    TrimmedPresentationDerivationalExposure D :=
  C.toSuccessfulSpineData.toDerivationalExposure

/-- Every selected anchor is exposed in the target language by its selected
context. -/
theorem anchor_exposed
    (C : TrimmedPresentationSuccessfulOccurrenceData D)
    (A : N) :
    ExposedWithContext G A (D.anchor A) (D.expose A) :=
  (C.occurrence A).exposedWithContext

end TrimmedPresentationSuccessfulOccurrenceData

end SuccessfulOccurrenceData


section FiniteSuccessfulOccurrenceRoute

variable {N : Type v} {α : Type u} {M : Type w}
variable [Finite N]
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

namespace TrimmedPresentationSuccessfulOccurrenceData

/-- Concrete finite characteristic sample obtained from successful occurrence
witnesses. -/
noncomputable def finiteSample
    (C : TrimmedPresentationSuccessfulOccurrenceData D)
    (hworking : G.BasicWorkingConditions) :
    Finset (Word α) :=
  C.toSuccessfulSpineData.finiteSample hworking

/-- The occurrence-generated sample is positive. -/
theorem finiteSample_positive
    (C : TrimmedPresentationSuccessfulOccurrenceData D)
    (hworking : G.BasicWorkingConditions) :
    (C.finiteSample hworking : Set (Word α)) ⊆
      G.StringLanguage :=
  C.toSuccessfulSpineData.finiteSample_positive hworking

/-- Exact reconstruction on every positive finite superset of the
occurrence-generated sample. -/
theorem exact_for_positive_superset
    (C : TrimmedPresentationSuccessfulOccurrenceData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hCK :
      (C.finiteSample hworking.basic : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f =
      G.StringLanguage :=
  C.toSuccessfulSpineData.exact_for_positive_superset
    hworking hfan hL hCK hKpos

/-- Eventual prefix-exact reconstruction from successful occurrence
witnesses. -/
theorem exact_prefix_reconstruction
    (C : TrimmedPresentationSuccessfulOccurrenceData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  C.toSuccessfulSpineData.exact_prefix_reconstruction
    hworking hfan hL

/-- Gold identification from successful occurrence witnesses. -/
theorem identifies_from_positive_text
    (C : TrimmedPresentationSuccessfulOccurrenceData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  C.toSuccessfulSpineData.identifies_from_positive_text
    hworking hfan hL

/-- Paper-facing identification theorem from one concrete successful occurrence
for each selected base representative. -/
theorem exact_working_paper_main_theorem
    (C : TrimmedPresentationSuccessfulOccurrenceData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  C.toSuccessfulSpineData.exact_working_paper_main_theorem
    hworking hfan hL

/-- Full characteristic-sample, prefix-exact, and Gold-identification package
from concrete successful occurrences. -/
theorem exact_working_paper_conclusion_package
    (C : TrimmedPresentationSuccessfulOccurrenceData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  C.toSuccessfulSpineData.exact_working_paper_conclusion_package
    hworking hfan hL

end TrimmedPresentationSuccessfulOccurrenceData

end FiniteSuccessfulOccurrenceRoute


section SuccessfulOccurrenceTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [Finite N]
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable paper-facing endpoint from concrete successful occurrences. -/
theorem trimmed_successful_occurrence_exact_working_main_theorem
    (C : TrimmedPresentationSuccessfulOccurrenceData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  C.exact_working_paper_main_theorem hworking hfan hL

/-- Stable full conclusion package from concrete successful occurrences. -/
theorem trimmed_successful_occurrence_exact_working_conclusion_package
    (C : TrimmedPresentationSuccessfulOccurrenceData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  C.exact_working_paper_conclusion_package hworking hfan hL

end SuccessfulOccurrenceTopLevel

end MCFG
