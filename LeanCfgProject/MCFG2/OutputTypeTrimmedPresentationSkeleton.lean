/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.OutputTypePresentationCompleteness

/-!
# OutputTypeTrimmedPresentationSkeleton.lean

Forty-first clean Lean experiment for the fixed-observation MCFG project.

The previous files introduced finite output-type presentations and a
completeness interface for them.

This file starts the trimmed-presentation layer.  It does **not** yet construct
the trimmed refinement `G̃₀`.  Instead, it packages the data that a future
trimmed construction should provide:

* a complete finite output-type presentation;
* for every typed nonterminal present in that presentation, an anchor tuple;
* for every such typed nonterminal, an exposing named context;
* the anchor has the stored output type;
* the exposing context accepts the anchor in the original grammar language.

This is the first bridge from the finite typed-presentation layer toward the
`ReachableSplicingBlueprint` construction.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PresentTypedNonterminals

variable {N : Type v} {α : Type u} {M : Type w} [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- A typed nonterminal together with proof that it is present in a finite
output-type presentation. -/
structure PresentTypedNonterminal
    (P : OutputTypeRefinementPresentation G obs) where
  node : TypedNonterminal G M
  mem : P.HasNonterminal node

namespace PresentTypedNonterminal

variable {P : OutputTypeRefinementPresentation G obs}

/-- The underlying base nonterminal. -/
def base
    (X : PresentTypedNonterminal P) : N :=
  X.node.base

/-- The arity inherited from the base grammar. -/
def arity
    (X : PresentTypedNonterminal P) : Nat :=
  G.arity X.base

/-- The stored output type of the typed nonterminal. -/
def out
    (X : PresentTypedNonterminal P) :
    Fin (G.arity X.node.base) → M :=
  X.node.out

/-- Repackage a present nonterminal from an explicit membership proof. -/
def mkOfMem
    (X : TypedNonterminal G M)
    (hX : P.HasNonterminal X) :
    PresentTypedNonterminal P where
  node := X
  mem := hX

@[simp] theorem base_eq
    (X : PresentTypedNonterminal P) :
    X.base = X.node.base :=
  rfl

@[simp] theorem arity_eq
    (X : PresentTypedNonterminal P) :
    X.arity = G.arity X.node.base :=
  rfl

@[simp] theorem out_eq
    (X : PresentTypedNonterminal P) :
    X.out = X.node.out :=
  rfl

end PresentTypedNonterminal

end PresentTypedNonterminals


section TrimmedWitnesses

variable {N : Type v} {α : Type u} {M : Type w} [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Anchor and exposure witnesses for every typed nonterminal present in a
finite output-type presentation. -/
structure TrimmedNonterminalWitnesses
    (P : OutputTypeRefinementPresentation G obs) where
  anchor :
    (X : PresentTypedNonterminal P) →
      Tuple α (G.arity X.node.base)
  expose :
    (X : PresentTypedNonterminal P) →
      NamedSentenceContext α (G.arity X.node.base)
  anchor_matches :
    ∀ X : PresentTypedNonterminal P,
      X.node.Matches obs (anchor X)
  expose_accepts :
    ∀ X : PresentTypedNonterminal P,
      namedFill (G.arity X.node.base) (expose X) (anchor X) ∈
        G.StringLanguage

namespace TrimmedNonterminalWitnesses

variable {P : OutputTypeRefinementPresentation G obs}

/-- The named word witnessing exposure of a present typed nonterminal. -/
def exposedWord
    (W : TrimmedNonterminalWitnesses P)
    (X : PresentTypedNonterminal P) : Word α :=
  namedFill (G.arity X.node.base) (W.expose X) (W.anchor X)

/-- The exposed word is accepted by the original grammar. -/
theorem exposedWord_mem
    (W : TrimmedNonterminalWitnesses P)
    (X : PresentTypedNonterminal P) :
    W.exposedWord X ∈ G.StringLanguage :=
  W.expose_accepts X

/-- The anchor tuple has the output type stored in the typed nonterminal. -/
theorem anchor_tupleType
    (W : TrimmedNonterminalWitnesses P)
    (X : PresentTypedNonterminal P) :
    tupleType obs (W.anchor X) = X.node.out :=
  W.anchor_matches X

end TrimmedNonterminalWitnesses

end TrimmedWitnesses


section TrimmedPresentation

variable {N : Type v} {α : Type u} {M : Type w} [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- A complete finite output-type presentation equipped with anchor and exposure
witnesses for all present typed nonterminals.

This is a skeleton for a future formalization of the trimmed output-type
refinement `G̃₀`. -/
structure TrimmedOutputTypePresentation
    (G : WorkingMCFG N α) (obs : α → M) where
  completePresentation : CompleteOutputTypePresentation G obs
  witnesses :
    TrimmedNonterminalWitnesses completePresentation.presentation

namespace TrimmedOutputTypePresentation

/-- The underlying finite output-type presentation. -/
def presentation
    (T : TrimmedOutputTypePresentation G obs) :
    OutputTypeRefinementPresentation G obs :=
  T.completePresentation.presentation

/-- The string language generated by the underlying presentation. -/
def language
    (T : TrimmedOutputTypePresentation G obs) : Set (Word α) :=
  PresentationStringLanguage T.presentation

/-- Construct a trimmed presentation from a complete presentation and witnesses. -/
def ofComplete
    (C : CompleteOutputTypePresentation G obs)
    (W : TrimmedNonterminalWitnesses C.presentation) :
    TrimmedOutputTypePresentation G obs where
  completePresentation := C
  witnesses := W

/-- The underlying finite presentation is sound. -/
theorem sound
    (T : TrimmedOutputTypePresentation G obs) :
    T.language ⊆ G.StringLanguage :=
  T.completePresentation.sound

/-- The underlying finite presentation is complete. -/
theorem complete_subset
    (T : TrimmedOutputTypePresentation G obs) :
    G.StringLanguage ⊆ T.language :=
  T.completePresentation.complete_subset

/-- The underlying finite presentation generates exactly the original grammar
language. -/
theorem language_eq
    (T : TrimmedOutputTypePresentation G obs) :
    T.language = G.StringLanguage :=
  T.completePresentation.language_eq

/-- Membership equivalence for the underlying complete presentation. -/
theorem mem_language_iff
    (T : TrimmedOutputTypePresentation G obs)
    {word : Word α} :
    word ∈ T.language ↔ word ∈ G.StringLanguage :=
  T.completePresentation.mem_iff

/-- A present typed nonterminal of the underlying presentation. -/
abbrev Present
    (T : TrimmedOutputTypePresentation G obs) :=
  PresentTypedNonterminal T.presentation

/-- The anchor of a present typed nonterminal. -/
def anchor
    (T : TrimmedOutputTypePresentation G obs)
    (X : T.Present) :
    Tuple α (G.arity X.node.base) :=
  T.witnesses.anchor X

/-- The exposing context of a present typed nonterminal. -/
def expose
    (T : TrimmedOutputTypePresentation G obs)
    (X : T.Present) :
    NamedSentenceContext α (G.arity X.node.base) :=
  T.witnesses.expose X

/-- The exposed word of a present typed nonterminal. -/
def exposedWord
    (T : TrimmedOutputTypePresentation G obs)
    (X : T.Present) : Word α :=
  namedFill (G.arity X.node.base) (T.expose X) (T.anchor X)

/-- The anchor has the output type stored in the typed nonterminal. -/
theorem anchor_tupleType
    (T : TrimmedOutputTypePresentation G obs)
    (X : T.Present) :
    tupleType obs (T.anchor X) = X.node.out :=
  T.witnesses.anchor_tupleType X

/-- The exposed word is accepted by the original grammar. -/
theorem exposedWord_mem
    (T : TrimmedOutputTypePresentation G obs)
    (X : T.Present) :
    T.exposedWord X ∈ G.StringLanguage :=
  T.witnesses.exposedWord_mem X

/-- A present typed terminal rule determines a present typed parent
nonterminal. -/
def terminalLHS
    (T : TrimmedOutputTypePresentation G obs)
    {τ : TypedTerminalRule G}
    (hτ : T.presentation.HasTerminalRule τ) :
    T.Present :=
  PresentTypedNonterminal.mkOfMem (τ.lhs obs)
    (T.presentation.terminal_lhs_present hτ)

/-- A present typed binary rule determines a present typed parent
nonterminal. -/
def binaryLHS
    (T : TrimmedOutputTypePresentation G obs)
    {τ : TypedBinaryRule G M}
    (hτ : T.presentation.HasBinaryRule τ) :
    T.Present :=
  PresentTypedNonterminal.mkOfMem (τ.lhs obs)
    (T.presentation.binary_lhs_present hτ)

/-- A present typed binary rule determines a present typed left child. -/
def binaryLeft
    (T : TrimmedOutputTypePresentation G obs)
    {τ : TypedBinaryRule G M}
    (hτ : T.presentation.HasBinaryRule τ) :
    T.Present :=
  PresentTypedNonterminal.mkOfMem τ.left
    (T.presentation.binary_left_present hτ)

/-- A present typed binary rule determines a present typed right child. -/
def binaryRight
    (T : TrimmedOutputTypePresentation G obs)
    {τ : TypedBinaryRule G M}
    (hτ : T.presentation.HasBinaryRule τ) :
    T.Present :=
  PresentTypedNonterminal.mkOfMem τ.right
    (T.presentation.binary_right_present hτ)

/-- A present typed start rule determines a present typed child. -/
def startChild
    (T : TrimmedOutputTypePresentation G obs)
    {σ : TypedStartRule G M}
    (hσ : T.presentation.HasStartRule σ) :
    T.Present :=
  PresentTypedNonterminal.mkOfMem σ.child
    (T.presentation.start_child_present hσ)

/-- The anchor of the parent of a present terminal rule has the correct output
type. -/
theorem terminalLHS_anchor_tupleType
    (T : TrimmedOutputTypePresentation G obs)
    {τ : TypedTerminalRule G}
    (hτ : T.presentation.HasTerminalRule τ) :
    tupleType obs (T.anchor (T.terminalLHS hτ)) =
      (τ.lhs obs).out :=
  T.anchor_tupleType (T.terminalLHS hτ)

/-- The anchor of the parent of a present binary rule has the correct output
type. -/
theorem binaryLHS_anchor_tupleType
    (T : TrimmedOutputTypePresentation G obs)
    {τ : TypedBinaryRule G M}
    (hτ : T.presentation.HasBinaryRule τ) :
    tupleType obs (T.anchor (T.binaryLHS hτ)) =
      (τ.lhs obs).out :=
  T.anchor_tupleType (T.binaryLHS hτ)

/-- The anchor of a present binary left child has the correct output type. -/
theorem binaryLeft_anchor_tupleType
    (T : TrimmedOutputTypePresentation G obs)
    {τ : TypedBinaryRule G M}
    (hτ : T.presentation.HasBinaryRule τ) :
    tupleType obs (T.anchor (T.binaryLeft hτ)) = τ.left.out :=
  T.anchor_tupleType (T.binaryLeft hτ)

/-- The anchor of a present binary right child has the correct output type. -/
theorem binaryRight_anchor_tupleType
    (T : TrimmedOutputTypePresentation G obs)
    {τ : TypedBinaryRule G M}
    (hτ : T.presentation.HasBinaryRule τ) :
    tupleType obs (T.anchor (T.binaryRight hτ)) = τ.right.out :=
  T.anchor_tupleType (T.binaryRight hτ)

/-- The anchor of a present start child has the correct output type. -/
theorem startChild_anchor_tupleType
    (T : TrimmedOutputTypePresentation G obs)
    {σ : TypedStartRule G M}
    (hσ : T.presentation.HasStartRule σ) :
    tupleType obs (T.anchor (T.startChild hσ)) = σ.child.out :=
  T.anchor_tupleType (T.startChild hσ)

end TrimmedOutputTypePresentation

end TrimmedPresentation

end MCFG
