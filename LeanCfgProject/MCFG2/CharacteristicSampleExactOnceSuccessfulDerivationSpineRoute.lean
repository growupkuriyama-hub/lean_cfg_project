/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleExactOnceFiniteNonterminalDerivationalExposureRoute

/-!
# CharacteristicSampleExactOnceSuccessfulDerivationSpineRoute.lean

The preceding exact-once route assumes the paper-faithful semantic invariant

```lean
TrimmedPresentationDerivationalExposure D
```

saying that each selected anchor is derivable and that each selected exposing
context accepts every tuple derivable from the corresponding nonterminal.

This file gives a more concrete source for the second half of that invariant.
An `ExactSuccessfulDerivationSpine G A c` is an explicit path from an occurrence
of `A` to the grammar start:

* the root is the one-hole identity context at the start symbol;
* a start rule transports a successful start context to its child;
* a binary rule transports a successful parent context to either child while
  fixing a genuinely derived sibling tuple.

The exact-once child contexts are the concrete contexts constructed in
`CharacteristicSampleNamedContextSplicingExactOnceConstruction.lean`.
Induction over a spine proves that its context accepts every tuple derivable
from its hole nonterminal.

Consequently, anchors plus explicit successful spines construct
`TrimmedPresentationDerivationalExposure D`, and the already verified finite
exact-once characteristic-sample route yields exact reconstruction and Gold
identification.

No unrestricted `NamedContextSplicingConstructor`, unconditional exposing
transport, `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section NamedContextTransport

variable {α : Type u}

/-- Transport a named sentence context across an equality of arities. -/
def transportNamedSentenceContext {d e : Nat}
    (h : d = e)
    (c : NamedSentenceContext α d) :
    NamedSentenceContext α e := by
  cases h
  exact c

@[simp] theorem transportNamedSentenceContext_rfl
    {d : Nat}
    (c : NamedSentenceContext α d) :
    transportNamedSentenceContext (rfl : d = d) c = c :=
  rfl

/-- Filling a transported context with a transported tuple is unchanged. -/
theorem namedFill_transportNamedSentenceContext
    {d e : Nat}
    (h : d = e)
    (c : NamedSentenceContext α d)
    (x : Tuple α d) :
    namedFill e
        (transportNamedSentenceContext h c)
        (castTuple h x) =
      namedFill d c x := by
  cases h
  rfl

/-- Symmetric form used when a rule transports a child tuple to its parent
arity. -/
theorem namedFill_transportNamedSentenceContext_symm
    {d e : Nat}
    (h : d = e)
    (c : NamedSentenceContext α e)
    (x : Tuple α d) :
    namedFill d
        (transportNamedSentenceContext h.symm c)
        x =
      namedFill e c (castTuple h x) := by
  cases h
  rfl

/-- Composition of tuple transports. -/
theorem castTuple_trans
    {d e k : Nat}
    (h₁ : d = e)
    (h₂ : e = k)
    (x : Tuple α d) :
    castTuple h₂ (castTuple h₁ x) =
      castTuple (h₁.trans h₂) x := by
  cases h₁
  cases h₂
  rfl

/-- The word represented by a tuple whose arity is known to be one. -/
def tupleWordOfArityOne
    {d : Nat}
    (h : 1 = d)
    (x : Tuple α d) :
    Word α :=
  (castTuple h.symm x) finOne

/-- Every tuple of arity one is the transported singleton tuple of its unique
component. -/
theorem castTuple_singleton_tupleWordOfArityOne
    {d : Nat}
    (h : 1 = d)
    (x : Tuple α d) :
    castTuple h
        (singletonTuple (tupleWordOfArityOne h x)) =
      x := by
  cases h
  funext i
  have hi : i = finOne := Subsingleton.elim _ _
  cases hi
  rfl

/-- The identity named context, transported to an arity propositionally equal
to one, extracts the unique tuple component. -/
theorem namedFill_transportUnaryIdentityContext
    {d : Nat}
    (h : 1 = d)
    (x : Tuple α d) :
    namedFill d
        (transportNamedSentenceContext h
          (unaryIdentityContext : NamedSentenceContext α 1))
        x =
      tupleWordOfArityOne h x := by
  rw [← castTuple_singleton_tupleWordOfArityOne h x]
  rw [namedFill_transportNamedSentenceContext]
  exact namedFill_unaryIdentityContext _

end NamedContextTransport


section SuccessfulDerivationSpines

variable {N : Type v} {α : Type u}

/-- The identity successful context at the grammar start symbol. -/
def startIdentityNamedContext
    (G : WorkingMCFG N α)
    (hstart : 1 = G.arity G.start) :
    NamedSentenceContext α (G.arity G.start) :=
  transportNamedSentenceContext hstart
    (unaryIdentityContext : NamedSentenceContext α 1)

/-- Every tuple genuinely derived by the start symbol is accepted by the
transported identity context. -/
theorem startIdentityNamedContext_accepts
    (G : WorkingMCFG N α)
    (hstart : 1 = G.arity G.start)
    {x : Tuple α (G.arity G.start)}
    (hx : DerivesTuple G G.start x) :
    namedFill (G.arity G.start)
        (startIdentityNamedContext G hstart)
        x ∈
      G.StringLanguage := by
  rw [namedFill_transportUnaryIdentityContext]
  apply mem_StringLanguage_of_start_derives G
    (tupleWordOfArityOne hstart x) hstart
  rw [castTuple_singleton_tupleWordOfArityOne]
  exact hx

/-- An explicit successful occurrence path from a nonterminal to the start
symbol.

The context index is part of the inductive object, so only contexts produced by
the root/start/binary spine constructors count as successful derivation
contexts. -/
inductive ExactSuccessfulDerivationSpine
    (G : WorkingMCFG N α) :
    (A : N) →
      NamedSentenceContext α (G.arity A) →
      Prop where

  /-- The start symbol is exposed by the transported one-hole identity
  context. -/
  | root
      (hstart : 1 = G.arity G.start) :
      ExactSuccessfulDerivationSpine G G.start
        (startIdentityNamedContext G hstart)

  /-- Follow a start rule downward from the start symbol to its child. -/
  | throughStart
      {ρ : StartRule N}
      (hρ : ρ ∈ G.startRules)
      (hwt : ρ.WellTyped G)
      {parent : NamedSentenceContext α (G.arity G.start)}
      (parentSpine :
        ExactSuccessfulDerivationSpine G G.start parent) :
      ExactSuccessfulDerivationSpine G ρ.child
        (transportNamedSentenceContext hwt.symm parent)

  /-- Follow an exact-once binary rule to its left child, fixing a derived
  right sibling tuple. -/
  | throughLeft
      {ρ : BinaryRule N α G.arity}
      (hρ : ρ ∈ G.binaryRules)
      (hexact : ρ.ExactlyOnce)
      {y : Tuple α (G.arity ρ.right)}
      (hy : DerivesTuple G ρ.right y)
      {parent : NamedSentenceContext α (G.arity ρ.lhs)}
      (parentSpine :
        ExactSuccessfulDerivationSpine G ρ.lhs parent) :
      ExactSuccessfulDerivationSpine G ρ.left
        (ExactSplicing.leftContextNSC
          parent ρ.body hexact.2.1 y)

  /-- Follow an exact-once binary rule to its right child, fixing a derived
  left sibling tuple. -/
  | throughRight
      {ρ : BinaryRule N α G.arity}
      (hρ : ρ ∈ G.binaryRules)
      (hexact : ρ.ExactlyOnce)
      {x : Tuple α (G.arity ρ.left)}
      (hx : DerivesTuple G ρ.left x)
      {parent : NamedSentenceContext α (G.arity ρ.lhs)}
      (parentSpine :
        ExactSuccessfulDerivationSpine G ρ.lhs parent) :
      ExactSuccessfulDerivationSpine G ρ.right
        (ExactSplicing.rightContextNSC
          parent ρ.body hexact.2.2 x)

namespace ExactSuccessfulDerivationSpine

/-- The semantic theorem justified by an explicit successful derivation spine:
its context accepts every tuple genuinely derivable from the hole
nonterminal. -/
def acceptsDerives
    {G : WorkingMCFG N α}
    {A : N}
    {c : NamedSentenceContext α (G.arity A)}
    (S : ExactSuccessfulDerivationSpine G A c) :
    ∀ {x : Tuple α (G.arity A)},
      DerivesTuple G A x →
        namedFill (G.arity A) c x ∈ G.StringLanguage :=
  match S with
  | .root hstart =>
      fun {_x} hx =>
        startIdentityNamedContext_accepts G hstart hx

  | .throughStart hρ hwt parentSpine =>
      fun {x} hx => by
        rw [namedFill_transportNamedSentenceContext_symm]
        exact acceptsDerives parentSpine
          (DerivesTuple.start hρ hx hwt)

  | .throughLeft hρ hexact hy parentSpine =>
      fun {x} hx => by
        rw [ExactSplicing.leftContext_fill_eq]
        simpa [BinaryRule.apply] using
          acceptsDerives parentSpine
            (DerivesTuple.binary hρ hx hy)

  | .throughRight hρ hexact hx parentSpine =>
      fun {y} hy => by
        rw [ExactSplicing.rightContext_fill_eq]
        simpa [BinaryRule.apply] using
          acceptsDerives parentSpine
            (DerivesTuple.binary hρ hx hy)
termination_by S

/-- Root spine constructed directly from the start-arity part of exact working
conditions. -/
def rootOfExactWorking
    {G : WorkingMCFG N α}
    (hworking : G.ExactWorkingConditions) :
    ExactSuccessfulDerivationSpine G G.start
      (startIdentityNamedContext G hworking.basic.1.symm) :=
  .root hworking.basic.1.symm

/-- Start-rule spine constructor with well-typedness extracted from exact
working conditions. -/
def throughStartOfExactWorking
    {G : WorkingMCFG N α}
    (hworking : G.ExactWorkingConditions)
    {ρ : StartRule N}
    (hρ : ρ ∈ G.startRules)
    {parent : NamedSentenceContext α (G.arity G.start)}
    (parentSpine :
      ExactSuccessfulDerivationSpine G G.start parent) :
    ExactSuccessfulDerivationSpine G ρ.child
      (transportNamedSentenceContext
        (hworking.basic.2.1 ρ hρ).symm parent) :=
  .throughStart hρ (hworking.basic.2.1 ρ hρ) parentSpine

/-- Left-child spine constructor with exact-once linearity extracted from exact
working conditions. -/
def throughLeftOfExactWorking
    {G : WorkingMCFG N α}
    (hworking : G.ExactWorkingConditions)
    {ρ : BinaryRule N α G.arity}
    (hρ : ρ ∈ G.binaryRules)
    {y : Tuple α (G.arity ρ.right)}
    (hy : DerivesTuple G ρ.right y)
    {parent : NamedSentenceContext α (G.arity ρ.lhs)}
    (parentSpine :
      ExactSuccessfulDerivationSpine G ρ.lhs parent) :
    ExactSuccessfulDerivationSpine G ρ.left
      (ExactSplicing.leftContextNSC
        parent ρ.body (hworking.2 ρ hρ).2.1 y) :=
  .throughLeft hρ (hworking.2 ρ hρ) hy parentSpine

/-- Right-child spine constructor with exact-once linearity extracted from
exact working conditions. -/
def throughRightOfExactWorking
    {G : WorkingMCFG N α}
    (hworking : G.ExactWorkingConditions)
    {ρ : BinaryRule N α G.arity}
    (hρ : ρ ∈ G.binaryRules)
    {x : Tuple α (G.arity ρ.left)}
    (hx : DerivesTuple G ρ.left x)
    {parent : NamedSentenceContext α (G.arity ρ.lhs)}
    (parentSpine :
      ExactSuccessfulDerivationSpine G ρ.lhs parent) :
    ExactSuccessfulDerivationSpine G ρ.right
      (ExactSplicing.rightContextNSC
        parent ρ.body (hworking.2 ρ hρ).2.2 x) :=
  .throughRight hρ (hworking.2 ρ hρ) hx parentSpine

end ExactSuccessfulDerivationSpine

end SuccessfulDerivationSpines


section SuccessfulOccurrenceData

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Concrete successful-occurrence data for the selected base representatives.

Unlike `TrimmedPresentationDerivationalExposure`, the exposure field is not an
arbitrary universal semantic function.  It must be supplied by an explicit
`ExactSuccessfulDerivationSpine` built from start and binary grammar rules. -/
structure TrimmedPresentationSuccessfulSpineData
    (D : TrimmedPresentationPreCoreData T f) where
  anchor_derives :
    ∀ A : N,
      DerivesTuple G A (D.anchor A)

  expose_spine :
    ∀ A : N,
      ExactSuccessfulDerivationSpine G A (D.expose A)

namespace TrimmedPresentationSuccessfulSpineData

/-- Explicit successful spines imply the derivational-exposure invariant used
by the characteristic-sample construction. -/
def toDerivationalExposure
    (S : TrimmedPresentationSuccessfulSpineData D) :
    TrimmedPresentationDerivationalExposure D where
  anchor_derives := S.anchor_derives
  expose_accepts_derives := by
    intro A x hx
    exact (S.expose_spine A).acceptsDerives hx

end TrimmedPresentationSuccessfulSpineData

end SuccessfulOccurrenceData


section FiniteSuccessfulOccurrenceRoute

variable {N : Type v} {α : Type u} {M : Type w}
variable [Finite N]
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

namespace TrimmedPresentationSuccessfulSpineData

/-- The concrete finite characteristic-sample candidate generated from anchors
and explicit successful derivation spines. -/
noncomputable def finiteSample
    (S : TrimmedPresentationSuccessfulSpineData D)
    (hworking : G.BasicWorkingConditions) :
    Finset (Word α) :=
  S.toDerivationalExposure.finiteSampleOfFinite hworking

/-- The generated sample is positive. -/
theorem finiteSample_positive
    (S : TrimmedPresentationSuccessfulSpineData D)
    (hworking : G.BasicWorkingConditions) :
    (S.finiteSample hworking : Set (Word α)) ⊆
      G.StringLanguage :=
  S.toDerivationalExposure.finiteSampleOfFinite_positive hworking

/-- Exact reconstruction on every positive finite superset of the generated
sample. -/
theorem exact_for_positive_superset
    (S : TrimmedPresentationSuccessfulSpineData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hSK :
      (S.finiteSample hworking.basic : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f =
      G.StringLanguage :=
  S.toDerivationalExposure.
    exact_for_positive_superset_of_finite_nonterminal_type
      hworking hfan hL hSK hKpos

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem exact_prefix_reconstruction
    (S : TrimmedPresentationSuccessfulSpineData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  S.toDerivationalExposure.
    exact_prefix_reconstruction_of_finite_nonterminal_type
      hworking hfan hL

/-- Gold identification from explicit successful derivation spines. -/
theorem identifies_from_positive_text
    (S : TrimmedPresentationSuccessfulSpineData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  S.toDerivationalExposure.
    identifies_from_positive_text_of_finite_nonterminal_type
      hworking hfan hL

/-- Paper-facing identification theorem from explicit successful occurrence
spines. -/
theorem exact_working_paper_main_theorem
    (S : TrimmedPresentationSuccessfulSpineData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  S.toDerivationalExposure.
    finite_nonterminal_exact_working_paper_main_theorem
      hworking hfan hL

/-- Full characteristic-sample, prefix-exact, and Gold-identification package
from explicit successful occurrence spines. -/
theorem exact_working_paper_conclusion_package
    (S : TrimmedPresentationSuccessfulSpineData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  S.toDerivationalExposure.
    finite_nonterminal_exact_working_paper_conclusion_package
      hworking hfan hL

end TrimmedPresentationSuccessfulSpineData

end FiniteSuccessfulOccurrenceRoute


section SuccessfulOccurrenceTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [Finite N]
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable paper-facing endpoint from explicit successful derivation spines. -/
theorem trimmed_successful_derivation_spine_exact_working_main_theorem
    (S : TrimmedPresentationSuccessfulSpineData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  S.exact_working_paper_main_theorem hworking hfan hL

/-- Stable full conclusion package from explicit successful derivation
spines. -/
theorem trimmed_successful_derivation_spine_exact_working_conclusion_package
    (S : TrimmedPresentationSuccessfulSpineData D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  S.exact_working_paper_conclusion_package hworking hfan hL

end SuccessfulOccurrenceTopLevel

end MCFG
