/- CI fix revision: Basic_CI487_fixed, generated after GitHub Actions #487. -/
/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Defs

/-!
# Basic.lean

First clean Lean experiment for the MCFG fixed finite-observation paper.

This file is intentionally self-contained. It does **not** import the previous
experimental MCFG files, because the old experiment chain may contain procedural
mistakes. The goal of this first restart file is to establish a small, stable
foundation:

* words and tuples;
* fixed monoid observations on words and tuples;
* abstract tuple distributions and fixed-observation substitutability;
* refinement of finite observations;
* concrete named sentence contexts;
* lightweight syntax for working binary linear nondeleting MCFG presentations;
* template evaluation and its compatibility with observations;
* a minimal derivation semantics and characteristic-sample skeleton.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w z

/-- Words over an alphabet. -/
abbrev Word (α : Type u) := List α

/-- A tuple of arity `d` is a `Fin d`-indexed family of words. -/
abbrev Tuple (α : Type u) (d : Nat) := Fin d → Word α

/-- The unique index of a one-component tuple. -/
def finOne : Fin 1 := ⟨0, by decide⟩

/-- The one-component tuple containing a single word. -/
def singletonTuple {α : Type u} (word : Word α) : Tuple α 1 :=
  fun _ => word

@[simp] theorem singletonTuple_apply {α : Type u} (word : Word α) (i : Fin 1) :
    singletonTuple word i = word := rfl

/-- Transport a tuple across an equality of arities. -/
def castTuple {α : Type u} {d e : Nat} (h : d = e) (x : Tuple α d) : Tuple α e := by
  subst h
  exact x

@[simp] theorem castTuple_rfl {α : Type u} {d : Nat} (x : Tuple α d) :
    castTuple (rfl : d = d) x = x := rfl


section Observation

variable {α : Type u} {M : Type v} [Monoid M]

/-- Extend a letter observation `obs : α → M` multiplicatively to words. -/
def evalObs (obs : α → M) : Word α → M
  | [] => 1
  | a :: rest => obs a * evalObs obs rest

@[simp] theorem evalObs_nil (obs : α → M) :
    evalObs obs ([] : Word α) = 1 := rfl

@[simp] theorem evalObs_cons (obs : α → M) (a : α) (rest : Word α) :
    evalObs obs (a :: rest) = obs a * evalObs obs rest := rfl

/-- Multiplicativity of the word observation. -/
theorem evalObs_append (obs : α → M) (u1 u2 : Word α) :
    evalObs obs (u1 ++ u2) = evalObs obs u1 * evalObs obs u2 := by
  induction u1 with
  | nil =>
      simp [evalObs]
  | cons a rest ih =>
      simp [evalObs, ih, mul_assoc]

/-- Componentwise observation type of a tuple. -/
def tupleType {d : Nat} (obs : α → M) (x : Tuple α d) : Fin d → M :=
  fun i => evalObs obs (x i)

/-- A small bundled wrapper for an explicit finite observation interface.

The actual multiplication table is represented by the finite monoid structure
on `M`; the letter map is stored as `obs`. -/
structure ExplicitFiniteObservation (α : Type u) (M : Type v) [Monoid M] [Fintype M] where
  obs : α → M

end Observation


section AbstractContexts

variable {α : Type u} {M : Type v} [Monoid M]
variable {Ctx : Nat → Type w}

-- An arity-indexed filling operation for contexts.
variable (fill : ∀ d : Nat, Ctx d → Tuple α d → Word α)

/-- The distribution of an arity-`d` tuple: all contexts that accept it. -/
def Distribution {d : Nat} (L : Set (Word α)) (x : Tuple α d) : Set (Ctx d) :=
  { c | fill d c x ∈ L }

/-- Two tuples share at least one accepting context. -/
def SharesContext {d : Nat} (L : Set (Word α)) (x y : Tuple α d) : Prop :=
  ∃ c : Ctx d, fill d c x ∈ L ∧ fill d c y ∈ L

/-- Abstract `(f,h)`-tuple substitutability.

Inside a fixed componentwise observation fiber, one shared accepting context
forces equality of all accepting contexts. -/
def FixedTupleSubstitutable (f : Nat) (obs : α → M) (L : Set (Word α)) : Prop :=
  ∀ {d : Nat}, d ≤ f → 0 < d →
    ∀ x y : Tuple α d,
      tupleType obs x = tupleType obs y →
      SharesContext fill L x y →
      Distribution fill L x = Distribution fill L y

end AbstractContexts


section Refinement

variable {α : Type u}
variable {M : Type v} {M' : Type w}
variable [Monoid M] [Monoid M']

/-- `obs'` refines `obs` if a multiplication-preserving map from the finer
monoid to the coarser monoid commutes with letter observations. -/
structure Refines (obs : α → M) (obs' : α → M') where
  map : M' → M
  map_one : map 1 = 1
  map_mul : ∀ x y : M', map (x * y) = map x * map y
  comm : ∀ a : α, map (obs' a) = obs a

variable {obs : α → M} {obs' : α → M'}

/-- Word observation commutes with refinement. -/
theorem evalObs_refines (r : Refines obs obs') (word : Word α) :
    r.map (evalObs obs' word) = evalObs obs word := by
  induction word with
  | nil =>
      exact r.map_one
  | cons a rest ih =>
      change r.map (obs' a * evalObs obs' rest) = obs a * evalObs obs rest
      rw [r.map_mul, r.comm a, ih]

/-- Pointwise tuple-type compatibility under refinement. -/
theorem tupleType_refines_apply {d : Nat} (r : Refines obs obs')
    (x : Tuple α d) (i : Fin d) :
    r.map (tupleType obs' x i) = tupleType obs x i := by
  exact evalObs_refines r (x i)

/-- Componentwise tuple types commute with refinement. -/
theorem tupleType_refines {d : Nat} (r : Refines obs obs') (x : Tuple α d) :
    (fun i : Fin d => r.map (tupleType obs' x i)) = tupleType obs x := by
  funext i
  exact tupleType_refines_apply r x i

variable {Ctx : Nat → Type z}
variable (fill : ∀ d : Nat, Ctx d → Tuple α d → Word α)

/-- Monotonicity under refinement of the fixed observation morphism. -/
theorem fixedTupleSubstitutable_of_refines
    {f : Nat} {L : Set (Word α)}
    (r : Refines obs obs')
    (hL : FixedTupleSubstitutable fill f obs L) :
    FixedTupleSubstitutable fill f obs' L := by
  intro d hd hpos x y htype hshare
  have hcoarse : tupleType obs x = tupleType obs y := by
    funext i
    have hx : tupleType obs x i = r.map (tupleType obs' x i) :=
      (tupleType_refines_apply r x i).symm
    have hxy : r.map (tupleType obs' x i) = r.map (tupleType obs' y i) := by
      exact congrArg r.map (congrFun htype i)
    have hy : r.map (tupleType obs' y i) = tupleType obs y i :=
      tupleType_refines_apply r y i
    exact hx.trans (hxy.trans hy)
  exact hL hd hpos x y hcoarse hshare

end Refinement


section NamedSentenceContexts

variable {α : Type u}

/-- A raw named sentence context of arity `d`.

`chunks` are the terminal pieces around holes. `holes` records which tuple
component is placed at each hole occurrence. -/
structure RawNamedSentenceContext (α : Type u) (d : Nat) where
  chunks : List (Word α)
  holes : List (Fin d)

namespace RawNamedSentenceContext

variable {d : Nat}

/-- Well-formedness for paper-style named sentence contexts:
one more terminal chunk than holes, no duplicated named hole, and every named
hole appears. -/
def WellFormed (c : RawNamedSentenceContext α d) : Prop :=
  c.chunks.length = c.holes.length + 1 ∧
  c.holes.Nodup ∧
  ∀ i : Fin d, i ∈ c.holes

end RawNamedSentenceContext

/-- Well-formed named sentence contexts. -/
abbrev NamedSentenceContext (α : Type u) (d : Nat) :=
  { c : RawNamedSentenceContext α d // c.WellFormed }

/-- Total auxiliary filling operation for raw contexts.

On well-formed contexts this is the intended named-hole substitution.
Malformed cases are made total only to keep the function easy to use. -/
def fillNamedAux {d : Nat} (x : Tuple α d) : List (Fin d) → List (Word α) → Word α
  | [], [] => []
  | [], chunk :: _ => chunk
  | h :: hs, [] => x h ++ fillNamedAux x hs []
  | h :: hs, chunk :: chunks => chunk ++ x h ++ fillNamedAux x hs chunks

/-- Fill a raw named sentence context with a tuple. -/
def rawNamedFill {d : Nat} (c : RawNamedSentenceContext α d) (x : Tuple α d) :
    Word α :=
  fillNamedAux x c.holes c.chunks

/-- Fill a well-formed named sentence context with a tuple. -/
def namedFill : ∀ d : Nat, NamedSentenceContext α d → Tuple α d → Word α :=
  fun _ c x => rawNamedFill c.1 x

/-- Named-context distribution. -/
def NamedDistribution {d : Nat} (L : Set (Word α)) (x : Tuple α d) :
    Set (NamedSentenceContext α d) :=
  Distribution namedFill L x

/-- Shared accepting named context. -/
def NamedSharesContext {d : Nat} (L : Set (Word α)) (x y : Tuple α d) : Prop :=
  SharesContext namedFill L x y

/-- Fixed-observation tuple substitutability specialized to named contexts. -/
def FixedNamedTupleSubstitutable
    {M : Type v} [Monoid M]
    (f : Nat) (obs : α → M) (L : Set (Word α)) : Prop :=
  FixedTupleSubstitutable namedFill f obs L

/-- Ordinary two-sided one-hole context as a raw named context. -/
def rawTwoSidedAsNamed (left right : Word α) : RawNamedSentenceContext α 1 :=
  { chunks := [left, right], holes := [finOne] }

@[simp] theorem rawNamedFill_twoSided (left right : Word α) (x : Tuple α 1) :
    rawNamedFill (rawTwoSidedAsNamed left right) x =
      left ++ x finOne ++ right := by
  simp [rawNamedFill, rawTwoSidedAsNamed, fillNamedAux]

theorem rawNamedFill_congr_tuple {d : Nat}
    (c : RawNamedSentenceContext α d) {x y : Tuple α d} (h : x = y) :
    rawNamedFill c x = rawNamedFill c y := by
  subst h
  rfl

theorem namedFill_congr_tuple {d : Nat}
    (c : NamedSentenceContext α d) {x y : Tuple α d} (h : x = y) :
    namedFill d c x = namedFill d c y := by
  subst h
  rfl

theorem fixedNamedTupleSubstitutable_of_refines
    {M : Type v} {M' : Type w}
    [Monoid M] [Monoid M']
    {obs : α → M} {obs' : α → M'}
    {f : Nat} {L : Set (Word α)}
    (r : Refines obs obs')
    (hL : FixedNamedTupleSubstitutable f obs L) :
    FixedNamedTupleSubstitutable f obs' L := by
  exact fixedTupleSubstitutable_of_refines namedFill r hL

end NamedSentenceContexts


section Templates

variable {α : Type u}

/-- Atoms in a binary MCFG template. -/
inductive TemplateAtom (α : Type u) (dB dC : Nat) where
  | terminal : α → TemplateAtom α dB dC
  | leftVar : Fin dB → TemplateAtom α dB dC
  | rightVar : Fin dC → TemplateAtom α dB dC
  deriving Repr

/-- A template word is a list of terminals and child-component variables. -/
abbrev TemplateWord (α : Type u) (dB dC : Nat) :=
  List (TemplateAtom α dB dC)

/-- Evaluate one template atom under a pair of child tuples. -/
def evalTemplateAtom {dB dC : Nat}
    (x : Tuple α dB) (y : Tuple α dC) :
    TemplateAtom α dB dC → Word α
  | TemplateAtom.terminal a => [a]
  | TemplateAtom.leftVar i => x i
  | TemplateAtom.rightVar j => y j

/-- Simultaneous substitution into a template word. -/
def evalTemplateWord {dB dC : Nat}
    (x : Tuple α dB) (y : Tuple α dC) :
    TemplateWord α dB dC → Word α
  | [] => []
  | atom :: rest => evalTemplateAtom x y atom ++ evalTemplateWord x y rest

@[simp] theorem evalTemplateWord_nil {dB dC : Nat}
    (x : Tuple α dB) (y : Tuple α dC) :
    evalTemplateWord x y ([] : TemplateWord α dB dC) = [] := rfl

@[simp] theorem evalTemplateWord_cons {dB dC : Nat}
    (x : Tuple α dB) (y : Tuple α dC)
    (atom : TemplateAtom α dB dC) (rest : TemplateWord α dB dC) :
    evalTemplateWord x y (atom :: rest) =
      evalTemplateAtom x y atom ++ evalTemplateWord x y rest := rfl

/-- A binary template tuple with output arity `e`. -/
abbrev TemplateTuple (α : Type u) (e dB dC : Nat) :=
  Fin e → TemplateWord α dB dC

/-- Evaluate a whole template tuple. -/
def evalTemplateTuple {e dB dC : Nat}
    (body : TemplateTuple α e dB dC)
    (x : Tuple α dB) (y : Tuple α dC) : Tuple α e :=
  fun i => evalTemplateWord x y (body i)

/-- Lightweight nondeleting condition: every child component occurs at least
once somewhere in the body.

The paper's exact working form asks for exactly once. This first Lean layer
keeps the weaker predicate so that later experiments can add exact-once
counting separately. -/
def TemplateTuple.Nondeleting {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) : Prop :=
  (∀ i : Fin dB, ∃ o : Fin e, TemplateAtom.leftVar i ∈ body o) ∧
  (∀ j : Fin dC, ∃ o : Fin e, TemplateAtom.rightVar j ∈ body o)

section TemplateObservation

variable {M : Type v} [Monoid M]

/-- Observation-level evaluation of a template atom. -/
def evalTemplateAtomObs {dB dC : Nat}
    (obs : α → M) (q : Fin dB → M) (r : Fin dC → M) :
    TemplateAtom α dB dC → M
  | TemplateAtom.terminal a => obs a
  | TemplateAtom.leftVar i => q i
  | TemplateAtom.rightVar j => r j

/-- Observation-level evaluation of a template word. -/
def evalTemplateWordObs {dB dC : Nat}
    (obs : α → M) (q : Fin dB → M) (r : Fin dC → M) :
    TemplateWord α dB dC → M
  | [] => 1
  | atom :: rest => evalTemplateAtomObs obs q r atom *
      evalTemplateWordObs obs q r rest

/-- Observation-level evaluation of a template tuple. -/
def evalTemplateTupleObs {e dB dC : Nat}
    (obs : α → M) (q : Fin dB → M) (r : Fin dC → M)
    (body : TemplateTuple α e dB dC) : Fin e → M :=
  fun i => evalTemplateWordObs obs q r (body i)

theorem evalTemplateAtom_obs {dB dC : Nat}
    (obs : α → M) (x : Tuple α dB) (y : Tuple α dC)
    (atom : TemplateAtom α dB dC) :
    evalObs obs (evalTemplateAtom x y atom) =
      evalTemplateAtomObs obs (tupleType obs x) (tupleType obs y) atom := by
  cases atom <;> simp [evalTemplateAtom, evalTemplateAtomObs, tupleType, evalObs]

theorem evalTemplateWord_obs {dB dC : Nat}
    (obs : α → M) (x : Tuple α dB) (y : Tuple α dC)
    (word : TemplateWord α dB dC) :
    evalObs obs (evalTemplateWord x y word) =
      evalTemplateWordObs obs (tupleType obs x) (tupleType obs y) word := by
  induction word with
  | nil =>
      simp [evalTemplateWord, evalTemplateWordObs]
  | cons atom rest ih =>
      simp [evalTemplateWord, evalTemplateWordObs, evalObs_append,
        evalTemplateAtom_obs, ih]

theorem evalTemplateTuple_obs {e dB dC : Nat}
    (obs : α → M) (body : TemplateTuple α e dB dC)
    (x : Tuple α dB) (y : Tuple α dC) :
    tupleType obs (evalTemplateTuple body x y) =
      evalTemplateTupleObs obs (tupleType obs x) (tupleType obs y) body := by
  funext i
  exact evalTemplateWord_obs obs x y (body i)

end TemplateObservation

end Templates


section GrammarSyntax

variable {N : Type v} {α : Type u}

/-- A start rule `S → A`, represented by its child. -/
structure StartRule (N : Type v) where
  child : N
  deriving Repr

/-- A terminal rule `A → (a)`. -/
structure TerminalRule (N : Type v) (α : Type u) where
  lhs : N
  terminal : α
  deriving Repr

namespace TerminalRule

/-- Terminal rules are well-typed when their left-hand side has arity one. -/
def WellTyped (arity : N → Nat) (ρ : TerminalRule N α) : Prop :=
  arity ρ.lhs = 1

/-- The one-component tuple generated by a terminal rule. -/
def outputTuple (ρ : TerminalRule N α) : Tuple α 1 :=
  fun _ => [ρ.terminal]

@[simp] theorem outputTuple_apply (ρ : TerminalRule N α) (i : Fin 1) :
    ρ.outputTuple i = [ρ.terminal] := rfl

end TerminalRule

/-- A binary MCFG rule with dependent arities. -/
structure BinaryRule (N : Type v) (α : Type u) (arity : N → Nat) where
  lhs : N
  left : N
  right : N
  body : TemplateTuple α (arity lhs) (arity left) (arity right)

namespace BinaryRule

/-- Apply a binary rule to two child tuples. -/
def apply {arity : N → Nat} (ρ : BinaryRule N α arity)
    (x : Tuple α (arity ρ.left))
    (y : Tuple α (arity ρ.right)) : Tuple α (arity ρ.lhs) :=
  evalTemplateTuple ρ.body x y

/-- Nondeleting predicate for a binary rule. -/
def Nondeleting {arity : N → Nat} (ρ : BinaryRule N α arity) : Prop :=
  TemplateTuple.Nondeleting ρ.body

@[simp] theorem apply_component {arity : N → Nat} (ρ : BinaryRule N α arity)
    (x : Tuple α (arity ρ.left))
    (y : Tuple α (arity ρ.right))
    (i : Fin (arity ρ.lhs)) :
    ρ.apply x y i = evalTemplateWord x y (ρ.body i) := rfl

/-- Observation type of the output of a binary rule is determined by the child
observation types and the rule template. -/
theorem tupleType_apply {M : Type w} [Monoid M]
    {arity : N → Nat} (obs : α → M) (ρ : BinaryRule N α arity)
    (x : Tuple α (arity ρ.left))
    (y : Tuple α (arity ρ.right)) :
    tupleType obs (ρ.apply x y) =
      evalTemplateTupleObs obs (tupleType obs x) (tupleType obs y) ρ.body := by
  exact evalTemplateTuple_obs obs ρ.body x y

end BinaryRule

/-- A lightweight record for working binary MCFG presentations. -/
structure WorkingMCFG (N : Type v) (α : Type u) where
  start : N
  arity : N → Nat
  arity_pos : ∀ A : N, 0 < arity A
  startRules : List (StartRule N)
  terminalRules : List (TerminalRule N α)
  binaryRules : List (BinaryRule N α arity)

namespace StartRule

/-- A start rule is well-typed when the child has the same arity as the start
symbol. Under the paper's working assumptions both are one. -/
def WellTyped (G : WorkingMCFG N α) (ρ : StartRule N) : Prop :=
  G.arity ρ.child = G.arity G.start

end StartRule

namespace WorkingMCFG

/-- Fan-out bound. -/
def FanoutAtMost (G : WorkingMCFG N α) (f : Nat) : Prop :=
  ∀ A : N, G.arity A ≤ f

/-- The start symbol has fan-out one. -/
def StartArityOne (G : WorkingMCFG N α) : Prop :=
  G.arity G.start = 1

/-- All start rules are well-typed. -/
def StartRulesWellTyped (G : WorkingMCFG N α) : Prop :=
  ∀ ρ : StartRule N, ρ ∈ G.startRules → ρ.WellTyped G

/-- All terminal rules are well-typed. -/
def TerminalRulesWellTyped (G : WorkingMCFG N α) : Prop :=
  ∀ ρ : TerminalRule N α, ρ ∈ G.terminalRules →
    TerminalRule.WellTyped G.arity ρ

/-- All binary rules satisfy the nondeleting side condition. -/
def BinaryRulesNondeleting (G : WorkingMCFG N α) : Prop :=
  ∀ ρ : BinaryRule N α G.arity, ρ ∈ G.binaryRules →
    BinaryRule.Nondeleting ρ

/-- The presentation-level working side conditions represented in this first
file. Exact-once linearity and start separation are intentionally postponed. -/
def BasicWorkingConditions (G : WorkingMCFG N α) : Prop :=
  G.StartArityOne ∧
  G.StartRulesWellTyped ∧
  G.TerminalRulesWellTyped ∧
  G.BinaryRulesNondeleting

/-- If a grammar has fan-out at most `f`, then each listed binary rule has
parent and children arities at most `f`. -/
theorem binaryRule_arities_le_of_fanout
    (G : WorkingMCFG N α) {f : Nat} (hG : G.FanoutAtMost f)
    {ρ : BinaryRule N α G.arity} (_hρ : ρ ∈ G.binaryRules) :
    G.arity ρ.lhs ≤ f ∧ G.arity ρ.left ≤ f ∧ G.arity ρ.right ≤ f := by
  exact ⟨hG ρ.lhs, hG ρ.left, hG ρ.right⟩

end WorkingMCFG

end GrammarSyntax


section DerivationSemantics

variable {N : Type v} {α : Type u}

/-- Minimal tuple-derivation semantics for the lightweight grammar syntax. -/
inductive DerivesTuple (G : WorkingMCFG N α) :
    (A : N) → Tuple α (G.arity A) → Prop where
  | terminal
      {ρ : TerminalRule N α}
      (hρ : ρ ∈ G.terminalRules)
      (hwt : G.arity ρ.lhs = 1) :
      DerivesTuple G ρ.lhs
        (castTuple hwt.symm ρ.outputTuple)
  | binary
      {ρ : BinaryRule N α G.arity}
      (hρ : ρ ∈ G.binaryRules)
      {x : Tuple α (G.arity ρ.left)}
      {y : Tuple α (G.arity ρ.right)}
      (hx : DerivesTuple G ρ.left x)
      (hy : DerivesTuple G ρ.right y) :
      DerivesTuple G ρ.lhs (ρ.apply x y)
  | start
      {ρ : StartRule N}
      (hρ : ρ ∈ G.startRules)
      {x : Tuple α (G.arity ρ.child)}
      (hx : DerivesTuple G ρ.child x)
      (hwt : G.arity ρ.child = G.arity G.start) :
      DerivesTuple G G.start (castTuple hwt x)

/-- The generated string language of a grammar. -/
def StringLanguage (G : WorkingMCFG N α) : Set (Word α) :=
  { word | ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple word)) }

namespace WorkingMCFG

/-- Namespace alias for projection notation. -/
abbrev StringLanguage (G : WorkingMCFG N α) : Set (Word α) :=
  MCFG.StringLanguage G

end WorkingMCFG

/-- If the start symbol derives the singleton tuple for `word`, then `word`
belongs to the string language. -/
theorem mem_StringLanguage_of_start_derives
    (G : WorkingMCFG N α) (word : Word α)
    (hstart : 1 = G.arity G.start)
    (hw : DerivesTuple G G.start (castTuple hstart (singletonTuple word))) :
    word ∈ G.StringLanguage := by
  exact ⟨hstart, hw⟩

/-- Unpack membership in the string language. -/
theorem start_derives_of_mem_StringLanguage
    (G : WorkingMCFG N α) (word : Word α)
    (hw : word ∈ G.StringLanguage) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple word)) := by
  exact hw

end DerivationSemantics


section GrammarContextBridge

variable {N : Type v} {α : Type u}

/-- A derived tuple exposed by an accepting named sentence context. -/
def ExposedWithContext
    (G : WorkingMCFG N α) (A : N)
    (x : Tuple α (G.arity A))
    (c : NamedSentenceContext α (G.arity A)) : Prop :=
  DerivesTuple G A x ∧ namedFill (G.arity A) c x ∈ G.StringLanguage

/-- Grammar-level named distribution. -/
def GrammarNamedDistribution
    (G : WorkingMCFG N α) {d : Nat} (x : Tuple α d) :
    Set (NamedSentenceContext α d) :=
  NamedDistribution G.StringLanguage x

/-- Grammar-level shared named context. -/
def GrammarNamedSharesContext
    (G : WorkingMCFG N α) {d : Nat} (x y : Tuple α d) : Prop :=
  NamedSharesContext G.StringLanguage x y

theorem grammarNamedSharesContext_of_two_exposures
    (G : WorkingMCFG N α) (A : N)
    {x y : Tuple α (G.arity A)}
    {c : NamedSentenceContext α (G.arity A)}
    (hx : ExposedWithContext G A x c)
    (hy : ExposedWithContext G A y c) :
    GrammarNamedSharesContext G x y := by
  exact ⟨c, hx.2, hy.2⟩

/-- Same type plus one shared accepting named context forces equality of
named-context distributions, assuming fixed-observation tuple substitutability. -/
theorem grammarNamedDistribution_eq_of_fixed_substitutable
    {M : Type w} [Monoid M]
    (G : WorkingMCFG N α) (A : N)
    {f : Nat} {obs : α → M}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {x y : Tuple α (G.arity A)}
    (htype : tupleType obs x = tupleType obs y)
    (hshare : GrammarNamedSharesContext G x y) :
    GrammarNamedDistribution G x = GrammarNamedDistribution G y := by
  exact hL (hfan A) (G.arity_pos A) x y htype hshare

end GrammarContextBridge


section PositiveSamples

variable {N : Type v} {α : Type u}

/-- A finite positive sample for a grammar. -/
def PositiveSample (G : WorkingMCFG N α) (K : Finset (Word α)) : Prop :=
  ∀ word : Word α, word ∈ K → word ∈ G.StringLanguage

/-- Sample-level named-context distribution. -/
def SampleNamedDistribution
    {d : Nat} (K : Finset (Word α)) (x : Tuple α d) :
    Set (NamedSentenceContext α d) :=
  { c | namedFill d c x ∈ K }

/-- Sample-level shared named context. -/
def SampleNamedSharesContext
    {d : Nat} (K : Finset (Word α)) (x y : Tuple α d) : Prop :=
  ∃ c : NamedSentenceContext α d,
    namedFill d c x ∈ K ∧ namedFill d c y ∈ K

/-- Every sample context is a target context when the sample is positive. -/
theorem sampleNamedDistribution_subset_grammarNamedDistribution
    (G : WorkingMCFG N α) {d : Nat} (K : Finset (Word α))
    (hK : PositiveSample G K) (x : Tuple α d) :
    SampleNamedDistribution K x ⊆ GrammarNamedDistribution G x := by
  intro c hc
  exact hK (namedFill d c x) hc

/-- A sample-level shared context is a genuine target shared context whenever
the sample is positive. -/
theorem sampleNamedSharesContext_to_grammarNamedSharesContext
    (G : WorkingMCFG N α) {d : Nat} (K : Finset (Word α))
    (hK : PositiveSample G K) {x y : Tuple α d}
    (hshare : SampleNamedSharesContext K x y) :
    GrammarNamedSharesContext G x y := by
  rcases hshare with ⟨c, hx, hy⟩
  exact ⟨c, hK (namedFill d c x) hx, hK (namedFill d c y) hy⟩

/-- Sample-level safe merge test. -/
def SampleSafeMerge
    {M : Type w} [Monoid M]
    {d : Nat} (K : Finset (Word α)) (obs : α → M)
    (x y : Tuple α d) : Prop :=
  tupleType obs x = tupleType obs y ∧ SampleNamedSharesContext K x y

/-- Soundness of the sample-level safe merge test. -/
theorem sampleSafeMerge_sound_for_grammar
    {M : Type w} [Monoid M]
    (G : WorkingMCFG N α) (A : N)
    {f : Nat} {obs : α → M}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (K : Finset (Word α))
    (hK : PositiveSample G K)
    {x y : Tuple α (G.arity A)}
    (hmerge : SampleSafeMerge K obs x y) :
    GrammarNamedDistribution G x = GrammarNamedDistribution G y := by
  have hshare : GrammarNamedSharesContext G x y :=
    sampleNamedSharesContext_to_grammarNamedSharesContext G K hK hmerge.2
  exact grammarNamedDistribution_eq_of_fixed_substitutable
    G A hfan hL hmerge.1 hshare

end PositiveSamples


section LearningSkeleton

variable {α : Type u}
variable {Hyp : Type v}

/-- A language-valued hypothesis interpretation. -/
abbrev HypLanguage (α : Type u) (Hyp : Type v) := Hyp → Set (Word α)

/-- Characteristic sample condition for a set-driven learner on finite samples. -/
def CharacteristicSample
    (lang : HypLanguage α Hyp)
    (learner : Finset (Word α) → Hyp)
    (S : Finset (Word α))
    (L : Set (Word α)) : Prop :=
  (S : Set (Word α)) ⊆ L ∧
  ∀ K : Finset (Word α),
    (S : Set (Word α)) ⊆ (K : Set (Word α)) →
    (K : Set (Word α)) ⊆ L →
    lang (learner K) = L

/-- Once a finite sample contains a characteristic sample and remains positive,
the learner's hypothesis is exactly the target language. -/
theorem characteristicSample_correct
    (lang : HypLanguage α Hyp)
    (learner : Finset (Word α) → Hyp)
    {S K : Finset (Word α)} {L : Set (Word α)}
    (hS : CharacteristicSample lang learner S L)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKL : (K : Set (Word α)) ⊆ L) :
    lang (learner K) = L := by
  exact hS.2 K hSK hKL

end LearningSkeleton

end MCFG
