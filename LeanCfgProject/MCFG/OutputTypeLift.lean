/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.OutputTypeRefinement

/-!
# OutputTypeLift.lean

Fourth clean Lean experiment for the fixed-observation MCFG project.

The previous file introduced output-typed nonterminals and output-typed
derivation wrappers.  This file records the next stable layer:

* every ordinary derivation has a canonical output-typed lift;
* any output-typed derivation has its output type determined by the yielded
  tuple;
* terminal, binary, and start rules have small lift/erase bridge lemmas;
* binary rules can be decorated canonically from the actual child tuples.

This is the Lean-friendly core of the paper statement that ordinary derivation
trees lift uniquely to the output-type refinement.  Full uniqueness as equality
of dependent typed trees is intentionally postponed.
-/

namespace MCFG

universe u v w

section OutputTypeDetermination

variable {N : Type v} {α : Type u} {M : Type w} [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- The canonical typed nonterminal attached to a tuple derived from `A`. -/
abbrev CanonicalTypedNonterminal
    (A : N) (x : Tuple α (G.arity A)) : TypedNonterminal G M :=
  TypedNonterminal.ofTuple obs A x

/-- Every ordinary derivation lifts to its canonical output-typed nonterminal. -/
theorem ordinaryDerivation_lifts_canonically
    {A : N} {x : Tuple α (G.arity A)}
    (h : DerivesTuple G A x) :
    OutputTypedDerives (G := G) (obs := obs)
      (CanonicalTypedNonterminal (G := G) (obs := obs) A x) x :=
  OutputTypedDerives.of_derives h

/-- In any output-typed derivation, the stored output type is determined by the
derived tuple. -/
theorem outputType_determined_by_tuple
    {X : TypedNonterminal G M} {x : Tuple α (G.arity X.base)}
    (h : OutputTypedDerives (G := G) (obs := obs) X x) :
    X.out = tupleType obs x :=
  h.tuple_type_eq.symm

/-- Output-typed derivability implies the matching predicate for the same typed
nonterminal and tuple. -/
theorem matches_of_outputTypedDerives
    {X : TypedNonterminal G M} {x : Tuple α (G.arity X.base)}
    (h : OutputTypedDerives (G := G) (obs := obs) X x) :
    TypedNonterminal.Matches obs X x :=
  h.tuple_type_eq

/-- Erasing the typed decoration of a canonical lift recovers the original
ordinary derivation. -/
theorem erase_ordinaryDerivation_lifts_canonically
    {A : N} {x : Tuple α (G.arity A)}
    (h : DerivesTuple G A x) :
    (ordinaryDerivation_lifts_canonically
      (G := G) (obs := obs) h).erase = h := by
  rfl

end OutputTypeDetermination


section TerminalLift

variable {N : Type v} {α : Type u} {M : Type w} [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- A well-typed terminal rule lifts to an output-typed derivation of its
computed typed left-hand side. -/
theorem typedTerminalRule_lifts
    (τ : TypedTerminalRule G) :
    OutputTypedDerives (G := G) (obs := obs)
      (τ.lhs obs)
      (castTuple τ.wellTyped.symm τ.baseRule.outputTuple) := by
  apply OutputTypedDerives.mk
  · exact DerivesTuple.terminal τ.inGrammar τ.wellTyped
  · exact τ.cast_outputTuple_matches_lhs obs

/-- The terminal lift erases to the corresponding ordinary terminal derivation. -/
theorem erase_typedTerminalRule_lifts
    (τ : TypedTerminalRule G) :
    (typedTerminalRule_lifts (G := G) (obs := obs) τ).erase =
      DerivesTuple.terminal τ.inGrammar τ.wellTyped := by
  rfl

end TerminalLift


section BinaryCanonicalDecoration

variable {N : Type v} {α : Type u} {M : Type w} [Monoid M]
variable {G : WorkingMCFG N α}

namespace TypedBinaryRule

/-- Decorate a binary rule by the actual output types of two child tuples. -/
def ofChildTuples
    (obs : α → M)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules)
    (x : Tuple α (G.arity ρ.left))
    (y : Tuple α (G.arity ρ.right)) :
    TypedBinaryRule G M :=
  { baseRule := ρ,
    inGrammar := hρ,
    leftOut := tupleType obs x,
    rightOut := tupleType obs y }

/-- The left child tuple matches the left type of the canonical decoration. -/
theorem left_matches_ofChildTuples
    (obs : α → M)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules)
    (x : Tuple α (G.arity ρ.left))
    (y : Tuple α (G.arity ρ.right)) :
    TypedNonterminal.Matches obs
      ((ofChildTuples (G := G) obs ρ hρ x y).left) x := by
  rfl

/-- The right child tuple matches the right type of the canonical decoration. -/
theorem right_matches_ofChildTuples
    (obs : α → M)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules)
    (x : Tuple α (G.arity ρ.left))
    (y : Tuple α (G.arity ρ.right)) :
    TypedNonterminal.Matches obs
      ((ofChildTuples (G := G) obs ρ hρ x y).right) y := by
  rfl

/-- The parent tuple produced by a binary rule matches the parent type computed
by the canonical decoration. -/
theorem apply_matches_lhs_ofChildTuples
    (obs : α → M)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules)
    (x : Tuple α (G.arity ρ.left))
    (y : Tuple α (G.arity ρ.right)) :
    TypedNonterminal.Matches obs
      ((ofChildTuples (G := G) obs ρ hρ x y).lhs obs)
      (ρ.apply x y) := by
  exact (ofChildTuples (G := G) obs ρ hρ x y).apply_matches_lhs obs
    (left_matches_ofChildTuples (G := G) obs ρ hρ x y)
    (right_matches_ofChildTuples (G := G) obs ρ hρ x y)

end TypedBinaryRule

variable {obs : α → M}

/-- Binary composition of two ordinary child derivations lifts to the output type
computed from the actual child tuples. -/
theorem binaryDerivation_lifts_to_computed_lhs
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules)
    {x : Tuple α (G.arity ρ.left)}
    {y : Tuple α (G.arity ρ.right)}
    (hx : DerivesTuple G ρ.left x)
    (hy : DerivesTuple G ρ.right y) :
    OutputTypedDerives (G := G) (obs := obs)
      ((TypedBinaryRule.ofChildTuples (G := G) obs ρ hρ x y).lhs obs)
      (ρ.apply x y) := by
  apply OutputTypedDerives.mk
  · exact DerivesTuple.binary hρ hx hy
  · exact TypedBinaryRule.apply_matches_lhs_ofChildTuples
      (G := G) obs ρ hρ x y

/-- The previous lift erases to the ordinary binary derivation. -/
theorem erase_binaryDerivation_lifts_to_computed_lhs
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules)
    {x : Tuple α (G.arity ρ.left)}
    {y : Tuple α (G.arity ρ.right)}
    (hx : DerivesTuple G ρ.left x)
    (hy : DerivesTuple G ρ.right y) :
    (binaryDerivation_lifts_to_computed_lhs
      (G := G) (obs := obs) ρ hρ hx hy).erase =
      DerivesTuple.binary hρ hx hy := by
  rfl

end BinaryCanonicalDecoration


section StartErase

variable {N : Type v} {α : Type u} {M : Type w} [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- A typed derivation of the child of a typed start rule erases to an ordinary
start derivation. -/
theorem typedStartRule_erases_to_start_derivation
    (τ : TypedStartRule G M)
    {x : Tuple α (G.arity τ.baseRule.child)}
    (hx : OutputTypedDerives (G := G) (obs := obs) τ.child x) :
    DerivesTuple G G.start (castTuple τ.wellTyped x) :=
  DerivesTuple.start τ.inGrammar hx.erase τ.wellTyped

/-- If the start symbol has arity one, a typed start-rule child derivation gives
membership of the corresponding singleton word after arity transport. -/
theorem mem_stringLanguage_of_typedStartRule
    (τ : TypedStartRule G M)
    {x : Tuple α (G.arity τ.baseRule.child)}
    (hx : OutputTypedDerives (G := G) (obs := obs) τ.child x)
    (hstart : 1 = G.arity G.start)
    (word : Word α)
    (hword : castTuple hstart (singletonTuple word) = castTuple τ.wellTyped x) :
    word ∈ G.StringLanguage := by
  refine ⟨hstart, ?_⟩
  rw [hword]
  exact typedStartRule_erases_to_start_derivation
    (G := G) (obs := obs) τ hx

end StartErase

end MCFG
