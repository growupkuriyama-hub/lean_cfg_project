/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ExactOnce

/-!
# OutputTypeRefinement.lean

Third clean Lean experiment for the fixed-observation MCFG project.

This file adds the first formal layer corresponding to the paper's output-type
refinement `G^h`.  The full construction of the trimmed refined grammar is
postponed.  Here we only formalize the stable core:

* typed nonterminals `(A, p)`, where `p` is the componentwise output type;
* terminal and binary output-type maps;
* typed terminal, binary, and start-rule skeletons;
* the basic type-invariance lemmas for binary composition;
* a tiny output-typed derivation wrapper.

The file is intentionally conservative and contains no `sorry`.
-/

namespace MCFG

universe u v w

section TypedNonterminals

variable {N : Type v} {α : Type u}

/-- A nonterminal of `G` decorated by an output observation type.

For a base nonterminal `A`, the decoration is a function
`Fin (G.arity A) → M`, i.e. one observation value for each tuple component. -/
structure TypedNonterminal (G : WorkingMCFG N α) (M : Type w) where
  base : N
  out : Fin (G.arity base) → M

namespace TypedNonterminal

/-- The arity of a typed nonterminal is the arity of its base nonterminal. -/
def arity {G : WorkingMCFG N α} {M : Type w} (X : TypedNonterminal G M) : Nat :=
  G.arity X.base

/-- A tuple matches the output type stored in a typed nonterminal. -/
def Matches
    {G : WorkingMCFG N α} {M : Type w} [Monoid M]
    (obs : α → M) (X : TypedNonterminal G M)
    (x : Tuple α (G.arity X.base)) : Prop :=
  tupleType obs x = X.out

/-- The typed nonterminal canonically attached to a derived tuple. -/
def ofTuple
    {G : WorkingMCFG N α} {M : Type w} [Monoid M]
    (obs : α → M) (A : N) (x : Tuple α (G.arity A)) :
    TypedNonterminal G M :=
  { base := A, out := tupleType obs x }

@[simp] theorem ofTuple_base
    {G : WorkingMCFG N α} {M : Type w} [Monoid M]
    (obs : α → M) (A : N) (x : Tuple α (G.arity A)) :
    (ofTuple obs A x).base = A := rfl

@[simp] theorem ofTuple_out
    {G : WorkingMCFG N α} {M : Type w} [Monoid M]
    (obs : α → M) (A : N) (x : Tuple α (G.arity A)) :
    (ofTuple obs A x).out = tupleType obs x := rfl

/-- A tuple always matches its canonical output-typed nonterminal. -/
theorem matches_ofTuple
    {G : WorkingMCFG N α} {M : Type w} [Monoid M]
    (obs : α → M) (A : N) (x : Tuple α (G.arity A)) :
    Matches obs (ofTuple obs A x) x := rfl

end TypedNonterminal

end TypedNonterminals


section RuleOutputTypes

variable {N : Type v} {α : Type u} {M : Type w} [Monoid M]

namespace TerminalRule

/-- The output observation type of a terminal rule `A → (a)`. -/
def outputType (obs : α → M) (ρ : TerminalRule N α) : Fin 1 → M :=
  fun _ => evalObs obs [ρ.terminal]

@[simp] theorem outputType_apply
    (obs : α → M) (ρ : TerminalRule N α) (i : Fin 1) :
    outputType obs ρ i = evalObs obs [ρ.terminal] := rfl

/-- The tuple produced by a terminal rule has the terminal rule's output type. -/
theorem tupleType_outputTuple
    (obs : α → M) (ρ : TerminalRule N α) :
    tupleType obs ρ.outputTuple = outputType obs ρ := by
  funext i
  simp [TerminalRule.outputTuple, outputType, tupleType, evalObs]

end TerminalRule

namespace BinaryRule

/-- The output type computed from a binary rule template and two child types. -/
def outputType
    {arity : N → Nat} (obs : α → M) (ρ : BinaryRule N α arity)
    (q : Fin (arity ρ.left) → M) (r : Fin (arity ρ.right) → M) :
    Fin (arity ρ.lhs) → M :=
  evalTemplateTupleObs obs q r ρ.body

/-- Applying a binary rule to child tuples with prescribed output types produces
a parent tuple with the template-computed output type. -/
theorem outputType_sound
    {arity : N → Nat} (obs : α → M) (ρ : BinaryRule N α arity)
    {x : Tuple α (arity ρ.left)}
    {y : Tuple α (arity ρ.right)}
    {q : Fin (arity ρ.left) → M}
    {r : Fin (arity ρ.right) → M}
    (hx : tupleType obs x = q)
    (hy : tupleType obs y = r) :
    tupleType obs (ρ.apply x y) = outputType obs ρ q r := by
  unfold outputType
  rw [BinaryRule.tupleType_apply obs ρ x y, hx, hy]

end BinaryRule

end RuleOutputTypes


section TypedRules

variable {N : Type v} {α : Type u}

/-- A terminal rule of `G`, together with its membership and arity witness.

The output type is computed later from the fixed observation map. -/
structure TypedTerminalRule (G : WorkingMCFG N α) where
  baseRule : TerminalRule N α
  inGrammar : baseRule ∈ G.terminalRules
  wellTyped : G.arity baseRule.lhs = 1

namespace TypedTerminalRule

/-- The typed left-hand side of a terminal rule under a fixed observation. -/
def lhs
    {G : WorkingMCFG N α} {M : Type w} [Monoid M]
    (τ : TypedTerminalRule G) (obs : α → M) :
    TypedNonterminal G M :=
  { base := τ.baseRule.lhs,
    out := fun _ => evalObs obs [τ.baseRule.terminal] }

/-- The terminal rule's explicit output tuple has the computed output type after
transporting along the rule's arity witness. -/
theorem cast_outputTuple_matches_lhs
    {G : WorkingMCFG N α} {M : Type w} [Monoid M]
    (τ : TypedTerminalRule G) (obs : α → M) :
    TypedNonterminal.Matches obs (τ.lhs obs)
      (castTuple τ.wellTyped.symm τ.baseRule.outputTuple) := by
  cases τ.wellTyped
  rfl

end TypedTerminalRule


/-- A binary rule of `G` decorated by output types for its two children. -/
structure TypedBinaryRule (G : WorkingMCFG N α) (M : Type w) where
  baseRule : BinaryRule N α G.arity
  inGrammar : baseRule ∈ G.binaryRules
  leftOut : Fin (G.arity baseRule.left) → M
  rightOut : Fin (G.arity baseRule.right) → M

namespace TypedBinaryRule

/-- The typed left child of a typed binary rule. -/
def left
    {G : WorkingMCFG N α} {M : Type w}
    (τ : TypedBinaryRule G M) :
    TypedNonterminal G M :=
  { base := τ.baseRule.left, out := τ.leftOut }

/-- The typed right child of a typed binary rule. -/
def right
    {G : WorkingMCFG N α} {M : Type w}
    (τ : TypedBinaryRule G M) :
    TypedNonterminal G M :=
  { base := τ.baseRule.right, out := τ.rightOut }

/-- The typed parent of a typed binary rule under a fixed observation. -/
def lhs
    {G : WorkingMCFG N α} {M : Type w} [Monoid M]
    (τ : TypedBinaryRule G M) (obs : α → M) :
    TypedNonterminal G M :=
  { base := τ.baseRule.lhs,
    out := BinaryRule.outputType obs τ.baseRule τ.leftOut τ.rightOut }

/-- If the two child tuples match the stored child types, then the parent tuple
matches the computed parent type. -/
theorem apply_matches_lhs
    {G : WorkingMCFG N α} {M : Type w} [Monoid M]
    (τ : TypedBinaryRule G M) (obs : α → M)
    {x : Tuple α (G.arity τ.baseRule.left)}
    {y : Tuple α (G.arity τ.baseRule.right)}
    (hx : TypedNonterminal.Matches obs τ.left x)
    (hy : TypedNonterminal.Matches obs τ.right y) :
    TypedNonterminal.Matches obs (τ.lhs obs) (τ.baseRule.apply x y) := by
  change tupleType obs (τ.baseRule.apply x y) =
    BinaryRule.outputType obs τ.baseRule τ.leftOut τ.rightOut
  exact BinaryRule.outputType_sound obs τ.baseRule hx hy

end TypedBinaryRule


/-- A start rule of `G` decorated by the output type of its child. -/
structure TypedStartRule (G : WorkingMCFG N α) (M : Type w) where
  baseRule : StartRule N
  inGrammar : baseRule ∈ G.startRules
  wellTyped : G.arity baseRule.child = G.arity G.start
  childOut : Fin (G.arity baseRule.child) → M

namespace TypedStartRule

/-- The typed child selected by a typed start rule. -/
def child
    {G : WorkingMCFG N α} {M : Type w}
    (τ : TypedStartRule G M) :
    TypedNonterminal G M :=
  { base := τ.baseRule.child, out := τ.childOut }

end TypedStartRule

end TypedRules


section OutputTypedDerivations

variable {N : Type v} {α : Type u} {M : Type w} [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- A wrapper saying that `x` is derivable from the base nonterminal of `X` and
has exactly the output type stored in `X`. -/
inductive OutputTypedDerives :
    (X : TypedNonterminal G M) → Tuple α (G.arity X.base) → Prop where
  | mk {X : TypedNonterminal G M} {x : Tuple α (G.arity X.base)}
      (derives : DerivesTuple G X.base x)
      (type_eq : tupleType obs x = X.out) :
      OutputTypedDerives X x

namespace OutputTypedDerives

/-- Erase the output-type decoration from an output-typed derivation. -/
theorem erase
    {X : TypedNonterminal G M} {x : Tuple α (G.arity X.base)}
    (h : OutputTypedDerives (G := G) (obs := obs) X x) :
    DerivesTuple G X.base x := by
  cases h with
  | mk derives _ => exact derives

/-- Recover the output-type invariant from an output-typed derivation. -/
theorem tuple_type_eq
    {X : TypedNonterminal G M} {x : Tuple α (G.arity X.base)}
    (h : OutputTypedDerives (G := G) (obs := obs) X x) :
    tupleType obs x = X.out := by
  cases h with
  | mk _ type_eq => exact type_eq

/-- Every ordinary derivation lifts to the canonical output type of its tuple. -/
theorem of_derives
    {A : N} {x : Tuple α (G.arity A)}
    (h : DerivesTuple G A x) :
    OutputTypedDerives (G := G) (obs := obs)
      (TypedNonterminal.ofTuple obs A x) x := by
  exact OutputTypedDerives.mk h rfl

/-- Binary composition preserves output-typed derivability for a typed binary
rule. -/
theorem binary
    (τ : TypedBinaryRule G M)
    {x : Tuple α (G.arity τ.baseRule.left)}
    {y : Tuple α (G.arity τ.baseRule.right)}
    (hx : OutputTypedDerives (G := G) (obs := obs) τ.left x)
    (hy : OutputTypedDerives (G := G) (obs := obs) τ.right y) :
    OutputTypedDerives (G := G) (obs := obs)
      (τ.lhs obs) (τ.baseRule.apply x y) := by
  apply OutputTypedDerives.mk
  · exact DerivesTuple.binary τ.inGrammar hx.erase hy.erase
  · exact τ.apply_matches_lhs obs hx.tuple_type_eq hy.tuple_type_eq

end OutputTypedDerives

end OutputTypedDerivations

end MCFG
