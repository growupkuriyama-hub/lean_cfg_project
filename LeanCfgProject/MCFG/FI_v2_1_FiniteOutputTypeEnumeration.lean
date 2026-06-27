import LeanCfgProject.MCFG.FI_v2_1_FiniteRefinedGrammar

/-!
# FI v2.1 Lean experiment: finite output-type enumeration certificates

This file is the nineteenth formalization layer for the FI v2.1 MCFG paper.

The previous layer packaged output-type refined grammars as explicit finite
lists of refined terminal, binary, and start rules.  This file isolates the
finite-output-type enumeration datum that such a construction needs: for each
arity `d`, a finite list of all componentwise output types `Fin d → M`.

The file deliberately keeps the actual construction from `[Fintype M]` out of
scope.  Instead, it records the exact certificate that a later concrete
enumerator must supply.  This is the right abstraction boundary for the paper:
finite monoids make the output-type choices finite; the present layer states
that requirement and connects it to refined nonterminals and refined rules.
-/

namespace FIv21

universe u v w

section OutputTypeEnumeration

variable {N : Type w} {α : Type u}
variable {M : Type v} [Monoid M]

/-- A finite enumeration of all output-type vectors over `M`.

For each arity `d`, the list `types d` is intended to contain every function
`Fin d → M`.  This is a certificate-style representation: later one can build
such an object from `[Fintype M]`, but the subsequent refined-grammar layers
only need the completeness field recorded here. -/
structure OutputTypeEnumeration (M : Type v) where
  types : (d : Nat) → List (Fin d → M)
  complete : ∀ {d : Nat}, ∀ ty : Fin d → M, ty ∈ types d

namespace OutputTypeEnumeration

/-- A type vector is listed by an output-type enumeration. -/
def Lists (E : OutputTypeEnumeration M) {d : Nat} (ty : Fin d → M) : Prop :=
  ty ∈ E.types d

/-- Number of listed output-type vectors at arity `d`. -/
def typeCount (E : OutputTypeEnumeration M) (d : Nat) : Nat :=
  (E.types d).length

/-- Completeness restated using the `Lists` predicate. -/
theorem lists_of_complete
    (E : OutputTypeEnumeration M) {d : Nat} (ty : Fin d → M) :
    E.Lists ty :=
  E.complete ty

/-- A refined nonterminal is supported by an output-type enumeration when its
advertised output-type vector occurs in the list for its base arity. -/
def SupportsRefinedNonterminal
    {G : WorkingMCFG N α}
    (E : OutputTypeEnumeration M) (A : RefinedNonterminal G M) : Prop :=
  A.outTy ∈ E.types (G.arity A.base)

/-- Every refined nonterminal is supported by a complete output-type
enumeration. -/
theorem supports_refinedNonterminal
    {G : WorkingMCFG N α}
    (E : OutputTypeEnumeration M) (A : RefinedNonterminal G M) :
    E.SupportsRefinedNonterminal A :=
  E.complete A.outTy

/-- The actual refined nonterminal associated with a derived tuple has a listed
output type. -/
theorem supports_actualRefinedNonterminal
    {G : WorkingMCFG N α} (obs : α → M)
    (E : OutputTypeEnumeration M)
    (A : N) (x : Tuple α (G.arity A)) :
    E.SupportsRefinedNonterminal
      (actualRefinedNonterminal G obs A x) := by
  exact E.supports_refinedNonterminal
    (actualRefinedNonterminal G obs A x)

/-- The child output-type choices carried by a refined binary rule are listed
by a complete output-type enumeration. -/
def SupportsRefinedBinaryRule
    {G : WorkingMCFG N α} {obs : α → M}
    (E : OutputTypeEnumeration M) (ρ : RefinedBinaryRule G obs) : Prop :=
  ρ.leftTy ∈ E.types (G.arity ρ.rule.left) ∧
  ρ.rightTy ∈ E.types (G.arity ρ.rule.right)

/-- Completeness lists both child output-type choices of every refined binary
rule. -/
theorem supports_refinedBinaryRule
    {G : WorkingMCFG N α} {obs : α → M}
    (E : OutputTypeEnumeration M) (ρ : RefinedBinaryRule G obs) :
    E.SupportsRefinedBinaryRule ρ := by
  constructor
  · exact E.complete ρ.leftTy
  · exact E.complete ρ.rightTy

/-- The child output-type choice carried by a refined start rule is listed by a
complete output-type enumeration. -/
def SupportsRefinedStartRule
    {G : WorkingMCFG N α} {obs : α → M}
    (E : OutputTypeEnumeration M) (ρ : RefinedStartRule G obs) : Prop :=
  ρ.childTy ∈ E.types (G.arity ρ.rule.child)

/-- Completeness lists the child output-type choice of every refined start
rule. -/
theorem supports_refinedStartRule
    {G : WorkingMCFG N α} {obs : α → M}
    (E : OutputTypeEnumeration M) (ρ : RefinedStartRule G obs) :
    E.SupportsRefinedStartRule ρ :=
  E.complete ρ.childTy

/-- The parent output type computed by a binary rule is also listed at the
parent arity. -/
theorem lists_binary_parent_outputType
    {G : WorkingMCFG N α} {obs : α → M}
    (E : OutputTypeEnumeration M)
    (ρ : BinaryRule N α G.arity)
    (leftTy : Fin (G.arity ρ.left) → M)
    (rightTy : Fin (G.arity ρ.right) → M) :
    ρ.outputType obs leftTy rightTy ∈ E.types (G.arity ρ.lhs) :=
  E.complete (ρ.outputType obs leftTy rightTy)

/-- The transported output type computed by a start rule is listed at the start
arity. -/
theorem lists_start_parent_outputType
    {G : WorkingMCFG N α}
    (E : OutputTypeEnumeration M)
    (ρ : StartRule N) (hwt : ρ.WellTyped G)
    (childTy : Fin (G.arity ρ.child) → M) :
    castOutputType hwt childTy ∈ E.types (G.arity G.start) :=
  E.complete (castOutputType hwt childTy)

end OutputTypeEnumeration

end OutputTypeEnumeration

section GrammarEnumerationCertificates

variable {N : Type w} {α : Type u}
variable {M : Type v} [Monoid M]

/-- A grammar together with a complete finite enumeration of output-type
vectors.  The observation is included because the intended use is tied to the
fixed observation of the paper, even though the bare enumeration of vectors
only depends on `M`. -/
structure GrammarOutputTypeEnumeration
    (G : WorkingMCFG N α) (obs : α → M) where
  outputTypes : OutputTypeEnumeration M

namespace GrammarOutputTypeEnumeration

/-- Output-type vectors of a given arity listed for this grammar. -/
def types
    {G : WorkingMCFG N α} {obs : α → M}
    (E : GrammarOutputTypeEnumeration G obs) (d : Nat) :
    List (Fin d → M) :=
  E.outputTypes.types d

/-- Every output-type vector at a grammar arity is listed. -/
theorem complete
    {G : WorkingMCFG N α} {obs : α → M}
    (E : GrammarOutputTypeEnumeration G obs)
    {d : Nat} (ty : Fin d → M) :
    ty ∈ E.types d :=
  E.outputTypes.complete ty

/-- Every refined nonterminal over the grammar has a listed output type. -/
theorem supports_refinedNonterminal
    {G : WorkingMCFG N α} {obs : α → M}
    (E : GrammarOutputTypeEnumeration G obs)
    (A : RefinedNonterminal G M) :
    E.outputTypes.SupportsRefinedNonterminal A :=
  E.outputTypes.supports_refinedNonterminal A

/-- Every actual refined nonterminal generated by a tuple is supported by the
grammar's output-type enumeration. -/
theorem supports_actualRefinedNonterminal
    {G : WorkingMCFG N α} {obs : α → M}
    (E : GrammarOutputTypeEnumeration G obs)
    (A : N) (x : Tuple α (G.arity A)) :
    E.outputTypes.SupportsRefinedNonterminal
      (actualRefinedNonterminal G obs A x) := by
  exact E.outputTypes.supports_actualRefinedNonterminal obs A x

/-- The child type choices of any refined binary rule are supported. -/
theorem supports_refinedBinaryRule
    {G : WorkingMCFG N α} {obs : α → M}
    (E : GrammarOutputTypeEnumeration G obs)
    (ρ : RefinedBinaryRule G obs) :
    E.outputTypes.SupportsRefinedBinaryRule ρ :=
  E.outputTypes.supports_refinedBinaryRule ρ

/-- The child type choice of any refined start rule is supported. -/
theorem supports_refinedStartRule
    {G : WorkingMCFG N α} {obs : α → M}
    (E : GrammarOutputTypeEnumeration G obs)
    (ρ : RefinedStartRule G obs) :
    E.outputTypes.SupportsRefinedStartRule ρ :=
  E.outputTypes.supports_refinedStartRule ρ

end GrammarOutputTypeEnumeration

end GrammarEnumerationCertificates

end FIv21
