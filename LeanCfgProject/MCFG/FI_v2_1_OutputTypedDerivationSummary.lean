import LeanCfgProject.MCFG.FI_v2_1_RefinedRules

/-!
# FI v2.1 Lean experiment: output-typed derivation summary

This file is the sixteenth formalization layer for the FI v2.1 MCFG paper.

The previous file introduced output-refined terminal, binary, and start-rule
steps.  This short layer records the semantic summary that every ordinary tuple
derivation has an associated *actual* output-typed refined nonterminal, namely
its base nonterminal together with the componentwise observation type of the
derived tuple.

This is still not the full refined grammar construction, but it is the clean
semantic target for that construction: the future refined grammar should derive
exactly these output-typed derivations.
-/

namespace FIv21

universe u v w

section OutputTypedLanguages

variable {N : Type w} {α : Type u}
variable {M : Type v} [Monoid M]

/-- The tuple language of a refined nonterminal: the underlying grammar derives
the tuple and the tuple has the refined nonterminal's advertised output type. -/
def OutputTypedTupleLanguage
    (G : WorkingMCFG N α) (obs : α → M)
    (A : RefinedNonterminal G M) : Set (Tuple α (G.arity A.base)) :=
  { x | DerivesOutputTypedTuple G obs A x }

/-- Membership in an output-typed tuple language implies ordinary tuple
derivability by the base nonterminal. -/
theorem outputTypedTupleLanguage_subset_tupleLanguage
    (G : WorkingMCFG N α) (obs : α → M)
    (A : RefinedNonterminal G M) :
    OutputTypedTupleLanguage G obs A ⊆ TupleLanguage G A.base := by
  intro x hx
  exact DerivesOutputTypedTuple.derives hx

/-- Membership in an output-typed tuple language also gives the advertised
componentwise output type. -/
theorem outputTypedTupleLanguage_has_type
    (G : WorkingMCFG N α) (obs : α → M)
    (A : RefinedNonterminal G M)
    {x : Tuple α (G.arity A.base)}
    (hx : x ∈ OutputTypedTupleLanguage G obs A) :
    tupleType obs x = A.outTy :=
  DerivesOutputTypedTuple.has_output_type hx

/-- The actual refined nonterminal associated with a concrete tuple derivation:
keep the base nonterminal and record the tuple's true componentwise observation
type. -/
def actualRefinedNonterminal
    (G : WorkingMCFG N α) (obs : α → M)
    (A : N) (x : Tuple α (G.arity A)) : RefinedNonterminal G M :=
  { base := A
    outTy := tupleType obs x }

@[simp] theorem actualRefinedNonterminal_base
    (G : WorkingMCFG N α) (obs : α → M)
    (A : N) (x : Tuple α (G.arity A)) :
    (actualRefinedNonterminal G obs A x).base = A := rfl

@[simp] theorem actualRefinedNonterminal_outTy
    (G : WorkingMCFG N α) (obs : α → M)
    (A : N) (x : Tuple α (G.arity A)) :
    (actualRefinedNonterminal G obs A x).outTy = tupleType obs x := rfl

/-- Every ordinary derivation lifts to the actual output-typed refined
nonterminal determined by the derived tuple. -/
theorem derives_actualRefinedNonterminal
    {G : WorkingMCFG N α} {obs : α → M}
    {A : N} {x : Tuple α (G.arity A)}
    (hx : DerivesTuple G A x) :
    DerivesOutputTypedTuple G obs
      (actualRefinedNonterminal G obs A x) x := by
  constructor
  · exact hx
  · rfl

/-- Conversely, an output-typed derivation for the actual refined nonterminal is
just an ordinary derivation. -/
theorem actualRefinedNonterminal_iff_derives
    {G : WorkingMCFG N α} {obs : α → M}
    {A : N} {x : Tuple α (G.arity A)} :
    DerivesOutputTypedTuple G obs
      (actualRefinedNonterminal G obs A x) x ↔
    DerivesTuple G A x := by
  constructor
  · intro h
    exact DerivesOutputTypedTuple.derives h
  · intro h
    exact derives_actualRefinedNonterminal h

/-- Every tuple in the untyped language is covered at its actual output type.

A tempting alternative is to existentially quantify an arbitrary refined
nonterminal `R` and then assert `R.base = A`, `R.outTy = tupleType obs x`, and
`DerivesOutputTypedTuple G obs R x`.  In Lean this creates dependent-arity
transport obligations, because the type of `R.outTy` and the tuple arity in
`DerivesOutputTypedTuple` depend on `R.base`.  The statement below keeps the
refined nonterminal definitionally equal to the actual one, avoiding those
spurious transports while expressing the same semantic coverage fact. -/
theorem tupleLanguage_covered_by_outputTypes
    (G : WorkingMCFG N α) (obs : α → M)
    (A : N) (x : Tuple α (G.arity A))
    (hx : x ∈ TupleLanguage G A) :
    x ∈ OutputTypedTupleLanguage G obs
      (actualRefinedNonterminal G obs A x) := by
  exact derives_actualRefinedNonterminal hx

/-- A packaged version of `tupleLanguage_covered_by_outputTypes` retaining the
actual refined nonterminal as data.  The typed derivation is intentionally kept
at the definitionally equal actual nonterminal, rather than at an arbitrary
existential variable, to avoid dependent arity transport. -/
theorem tupleLanguage_covered_by_actual_outputType
    (G : WorkingMCFG N α) (obs : α → M)
    (A : N) (x : Tuple α (G.arity A))
    (hx : x ∈ TupleLanguage G A) :
    ∃ R : RefinedNonterminal G M,
      R = actualRefinedNonterminal G obs A x ∧
      x ∈ OutputTypedTupleLanguage G obs
        (actualRefinedNonterminal G obs A x) := by
  refine ⟨actualRefinedNonterminal G obs A x, rfl, ?_⟩
  exact tupleLanguage_covered_by_outputTypes G obs A x hx

/-- Output-type refinement is semantically conservative at the tuple level:
forgetting the output type of any refined derivation yields an ordinary
derivation, and every ordinary derivation appears at its actual output type. -/
def OutputTypeRefinementConservative
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  (∀ R : RefinedNonterminal G M,
      OutputTypedTupleLanguage G obs R ⊆ TupleLanguage G R.base) ∧
  (∀ A : N, ∀ x : Tuple α (G.arity A),
      x ∈ TupleLanguage G A →
      x ∈ OutputTypedTupleLanguage G obs
        (actualRefinedNonterminal G obs A x))

/-- The semantic output-type refinement relation is conservative for every
grammar and every fixed observation. -/
theorem outputTypeRefinementConservative
    (G : WorkingMCFG N α) (obs : α → M) :
    OutputTypeRefinementConservative G obs := by
  constructor
  · intro R
    exact outputTypedTupleLanguage_subset_tupleLanguage G obs R
  · intro A x hx
    exact derives_actualRefinedNonterminal hx

end OutputTypedLanguages

end FIv21
