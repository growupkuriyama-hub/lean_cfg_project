import LeanCfgProject.MCFG.FI_v2_1_FixedObservation

/-!
# FI v2.1 Lean experiment: named sentence contexts

This file is the second formalization layer for the paper.  The previous file
formalizes the fixed finite-monoid observation interface and the abstract
notion of tuple distribution.  Here we give a concrete, lightweight model of
named sentence contexts.

The representation is intentionally modest.  A raw context stores a list of
terminal chunks and a list of named holes.  A separate `WellFormed` predicate
records the paper condition that there is one more chunk than hole and that
every named hole occurs exactly once.  This keeps the filling operation total
and easy to use in later experiments, while still making the intended
well-formedness condition explicit.
-/

namespace FIv21

universe u v w

section RawNamedContexts

variable {α : Type u}

/-- A raw named sentence context of arity `d`.

The list `chunks` contains the terminal material around the holes.  The list
`holes` records which tuple component is exposed at each hole occurrence.
For the paper's genuine sentence contexts, `holes` should list every element of
`Fin d` exactly once and `chunks.length = holes.length + 1`.  That condition is
kept as the separate predicate `WellFormed` below. -/
structure RawNamedSentenceContext (α : Type u) (d : Nat) where
  chunks : List (Word α)
  holes : List (Fin d)

namespace RawNamedSentenceContext

variable {d : Nat}

/-- The well-formedness condition corresponding to an arity-`d` named sentence
context in the paper: exactly one occurrence of each named hole, with terminal
chunks before, between, and after the holes. -/
def WellFormed (c : RawNamedSentenceContext α d) : Prop :=
  c.chunks.length = c.holes.length + 1 ∧
  c.holes.Nodup ∧
  ∀ i : Fin d, i ∈ c.holes

end RawNamedSentenceContext

/-- Well-formed named sentence contexts, as a subtype of raw contexts. -/
abbrev NamedSentenceContext (α : Type u) (d : Nat) :=
  { c : RawNamedSentenceContext α d // c.WellFormed }

/-- Fill a list of named holes using a tuple.  This auxiliary function is total,
even for raw malformed contexts.  If there are fewer chunks than expected, it
continues by concatenating the tuple components; if there are extra chunks after
all holes have been filled, it keeps the first remaining chunk and ignores the
rest.  On well-formed contexts, the usual paper behavior is obtained. -/
def fillNamedAux {d : Nat} (x : Tuple α d) : List (Fin d) → List (Word α) → Word α
  | [], [] => []
  | [], c :: _ => c
  | h :: hs, [] => x h ++ fillNamedAux x hs []
  | h :: hs, c :: cs => c ++ x h ++ fillNamedAux x hs cs

/-- Fill a raw named sentence context with a tuple. -/
def rawNamedFill {d : Nat} (c : RawNamedSentenceContext α d) (x : Tuple α d) : Word α :=
  fillNamedAux x c.holes c.chunks

/-- Arity-indexed filling operation for well-formed named sentence contexts. -/
def namedFill : ∀ d : Nat, NamedSentenceContext α d → Tuple α d → Word α :=
  fun d c x => rawNamedFill c.1 x

/-- Distribution using concrete named sentence contexts. -/
def NamedDistribution {d : Nat} (L : Set (Word α)) (x : Tuple α d) :
    Set (NamedSentenceContext α d) :=
  Distribution namedFill L x

/-- Shared accepting named context. -/
def NamedSharesContext {d : Nat} (L : Set (Word α)) (x y : Tuple α d) : Prop :=
  SharesContext namedFill L x y

/-- The paper's fixed-observation tuple-substitutability specialized to
well-formed named sentence contexts. -/
def FixedNamedTupleSubstitutable
    {M : Type v} [Monoid M]
    (f : Nat) (obs : α → M) (L : Set (Word α)) : Prop :=
  FixedTupleSubstitutable namedFill f obs L

/-- Ordinary one-hole context as a raw named sentence context. -/
def rawTwoSidedAsNamed (left right : Word α) : RawNamedSentenceContext α 1 :=
  { chunks := [left, right], holes := [finOne] }

@[simp] theorem rawNamedFill_twoSided (left right : Word α) (x : Tuple α 1) :
    rawNamedFill (rawTwoSidedAsNamed left right) x = left ++ x finOne ++ right := by
  simp [rawNamedFill, rawTwoSidedAsNamed, fillNamedAux]

/-- Filling is invariant under equality of tuples.  This tiny lemma is useful
when later proofs replace a tuple by an extensionally equal one. -/
theorem rawNamedFill_congr_tuple {d : Nat}
    (c : RawNamedSentenceContext α d) {x y : Tuple α d} (h : x = y) :
    rawNamedFill c x = rawNamedFill c y := by
  subst h
  rfl

/-- Same congruence lemma for well-formed named contexts. -/
theorem namedFill_congr_tuple {d : Nat}
    (c : NamedSentenceContext α d) {x y : Tuple α d} (h : x = y) :
    namedFill d c x = namedFill d c y := by
  subst h
  rfl

end RawNamedContexts

section NamedRefinement

variable {α : Type u}
variable {M : Type v} {M' : Type w}
variable [Monoid M] [Monoid M']
variable {obs : α → M} {obs' : α → M'}

/-- Monotonicity under observation refinement for the concrete named-context
specialization.  This is a direct corollary of the abstract monotonicity theorem
from `FI_v2_1_FixedObservation.lean`. -/
theorem fixedNamedTupleSubstitutable_of_refines
    {f : Nat} {L : Set (Word α)}
    (r : Refines obs obs')
    (hL : FixedNamedTupleSubstitutable f obs L) :
    FixedNamedTupleSubstitutable f obs' L := by
  exact fixedTupleSubstitutable_of_refines namedFill r hL

end NamedRefinement

end FIv21
