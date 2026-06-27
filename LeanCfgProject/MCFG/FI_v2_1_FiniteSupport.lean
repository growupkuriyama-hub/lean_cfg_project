import LeanCfgProject.MCFG.FI_v2_1_IdentificationSummary

/-!
# FI v2.1 Lean experiment: finite support layer

This file is the eleventh formalization layer for the FI v2.1 MCFG paper.

The previous files prove the distribution-level Gold stabilization theorem from
an abstract finite characteristic sample.  This file adds a lightweight finite
support layer for the canonical learner.  The goal is deliberately modest:

* package the finite objects that a sample-based learner enumerates;
* represent supported tuples, contexts, and unit edges by lists;
* state and prove that listed unit edges are sound when each listed edge passes
  the already-formalized sample-safe merge test;
* provide a bridge from list-supported unit edges to the existing
  `LearnerUnitEdge` and `LearnerUnitReach` notions.

This is not yet the full canonical learner grammar.  It is the finite-support
substrate on which such a learner can be built.
-/

namespace FIv21

universe u v

section Atoms

variable (α : Type u)

/-- A tuple together with its arity.  This is a convenient finite-support atom:
the learner enumerates tuples of several arities, and the arity is part of the
object. -/
abbrev TupleAtom := Sigma (fun d : Nat => Tuple α d)

/-- A named context together with its arity. -/
abbrev ContextAtom := Sigma (fun d : Nat => NamedSentenceContext α d)

/-- A directed unit edge between two tuples of the same arity, with the arity
stored explicitly. -/
abbrev UnitEdgeAtom := Sigma (fun d : Nat => Tuple α d × Tuple α d)

end Atoms

section FiniteSupport

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]

/-- Finite support data extracted from a positive sample.

The support is intentionally represented by lists for the arity-indexed objects
because the later canonical learner only needs finite enumerability here, not a
canonical duplicate-free representation.  The positive sample itself remains a
`Finset` of words. -/
structure FiniteLearnerSupport (α : Type u) where
  sample : Finset (Word α)
  tuples : List (TupleAtom α)
  contexts : List (ContextAtom α)
  unitEdges : List (UnitEdgeAtom α)

namespace FiniteLearnerSupport

/-- A tuple is listed in the finite tuple support. -/
def SupportsTuple (S : FiniteLearnerSupport α) {d : Nat} (x : Tuple α d) : Prop :=
  (Sigma.mk d x : TupleAtom α) ∈ S.tuples

/-- A named context is listed in the finite context support. -/
def SupportsContext (S : FiniteLearnerSupport α) {d : Nat}
    (c : NamedSentenceContext α d) : Prop :=
  (Sigma.mk d c : ContextAtom α) ∈ S.contexts

/-- A directed unit edge is listed in the finite unit-edge support. -/
def SupportsUnitEdge (S : FiniteLearnerSupport α) {d : Nat}
    (x y : Tuple α d) : Prop :=
  (Sigma.mk d (x, y) : UnitEdgeAtom α) ∈ S.unitEdges

/-- Every listed unit edge is certified by the sample-safe merge test and by the
fan-out/positive-arity side conditions needed by the reconstruction proof. -/
def ListedUnitEdgesAreSafe
    (S : FiniteLearnerSupport α) (obs : α → M) (f : Nat) : Prop :=
  ∀ {d : Nat} {x y : Tuple α d},
    S.SupportsUnitEdge x y →
      d ≤ f ∧ 0 < d ∧ SampleSafeMerge S.sample obs x y

/-- Convert a listed safe unit edge into the learner's existing unit-edge
structure. -/
def toLearnerUnitEdge
    {S : FiniteLearnerSupport α} {obs : α → M} {f : Nat}
    (hsafe : S.ListedUnitEdgesAreSafe obs f)
    {d : Nat} {x y : Tuple α d}
    (hxy : S.SupportsUnitEdge x y) : LearnerUnitEdge S.sample obs f := by
  rcases hsafe hxy with ⟨hd, hpos, hmerge⟩
  exact
    { d := d
      hd := hd
      hpos := hpos
      src := x
      tgt := y
      merge := hmerge }

/-- A listed safe unit edge gives one-step unit reachability. -/
theorem listedUnitEdge_reach
    {S : FiniteLearnerSupport α} {obs : α → M} {f : Nat}
    (hsafe : S.ListedUnitEdgesAreSafe obs f)
    {d : Nat} {x y : Tuple α d}
    (hxy : S.SupportsUnitEdge x y) :
    LearnerUnitReach S.sample obs f x y := by
  exact LearnerUnitReach.step (S.toLearnerUnitEdge hsafe hxy)

/-- Soundness of a single listed safe unit edge for a target language. -/
theorem listedUnitEdge_sound_for_language
    {S : FiniteLearnerSupport α} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hK : PositiveForLanguage S.sample L)
    (hL : FixedNamedTupleSubstitutable f obs L)
    (hsafe : S.ListedUnitEdgesAreSafe obs f)
    {d : Nat} {x y : Tuple α d}
    (hxy : S.SupportsUnitEdge x y) :
    NamedDistribution L x = NamedDistribution L y := by
  rcases hsafe hxy with ⟨hd, hpos, hmerge⟩
  exact sampleSafeMerge_sound_for_language
    (K := S.sample) (L := L) (obs := obs)
    hK hL hd hpos hmerge

/-- Soundness of the reachability step induced by a listed edge. -/
theorem listedUnitEdge_reach_sound_for_language
    {S : FiniteLearnerSupport α} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hK : PositiveForLanguage S.sample L)
    (hL : FixedNamedTupleSubstitutable f obs L)
    (hsafe : S.ListedUnitEdgesAreSafe obs f)
    {d : Nat} {x y : Tuple α d}
    (hxy : S.SupportsUnitEdge x y) :
    NamedDistribution L x = NamedDistribution L y := by
  exact LearnerUnitReach.sound_for_language
    hK hL (S.listedUnitEdge_reach hsafe hxy)

/-- If an observed context for `x` is in the sample distribution and `x` reaches
`y` through a listed edge, then the context is sound for `y` in the target
language.  This is the finite-support version of context transport. -/
theorem sample_context_transport_sound_for_listed_edge
    {S : FiniteLearnerSupport α} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hK : PositiveForLanguage S.sample L)
    (hL : FixedNamedTupleSubstitutable f obs L)
    (hsafe : S.ListedUnitEdgesAreSafe obs f)
    {d : Nat} {x y : Tuple α d}
    (hxy : S.SupportsUnitEdge x y)
    {c : NamedSentenceContext α d}
    (hc : c ∈ SampleNamedDistribution S.sample x) :
    c ∈ NamedDistribution L y := by
  have hreach : LearnerUnitReach S.sample obs f x y :=
    S.listedUnitEdge_reach hsafe hxy
  have hcL : c ∈ NamedDistribution L x :=
    sampleNamedDistribution_subset_namedDistribution S.sample hK x hc
  exact LearnerUnitReach.mem_namedDistribution_of_reachable
    hK hL hreach hcL

end FiniteLearnerSupport

end FiniteSupport

end FIv21
