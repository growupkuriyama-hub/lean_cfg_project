import LeanCfgProject.MCFG.FI_v2_1_MCFG_ContextualSemantics

/-!
# FI v2.1 Lean experiment: learner unit closure

This file is the sixth formalization layer for the FI v2.1 MCFG paper.

The previous contextual-semantics layer proved that a finite positive sample
justifies a typed shared-context merge: if two observed tuples have the same
fixed observation type and share one accepting sample context, then fixed-`h`
tuple substitutability makes their full target distributions equal.

This file packages that semantic gate as the unit-rule layer of the canonical
learner.  It deliberately stops short of constructing the full MCFG hypothesis:
we formalize the safe unit edges that the learner is allowed to add, their
reflexive-transitive closure, and the preservation theorem saying that every
path of such learner unit edges preserves the target named-context distribution.

This corresponds to the proof-theoretic role of the learner's unit-rule closure
in the paper: the closure may identify more tuples than are directly observed,
but every identification obtained by iterating the sample-level safe-merge test
is sound for the target language under the fixed-substitutability promise.
-/

namespace FIv21

universe u v

section LanguageLevelSamples

variable {α : Type u}
variable [DecidableEq α]

/-- A finite sample is positive for an abstract target language `L` when every
sampled word belongs to `L`.

The earlier file defined `PositiveSample G K` for grammar targets.  This
language-level variant is useful for the learner skeleton, whose soundness
argument only needs positivity with respect to the target string language. -/
def PositiveForLanguage (K : Finset (Word α)) (L : Set (Word α)) : Prop :=
  ∀ w : Word α, w ∈ K → w ∈ L

/-- Grammar positivity is a special case of language-level positivity. -/
theorem positiveForLanguage_of_positiveSample
    {N : Type v} (G : WorkingMCFG N α) (K : Finset (Word α))
    (hK : PositiveSample G K) :
    PositiveForLanguage K G.StringLanguage := by
  intro w hw
  exact hK w hw

/-- A sample-level named context is a target context when the sample is positive
for the target language. -/
theorem sampleNamedDistribution_subset_namedDistribution
    {d : Nat} (K : Finset (Word α)) {L : Set (Word α)}
    (hK : PositiveForLanguage K L) (x : Tuple α d) :
    SampleNamedDistribution K x ⊆ NamedDistribution L x := by
  intro c hc
  exact hK (namedFill d c x) hc

/-- A sample-level shared context becomes a genuine target shared context under
positivity. -/
theorem sampleNamedSharesContext_to_namedSharesContext
    {d : Nat} (K : Finset (Word α)) {L : Set (Word α)}
    (hK : PositiveForLanguage K L) {x y : Tuple α d}
    (hshare : SampleNamedSharesContext K x y) :
    NamedSharesContext L x y := by
  rcases hshare with ⟨c, hx, hy⟩
  exact ⟨c, hK (namedFill d c x) hx, hK (namedFill d c y) hy⟩

/-- Language-level soundness of the sample safe-merge test. -/
theorem sampleSafeMerge_sound_for_language
    {M : Type v} [Monoid M]
    {d f : Nat} (K : Finset (Word α)) {L : Set (Word α)}
    {obs : α → M}
    (hK : PositiveForLanguage K L)
    (hL : FixedNamedTupleSubstitutable f obs L)
    (hd : d ≤ f) (hpos : 0 < d)
    {x y : Tuple α d}
    (hmerge : SampleSafeMerge K obs x y) :
    NamedDistribution L x = NamedDistribution L y := by
  exact hL hd hpos x y hmerge.1
    (sampleNamedSharesContext_to_namedSharesContext K hK hmerge.2)

end LanguageLevelSamples

section LearnerUnitEdges

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]

/-- A single safe unit edge admitted by the learner from a finite sample.

The edge carries its arity together with the fan-out bound proof and the
positive-arity proof needed to invoke fixed-`h` tuple substitutability.  The
source and target are concrete tuples of that same arity. -/
structure LearnerUnitEdge
    (K : Finset (Word α)) (obs : α → M) (f : Nat) where
  d : Nat
  hd : d ≤ f
  hpos : 0 < d
  src : Tuple α d
  tgt : Tuple α d
  merge : SampleSafeMerge K obs src tgt

namespace LearnerUnitEdge

/-- The source and target have the same fixed observation type. -/
theorem type_eq
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    (e : LearnerUnitEdge K obs f) :
    tupleType obs e.src = tupleType obs e.tgt :=
  e.merge.1

/-- The source and target share a sample context. -/
theorem shares_sample_context
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    (e : LearnerUnitEdge K obs f) :
    SampleNamedSharesContext K e.src e.tgt :=
  e.merge.2

/-- Soundness of one learner unit edge. -/
theorem sound_for_language
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hK : PositiveForLanguage K L)
    (hL : FixedNamedTupleSubstitutable f obs L)
    (e : LearnerUnitEdge K obs f) :
    NamedDistribution L e.src = NamedDistribution L e.tgt := by
  exact sampleSafeMerge_sound_for_language K hK hL e.hd e.hpos e.merge

end LearnerUnitEdge

/-- Reflexive-transitive closure of learner unit edges at a fixed arity.

`LearnerUnitReach K obs f x y` says that `y` can be reached from `x` by zero or
more sample-safe unit steps.  The arity is implicit in the tuple type, so paths
never mix different arities. -/
inductive LearnerUnitReach
    (K : Finset (Word α)) (obs : α → M) (f : Nat) :
    {d : Nat} → Tuple α d → Tuple α d → Prop where
  | refl {d : Nat} (x : Tuple α d) :
      LearnerUnitReach K obs f x x
  | step (e : LearnerUnitEdge K obs f) :
      LearnerUnitReach K obs f e.src e.tgt
  | trans {d : Nat} {x y z : Tuple α d}
      (hxy : LearnerUnitReach K obs f x y)
      (hyz : LearnerUnitReach K obs f y z) :
      LearnerUnitReach K obs f x z

namespace LearnerUnitReach

/-- One directly admitted edge is a reachability step. -/
theorem of_edge
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    (e : LearnerUnitEdge K obs f) :
    LearnerUnitReach K obs f e.src e.tgt :=
  LearnerUnitReach.step e

/-- Soundness of the reflexive-transitive unit closure: every path of learner
unit edges preserves the full target named-context distribution. -/
theorem sound_for_language
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hK : PositiveForLanguage K L)
    (hL : FixedNamedTupleSubstitutable f obs L) :
    ∀ {d : Nat} {x y : Tuple α d},
      LearnerUnitReach K obs f x y →
      NamedDistribution L x = NamedDistribution L y
  | _, _, _, LearnerUnitReach.refl x => rfl
  | _, _, _, LearnerUnitReach.step e =>
      LearnerUnitEdge.sound_for_language hK hL e
  | _, _, _, LearnerUnitReach.trans hxy hyz => by
      exact (sound_for_language hK hL hxy).trans
        (sound_for_language hK hL hyz)

/-- Reachability preserves distribution membership in the forward direction. -/
theorem mem_namedDistribution_of_reachable
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hK : PositiveForLanguage K L)
    (hL : FixedNamedTupleSubstitutable f obs L)
    {d : Nat} {x y : Tuple α d}
    (hxy : LearnerUnitReach K obs f x y)
    {c : NamedSentenceContext α d}
    (hc : c ∈ NamedDistribution L x) :
    c ∈ NamedDistribution L y := by
  have hdist : NamedDistribution L x = NamedDistribution L y :=
    sound_for_language hK hL hxy
  rw [← hdist]
  exact hc

/-- Reachability preserves distribution membership in the reverse direction as
well, because the soundness theorem gives equality of distributions. -/
theorem mem_namedDistribution_iff_of_reachable
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hK : PositiveForLanguage K L)
    (hL : FixedNamedTupleSubstitutable f obs L)
    {d : Nat} {x y : Tuple α d}
    (hxy : LearnerUnitReach K obs f x y)
    {c : NamedSentenceContext α d} :
    c ∈ NamedDistribution L x ↔ c ∈ NamedDistribution L y := by
  have hdist : NamedDistribution L x = NamedDistribution L y :=
    sound_for_language hK hL hxy
  constructor
  · intro hc
    rw [← hdist]
    exact hc
  · intro hc
    rw [hdist]
    exact hc

end LearnerUnitReach

end LearnerUnitEdges

section LearnerHypothesisSkeleton

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]

/-- A lightweight hypothesis object for the current sample.

This is not yet the full canonical MCFG of the paper.  It records exactly the
part of the hypothesis that is justified in this file: the current sample, the
fixed observation, the fan-out bound, and the unit-closure relation generated by
sample-safe typed shared-context merges. -/
structure LearnerUnitHypothesis (α : Type u) (M : Type v) [Monoid M] where
  f : Nat
  obs : α → M
  sample : Finset (Word α)

namespace LearnerUnitHypothesis

/-- Unit reachability relation associated with a learner unit hypothesis. -/
def Reach (H : LearnerUnitHypothesis α M) {d : Nat}
    (x y : Tuple α d) : Prop :=
  LearnerUnitReach H.sample H.obs H.f x y

/-- Soundness of the hypothesis's unit closure under a target promise. -/
theorem reach_sound_for_language
    (H : LearnerUnitHypothesis α M)
    {L : Set (Word α)}
    (hK : PositiveForLanguage H.sample L)
    (hL : FixedNamedTupleSubstitutable H.f H.obs L)
    {d : Nat} {x y : Tuple α d}
    (hxy : H.Reach x y) :
    NamedDistribution L x = NamedDistribution L y := by
  exact LearnerUnitReach.sound_for_language hK hL hxy

end LearnerUnitHypothesis

end LearnerHypothesisSkeleton

end FIv21
