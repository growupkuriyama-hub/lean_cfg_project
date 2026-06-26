import LeanCfgProject.MCFG.FI_v2_1_LearnerUnitClosure

/-!
# FI v2.1 Lean experiment: learner distributions and transported contexts

This file is the seventh formalization layer for the FI v2.1 MCFG paper.

The previous layer introduced the learner's sample-safe unit edges and proved
that their reflexive-transitive closure preserves target named-context
distributions under the fixed-substitutability promise.  This file packages the
next proof-theoretic idea used by the canonical learner:

* a context observed in the finite sample for a tuple may be transported along
  unit-closure paths;
* every transported context is sound for the target language when the sample is
  positive and the target satisfies fixed-`h` tuple substitutability;
* if a characteristic sample is distribution-complete with respect to this
  transported-context approximation, then the approximation is extensionally
  equal to the target distribution.

This still does not construct the full learner MCFG.  It isolates the
``observed contexts + unit closure'' component of the reconstruction proof in a
form that later files can connect to learner rules and characteristic samples.
-/

namespace FIv21

universe u v

section SymmetryOfSafeMerges

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]

/-- Sharing a sample context is symmetric. -/
theorem sampleNamedSharesContext_symm
    {d : Nat} {K : Finset (Word α)} {x y : Tuple α d}
    (h : SampleNamedSharesContext K x y) :
    SampleNamedSharesContext K y x := by
  rcases h with ⟨c, hx, hy⟩
  exact ⟨c, hy, hx⟩

/-- The sample-safe merge test is symmetric. -/
theorem sampleSafeMerge_symm
    {d : Nat} {K : Finset (Word α)} {obs : α → M}
    {x y : Tuple α d}
    (h : SampleSafeMerge K obs x y) :
    SampleSafeMerge K obs y x := by
  exact ⟨h.1.symm, sampleNamedSharesContext_symm h.2⟩

namespace LearnerUnitEdge

/-- Every learner unit edge has a reverse edge, because the underlying safe-merge
condition is symmetric. -/
def reverse
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    (e : LearnerUnitEdge K obs f) : LearnerUnitEdge K obs f where
  d := e.d
  hd := e.hd
  hpos := e.hpos
  src := e.tgt
  tgt := e.src
  merge := sampleSafeMerge_symm e.merge

@[simp] theorem reverse_src
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    (e : LearnerUnitEdge K obs f) :
    e.reverse.src = e.tgt := rfl

@[simp] theorem reverse_tgt
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    (e : LearnerUnitEdge K obs f) :
    e.reverse.tgt = e.src := rfl

end LearnerUnitEdge

namespace LearnerUnitReach

/-- Unit reachability is symmetric, because every direct safe unit edge is
symmetric.  Thus the learner's unit closure is an equivalence relation on tuples
of a fixed arity. -/
theorem symm
    {K : Finset (Word α)} {obs : α → M} {f : Nat} :
    ∀ {d : Nat} {x y : Tuple α d},
      LearnerUnitReach K obs f x y → LearnerUnitReach K obs f y x
  | _, _, _, LearnerUnitReach.refl x => LearnerUnitReach.refl x
  | _, _, _, LearnerUnitReach.step e => LearnerUnitReach.step e.reverse
  | _, _, _, LearnerUnitReach.trans hxy hyz =>
      LearnerUnitReach.trans (symm hyz) (symm hxy)

/-- Reachability preserves target distributions in both directions.  This is a
restatement of soundness using symmetry of the unit closure. -/
theorem distribution_eq_of_reachable
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hK : PositiveForLanguage K L)
    (hL : FixedNamedTupleSubstitutable f obs L)
    {d : Nat} {x y : Tuple α d}
    (hxy : LearnerUnitReach K obs f x y) :
    NamedDistribution L x = NamedDistribution L y := by
  exact LearnerUnitReach.sound_for_language hK hL hxy

end LearnerUnitReach

end SymmetryOfSafeMerges

section LearnerApproxDistributions

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]

/-- A context is licensed for a tuple by the learner if it was observed in the
sample for some tuple that can reach the tuple by unit closure.

This is the context-distribution part of the canonical learner: sample contexts
are not only attached to the tuple where they were observed, but are transported
across all unit identifications justified by typed shared contexts. -/
def LearnerLicensedContext
    {d : Nat} (K : Finset (Word α)) (obs : α → M) (f : Nat)
    (x : Tuple α d) (c : NamedSentenceContext α d) : Prop :=
  ∃ y : Tuple α d,
    LearnerUnitReach K obs f y x ∧ c ∈ SampleNamedDistribution K y

/-- The learner's approximate named-context distribution for a tuple. -/
def LearnerApproxDistribution
    {d : Nat} (K : Finset (Word α)) (obs : α → M) (f : Nat)
    (x : Tuple α d) : Set (NamedSentenceContext α d) :=
  { c | LearnerLicensedContext K obs f x c }

/-- Every sample context is licensed for the tuple where it was observed. -/
theorem sample_context_subset_learnerApproxDistribution
    {d : Nat} (K : Finset (Word α)) (obs : α → M) (f : Nat)
    (x : Tuple α d) :
    SampleNamedDistribution K x ⊆ LearnerApproxDistribution K obs f x := by
  intro c hc
  exact ⟨x, LearnerUnitReach.refl x, hc⟩

/-- Learner approximate distributions are monotone along unit reachability. -/
theorem learnerApproxDistribution_subset_of_reachable
    {d : Nat} {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {x y : Tuple α d}
    (hxy : LearnerUnitReach K obs f x y) :
    LearnerApproxDistribution K obs f x ⊆
      LearnerApproxDistribution K obs f y := by
  intro c hc
  rcases hc with ⟨z, hzx, hcz⟩
  exact ⟨z, LearnerUnitReach.trans hzx hxy, hcz⟩

/-- Because unit reachability is symmetric, reachable tuples have the same
learner approximate distribution. -/
theorem learnerApproxDistribution_eq_of_reachable
    {d : Nat} {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {x y : Tuple α d}
    (hxy : LearnerUnitReach K obs f x y) :
    LearnerApproxDistribution K obs f x =
      LearnerApproxDistribution K obs f y := by
  apply Set.Subset.antisymm
  · exact learnerApproxDistribution_subset_of_reachable hxy
  · exact learnerApproxDistribution_subset_of_reachable
      (LearnerUnitReach.symm hxy)

/-- Soundness of licensed contexts: every context licensed by the learner is a
true accepting context of the target language under positivity and the fixed-`h`
substitutability promise. -/
theorem learnerLicensedContext_sound_for_language
    {d : Nat} {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hK : PositiveForLanguage K L)
    (hL : FixedNamedTupleSubstitutable f obs L)
    {x : Tuple α d} {c : NamedSentenceContext α d}
    (hc : LearnerLicensedContext K obs f x c) :
    c ∈ NamedDistribution L x := by
  rcases hc with ⟨y, hyx, hcy⟩
  have hcyL : c ∈ NamedDistribution L y :=
    sampleNamedDistribution_subset_namedDistribution K hK y hcy
  exact LearnerUnitReach.mem_namedDistribution_of_reachable hK hL hyx hcyL

/-- Soundness of the whole learner approximate distribution. -/
theorem learnerApproxDistribution_sound_for_language
    {d : Nat} {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hK : PositiveForLanguage K L)
    (hL : FixedNamedTupleSubstitutable f obs L)
    (x : Tuple α d) :
    LearnerApproxDistribution K obs f x ⊆ NamedDistribution L x := by
  intro c hc
  exact learnerLicensedContext_sound_for_language hK hL hc

/-- Distribution completeness of a sample with respect to the learner's unit
closure approximation.

This is a characteristic-sample-style property: every true accepting context of
every tuple is already licensed by the finite sample after transporting observed
contexts along unit closure. -/
def DistributionComplete
    (K : Finset (Word α)) (obs : α → M) (f : Nat)
    (L : Set (Word α)) : Prop :=
  ∀ {d : Nat} (x : Tuple α d),
    NamedDistribution L x ⊆ LearnerApproxDistribution K obs f x

/-- If the finite sample is distribution-complete, then the learner approximate
distribution is exactly the true target distribution. -/
theorem learnerApproxDistribution_exact_of_complete
    {d : Nat} {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hK : PositiveForLanguage K L)
    (hL : FixedNamedTupleSubstitutable f obs L)
    (hcomplete : DistributionComplete K obs f L)
    (x : Tuple α d) :
    LearnerApproxDistribution K obs f x = NamedDistribution L x := by
  apply Set.Subset.antisymm
  · exact learnerApproxDistribution_sound_for_language hK hL x
  · exact hcomplete x

end LearnerApproxDistributions

section ObservedNodes

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]

/-- A tuple occurrence observed in the finite sample, forgetting the grammar
nonterminal that produced it.

This is a small bridge object for later characteristic-sample formalization:
it records the arity bound, a tuple, a named context, and the sampled word
obtained by filling that context. -/
structure LearnerObservedNode
    (K : Finset (Word α)) (f : Nat) where
  d : Nat
  hd : d ≤ f
  hpos : 0 < d
  tuple : Tuple α d
  context : NamedSentenceContext α d
  observed : namedFill d context tuple ∈ K

namespace LearnerObservedNode

/-- The observed context of an observed node is sample-distributed for its tuple. -/
theorem context_mem_sampleDistribution
    {K : Finset (Word α)} {f : Nat}
    (n : LearnerObservedNode K f) :
    n.context ∈ SampleNamedDistribution K n.tuple := by
  exact n.observed

/-- The observed context is licensed for the observed tuple itself. -/
theorem context_mem_learnerApproxDistribution
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    (n : LearnerObservedNode K f) :
    n.context ∈ LearnerApproxDistribution K obs f n.tuple := by
  exact sample_context_subset_learnerApproxDistribution K obs f n.tuple n.observed

/-- If an observed tuple reaches another tuple by learner unit closure, then its
observed context is licensed for the reached tuple. -/
theorem context_mem_learnerApproxDistribution_of_reachable
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    (n : LearnerObservedNode K f)
    {y : Tuple α n.d}
    (hreach : LearnerUnitReach K obs f n.tuple y) :
    n.context ∈ LearnerApproxDistribution K obs f y := by
  exact learnerApproxDistribution_subset_of_reachable hreach
    (context_mem_learnerApproxDistribution (M := M) (obs := obs) n)

/-- Semantic soundness of an observed node's context after transport along unit
closure. -/
theorem transported_context_sound_for_language
    {K : Finset (Word α)} {obs : α → M} {f : Nat}
    {L : Set (Word α)}
    (hK : PositiveForLanguage K L)
    (hL : FixedNamedTupleSubstitutable f obs L)
    (n : LearnerObservedNode K f)
    {y : Tuple α n.d}
    (hreach : LearnerUnitReach K obs f n.tuple y) :
    n.context ∈ NamedDistribution L y := by
  have hlic : n.context ∈ LearnerApproxDistribution K obs f y :=
    context_mem_learnerApproxDistribution_of_reachable (obs := obs) n hreach
  exact learnerApproxDistribution_sound_for_language hK hL y hlic

end LearnerObservedNode

end ObservedNodes

end FIv21
