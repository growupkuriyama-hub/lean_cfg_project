import LeanCfgProject.MCFG.FI_v2_1_MCFG_Derivation
import LeanCfgProject.MCFG.FI_v2_1_NamedSentenceContext

/-!
# FI v2.1 Lean experiment: contextual semantics and positive samples

This file is the fifth formalization layer for the FI v2.1 MCFG paper.

The previous files introduced:

* fixed finite-monoid observations and tuple substitutability;
* concrete named sentence contexts;
* a lightweight syntax for working binary MCFGs;
* the first derivation semantics and the generated string language.

This file connects these layers.  It defines when a derived tuple is exposed by
an accepting named sentence context, when the same phenomenon is already visible
inside a finite positive sample, and proves the basic soundness bridge used by
the paper's canonical learner: a sample-level typed shared-context merge is
sound for the target language whenever the sample is positive and the target is
fixed-`h` tuple-substitutable.

The file is still deliberately abstract about the actual learner grammar.  It
formalizes the semantic gate that justifies adding a safe unit rule; later files
can use this gate when constructing the learner presentation.
-/

namespace FIv21

universe u v w

section GrammarContextualSemantics

variable {N : Type v} {α : Type u}

/-- A derived tuple exposed by an accepting named sentence context.

`ExposedWithContext G A x c` says that `A` derives `x`, and filling the named
sentence context `c` with `x` gives a word in the string language of `G`.
This is the semantic version of an occurrence of a nonterminal tuple inside a
complete accepting derivation. -/
def ExposedWithContext
    (G : WorkingMCFG N α) (A : N)
    (x : Tuple α (G.arity A))
    (c : NamedSentenceContext α (G.arity A)) : Prop :=
  DerivesTuple G A x ∧ namedFill (G.arity A) c x ∈ G.StringLanguage

/-- The set of accepting named contexts for a tuple, using the grammar's string
language as the target language. -/
def GrammarNamedDistribution
    (G : WorkingMCFG N α) {d : Nat} (x : Tuple α d) :
    Set (NamedSentenceContext α d) :=
  NamedDistribution G.StringLanguage x

/-- Two tuples share an accepting named context in the grammar's string
language. -/
def GrammarNamedSharesContext
    (G : WorkingMCFG N α) {d : Nat} (x y : Tuple α d) : Prop :=
  NamedSharesContext G.StringLanguage x y

/-- Two exposures with the same named context give a shared accepting named
context. -/
theorem grammarNamedSharesContext_of_two_exposures
    (G : WorkingMCFG N α) (A : N)
    {x y : Tuple α (G.arity A)}
    {c : NamedSentenceContext α (G.arity A)}
    (hx : ExposedWithContext G A x c)
    (hy : ExposedWithContext G A y c) :
    GrammarNamedSharesContext G x y := by
  exact ⟨c, hx.2, hy.2⟩

/-- Under fixed-`h` tuple substitutability, same type plus one shared accepting
named context forces equality of named-context distributions for derived tuples.

This is the grammar-specialized form of the paper's safe-substitution step. -/
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

/-- A convenient version in which the shared context is produced by two exposed
occurrences with the same surrounding named context. -/
theorem grammarNamedDistribution_eq_of_two_exposures
    {M : Type w} [Monoid M]
    (G : WorkingMCFG N α) (A : N)
    {f : Nat} {obs : α → M}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {x y : Tuple α (G.arity A)}
    {c : NamedSentenceContext α (G.arity A)}
    (htype : tupleType obs x = tupleType obs y)
    (hx : ExposedWithContext G A x c)
    (hy : ExposedWithContext G A y c) :
    GrammarNamedDistribution G x = GrammarNamedDistribution G y := by
  exact grammarNamedDistribution_eq_of_fixed_substitutable
    G A hfan hL htype (grammarNamedSharesContext_of_two_exposures G A hx hy)

end GrammarContextualSemantics

section PositiveSamples

variable {N : Type v} {α : Type u}
variable [DecidableEq α]

/-- A finite positive sample for a grammar: every sampled word is in the target
string language.  This avoids coercion-heavy notation and is convenient for CI. -/
def PositiveSample (G : WorkingMCFG N α) (K : Finset (Word α)) : Prop :=
  ∀ w : Word α, w ∈ K → w ∈ G.StringLanguage

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

/-- A derived tuple observed inside a finite sample with a named context. -/
def ObservedInSampleWithContext
    (G : WorkingMCFG N α) (K : Finset (Word α)) (A : N)
    (x : Tuple α (G.arity A))
    (c : NamedSentenceContext α (G.arity A)) : Prop :=
  DerivesTuple G A x ∧ namedFill (G.arity A) c x ∈ K

/-- Sample observations become genuine accepting exposures when the sample is
positive. -/
theorem observedInSample_to_exposedWithContext
    (G : WorkingMCFG N α) (K : Finset (Word α)) (A : N)
    {x : Tuple α (G.arity A)}
    {c : NamedSentenceContext α (G.arity A)}
    (hK : PositiveSample G K)
    (hx : ObservedInSampleWithContext G K A x c) :
    ExposedWithContext G A x c := by
  exact ⟨hx.1, hK (namedFill (G.arity A) c x) hx.2⟩

/-- The sample-level merge test used by the canonical learner: same fixed
observation type and one shared sample context. -/
def SampleSafeMerge
    {M : Type w} [Monoid M]
    {d : Nat} (K : Finset (Word α)) (obs : α → M)
    (x y : Tuple α d) : Prop :=
  tupleType obs x = tupleType obs y ∧ SampleNamedSharesContext K x y

/-- Soundness of the sample-level safe merge test.

If the finite sample is positive for `G`, and `G.StringLanguage` is fixed-`h`
tuple-substitutable, then any sample-level typed shared-context merge yields
equality of the full target named-context distributions. -/
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

/-- A version using two observed sample exposures with the same context. -/
theorem sampleObservedExposures_sound_for_grammar
    {M : Type w} [Monoid M]
    (G : WorkingMCFG N α) (A : N)
    {f : Nat} {obs : α → M}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (K : Finset (Word α))
    (hK : PositiveSample G K)
    {x y : Tuple α (G.arity A)}
    {c : NamedSentenceContext α (G.arity A)}
    (htype : tupleType obs x = tupleType obs y)
    (hx : ObservedInSampleWithContext G K A x c)
    (hy : ObservedInSampleWithContext G K A y c) :
    GrammarNamedDistribution G x = GrammarNamedDistribution G y := by
  have hx' : ExposedWithContext G A x c :=
    observedInSample_to_exposedWithContext G K A hK hx
  have hy' : ExposedWithContext G A y c :=
    observedInSample_to_exposedWithContext G K A hK hy
  exact grammarNamedDistribution_eq_of_two_exposures G A hfan hL htype hx' hy'

end PositiveSamples

end FIv21
