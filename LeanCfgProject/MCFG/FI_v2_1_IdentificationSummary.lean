import LeanCfgProject.MCFG.FI_v2_1_GoldStabilization

/-!
# FI v2.1 Lean experiment: identification summary layer

This file is the tenth formalization layer for the FI v2.1 MCFG paper.

The previous layer proved the Gold-style stabilization theorem for a single
language or grammar target, assuming a finite distribution characteristic
sample.  This file packages that result at the class level.  It is deliberately
an abstract wrapper:

* a class is distribution-learnable if every target in the class has a finite
  distribution characteristic sample and satisfies the fixed-observation
  substitutability promise;
* such a class is identified in the limit at the already-formalized
  distribution level;
* the same statement is also given for classes of working MCFG presentations.

This file still does not construct the characteristic sample from a grammar
presentation.  It records the theorem schema that the paper uses after the
presentation-relative characteristic sample has been built.
-/

namespace FIv21

universe u v w

section LanguageClasses

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]

/-- A class of string languages over `α`. -/
abbrev LanguageClass (α : Type u) := Set (Set (Word α))

/-- A language class has finite distribution telltales for the fixed observation
`obs` and fan-out bound `f` if every member has a finite distribution
characteristic sample and satisfies the fixed-`h` substitutability promise.

This is the Lean analogue of the paper's post-reconstruction situation: the
hard grammar-specific work is to construct such an `S` for each target. -/
def DistributionTelltaleClass
    (C : LanguageClass α) (obs : α → M) (f : Nat) : Prop :=
  ∀ L : Set (Word α), L ∈ C →
    ∃ S : Finset (Word α),
      DistributionCharacteristicSample S obs f L ∧
      FixedNamedTupleSubstitutable f obs L

/-- Distribution-level identification of every language in a class. -/
def DistributionIdentifiesLanguageClass
    (C : LanguageClass α) (obs : α → M) (f : Nat) : Prop :=
  ∀ L : Set (Word α), L ∈ C → DistributionIdentifiesInLimit obs f L

/-- Finite distribution telltales imply distribution-level identification in
Gold's sense, uniformly for every language in the class. -/
theorem DistributionTelltaleClass.identifies
    {C : LanguageClass α} {obs : α → M} {f : Nat}
    (hC : DistributionTelltaleClass C obs f) :
    DistributionIdentifiesLanguageClass C obs f := by
  intro L hL
  rcases hC L hL with ⟨S, hS, hsub⟩
  exact distributionCharacteristicSample_identifiesInLimit hS hsub

/-- Pointwise class-level form: for every text of every target in the class,
there is a stage after which the learner's licensed contexts agree with the
true target named-context distribution for every tuple. -/
theorem DistributionTelltaleClass.eventually_licensed_iff
    {C : LanguageClass α} {obs : α → M} {f : Nat}
    (hC : DistributionTelltaleClass C obs f)
    {L : Set (Word α)} (hL : L ∈ C)
    {t : Text α} (ht : TextFor t L) :
    ∃ N : Nat,
      ∀ n : Nat, N ≤ n →
        ∀ {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d),
          c ∈ LearnerApproxDistribution (PrefixSample t n) obs f x ↔
            c ∈ NamedDistribution L x := by
  rcases hC L hL with ⟨S, hS, hsub⟩
  exact eventually_licensed_iff_target_context hS hsub ht

/-- A single packaged target-level witness.  This is convenient when a later
file constructs the characteristic sample for a concrete target and wants to
reuse the class-level theorem. -/
structure DistributionTargetWitness
    (obs : α → M) (f : Nat) (L : Set (Word α)) where
  sample : Finset (Word α)
  characteristic : DistributionCharacteristicSample sample obs f L
  substitutable : FixedNamedTupleSubstitutable f obs L

namespace DistributionTargetWitness

/-- A target witness gives identification in the limit for that target. -/
theorem identifiesInLimit
    {obs : α → M} {f : Nat} {L : Set (Word α)}
    (W : DistributionTargetWitness obs f L) :
    DistributionIdentifiesInLimit obs f L := by
  exact distributionCharacteristicSample_identifiesInLimit
    W.characteristic W.substitutable

/-- Pointwise target-level form of `identifiesInLimit`. -/
theorem eventually_licensed_iff
    {obs : α → M} {f : Nat} {L : Set (Word α)}
    (W : DistributionTargetWitness obs f L)
    {t : Text α} (ht : TextFor t L) :
    ∃ N : Nat,
      ∀ n : Nat, N ≤ n →
        ∀ {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d),
          c ∈ LearnerApproxDistribution (PrefixSample t n) obs f x ↔
            c ∈ NamedDistribution L x := by
  exact eventually_licensed_iff_target_context
    W.characteristic W.substitutable ht

/-- A target witness can be viewed as a one-element class telltale theorem. -/
theorem singletonClass_identifies
    {obs : α → M} {f : Nat} {L : Set (Word α)}
    (W : DistributionTargetWitness obs f L) :
    DistributionIdentifiesLanguageClass ({L} : LanguageClass α) obs f := by
  intro L' hL'
  have hEq : L' = L := by
    simpa using hL'
  subst hEq
  exact W.identifiesInLimit

end DistributionTargetWitness

end LanguageClasses

section GrammarClasses

variable {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M]
variable {N : Type w}

/-- A class of working MCFG presentations over a fixed nonterminal type and
alphabet. -/
abbrev GrammarClass (N : Type w) (α : Type u) := Set (WorkingMCFG N α)

/-- A grammar class has finite distribution telltales if the string language of
every grammar in the class has a finite distribution characteristic sample and
satisfies the fixed-`h` substitutability promise. -/
def GrammarDistributionTelltaleClass
    (C : GrammarClass N α) (obs : α → M) (f : Nat) : Prop :=
  ∀ G : WorkingMCFG N α, G ∈ C →
    ∃ S : Finset (Word α),
      DistributionCharacteristicSample S obs f G.StringLanguage ∧
      FixedNamedTupleSubstitutable f obs G.StringLanguage

/-- Distribution-level identification of every grammar target in a class. -/
def DistributionIdentifiesGrammarClass
    (C : GrammarClass N α) (obs : α → M) (f : Nat) : Prop :=
  ∀ G : WorkingMCFG N α, G ∈ C →
    DistributionIdentifiesInLimitForGrammar obs f G

/-- Grammar-class version of the finite-telltale to identification theorem. -/
theorem GrammarDistributionTelltaleClass.identifies
    {C : GrammarClass N α} {obs : α → M} {f : Nat}
    (hC : GrammarDistributionTelltaleClass C obs f) :
    DistributionIdentifiesGrammarClass C obs f := by
  intro G hG
  rcases hC G hG with ⟨S, hS, hsub⟩
  exact distributionCharacteristicSample_identifiesGrammarInLimit G hS hsub

/-- Pointwise grammar-class form. -/
theorem GrammarDistributionTelltaleClass.eventually_licensed_iff
    {C : GrammarClass N α} {obs : α → M} {f : Nat}
    (hC : GrammarDistributionTelltaleClass C obs f)
    {G : WorkingMCFG N α} (hG : G ∈ C)
    {t : Text α} (ht : TextForGrammar t G) :
    ∃ N0 : Nat,
      ∀ n : Nat, N0 ≤ n →
        ∀ {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d),
          c ∈ LearnerApproxDistribution (PrefixSample t n) obs f x ↔
            c ∈ NamedDistribution G.StringLanguage x := by
  rcases hC G hG with ⟨S, hS, hsub⟩
  exact eventually_licensed_iff_grammar_context G hS hsub ht

/-- A packaged grammar-target witness. -/
structure GrammarDistributionTargetWitness
    (obs : α → M) (f : Nat) (G : WorkingMCFG N α) where
  sample : Finset (Word α)
  characteristic : DistributionCharacteristicSample sample obs f G.StringLanguage
  substitutable : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace GrammarDistributionTargetWitness

/-- A grammar witness gives distribution-level identification in the limit for
that grammar target. -/
theorem identifiesInLimit
    {obs : α → M} {f : Nat} {G : WorkingMCFG N α}
    (W : GrammarDistributionTargetWitness obs f G) :
    DistributionIdentifiesInLimitForGrammar obs f G := by
  exact distributionCharacteristicSample_identifiesGrammarInLimit
    G W.characteristic W.substitutable

/-- Pointwise grammar-target form. -/
theorem eventually_licensed_iff
    {obs : α → M} {f : Nat} {G : WorkingMCFG N α}
    (W : GrammarDistributionTargetWitness obs f G)
    {t : Text α} (ht : TextForGrammar t G) :
    ∃ N0 : Nat,
      ∀ n : Nat, N0 ≤ n →
        ∀ {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d),
          c ∈ LearnerApproxDistribution (PrefixSample t n) obs f x ↔
            c ∈ NamedDistribution G.StringLanguage x := by
  exact eventually_licensed_iff_grammar_context
    G W.characteristic W.substitutable ht

/-- A grammar witness induces the corresponding language-level witness for its
string language. -/
def toLanguageWitness
    {obs : α → M} {f : Nat} {G : WorkingMCFG N α}
    (W : GrammarDistributionTargetWitness obs f G) :
    DistributionTargetWitness obs f G.StringLanguage where
  sample := W.sample
  characteristic := W.characteristic
  substitutable := W.substitutable

end GrammarDistributionTargetWitness

end GrammarClasses

end FIv21
