import LeanCfgProject.MCFG.FI_v2_1_CanonicalLearnerGrammarInterface

/-!
# FI v2.1 Lean experiment: exact canonical learner grammar package

This fifty-first layer combines the one-sample canonical learner grammar package
with the already-checked exact/context/word/start witness certificate for the
same extracted data.

This still does not construct the canonical grammar.  It records the exactness
obligations that such a grammar package must satisfy once constructed.
-/

namespace FIv21

universe u v w

section CanonicalLearnerGrammarExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact one-sample canonical learner grammar package for a grammar target. -/
structure CanonicalLearnerGrammarExactForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  exact_start : ConcreteExtractedSampleExactContextWordStartForGrammar P.data

namespace CanonicalLearnerGrammarExactForGrammar

/-- Forget to the exact-with-packaged-word-semantics certificate from the
previous layer. -/
def toExactWithWordSemanticsForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactForGrammar P) :
    ConcreteExtractedSampleExactWithWordSemanticsForGrammar P.data :=
  { exact_start := C.exact_start
    semantics := P.semantics }

/-- Exact equality of the package-level approximate distribution and the target
named-context distribution. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactForGrammar P)
    {d : Nat} (x : Tuple α d) :
    P.ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact C.toExactWithWordSemanticsForGrammar.approxDistribution_exact x

/-- Exact context-membership form. -/
theorem licensed_iff_target_context
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactForGrammar P)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d) :
    c ∈ P.ApproxDistribution x ↔ c ∈ NamedDistribution G.StringLanguage x := by
  exact C.toExactWithWordSemanticsForGrammar.licensed_iff_target_context x c

/-- Target-side membership of a sampled word. -/
theorem sample_word_in_target
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactForGrammar P)
    (w : Word α) (hw : w ∈ K) :
    w ∈ G.StringLanguage := by
  exact C.toExactWithWordSemanticsForGrammar.sample_word_in_target w hw

/-- Target-side start-symbol derivation witness for a sampled word. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactForGrammar P)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact C.toExactWithWordSemanticsForGrammar.sample_word_start_derives w hw

/-- Learner-side generation of a sampled word by the package semantics. -/
theorem sample_word_generated_by_learner
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactForGrammar P)
    (w : Word α) (hw : w ∈ K) :
    w ∈ P.wordLanguage := by
  exact C.toExactWithWordSemanticsForGrammar.sample_word_generated_by_learner w hw

/-- Positivity of the finite sample for the target grammar. -/
theorem positiveSample
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactForGrammar P) :
    PositiveSample G K := by
  exact C.toExactWithWordSemanticsForGrammar.positiveSample

/-- The exact package inherits the package-level learner-word consistency. -/
theorem learner_word_consistent
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (_C : CanonicalLearnerGrammarExactForGrammar P) :
    ConcreteExtractedSampleLearnerWordConsistent P.data P.wordLanguage := by
  exact P.learner_word_consistent

end CanonicalLearnerGrammarExactForGrammar

end CanonicalLearnerGrammarExact

end FIv21
