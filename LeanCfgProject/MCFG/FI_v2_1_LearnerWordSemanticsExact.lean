import LeanCfgProject.MCFG.FI_v2_1_LearnerWordSemanticsInterface

/-!
# FI v2.1 Lean experiment: exact extraction with packaged word semantics

This forty-eighth layer combines the grammar-target exact/context/word/start
certificate with a packaged learner-side word-semantics certificate.

Compared with the previous learner-word-consistency layer, the learner-side
language is no longer passed around as a loose parameter.  It is a named field
of a semantics certificate, matching the shape expected from a future canonical
learner grammar construction.
-/

namespace FIv21

universe u v w

section LearnerWordSemanticsExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact concrete extraction for a grammar target, together with packaged
learner-side word semantics for the extracted sample. -/
structure ConcreteExtractedSampleExactWithWordSemanticsForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) where
  exact_start : ConcreteExtractedSampleExactContextWordStartForGrammar E
  semantics : ConcreteExtractedSampleWordSemanticsCertificate E

namespace ConcreteExtractedSampleExactWithWordSemanticsForGrammar

/-- Forget the packaged semantics and recover the previous exact/start/learner
word-consistency certificate. -/
def toExactStartLearnerWordForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactWithWordSemanticsForGrammar E) :
    ConcreteExtractedSampleExactStartLearnerWordForGrammar
      E C.semantics.wordLanguage :=
  { exact_start := C.exact_start
    learner_word := C.semantics.sample_consistent }

/-- Exact equality of extracted and target named-context distributions. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactWithWordSemanticsForGrammar E)
    {d : Nat} (x : Tuple α d) :
    E.ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact C.exact_start.approxDistribution_exact x

/-- Exact context-membership form. -/
theorem licensed_iff_target_context
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactWithWordSemanticsForGrammar E)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d) :
    c ∈ E.ApproxDistribution x ↔ c ∈ NamedDistribution G.StringLanguage x := by
  exact C.exact_start.licensed_iff_target_context x c

/-- Target-side start-symbol derivation witness for a sampled word. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactWithWordSemanticsForGrammar E)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact C.exact_start.sample_word_start_derives w hw

/-- Target-side membership of a sampled word. -/
theorem sample_word_in_target
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactWithWordSemanticsForGrammar E)
    (w : Word α) (hw : w ∈ K) :
    w ∈ G.StringLanguage := by
  exact C.exact_start.sample_word_in_stringLanguage w hw

/-- Learner-side generation of a sampled word by the packaged learner-side word
semantics. -/
theorem sample_word_generated_by_learner
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactWithWordSemanticsForGrammar E)
    (w : Word α) (hw : w ∈ K) :
    w ∈ C.semantics.wordLanguage := by
  exact C.semantics.sample_word_generated w hw

/-- Positivity for the external sample, recovered from the target-side start
witnesses. -/
theorem positiveSample
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactWithWordSemanticsForGrammar E) :
    PositiveSample G K := by
  exact C.exact_start.positiveSample

end ConcreteExtractedSampleExactWithWordSemanticsForGrammar

end LearnerWordSemanticsExact

end FIv21
