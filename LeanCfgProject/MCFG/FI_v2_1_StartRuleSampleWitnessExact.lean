import LeanCfgProject.MCFG.FI_v2_1_StartRuleSampleWitness

/-!
# FI v2.1 Lean experiment: exact extraction with start witnesses

This forty-second layer combines distributional exactness, sample-context
consistency, sample-word consistency, and explicit target start-derivation
witnesses for sampled words.
-/

namespace FIv21

universe u v w

section StartRuleSampleWitnessExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Grammar-target exact concrete extraction, now also carrying explicit
start-symbol derivation witnesses for every externally sampled word. -/
structure ConcreteExtractedSampleExactContextWordStartForGrammar
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (E : ConcreteExtractedSampleData G obs K) : Prop where
  exact_context_word : ConcreteExtractedSampleExactContextWordForGrammar E
  start_witnesses : ConcreteExtractedSampleStartWitnessForGrammar E

namespace ConcreteExtractedSampleExactContextWordStartForGrammar

/-- The start-witness component is automatic from exact/context/word grammar
extraction. -/
def ofExactContextWord
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactContextWordForGrammar E) :
    ConcreteExtractedSampleExactContextWordStartForGrammar E :=
  { exact_context_word := C
    start_witnesses :=
      ConcreteExtractedSampleStartWitnessForGrammar.ofExactContextWord C }

/-- Exact equality of extracted and target named-context distributions. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactContextWordStartForGrammar E)
    {d : Nat} (x : Tuple α d) :
    E.ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact C.exact_context_word.approxDistribution_exact x

/-- Exact context-membership form. -/
theorem licensed_iff_target_context
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactContextWordStartForGrammar E)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d) :
    c ∈ E.ApproxDistribution x ↔ c ∈ NamedDistribution G.StringLanguage x := by
  exact C.exact_context_word.exact_and_context.licensed_iff_target_context x c

/-- Sample-observed contexts are target contexts. -/
theorem sample_context_in_target_distribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactContextWordStartForGrammar E)
    {d : Nat} (x : Tuple α d) (c : NamedSentenceContext α d)
    (hc : c ∈ SampleNamedDistribution K x) :
    c ∈ NamedDistribution G.StringLanguage x := by
  exact C.exact_context_word.sample_context_in_target_distribution x c hc

/-- Pointwise target membership for an externally sampled word. -/
theorem sample_word_in_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactContextWordStartForGrammar E)
    (w : Word α) (hw : w ∈ K) :
    w ∈ G.StringLanguage := by
  exact C.start_witnesses.sample_word_in_stringLanguage w hw

/-- Pointwise start-symbol derivation witness for an externally sampled word. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactContextWordStartForGrammar E)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact C.start_witnesses.sample_word_start_derives w hw

/-- Positivity for the external sample, recovered from the start witnesses. -/
theorem positiveSample
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {E : ConcreteExtractedSampleData G obs K}
    (C : ConcreteExtractedSampleExactContextWordStartForGrammar E) :
    PositiveSample G K := by
  exact C.start_witnesses.positiveSample

end ConcreteExtractedSampleExactContextWordStartForGrammar

end StartRuleSampleWitnessExact

end FIv21
