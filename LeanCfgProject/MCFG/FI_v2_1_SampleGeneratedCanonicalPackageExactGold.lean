import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedCanonicalPackageExactLearner

/-!
# FI v2.1 Lean experiment: Gold summary for exact sample-generated packages

This layer gives the sample-generated canonical-package exactness bridge a
Gold-style summary.  It is still conditional on the remaining target-side
exactness/start-witness certificates, but the constructive branch now reaches
canonical package exactness whenever those certificates are supplied.
-/

namespace FIv21

universe u v w

section SampleGeneratedCanonicalPackageExactGold

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Gold-style summary for exact sample-generated canonical packages. -/
structure SampleGeneratedCanonicalPackageExactGoldSummary
    (G : WorkingMCFG N α) (obs : α → M) where
  learner : SampleGeneratedCanonicalPackageExactLearner G obs
  characteristicSample : Finset (Word α)

namespace SampleGeneratedCanonicalPackageExactGoldSummary

/-- Exact package at sample `K`. -/
def exactPackage
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedCanonicalPackageExactGoldSummary G obs)
    (K : Finset (Word α)) :
    SampleGeneratedCanonicalPackageExact G obs K :=
  S.learner.exactPackage K

/-- Canonical learner package at sample `K`. -/
noncomputable def canonicalPackage
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedCanonicalPackageExactGoldSummary G obs)
    (K : Finset (Word α)) :
    CanonicalLearnerGrammarPackage G obs K :=
  S.learner.canonicalPackage K

/-- Exact canonical-package certificate at sample `K`. -/
noncomputable def canonicalExact
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedCanonicalPackageExactGoldSummary G obs)
    (K : Finset (Word α)) :
    CanonicalLearnerGrammarExactForGrammar (S.canonicalPackage K) :=
  S.learner.canonicalExact K

/-- Generated word language at sample `K`. -/
noncomputable def wordLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedCanonicalPackageExactGoldSummary G obs)
    (K : Finset (Word α)) : Set (Word α) :=
  S.learner.wordLanguage K

/-- Each finite sample is positive for its generated word language. -/
theorem sample_subset_wordLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedCanonicalPackageExactGoldSummary G obs)
    (K : Finset (Word α)) :
    PositiveForLanguage K (S.wordLanguage K) := by
  exact S.learner.sample_subset_wordLanguage K

/-- Pointwise sample generation through the canonical package. -/
theorem canonicalPackage_sample_word_generated
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedCanonicalPackageExactGoldSummary G obs)
    (K : Finset (Word α)) {x : Word α} (hx : x ∈ K) :
    x ∈ (S.canonicalPackage K).wordLanguage := by
  exact S.learner.canonicalPackage_sample_word_generated K hx

/-- Exact approximation-distribution equality for every finite sample. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedCanonicalPackageExactGoldSummary G obs)
    (K : Finset (Word α)) {d : Nat} (x : Tuple α d) :
    (S.canonicalPackage K).ApproxDistribution x =
      NamedDistribution G.StringLanguage x := by
  exact S.learner.approxDistribution_exact K x

/-- Sample words are target-language members, once the exactness certificates are
supplied. -/
theorem sample_word_in_target
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedCanonicalPackageExactGoldSummary G obs)
    (K : Finset (Word α)) (w : Word α) (hw : w ∈ K) :
    w ∈ G.StringLanguage := by
  exact S.learner.sample_word_in_target K w hw

/-- Each finite sample is positive for the target grammar, once the exactness
certificates are supplied. -/
theorem positiveSample_target
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedCanonicalPackageExactGoldSummary G obs)
    (K : Finset (Word α)) :
    PositiveSample G K := by
  exact S.learner.positiveSample_target K

end SampleGeneratedCanonicalPackageExactGoldSummary

/-- Build a Gold summary from a semantics-bridge Gold summary plus a target-side
exactness/start-witness certificate for every finite sample. -/
noncomputable def SampleGeneratedCanonicalPackageExactGoldSummary.ofSemanticsBridgeGold
    {G : WorkingMCFG N α} {obs : α → M}
    (S : SampleGeneratedPackageSemanticsBridgeGoldSummary G obs)
    (H : (K : Finset (Word α)) →
      ConcreteExtractedSampleExactContextWordStartForGrammar
        (S.learner.bridge K).extractedData) :
    SampleGeneratedCanonicalPackageExactGoldSummary G obs :=
  { learner :=
      SampleGeneratedCanonicalPackageExactLearner.ofBridgeLearner
        S.learner H
    characteristicSample := S.characteristicSample }

end SampleGeneratedCanonicalPackageExactGold

end FIv21
