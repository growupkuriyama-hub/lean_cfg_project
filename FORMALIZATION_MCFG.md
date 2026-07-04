# Lean formalization companion for the fixed-observation MCFG paper

This note documents the current Lean companion for the paper

> **Fixed-Monoid Tuple Substitution for Positive-Data Learning of Multiple Context-Free Grammars**

The Lean development is a companion formalization of the paper's bookkeeping
infrastructure around fixed finite observations, named sentence contexts, MCFG
derivations, sample-safe unit closure, transported distributions, finite
hypotheses, output-type refinement, finite enumeration, concrete refined rule
lists, sample-extraction data, raw sample decompositions, subword-context
enumeration, subword unit-edge enumeration, and Gold-style identification
wrappers.  Later sample-generated nonterminal / grammar-skeleton / rule-skeleton
files exist in the repository history, but they are now recorded below as
pending re-confirmation in the current restart pass.

This document is intended to be self-contained: a reader should be able to
understand the current scope of the Lean experiment, its CI status, the layers
that have been checked, and the remaining formalization gap from this file
alone.

---

## 0. Current CI status

```text
Repository: growupkuriyama-hub/lean_cfg_project
Latest reconfirmed CI: Lean CI #485
Latest commit reported by user: ff2b74c
Status: succeeded
Top reconfirmed module: LeanCfgProject.MCFG.FI_v2_1_SubwordUnitEdgeEnumerationGold
Aggregate import currently used for the restart pass: LeanCfgProject.MCFG.Basic
```

### Reconfirmation note

The previous version of this note recorded an older checkpoint:

```text
Lean CI #429 / commit 0cf10b2 / FI_v2_1_SampleGeneratedRuleSkeletonGold
```

During the current repair session, the aggregate import was intentionally
narrowed and then restored step by step.  That means the old `#429` line should
not be used as the current trusted frontier.  The current trusted frontier is
**CI #485 / commit `ff2b74c`**, which re-confirms the chain through:

```text
FI_v2_1_SubwordUnitEdgeEnumeration
FI_v2_1_SubwordUnitEdgeEnumerationExact
FI_v2_1_SubwordUnitEdgeEnumerationGold
```

The next file family, starting with
`FI_v2_1_CanonicalLearnerNonterminalGold`, is **not yet re-confirmed in the
current restart pass**.  Files after that point may have existed in the older
repository state and may have been described in the previous version of this
note, but they should now be treated as pending until the stepwise CI restoration
reaches them again.

A typical current check is:

```bash
lake build LeanCfgProject.MCFG.FI_v2_1_SubwordUnitEdgeEnumerationGold
lake build LeanCfgProject.MCFG.Basic
lake build LeanCfgProject
```

Warnings about unused section variables, unused simp arguments, long lines, or
GitHub Actions runtime notices may remain.  They are not failed proof
obligations.

---

## 1. Scope statement

This document now distinguishes two notions of status:

1. **reconfirmed in the current restart pass**, meaning the layer has been
   checked again by the stepwise `Basic.lean` restoration ending at CI #485; and
2. **present in the older file / repository plan but not yet re-confirmed**, meaning
   the layer appeared in the earlier `#429`-based documentation but is currently
   beyond the verified restart frontier.

As of CI #485, the current restart pass **does formalize and re-confirm**
substantial parts of the paper's bookkeeping infrastructure:

- fixed monoid observations on words and tuples;
- fixed-observation tuple substitutability and refinement monotonicity;
- named sentence contexts and named filling;
- a working MCFG syntax layer and first tuple/string derivation semantics;
- grammar-level and sample-level named tuple distributions;
- sample-safe merging and unit-rule closure soundness;
- transported learner distributions;
- reconstruction certificates and Gold-style stabilization wrappers;
- class-level and finite-hypothesis identification wrappers;
- finite support for sample-derived learner nodes and unit edges;
- output-type refinement substrate for MCFG rules;
- refined terminal, binary, and start rule skeletons;
- refined derivation and refined grammar skeletons;
- finite refined grammar certificates;
- finite output-type enumeration certificates;
- construction of output-type enumeration from `[Fintype M]`;
- finite base-rule support and finite-monoid rule-enumeration plans;
- concrete refined-rule enumeration certificate interfaces;
- actual refined terminal/binary/start rule lists from finite rule-enumeration data;
- relative and concrete sample-extraction certificates;
- sample-context consistency and sample-word consistency wrappers;
- target-side start-symbol derivation witnesses for sample words;
- learner-side sample-word generation interfaces;
- packaged learner word-semantics certificates;
- canonical learner grammar package interfaces;
- canonical rule-list specifications;
- rule-count summaries;
- enumeration-bound certificates;
- abstract polynomial-bound witnesses;
- parameter profiles for sample size, monoid size, and related bounds;
- shape / bounded-spine placeholder profiles;
- bounded-data recovery profile certificates;
- presentation-relative recovery profile certificates;
- main-theorem style interfaces connecting presentation-relative characteristic
  samples to post-threshold exactness and Gold-style identification;
- sample-support extraction from finite samples, first as sample-only support
  and then as support generated by observed tuple/context/unit-edge atoms;
- raw sample decomposition witnesses `w = namedFill d c x`, together with raw
  unit-edge witnesses from pairs of sample fillings with equal output type;
- generated-support lemmas connecting raw decomposition witnesses to sample
  named distributions and learner unit reachability;
- finite identity decomposition enumeration for every sample word;
- two-sided subword-context decomposition witnesses of the form
  `sampleWord = left ++ middle ++ right`;
- finite prefix/suffix and subword-cut enumeration for sample words;
- unit-edge witness enumeration from same-context/same-type subword pairs.

The following layers were claimed in the older `#429`-based document but are
**not yet re-confirmed in the current restart pass**:

- canonical learner nonterminals;
- sample-generated learner grammar skeletons;
- sample-generated start/terminal/binary/unit rule skeletons.

The current development **does not yet formalize** the full paper theorem in
its concrete grammar-construction form.  In particular, it does not yet
construct the actual canonical MCFG learner as a concrete `WorkingMCFG`, does
not yet implement the full sample-extracted terminal/binary/start/unit rule
generation algorithm as final grammar rules, does not yet construct the
presentation-relative characteristic sample from an arbitrary witnessing
presentation, and does not yet prove the hybrid filling lemma,
no-advice non-identifiability theorem, or bounded-spine polynomial-data theorem.

A safe one-sentence summary is:

> The Lean companion has been re-confirmed through CI #485 / commit `ff2b74c`
> up to the fixed-observation, distributional, finite-hypothesis,
> output-type-refinement, finite-enumeration, actual-refined-rule-list,
> sample-extraction, raw/subword-decomposition, subword-context-enumeration, and
> subword unit-edge-enumeration infrastructure for the MCFG learning
> construction; the canonical-nonterminal and sample-generated grammar/rule
> skeleton layers are the next unconfirmed frontier in the current restart pass,
> and the full concrete canonical-grammar reconstruction theorem remains future
> work.

---

## 2. Repository layout

The repository still contains the longer MCFG file sequence.  The status table
below distinguishes files re-confirmed by CI #485 from files that are only
listed as the next restoration targets.

The current MCFG formalization is organized as a sequence of small layers.

```text
LeanCfgProject.lean
LeanCfgProject/MCFG/Basic.lean

LeanCfgProject/MCFG/FI_v2_1_FixedObservation.lean
LeanCfgProject/MCFG/FI_v2_1_NamedSentenceContext.lean
LeanCfgProject/MCFG/FI_v2_1_MCFG_Syntax.lean
LeanCfgProject/MCFG/FI_v2_1_MCFG_Derivation.lean
LeanCfgProject/MCFG/FI_v2_1_MCFG_ContextualSemantics.lean
LeanCfgProject/MCFG/FI_v2_1_LearnerUnitClosure.lean
LeanCfgProject/MCFG/FI_v2_1_LearnerDistribution.lean
LeanCfgProject/MCFG/FI_v2_1_ReconstructionCertificate.lean
LeanCfgProject/MCFG/FI_v2_1_GoldStabilization.lean
LeanCfgProject/MCFG/FI_v2_1_IdentificationSummary.lean
LeanCfgProject/MCFG/FI_v2_1_FiniteSupport.lean
LeanCfgProject/MCFG/FI_v2_1_FiniteHypothesis.lean
LeanCfgProject/MCFG/FI_v2_1_FiniteHypothesisGold.lean
LeanCfgProject/MCFG/FI_v2_1_OutputTypeRefinement.lean
LeanCfgProject/MCFG/FI_v2_1_RefinedRules.lean
LeanCfgProject/MCFG/FI_v2_1_OutputTypedDerivationSummary.lean
LeanCfgProject/MCFG/FI_v2_1_RefinedGrammar.lean
LeanCfgProject/MCFG/FI_v2_1_FiniteRefinedGrammar.lean
LeanCfgProject/MCFG/FI_v2_1_FiniteOutputTypeEnumeration.lean
LeanCfgProject/MCFG/FI_v2_1_FiniteEnumerationSummary.lean
LeanCfgProject/MCFG/FI_v2_1_FintypeOutputEnumeration.lean
LeanCfgProject/MCFG/FI_v2_1_FintypeEnumerationCertificate.lean
LeanCfgProject/MCFG/FI_v2_1_FiniteBaseRuleSupport.lean
LeanCfgProject/MCFG/FI_v2_1_FiniteRuleEnumerationPlan.lean
LeanCfgProject/MCFG/FI_v2_1_FintypeRuleEnumerationPlan.lean
LeanCfgProject/MCFG/FI_v2_1_ConcreteRuleEnumerationSkeleton.lean
LeanCfgProject/MCFG/FI_v2_1_ConcreteRuleEnumerationCertificate.lean
LeanCfgProject/MCFG/FI_v2_1_FintypeConcreteRuleEnumeration.lean
LeanCfgProject/MCFG/FI_v2_1_RelativeSampleExtraction.lean
LeanCfgProject/MCFG/FI_v2_1_RelativeSampleExtractionExact.lean
LeanCfgProject/MCFG/FI_v2_1_RelativeSampleExtractionGold.lean
LeanCfgProject/MCFG/FI_v2_1_ConcreteExtractedSampleData.lean
LeanCfgProject/MCFG/FI_v2_1_ConcreteExtractedSampleExact.lean
LeanCfgProject/MCFG/FI_v2_1_ConcreteExtractedSampleGold.lean
LeanCfgProject/MCFG/FI_v2_1_ConcreteSampleConsistency.lean
LeanCfgProject/MCFG/FI_v2_1_ConcreteSampleConsistencyExact.lean
LeanCfgProject/MCFG/FI_v2_1_ConcreteSampleConsistencyGold.lean
LeanCfgProject/MCFG/FI_v2_1_SampleWordConsistencySkeleton.lean
LeanCfgProject/MCFG/FI_v2_1_SampleWordConsistencyExact.lean
LeanCfgProject/MCFG/FI_v2_1_SampleWordConsistencyGold.lean
LeanCfgProject/MCFG/FI_v2_1_StartRuleSampleWitness.lean
LeanCfgProject/MCFG/FI_v2_1_StartRuleSampleWitnessExact.lean
LeanCfgProject/MCFG/FI_v2_1_StartRuleSampleWitnessGold.lean
LeanCfgProject/MCFG/FI_v2_1_LearnerWordConsistencySkeleton.lean
LeanCfgProject/MCFG/FI_v2_1_LearnerWordConsistencyExact.lean
LeanCfgProject/MCFG/FI_v2_1_LearnerWordConsistencyGold.lean
LeanCfgProject/MCFG/FI_v2_1_LearnerWordSemanticsInterface.lean
LeanCfgProject/MCFG/FI_v2_1_LearnerWordSemanticsExact.lean
LeanCfgProject/MCFG/FI_v2_1_LearnerWordSemanticsGold.lean
LeanCfgProject/MCFG/FI_v2_1_CanonicalLearnerGrammarInterface.lean
LeanCfgProject/MCFG/FI_v2_1_CanonicalLearnerGrammarExact.lean
LeanCfgProject/MCFG/FI_v2_1_CanonicalLearnerGrammarGold.lean
LeanCfgProject/MCFG/FI_v2_1_CanonicalRuleListSpecification.lean
LeanCfgProject/MCFG/FI_v2_1_CanonicalRuleListSpecificationExact.lean
LeanCfgProject/MCFG/FI_v2_1_CanonicalRuleListSpecificationGold.lean
LeanCfgProject/MCFG/FI_v2_1_CanonicalRuleListCounting.lean
LeanCfgProject/MCFG/FI_v2_1_CanonicalRuleListCountingExact.lean
LeanCfgProject/MCFG/FI_v2_1_CanonicalRuleListCountingGold.lean
LeanCfgProject/MCFG/FI_v2_1_CanonicalEnumerationBoundInterface.lean
LeanCfgProject/MCFG/FI_v2_1_CanonicalEnumerationBoundExact.lean
LeanCfgProject/MCFG/FI_v2_1_CanonicalEnumerationBoundGold.lean
LeanCfgProject/MCFG/FI_v2_1_PolynomialBoundInterface.lean
LeanCfgProject/MCFG/FI_v2_1_PolynomialBoundExact.lean
LeanCfgProject/MCFG/FI_v2_1_PolynomialBoundGold.lean
LeanCfgProject/MCFG/FI_v2_1_ParameterProfileInterface.lean
LeanCfgProject/MCFG/FI_v2_1_ParameterProfileExact.lean
LeanCfgProject/MCFG/FI_v2_1_ParameterProfileGold.lean
LeanCfgProject/MCFG/FI_v2_1_ShapeProfileInterface.lean
LeanCfgProject/MCFG/FI_v2_1_ShapeProfileExact.lean
LeanCfgProject/MCFG/FI_v2_1_ShapeProfileGold.lean
LeanCfgProject/MCFG/FI_v2_1_BoundedDataRecoveryInterface.lean
LeanCfgProject/MCFG/FI_v2_1_BoundedDataRecoveryExact.lean
LeanCfgProject/MCFG/FI_v2_1_BoundedDataRecoveryGold.lean
LeanCfgProject/MCFG/FI_v2_1_PresentationRecoveryInterface.lean
LeanCfgProject/MCFG/FI_v2_1_PresentationRecoveryExact.lean
LeanCfgProject/MCFG/FI_v2_1_PresentationRecoveryGold.lean
LeanCfgProject/MCFG/FI_v2_1_MainTheoremInterface.lean
LeanCfgProject/MCFG/FI_v2_1_MainTheoremExact.lean
LeanCfgProject/MCFG/FI_v2_1_MainTheoremGold.lean
LeanCfgProject/MCFG/FI_v2_1_ActualRefinedRuleLists.lean
LeanCfgProject/MCFG/FI_v2_1_ActualRefinedRuleListsFintype.lean
LeanCfgProject/MCFG/FI_v2_1_ActualRefinedRuleListsSummary.lean
LeanCfgProject/MCFG/FI_v2_1_SampleExtractedRuleLists.lean
LeanCfgProject/MCFG/FI_v2_1_SampleExtractedRuleListsExact.lean
LeanCfgProject/MCFG/FI_v2_1_SampleExtractedRuleListsGold.lean
LeanCfgProject/MCFG/FI_v2_1_SampleSupportExtraction.lean
LeanCfgProject/MCFG/FI_v2_1_SampleSupportExtractionExact.lean
LeanCfgProject/MCFG/FI_v2_1_SampleSupportExtractionGold.lean
LeanCfgProject/MCFG/FI_v2_1_ObservedSampleAtoms.lean
LeanCfgProject/MCFG/FI_v2_1_ObservedSampleAtomsExact.lean
LeanCfgProject/MCFG/FI_v2_1_ObservedSampleAtomsGold.lean
LeanCfgProject/MCFG/FI_v2_1_RawSampleDecomposition.lean
LeanCfgProject/MCFG/FI_v2_1_RawSampleDecompositionExact.lean
LeanCfgProject/MCFG/FI_v2_1_RawSampleDecompositionGold.lean
LeanCfgProject/MCFG/FI_v2_1_RawSampleDecompositionGeneration.lean
LeanCfgProject/MCFG/FI_v2_1_RawSampleDecompositionGenerationExact.lean
LeanCfgProject/MCFG/FI_v2_1_RawSampleDecompositionGenerationGold.lean
LeanCfgProject/MCFG/FI_v2_1_RawSampleDecompositionEnumeration.lean
LeanCfgProject/MCFG/FI_v2_1_RawSampleDecompositionEnumerationExact.lean
LeanCfgProject/MCFG/FI_v2_1_RawSampleDecompositionEnumerationGold.lean
LeanCfgProject/MCFG/FI_v2_1_SubwordContextDecomposition.lean
LeanCfgProject/MCFG/FI_v2_1_SubwordContextDecompositionExact.lean
LeanCfgProject/MCFG/FI_v2_1_SubwordContextDecompositionGold.lean
LeanCfgProject/MCFG/FI_v2_1_SubwordContextEnumeration.lean
LeanCfgProject/MCFG/FI_v2_1_SubwordContextEnumerationExact.lean
LeanCfgProject/MCFG/FI_v2_1_SubwordContextEnumerationGold.lean
LeanCfgProject/MCFG/FI_v2_1_SubwordUnitEdgeEnumeration.lean
LeanCfgProject/MCFG/FI_v2_1_SubwordUnitEdgeEnumerationExact.lean
LeanCfgProject/MCFG/FI_v2_1_SubwordUnitEdgeEnumerationGold.lean
LeanCfgProject/MCFG/FI_v2_1_CanonicalLearnerNonterminal.lean
LeanCfgProject/MCFG/FI_v2_1_CanonicalLearnerNonterminalExact.lean
LeanCfgProject/MCFG/FI_v2_1_CanonicalLearnerNonterminalGold.lean
LeanCfgProject/MCFG/FI_v2_1_SampleGeneratedLearnerGrammarSkeleton.lean
LeanCfgProject/MCFG/FI_v2_1_SampleGeneratedLearnerGrammarSkeletonExact.lean
LeanCfgProject/MCFG/FI_v2_1_SampleGeneratedLearnerGrammarSkeletonGold.lean
LeanCfgProject/MCFG/FI_v2_1_SampleGeneratedRuleSkeleton.lean
LeanCfgProject/MCFG/FI_v2_1_SampleGeneratedRuleSkeletonExact.lean
LeanCfgProject/MCFG/FI_v2_1_SampleGeneratedRuleSkeletonGold.lean

.github/workflows/lean.yml
```

The intended root import chain is:

```lean
-- LeanCfgProject.lean
import LeanCfgProject.MCFG.Basic
```

In the current restart pass, the aggregate file is intentionally minimal and
imports only the latest re-confirmed top module:

```lean
-- LeanCfgProject/MCFG/Basic.lean
import LeanCfgProject.MCFG.FI_v2_1_SubwordUnitEdgeEnumerationGold
```

The long list above records the repository layout and the intended restoration
order.  In the current restart pass, files after
`FI_v2_1_SubwordUnitEdgeEnumerationGold` are not yet part of the confirmed
frontier.


---

## 3. File-by-file checked status

The table is file-by-file rather than theorem-by-theorem.  Some files are
interface or wrapper layers.  In the current restart pass, rows 1--109 are
re-confirmed by CI #485.  Rows 110--118 are the next restoration targets: they
were present in the older `#429`-based documentation, but they have not yet
been re-confirmed after the aggregate import was narrowed and rebuilt step by
step.

| # | File | Main role | Status |
|---:|---|---|---|
| 1 | `FI_v2_1_FixedObservation.lean` | Words, tuples, observation evaluation, tuple types, fixed-`h` substitutability, refinement monotonicity | reconfirmed in CI #485 |
| 2 | `FI_v2_1_NamedSentenceContext.lean` | Raw and well-formed named sentence contexts, named filling | reconfirmed in CI #485 |
| 3 | `FI_v2_1_MCFG_Syntax.lean` | Working binary MCFG syntax: templates, rules, fan-out, nondeleting side conditions | reconfirmed in CI #485 |
| 4 | `FI_v2_1_MCFG_Derivation.lean` | First derivation semantics: tuple and string languages | reconfirmed in CI #485 |
| 5 | `FI_v2_1_MCFG_ContextualSemantics.lean` | Exposed tuples, grammar/sample named distributions, sample-safe merge soundness | reconfirmed in CI #485 |
| 6 | `FI_v2_1_LearnerUnitClosure.lean` | Learner unit edges, unit reachability, soundness of unit-rule closure | reconfirmed in CI #485 |
| 7 | `FI_v2_1_LearnerDistribution.lean` | Transported contexts and learner approximate distributions | reconfirmed in CI #485 |
| 8 | `FI_v2_1_ReconstructionCertificate.lean` | Distribution-level reconstruction certificates and characteristic-sample skeleton | reconfirmed in CI #485 |
| 9 | `FI_v2_1_GoldStabilization.lean` | Texts, prefix samples, eventual containment, Gold-style stabilization | reconfirmed in CI #485 |
| 10 | `FI_v2_1_IdentificationSummary.lean` | Class-level identification wrappers from characteristic samples | reconfirmed in CI #485 |
| 11 | `FI_v2_1_FiniteSupport.lean` | Finite sample support for tuples, contexts, and listed unit edges | reconfirmed in CI #485 |
| 12 | `FI_v2_1_FiniteHypothesis.lean` | Finite learner hypothesis object, soundness, completeness-to-exactness certificate | reconfirmed in CI #485 |
| 13 | `FI_v2_1_FiniteHypothesisGold.lean` | Finite-hypothesis Gold wrapper and telltale-style class summaries | reconfirmed in CI #485 |
| 14 | `FI_v2_1_OutputTypeRefinement.lean` | Output-type computation for templates and rule applications | reconfirmed in CI #485 |
| 15 | `FI_v2_1_RefinedRules.lean` | Refined terminal, binary, and start rule skeletons | reconfirmed in CI #485 |
| 16 | `FI_v2_1_OutputTypedDerivationSummary.lean` | Output-typed tuple language and tuple-level conservativity summaries | reconfirmed in CI #485 |
| 17 | `FI_v2_1_RefinedGrammar.lean` | Predicate-style output-type refined grammar skeleton and refined derivations | reconfirmed in CI #485 |
| 18 | `FI_v2_1_FiniteRefinedGrammar.lean` | Finite refined grammar certificate using explicit finite rule lists | reconfirmed in CI #485 |
| 19 | `FI_v2_1_FiniteOutputTypeEnumeration.lean` | Certificate interface for finite enumeration of output-type vectors | reconfirmed in CI #485 |
| 20 | `FI_v2_1_FiniteEnumerationSummary.lean` | Bundles finite refined grammar certificates with output-type enumeration support | reconfirmed in CI #485 |
| 21 | `FI_v2_1_FintypeOutputEnumeration.lean` | Builds output-type enumeration from `[Fintype M]` via `Fintype.elems` | reconfirmed in CI #485 |
| 22 | `FI_v2_1_FintypeEnumerationCertificate.lean` | Finite-monoid output-type refinement certificates | reconfirmed in CI #485 |
| 23 | `FI_v2_1_FiniteBaseRuleSupport.lean` | Explicit finite support for ordinary terminal, binary, and start rules | reconfirmed in CI #485 |
| 24 | `FI_v2_1_FiniteRuleEnumerationPlan.lean` | Finite rule-enumeration plans from base rules plus output-type lists | reconfirmed in CI #485 |
| 25 | `FI_v2_1_FintypeRuleEnumerationPlan.lean` | Canonical rule-enumeration plans when the observation monoid is finite | reconfirmed in CI #485 |
| 26 | `FI_v2_1_ConcreteRuleEnumerationSkeleton.lean` | Support predicates for concrete refined terminal/binary/start rules under a finite plan | reconfirmed in CI #485 |
| 27 | `FI_v2_1_ConcreteRuleEnumerationCertificate.lean` | Certificate interface for concrete refined rule enumerations | reconfirmed in CI #485 |
| 28 | `FI_v2_1_FintypeConcreteRuleEnumeration.lean` | Connects concrete refined rule enumerations to finite-monoid rule-enumeration plans | reconfirmed in CI #485 |
| 29 | `FI_v2_1_RelativeSampleExtraction.lean` | Relative sample-extraction certificates linking finite hypotheses and concrete refined enumerations | reconfirmed in CI #485 |
| 30 | `FI_v2_1_RelativeSampleExtractionExact.lean` | Exactness interface for relative sample extraction | reconfirmed in CI #485 |
| 31 | `FI_v2_1_RelativeSampleExtractionGold.lean` | Gold wrapper for relative sample extraction | reconfirmed in CI #485 |
| 32 | `FI_v2_1_ConcreteExtractedSampleData.lean` | Implementation-facing concrete extracted sample data certificates | reconfirmed in CI #485 |
| 33 | `FI_v2_1_ConcreteExtractedSampleExact.lean` | Exactness certificate for concrete extracted sample data | reconfirmed in CI #485 |
| 34 | `FI_v2_1_ConcreteExtractedSampleGold.lean` | Gold wrapper for concrete extracted sample data | reconfirmed in CI #485 |
| 35 | `FI_v2_1_ConcreteSampleConsistency.lean` | Sample-context consistency for concrete extracted samples | reconfirmed in CI #485 |
| 36 | `FI_v2_1_ConcreteSampleConsistencyExact.lean` | Exactness plus sample-context consistency | reconfirmed in CI #485 |
| 37 | `FI_v2_1_ConcreteSampleConsistencyGold.lean` | Gold wrapper for sample-context consistent extraction | reconfirmed in CI #485 |
| 38 | `FI_v2_1_SampleWordConsistencySkeleton.lean` | Target-side sample-word consistency skeleton | reconfirmed in CI #485 |
| 39 | `FI_v2_1_SampleWordConsistencyExact.lean` | Exactness plus sample-word consistency | reconfirmed in CI #485 |
| 40 | `FI_v2_1_SampleWordConsistencyGold.lean` | Gold wrapper for word-consistent extraction | reconfirmed in CI #485 |
| 41 | `FI_v2_1_StartRuleSampleWitness.lean` | Start-symbol derivation witnesses for sample words | reconfirmed in CI #485 |
| 42 | `FI_v2_1_StartRuleSampleWitnessExact.lean` | Exactness plus target-side start derivation witnesses | reconfirmed in CI #485 |
| 43 | `FI_v2_1_StartRuleSampleWitnessGold.lean` | Gold wrapper for start-witness consistent extraction | reconfirmed in CI #485 |
| 44 | `FI_v2_1_LearnerWordConsistencySkeleton.lean` | Learner-side sample-word generation interface | reconfirmed in CI #485 |
| 45 | `FI_v2_1_LearnerWordConsistencyExact.lean` | Exactness plus learner-side sample-word generation | reconfirmed in CI #485 |
| 46 | `FI_v2_1_LearnerWordConsistencyGold.lean` | Gold wrapper for learner-side sample-word consistency | reconfirmed in CI #485 |
| 47 | `FI_v2_1_LearnerWordSemanticsInterface.lean` | Packaged learner word-semantics certificates | reconfirmed in CI #485 |
| 48 | `FI_v2_1_LearnerWordSemanticsExact.lean` | Exactness plus packaged learner word semantics | reconfirmed in CI #485 |
| 49 | `FI_v2_1_LearnerWordSemanticsGold.lean` | Gold wrapper for packaged learner word semantics | reconfirmed in CI #485 |
| 50 | `FI_v2_1_CanonicalLearnerGrammarInterface.lean` | Canonical learner grammar package interface | reconfirmed in CI #485 |
| 51 | `FI_v2_1_CanonicalLearnerGrammarExact.lean` | Exactness certificate for canonical learner grammar packages | reconfirmed in CI #485 |
| 52 | `FI_v2_1_CanonicalLearnerGrammarGold.lean` | Gold wrapper for canonical learner grammar packages | reconfirmed in CI #485 |
| 53 | `FI_v2_1_CanonicalRuleListSpecification.lean` | Rule-list coverage and plan-support specification for canonical learner packages | reconfirmed in CI #485 |
| 54 | `FI_v2_1_CanonicalRuleListSpecificationExact.lean` | Exact canonical package plus rule-list specification | reconfirmed in CI #485 |
| 55 | `FI_v2_1_CanonicalRuleListSpecificationGold.lean` | Gold wrapper preserving rule-list specification after the characteristic sample | reconfirmed in CI #485 |
| 56 | `FI_v2_1_CanonicalRuleListCounting.lean` | Counting summaries for ordinary and refined rule lists | reconfirmed in CI #485 |
| 57 | `FI_v2_1_CanonicalRuleListCountingExact.lean` | Exact canonical package plus rule-list counting summary | reconfirmed in CI #485 |
| 58 | `FI_v2_1_CanonicalRuleListCountingGold.lean` | Gold wrapper preserving rule-count summaries after the characteristic sample | reconfirmed in CI #485 |
| 59 | `FI_v2_1_CanonicalEnumerationBoundInterface.lean` | External enumeration-bound certificates for refined rule counts and related finite data | reconfirmed in CI #485 |
| 60 | `FI_v2_1_CanonicalEnumerationBoundExact.lean` | Exact canonical package plus enumeration-bound certificate | reconfirmed in CI #485 |
| 61 | `FI_v2_1_CanonicalEnumerationBoundGold.lean` | Gold wrapper preserving enumeration bounds after the characteristic sample | reconfirmed in CI #485 |
| 62 | `FI_v2_1_PolynomialBoundInterface.lean` | Abstract polynomial-bound witness interface for enumeration bounds | reconfirmed in CI #485 |
| 63 | `FI_v2_1_PolynomialBoundExact.lean` | Exact canonical package plus polynomial-bound witnesses | reconfirmed in CI #485 |
| 64 | `FI_v2_1_PolynomialBoundGold.lean` | Gold wrapper preserving polynomial-bound witnesses after the characteristic sample | reconfirmed in CI #485 |
| 65 | `FI_v2_1_ParameterProfileInterface.lean` | Parameter profile interface for sample size, monoid size, fanout placeholders, and total bounds | reconfirmed in CI #485 |
| 66 | `FI_v2_1_ParameterProfileExact.lean` | Exact canonical package plus parameter profile | reconfirmed in CI #485 |
| 67 | `FI_v2_1_ParameterProfileGold.lean` | Gold wrapper preserving parameter profiles after the characteristic sample | reconfirmed in CI #485 |
| 68 | `FI_v2_1_ShapeProfileInterface.lean` | Shape/bounded-spine placeholder profile interface | reconfirmed in CI #485 |
| 69 | `FI_v2_1_ShapeProfileExact.lean` | Exact canonical package plus shape profile | reconfirmed in CI #485 |
| 70 | `FI_v2_1_ShapeProfileGold.lean` | Gold wrapper preserving shape profiles after the characteristic sample | reconfirmed in CI #485 |
| 71 | `FI_v2_1_BoundedDataRecoveryInterface.lean` | Bounded-data recovery profile interface above shape profiles | reconfirmed in CI #485 |
| 72 | `FI_v2_1_BoundedDataRecoveryExact.lean` | Exact canonical package plus bounded-data recovery profile | reconfirmed in CI #485 |
| 73 | `FI_v2_1_BoundedDataRecoveryGold.lean` | Gold wrapper preserving bounded-data recovery profiles after the characteristic sample | reconfirmed in CI #485 |
| 74 | `FI_v2_1_PresentationRecoveryInterface.lean` | Presentation-relative recovery profile interface | reconfirmed in CI #485 |
| 75 | `FI_v2_1_PresentationRecoveryExact.lean` | Exact canonical package plus presentation-relative recovery profile | reconfirmed in CI #485 |
| 76 | `FI_v2_1_PresentationRecoveryGold.lean` | Gold wrapper preserving presentation-relative recovery profiles | reconfirmed in CI #485 |
| 77 | `FI_v2_1_MainTheoremInterface.lean` | Main-theorem style package from presentation-relative characteristic samples to identification | reconfirmed in CI #485 |
| 78 | `FI_v2_1_MainTheoremExact.lean` | Post-threshold exact recovery interface for samples containing the characteristic sample | reconfirmed in CI #485 |
| 79 | `FI_v2_1_MainTheoremGold.lean` | Gold-style main-theorem summary package | reconfirmed in CI #485 |
| 80 | `FI_v2_1_ActualRefinedRuleLists.lean` | Actual refined terminal/binary/start rule lists generated from finite rule-enumeration data | reconfirmed in CI #485 |
| 81 | `FI_v2_1_ActualRefinedRuleListsFintype.lean` | Finite-monoid instantiation of actual refined rule lists | reconfirmed in CI #485 |
| 82 | `FI_v2_1_ActualRefinedRuleListsSummary.lean` | Summary interface connecting actual refined rule lists to existing certificates | reconfirmed in CI #485 |
| 83 | `FI_v2_1_SampleExtractedRuleLists.lean` | Sample-extracted rule-list data using actual refined rule enumerations | reconfirmed in CI #485 |
| 84 | `FI_v2_1_SampleExtractedRuleListsExact.lean` | Exactness wrapper for sample-extracted rule-list data | reconfirmed in CI #485 |
| 85 | `FI_v2_1_SampleExtractedRuleListsGold.lean` | Gold wrapper for sample-extracted rule-list data | reconfirmed in CI #485 |
| 86 | `FI_v2_1_SampleSupportExtraction.lean` | Constructs a sample-only finite learner support from a finite sample | reconfirmed in CI #485 |
| 87 | `FI_v2_1_SampleSupportExtractionExact.lean` | Exactness wrapper for sample-support extraction | reconfirmed in CI #485 |
| 88 | `FI_v2_1_SampleSupportExtractionGold.lean` | Gold wrapper for sample-support extraction | reconfirmed in CI #485 |
| 89 | `FI_v2_1_ObservedSampleAtoms.lean` | Finite support built from observed tuple/context/unit-edge atom lists | reconfirmed in CI #485 |
| 90 | `FI_v2_1_ObservedSampleAtomsExact.lean` | Exactness wrapper for observed sample atoms | reconfirmed in CI #485 |
| 91 | `FI_v2_1_ObservedSampleAtomsGold.lean` | Gold wrapper for observed sample atoms | reconfirmed in CI #485 |
| 92 | `FI_v2_1_RawSampleDecomposition.lean` | Raw sample decompositions `w = namedFill d c x` and unit-edge witnesses | reconfirmed in CI #485 |
| 93 | `FI_v2_1_RawSampleDecompositionExact.lean` | Exactness wrapper for raw sample decomposition data | reconfirmed in CI #485 |
| 94 | `FI_v2_1_RawSampleDecompositionGold.lean` | Gold wrapper for raw sample decomposition data | reconfirmed in CI #485 |
| 95 | `FI_v2_1_RawSampleDecompositionGeneration.lean` | Turns raw decomposition witnesses into generated support, sample-distribution facts, and unit reachability facts | reconfirmed in CI #485 |
| 96 | `FI_v2_1_RawSampleDecompositionGenerationExact.lean` | Exactness wrapper for raw sample decomposition generation | reconfirmed in CI #485 |
| 97 | `FI_v2_1_RawSampleDecompositionGenerationGold.lean` | Gold wrapper for raw sample decomposition generation | reconfirmed in CI #485 |
| 98 | `FI_v2_1_RawSampleDecompositionEnumeration.lean` | Enumerates identity one-hole decompositions for every sample word | reconfirmed in CI #485 |
| 99 | `FI_v2_1_RawSampleDecompositionEnumerationExact.lean` | Exactness wrapper for raw sample decomposition enumeration | reconfirmed in CI #485 |
| 100 | `FI_v2_1_RawSampleDecompositionEnumerationGold.lean` | Gold wrapper for raw sample decomposition enumeration | reconfirmed in CI #485 |
| 101 | `FI_v2_1_SubwordContextDecomposition.lean` | Two-sided `left ++ middle ++ right` subword/context decomposition witnesses | reconfirmed in CI #485 |
| 102 | `FI_v2_1_SubwordContextDecompositionExact.lean` | Exactness wrapper for subword/context decomposition | reconfirmed in CI #485 |
| 103 | `FI_v2_1_SubwordContextDecompositionGold.lean` | Gold wrapper for subword/context decomposition | reconfirmed in CI #485 |
| 104 | `FI_v2_1_SubwordContextEnumeration.lean` | Finite prefix/suffix and subword-cut enumeration for sample words | reconfirmed in CI #485 |
| 105 | `FI_v2_1_SubwordContextEnumerationExact.lean` | Exactness wrapper for subword/context enumeration | reconfirmed in CI #485 |
| 106 | `FI_v2_1_SubwordContextEnumerationGold.lean` | Gold wrapper for subword/context enumeration | reconfirmed in CI #485 |
| 107 | `FI_v2_1_SubwordUnitEdgeEnumeration.lean` | Enumerates same-context/same-type subword pairs as unit-edge witnesses | reconfirmed in CI #485 |
| 108 | `FI_v2_1_SubwordUnitEdgeEnumerationExact.lean` | Exactness wrapper for subword unit-edge enumeration | reconfirmed in CI #485 |
| 109 | `FI_v2_1_SubwordUnitEdgeEnumerationGold.lean` | Gold wrapper for subword unit-edge enumeration | reconfirmed in CI #485 |
| 110 | `FI_v2_1_CanonicalLearnerNonterminal.lean` | Canonical learner nonterminal type generated from sample support | pending re-confirmation in current restart |
| 111 | `FI_v2_1_CanonicalLearnerNonterminalExact.lean` | Exactness wrapper for canonical learner nonterminals | pending re-confirmation in current restart |
| 112 | `FI_v2_1_CanonicalLearnerNonterminalGold.lean` | Gold wrapper for canonical learner nonterminals | pending re-confirmation in current restart |
| 113 | `FI_v2_1_SampleGeneratedLearnerGrammarSkeleton.lean` | Sample-generated learner grammar skeleton with arity and nonterminal membership facts | pending re-confirmation in current restart |
| 114 | `FI_v2_1_SampleGeneratedLearnerGrammarSkeletonExact.lean` | Exactness wrapper for sample-generated learner grammar skeletons | pending re-confirmation in current restart |
| 115 | `FI_v2_1_SampleGeneratedLearnerGrammarSkeletonGold.lean` | Gold wrapper for sample-generated learner grammar skeletons | pending re-confirmation in current restart |
| 116 | `FI_v2_1_SampleGeneratedRuleSkeleton.lean` | Start, terminal, concatenation, and unit rule candidate skeletons generated from sample data | pending re-confirmation in current restart |
| 117 | `FI_v2_1_SampleGeneratedRuleSkeletonExact.lean` | Exactness wrapper for sample-generated rule skeletons | pending re-confirmation in current restart |
| 118 | `FI_v2_1_SampleGeneratedRuleSkeletonGold.lean` | Gold wrapper for sample-generated rule skeletons | pending re-confirmation in current restart |

---

## 4. What is currently formalized

### 4.1 Core fixed-observation substrate

Main checked layers: `FixedObservation`, `NamedSentenceContext`, `MCFG_Syntax`,
`MCFG_Derivation`, `MCFG_ContextualSemantics`.

Representative declarations:

```lean
abbrev Word (α : Type u) := List α
abbrev Tuple (α : Type u) (d : Nat) := Fin d → Word α

def evalObs (obs : α → M) : Word α → M
def tupleType {d : Nat} (obs : α → M) (x : Tuple α d) : Fin d → M

structure Refines (obs : α → M) (obs' : α → M') where
  map : M' → M
  map_one : map 1 = 1
  map_mul : ∀ x y : M', map (x * y) = map x * map y
  comm : ∀ a : α, map (obs' a) = obs a
```

The development checks the append law for observations, compatibility under
refinement, fixed-observation tuple substitutability, and the named-context
version of the same idea.  It also introduces working MCFG syntax with terminal,
binary, and start rules, plus a first tuple/string derivation semantics.

### 4.2 Sample-safe context transport and unit closure

Main checked layers: `LearnerUnitClosure`, `LearnerDistribution`,
`ReconstructionCertificate`, `GoldStabilization`.

Representative declarations:

```lean
PositiveSample
SampleSafeMerge
LearnerUnitEdge
LearnerUnitReach
LearnerApproxDistribution
DistributionReconstructionCertificate
DistributionCharacteristicSample
DistributionIdentifiesInLimit
```

The checked content is distributional: sample-safe unit edges preserve target
named-context distributions, the reflexive-transitive closure of such edges is
sound, and observed contexts can be transported along safe unit reachability.
The reconstruction-certificate and Gold layers package the usual finite
characteristic-sample argument.

### 4.3 Output-type refinement and finite enumeration

Main checked layers: `OutputTypeRefinement`, `RefinedRules`,
`OutputTypedDerivationSummary`, `RefinedGrammar`, `FiniteRefinedGrammar`,
`FiniteOutputTypeEnumeration`, `FintypeOutputEnumeration`,
`FiniteRuleEnumerationPlan`, and `FintypeRuleEnumerationPlan`.

Representative declarations:

```lean
templateAtomType
templateWordType
templateTupleType
TerminalRule.outputType
BinaryRule.outputType

RefinedNonterminal
RefinedTerminalRule
RefinedBinaryRule
RefinedStartRule

OutputTypedTupleLanguage
actualRefinedNonterminal
FiniteOutputTypeRefinedGrammar
OutputTypeEnumeration
OutputTypeEnumeration.ofFintype
FiniteRuleEnumerationPlan.ofFintype
```

This block formalizes nonterminals refined by componentwise observation type,
finite certificates for refined grammars, and finite output-type enumeration
from `[Fintype M]`.

### 4.4 Actual refined rule lists

Current constructive layers: `ActualRefinedRuleLists`,
`ActualRefinedRuleListsFintype`, `ActualRefinedRuleListsSummary`.

Representative declarations include:

```lean
actualRefinedTerminalRules
actualRefinedBinaryRules
actualRefinedStartRules

mem_actualRefinedTerminalRules
mem_actualRefinedBinaryRules
mem_actualRefinedStartRules

actualFiniteOutputTypeRefinedGrammar
actualFiniteOutputTypeRefinedGrammar_coversAll
actualConcreteRefinedRuleEnumeration
actualFintypeConcreteRuleEnumeration
```

This is a substantial vertical step beyond the earlier certificate interfaces.
The development now defines actual finite lists of refined terminal, binary, and
start rules from finite rule-enumeration data and proves that ordinary
rule-refinement instances are included in those lists.  The finite-monoid
version plugs these actual lists into the previously defined
`FintypeConcreteRuleEnumeration` interface.

### 4.5 Sample extraction, support extraction, and observed atoms

Current constructive layers: `SampleExtractedRuleLists`,
`SampleSupportExtraction`, `ObservedSampleAtoms`, and their exactness/Gold
wrappers.

Representative declarations include:

```lean
SampleExtractedRuleLists
SampleExtractedRuleLists.concreteRules
SampleExtractedRuleLists.toConcreteExtractedSampleData

sampleOnlySupport
sampleOnlySupport.listedUnitEdgesAreSafe

supportOfObservedAtoms
supportOfObservedAtoms.sample_eq
supportOfObservedAtoms.supportsTuple_iff
supportOfObservedAtoms.supportsContext_iff
supportOfObservedAtoms.supportsUnitEdge_iff

ObservedSampleAtoms
ObservedSampleAtoms.toSampleExtractedRuleLists
ObservedSampleAtoms.toFiniteLearnerHypothesis
```

The sample side has moved vertically.  Instead of taking an arbitrary
`FiniteLearnerSupport` as an opaque input, the development defines a sample-only
support and then a support built from explicit observed tuple, context, and
unit-edge atom lists.  These supports can be fed into the existing concrete
sample-extraction and finite-hypothesis pipeline.

### 4.6 Raw sample decomposition and generated support

Checked layers: `RawSampleDecomposition`, `RawSampleDecompositionGeneration`,
`RawSampleDecompositionEnumeration`, and their exactness/Gold wrappers.

Representative declarations include:

```lean
RawSampleDecomposition
RawSampleUnitEdgeWitness
RawSampleDecompositionData
RawSampleGeneratedSupport

RawSampleDecompositionData.generatedSupport
RawSampleDecompositionData.decomposition_supported
RawSampleDecompositionData.decomposition_sample_licensed
RawSampleDecompositionData.unitEdge_supported_and_safe
RawSampleDecompositionData.unitEdge_reaches_in_sampleExtractedRuleLists

identityNamedContext
singletonRawSampleDecomposition
singletonRawSampleDecompositions
sampleWordOnlyRawSampleDecompositionData_covers_sample
sampleWordOnlyRawSampleDecompositionData_supported_sample_word
```

A `RawSampleDecomposition` records that a sample word is obtained by filling a
named context with a tuple:

```text
sampleWord ∈ K
namedFill d context tuple = sampleWord
```

A `RawSampleUnitEdgeWitness` records two sample fillings in the same named
context with equal output type:

```text
namedFill d context src ∈ K
namedFill d context tgt ∈ K
tupleType obs src = tupleType obs tgt
```

The generation layer turns such witnesses into support membership, sample
named-distribution facts, and learner unit reachability.  The enumeration layer
adds a concrete identity one-hole decomposition for every sample word.

### 4.7 Subword-context and unit-edge enumeration

Checked layers: `SubwordContextDecomposition`, `SubwordContextEnumeration`,
`SubwordUnitEdgeEnumeration`, and their exactness/Gold wrappers.

Representative declarations include:

```lean
SubwordSampleDecomposition
twoSidedNamedContext
SubwordSampleDecomposition.toRawSampleDecomposition
SubwordContextDecompositionData.toRawSampleDecompositionData
SubwordContextDecompositionData.subword_context_mem_sampleDistribution

PrefixSuffixCut
prefixSuffixCuts
SubwordCut
subwordCuts
subwordDecompositionsForWord
enumeratedSubwordDecompositions
enumeratedSubwordContextDecompositionData
enumeratedSubwordContextDecompositionData_supported_sample_word

SubwordDecompositionPair
subwordDecompositionPairs
typedSameContextSubwordPairs
rawUnitEdgeWitnessOfSubwordPair
rawUnitEdgeWitnessesOfSubwordPairs
SubwordUnitEdgeEnumerationData.typedPair_unitReach
```

This is the current strongest sample-to-support path.  For a sample word,
finite prefix/suffix cuts enumerate candidate decompositions of the form

```text
sampleWord = left ++ middle ++ right.
```

Such decompositions induce one-hole named contexts and singleton tuples.  Pairs
of listed decompositions with the same context and the same tuple observation
type are then converted into raw unit-edge witnesses and into learner unit
reachability facts.

### 4.8 Next unconfirmed frontier: canonical learner nonterminals and grammar/rule skeletons

The following layers appeared in the older `#429`-based documentation, but they
are **not yet re-confirmed in the current restart pass**:

```lean
FI_v2_1_CanonicalLearnerNonterminal
FI_v2_1_CanonicalLearnerNonterminalExact
FI_v2_1_CanonicalLearnerNonterminalGold
FI_v2_1_SampleGeneratedLearnerGrammarSkeleton
FI_v2_1_SampleGeneratedLearnerGrammarSkeletonExact
FI_v2_1_SampleGeneratedLearnerGrammarSkeletonGold
FI_v2_1_SampleGeneratedRuleSkeleton
FI_v2_1_SampleGeneratedRuleSkeletonExact
FI_v2_1_SampleGeneratedRuleSkeletonGold
```

These are the immediate next files to restore.  Until a later CI run imports
and succeeds through these modules again, they should be described as planned /
previously documented layers rather than as part of the current trusted CI
frontier.

### 4.9 Canonical learner packages and main-theorem style wrappers

Main checked layers: `CanonicalLearnerGrammarInterface` through
`MainTheoremGold`.

Representative declarations include:

```lean
CanonicalLearnerGrammarPackage
CanonicalRuleListSpecification
CanonicalRuleListCountingSpecification
CanonicalEnumerationBounds
PolynomialBoundWitness
CanonicalParameterProfile
CanonicalShapeProfile
CanonicalBoundedDataRecoveryProfile
CanonicalPresentationRecoveryProfile

FixedMonoidMCFGLearningMainPackage
FixedMonoidMCFGLearningPostThresholdSample
FixedMonoidMCFGLearningGoldTheorem
```

These layers are mostly certificate interfaces and wrappers.  They are useful
because they show that once the remaining concrete construction obligations are
supplied, the existing infrastructure carries them to post-threshold exactness
and Gold-style distributional identification.  They should not be mistaken for
a complete construction of the canonical learner grammar.

---

## 5. Correspondence with paper notions

| Paper notion | Lean declaration | Status |
|---|---|---|
| alphabet `Σ` | type variable `α` | formalized abstractly |
| word over `Σ` | `Word α := List α` | formalized |
| tuple of arity `d` | `Tuple α d := Fin d → Word α` | formalized |
| fixed observation on letters | `obs : α → M` | formalized |
| extension to words | `evalObs obs` | formalized |
| componentwise tuple type | `tupleType obs x` | formalized |
| refinement of observations | `Refines obs obs'` | formalized |
| monotonicity under refinement | `fixedTupleSubstitutable_of_refines` | proved |
| named sentence contexts | `NamedSentenceContext` | formalized |
| named context filling | `namedFill` | formalized |
| named tuple distribution | `NamedDistribution` | formalized |
| fixed named tuple substitutability | `FixedNamedTupleSubstitutable` | formalized |
| MCFG templates | `TemplateAtom`, `TemplateWord`, `TemplateTuple` | formalized |
| nondeleting templates | `TemplateTuple.Nondeleting` | formalized |
| start, terminal, binary rules | `StartRule`, `TerminalRule`, `BinaryRule` | formalized |
| working MCFG presentation skeleton | `WorkingMCFG` | formalized |
| tuple derivability | `DerivesTuple` | formalized |
| tuple and string languages | `TupleLanguage`, `StringLanguage` | formalized |
| sample-safe merge | `SampleSafeMerge` | formalized |
| unit-rule closure | `LearnerUnitReach` | formalized |
| learner transported distribution | `LearnerApproxDistribution` | formalized |
| finite learner support | `FiniteLearnerSupport` | formalized |
| output-type computation | `templateWordType`, `templateTupleType`, `TerminalRule.outputType`, `BinaryRule.outputType` | formalized |
| refined nonterminal and rules | `RefinedNonterminal`, `RefinedTerminalRule`, `RefinedBinaryRule`, `RefinedStartRule` | formalized |
| finite refined grammar certificate | `FiniteOutputTypeRefinedGrammar` | formalized |
| output-type enumeration from finite monoid | `OutputTypeEnumeration.ofFintype` | formalized |
| finite rule-enumeration plan | `FiniteRuleEnumerationPlan` | formalized |
| actual refined terminal/binary/start rule lists | `actualRefinedTerminalRules`, `actualRefinedBinaryRules`, `actualRefinedStartRules` | formalized |
| coverage of actual refined rule lists | `actualFiniteOutputTypeRefinedGrammar_coversAll` and related membership theorems | proved |
| sample-only finite support | `sampleOnlySupport` | formalized |
| finite support from observed atoms | `supportOfObservedAtoms` | formalized |
| raw sample decomposition | `RawSampleDecomposition` | formalized |
| raw sample unit-edge witness | `RawSampleUnitEdgeWitness` | formalized |
| generated support from raw witnesses | `RawSampleGeneratedSupport` and related theorems | formalized |
| identity decomposition for sample words | `singletonRawSampleDecompositions` | formalized |
| two-sided subword decomposition | `SubwordSampleDecomposition` | formalized |
| finite subword-cut enumeration | `prefixSuffixCuts`, `subwordCuts`, `enumeratedSubwordDecompositions` | formalized |
| unit-edge enumeration from subword pairs | `typedSameContextSubwordPairs`, `rawUnitEdgeWitnessesOfSubwordPairs` | formalized |
| canonical learner nonterminal type | `CanonicalLearnerNonterminal` | pending re-confirmation in current restart |
| finite learner nonterminal list from support | `supportCanonicalNonterminals` | pending re-confirmation in current restart |
| sample-generated learner grammar skeleton | `SampleGeneratedLearnerGrammarSkeleton` | pending re-confirmation in current restart |
| sample-generated rule skeleton | `SampleGeneratedRuleSkeleton` | pending re-confirmation in current restart |
| canonical learner grammar package | `CanonicalLearnerGrammarPackage` | formalized as interface |
| main theorem package | `FixedMonoidMCFGLearningMainPackage` | formalized as certificate interface |
| Gold-style main theorem summary | `FixedMonoidMCFGLearningGoldTheorem` | formalized as interface |
| concrete canonical learner grammar as `WorkingMCFG` | not yet formalized | pending |
| final sample-extracted rule-generation algorithm as grammar rules | partially prepared, not fully formalized | pending |
| full grammar-level exact reconstruction theorem | not yet formalized | pending |
| no-advice non-identifiability | not yet formalized | pending |
| bounded-spine polynomial-data theorem | not yet formalized | pending |

---

## 6. What is not formalized yet

The current Lean development should not be described as a complete
machine-checked proof of the paper.  In addition, because this file is now
tracking a restart/reconfirmation pass, the canonical-nonterminal and
sample-generated learner/rule skeleton files should be treated as pending
re-confirmation until CI is extended beyond `SubwordUnitEdgeEnumerationGold`.

The following major parts remain outside the current confirmed formalization.

1. **Concrete canonical learner grammar as a `WorkingMCFG`.**  The current top
   layers define nonterminals and rule candidates, but they do not yet assemble
   them as a concrete `WorkingMCFG` with final terminal/binary/start rule lists.

2. **Final sample-extracted rule generation as grammar rules.**  The development
   now has subword decompositions, unit-edge witnesses, nonterminals, and rule
   candidates.  The remaining step is to convert these candidates into the
   final grammar-rule lists and prove the advertised coverage properties.

3. **Sample consistency for the fully constructed learner grammar.**  The
   development can produce start candidates for sample words and learner-side
   word-semantics interfaces, but it does not yet prove sample generation from
   an actual concrete grammar.

4. **Construction of the presentation-relative characteristic sample.**  The
   certificate layers assume distribution-level, finite-hypothesis,
   package-level, or presentation-recovery characteristic-sample witnesses.
   They do not yet prove that the paper's finite characteristic sample can be
   extracted from every witnessing working MCFG presentation.

5. **Occurrence witnesses in derivation trees.**  `ExposedWithContext` is still
   abstract.  A full derivation-tree occurrence notion connecting nonterminal
   occurrences to named contexts remains pending.

6. **The hybrid filling lemma in final grammar form.**  Distributional transport
   is checked, but the full MCFG hybrid replacement lemma for arbitrary binary
   derivation contexts is not yet formalized.

7. **Full grammar-level exact reconstruction theorem.**  The development does
   not yet combine output-type refinement, characteristic-sample coverage,
   extracted rules, unit transport, sample consistency, and hybrid filling into
   the final theorem that the learned concrete grammar has exactly the target
   language.

8. **Productivity, reachability, and reducedness closure.**  The syntax and
   derivation layers include basic working conditions, but not the full
   reducedness/productivity/reachability infrastructure used in a polished paper
   proof.

9. **No-advice non-identifiability.**  The superfinite-chain argument for the
   union over all finite observations is not yet formalized.

10. **Concrete polynomial-time and polynomial-data statements.**  The
    development contains enumeration-bound, polynomial-bound, parameter-profile,
    shape-profile, and bounded-data recovery interfaces.  These are certificate
    slots, not a proof of concrete polynomial complexity bounds.

11. **Compression lower bound and bounded spine width.**  The unary singleton
    compression example, bounded-spine-width definitions, and polynomial-data
    recovery theorem are not yet formalized.

---

## 7. Suggested wording for the paper

A safe current paragraph is:

```latex
A Lean companion formalizes substantial bookkeeping infrastructure for the
fixed-observation MCFG construction.  The current re-confirmed CI frontier
checks fixed monoid observations on words and tuples, named sentence contexts,
a working MCFG syntax and derivation skeleton, sample-safe unit closure,
transported learner distributions, distribution-level reconstruction
certificates, finite-hypothesis certificates, output-type refined rule and
grammar skeletons, finite refined-grammar certificates, finite
rule-enumeration plans derived from a finite observation monoid, actual finite
lists of refined terminal/binary/start rules generated from such plans, finite
support generated from observed sample atoms, raw and subword sample
decomposition witnesses, finite subword-cut enumeration, and unit-edge
enumeration from same-context/same-type subword pairs.  The current restart pass
has been re-confirmed through CI #485 / commit ff2b74c, whose top checked module
is FI_v2_1_SubwordUnitEdgeEnumerationGold.  The canonical-nonterminal and
sample-generated learner/rule skeleton layers are the next unconfirmed frontier
in this restart pass.  The formalization is not yet a machine-checked proof of
the full concrete reconstruction theorem: the concrete canonical learner
grammar, final sample-extracted grammar-rule construction,
presentation-relative characteristic-sample construction, hybrid filling lemma,
no-advice boundary, and bounded-spine polynomial-data theorem remain outside the
current Lean development.
```

A shorter footnote version is:

```latex
A Lean companion checks the fixed-observation and distributional bookkeeping
layers of the construction, including named contexts, MCFG syntax and derivation
skeletons, safe unit-rule closure, transported distributions, finite-hypothesis
wrappers, output-type refinement, finite refined-grammar certificates, actual
refined rule lists from finite monoid enumeration data, subword-based sample
support, and unit-edge extraction.  The current restart pass is re-confirmed
through FI_v2_1_SubwordUnitEdgeEnumerationGold (CI #485 / commit ff2b74c).  The
canonical-nonterminal and sample-generated grammar/rule skeleton layers are the
next unconfirmed frontier, and the full concrete canonical-grammar
reconstruction theorem is not yet machine-checked.
```

An even shorter introduction version is:

```latex
A Lean companion is available for the main bookkeeping infrastructure of the
construction.  In the current restart pass it is re-confirmed through finite
subword-context enumeration and same-context/same-type unit-edge extraction,
while the canonical-nonterminal / sample-generated skeleton layers and the full
concrete canonical-grammar reconstruction theorem remain future work.
```

These statements are intentionally conservative.  They emphasize what is
checked in the current restart pass without reusing the older `#429` frontier as
if it were still the current trusted checkpoint.

---

## 8. Suggested next formalization milestones

The immediate next milestones are now restart/reconfirmation milestones:

1. **Re-confirm canonical learner nonterminals.**  Restore `Basic.lean` to import
   `FI_v2_1_CanonicalLearnerNonterminalGold` and repair any breakage there.

2. **Re-confirm sample-generated learner grammar skeletons.**  Next restore
   `FI_v2_1_SampleGeneratedLearnerGrammarSkeletonGold`.

3. **Re-confirm sample-generated rule skeletons.**  Then restore
   `FI_v2_1_SampleGeneratedRuleSkeletonGold`, which was the older `#429`
   frontier but is not yet re-confirmed in the current restart pass.

After the older frontier is recovered, the most valuable new formalization
milestones are:

4. **Sample-generated `WorkingMCFG` construction.**  Assemble the current
   nonterminals and rule candidates into an actual grammar object, probably
   first with terminal/binary/start rules and unit transport kept as the existing
   `LearnerUnitReach` layer.

5. **Rule-candidate-to-rule-list conversion.**  Convert
   `SampleGeneratedStartCandidate`, `SampleGeneratedTerminalCandidate`, and
   `SampleGeneratedConcatCandidate` into concrete `StartRule`, `TerminalRule`,
   and `BinaryRule` lists.

6. **Sample consistency for the concrete learner grammar.**  Prove that every
   sample word has a start derivation in the generated grammar, at least through
   the currently enumerated subword decomposition path.

7. **Occurrence witnesses in derivation trees.**  Strengthen
   `ExposedWithContext` into a derivation-tree occurrence notion.

8. **Hybrid filling lemma.**  Prove that replacing a tuple by a
   distribution-equivalent tuple inside a derivation context preserves target
   membership.

9. **Presentation-relative characteristic sample construction.**  Build the
   finite characteristic sample from a witnessing presentation rather than
   assuming it as a certificate input.

10. **Exact reconstruction theorem.**  Combine output-type refinement,
    characteristic-sample coverage, extracted rules, unit transport, sample
    consistency, and hybrid filling into the grammar-level exact reconstruction
    theorem.

11. **No-advice boundary and bounded-spine results.**  Formalize the no-advice
    superfinite-chain boundary and replace the current complexity-profile
    interfaces with actual bounded-spine estimates.

For the paper's credibility, the highest-value immediate step is to finish the
reconfirmation up to the previous `SampleGeneratedRuleSkeletonGold` frontier.
After that, the highest-value new step is the concrete sample-to-grammar path:
convert the rule skeleton into actual `WorkingMCFG` rule lists, prove sample
generation, and then attack occurrence/hybrid filling.

---

## 9. Current status summary

```text
Checked by CI: yes
Latest reconfirmed CI: Lean CI #485
Latest commit reported by user: ff2b74c
Repository: growupkuriyama-hub/lean_cfg_project
Top reconfirmed module: LeanCfgProject.MCFG.FI_v2_1_SubwordUnitEdgeEnumerationGold
Aggregate import: LeanCfgProject.MCFG.Basic

Important status correction:
  The previous version of this note recorded CI #429 / commit 0cf10b2 /
  FI_v2_1_SampleGeneratedRuleSkeletonGold as the top checked frontier.
  The current work is a restart/reconfirmation pass after narrowing Basic.lean
  and rebuilding the import chain step by step.  Therefore CI #429 is now
  historical context, not the current trusted frontier.

Currently re-confirmed scope:
  fixed observations;
  named contexts;
  MCFG syntax and first derivation semantics;
  sample-safe distribution transport;
  unit-rule closure;
  reconstruction certificates;
  Gold-style stabilization;
  finite learner support and finite hypotheses;
  output-type refinement;
  refined rules and refined grammar skeletons;
  finite refined grammar certificates;
  output-type enumeration;
  Fintype-derived finite output-type enumeration;
  finite base-rule support;
  finite-monoid rule-enumeration plans;
  actual refined terminal/binary/start rule lists;
  concrete refined-rule enumeration certificates;
  relative and concrete sample-extraction certificates;
  sample-context consistency;
  sample-word consistency;
  target-side start-symbol derivation witnesses;
  learner-side sample-word generation interfaces;
  packaged learner word semantics;
  canonical learner grammar package interfaces;
  rule-list specifications and counting summaries;
  enumeration-bound and polynomial-bound interfaces;
  parameter and shape profiles;
  bounded-data recovery and presentation-relative recovery profiles;
  main-theorem style interface;
  post-threshold exact recovery interface;
  Gold-style main theorem summary;
  sample-only finite support;
  finite support from observed tuple/context/unit-edge atoms;
  raw sample decomposition witnesses;
  generated support from raw decompositions;
  identity decomposition enumeration for sample words;
  two-sided subword context decompositions;
  finite subword-cut enumeration;
  unit-edge enumeration from same-context/same-type subword pairs.

Not yet re-confirmed in the current restart pass:
  canonical learner nonterminals;
  sample-generated learner grammar skeletons;
  sample-generated start/terminal/binary/unit rule skeletons.

Full concrete canonical learner grammar checked: no
Final sample-extracted grammar-rule construction checked: no
Full grammar-level reconstruction theorem checked: no
Presentation-relative characteristic-sample construction checked: no
Hybrid filling lemma checked: no
No-advice theorem checked: no
Bounded-spine theorem checked: no
```

In one sentence:

> The current Lean restart pass machine-checks the fixed-observation,
> distributional, finite-hypothesis, output-type-refinement, finite-enumeration,
> actual-refined-rule-list, sample-extraction, raw/subword-decomposition,
> subword-context-enumeration, and subword unit-edge-enumeration infrastructure
> of the MCFG learning construction through CI #485 / commit `ff2b74c`; the
> canonical-nonterminal and sample-generated grammar/rule skeleton layers are
> the next unconfirmed frontier, and the full concrete presentation-relative
> canonical-grammar reconstruction theorem remains future formalization.
