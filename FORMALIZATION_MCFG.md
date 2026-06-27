# Lean formalization companion for the fixed-observation MCFG paper

This note documents the current Lean companion for the paper

> **Fixed-Monoid Tuple Substitution for Positive-Data Learning of Multiple Context-Free Grammars**

The Lean development is a companion formalization of the paper's core
bookkeeping infrastructure around fixed finite observations, named sentence
contexts, MCFG derivations, sample-safe unit closure, transported distributions,
finite-hypothesis certificates, output-type refinement, finite enumeration
plans, concrete sample-extraction certificates, sample consistency witnesses,
learner-side word semantics, and a canonical learner grammar package interface.

This document is intended to be self-contained: a reader should be able to
understand the current scope of the Lean experiment, its CI status, the layers
that have been checked, and the remaining formalization gap from this file
alone.

---

## 0. Current CI status

```text
Repository: growupkuriyama-hub/lean_cfg_project
Latest checked CI: Lean CI #408
Latest commit reported by user: 8f598b9
Status: succeeded
Top checked module: LeanCfgProject.MCFG.FI_v2_1_CanonicalLearnerGrammarGold
Aggregate import: LeanCfgProject.MCFG.Basic
```

The current CI chain checks all MCFG companion files through Lake.  The top
currently checked layer is no longer merely the finite-monoid rule-enumeration
plan: it now reaches a **canonical learner grammar package interface** with
exactness and Gold-style wrappers.

A typical local check is:

```bash
lake build LeanCfgProject.MCFG.FI_v2_1_CanonicalLearnerGrammarGold
lake build LeanCfgProject.MCFG.Basic
lake build LeanCfgProject
```

Warnings about unused section variables or unused simp arguments may remain in
some files.  They are linter warnings, not failed proof obligations.

---

## 1. Scope statement

The current development **does formalize** substantial parts of the paper's
bookkeeping infrastructure:

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
- relative and concrete sample-extraction certificates;
- sample-context consistency and sample-word consistency wrappers;
- target-side start-symbol derivation witnesses for sample words;
- learner-side sample-word generation interfaces;
- packaged learner word-semantics certificates;
- canonical learner grammar package interfaces;
- exactness and Gold-style wrappers for these package interfaces.

The current development **does not yet formalize** the full paper theorem.
In particular, it does not yet construct the actual canonical MCFG learner as a
concrete `WorkingMCFG`, does not yet implement the full sample-extracted
terminal/binary/start/unit rule generation algorithm, does not yet construct the
presentation-relative characteristic sample from an arbitrary witnessing
presentation, and does not yet prove the hybrid filling lemma, no-advice
non-identifiability theorem, or bounded-spine polynomial-data theorem.

A safe one-sentence summary is:

> The Lean companion currently machine-checks the fixed-observation,
> distributional, finite-hypothesis, output-type-refinement, finite-enumeration,
> sample-extraction, consistency, learner-word-semantics, and canonical learner
> package infrastructure for the MCFG learning construction, while the full
> concrete canonical-grammar reconstruction theorem remains future work.

---

## 2. Repository layout

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

.github/workflows/lean.yml
```

The intended root import chain is:

```lean
-- LeanCfgProject.lean
import LeanCfgProject.MCFG.Basic
```

The aggregate file imports all current MCFG companion layers:

```lean
-- LeanCfgProject/MCFG/Basic.lean
import LeanCfgProject.MCFG.FI_v2_1_FixedObservation
import LeanCfgProject.MCFG.FI_v2_1_NamedSentenceContext
import LeanCfgProject.MCFG.FI_v2_1_MCFG_Syntax
import LeanCfgProject.MCFG.FI_v2_1_MCFG_Derivation
import LeanCfgProject.MCFG.FI_v2_1_MCFG_ContextualSemantics
import LeanCfgProject.MCFG.FI_v2_1_LearnerUnitClosure
import LeanCfgProject.MCFG.FI_v2_1_LearnerDistribution
import LeanCfgProject.MCFG.FI_v2_1_ReconstructionCertificate
import LeanCfgProject.MCFG.FI_v2_1_GoldStabilization
import LeanCfgProject.MCFG.FI_v2_1_IdentificationSummary
import LeanCfgProject.MCFG.FI_v2_1_FiniteSupport
import LeanCfgProject.MCFG.FI_v2_1_FiniteHypothesis
import LeanCfgProject.MCFG.FI_v2_1_FiniteHypothesisGold
import LeanCfgProject.MCFG.FI_v2_1_OutputTypeRefinement
import LeanCfgProject.MCFG.FI_v2_1_RefinedRules
import LeanCfgProject.MCFG.FI_v2_1_OutputTypedDerivationSummary
import LeanCfgProject.MCFG.FI_v2_1_RefinedGrammar
import LeanCfgProject.MCFG.FI_v2_1_FiniteRefinedGrammar
import LeanCfgProject.MCFG.FI_v2_1_FiniteOutputTypeEnumeration
import LeanCfgProject.MCFG.FI_v2_1_FiniteEnumerationSummary
import LeanCfgProject.MCFG.FI_v2_1_FintypeOutputEnumeration
import LeanCfgProject.MCFG.FI_v2_1_FintypeEnumerationCertificate
import LeanCfgProject.MCFG.FI_v2_1_FiniteBaseRuleSupport
import LeanCfgProject.MCFG.FI_v2_1_FiniteRuleEnumerationPlan
import LeanCfgProject.MCFG.FI_v2_1_FintypeRuleEnumerationPlan
import LeanCfgProject.MCFG.FI_v2_1_ConcreteRuleEnumerationSkeleton
import LeanCfgProject.MCFG.FI_v2_1_ConcreteRuleEnumerationCertificate
import LeanCfgProject.MCFG.FI_v2_1_FintypeConcreteRuleEnumeration
import LeanCfgProject.MCFG.FI_v2_1_RelativeSampleExtraction
import LeanCfgProject.MCFG.FI_v2_1_RelativeSampleExtractionExact
import LeanCfgProject.MCFG.FI_v2_1_RelativeSampleExtractionGold
import LeanCfgProject.MCFG.FI_v2_1_ConcreteExtractedSampleData
import LeanCfgProject.MCFG.FI_v2_1_ConcreteExtractedSampleExact
import LeanCfgProject.MCFG.FI_v2_1_ConcreteExtractedSampleGold
import LeanCfgProject.MCFG.FI_v2_1_ConcreteSampleConsistency
import LeanCfgProject.MCFG.FI_v2_1_ConcreteSampleConsistencyExact
import LeanCfgProject.MCFG.FI_v2_1_ConcreteSampleConsistencyGold
import LeanCfgProject.MCFG.FI_v2_1_SampleWordConsistencySkeleton
import LeanCfgProject.MCFG.FI_v2_1_SampleWordConsistencyExact
import LeanCfgProject.MCFG.FI_v2_1_SampleWordConsistencyGold
import LeanCfgProject.MCFG.FI_v2_1_StartRuleSampleWitness
import LeanCfgProject.MCFG.FI_v2_1_StartRuleSampleWitnessExact
import LeanCfgProject.MCFG.FI_v2_1_StartRuleSampleWitnessGold
import LeanCfgProject.MCFG.FI_v2_1_LearnerWordConsistencySkeleton
import LeanCfgProject.MCFG.FI_v2_1_LearnerWordConsistencyExact
import LeanCfgProject.MCFG.FI_v2_1_LearnerWordConsistencyGold
import LeanCfgProject.MCFG.FI_v2_1_LearnerWordSemanticsInterface
import LeanCfgProject.MCFG.FI_v2_1_LearnerWordSemanticsExact
import LeanCfgProject.MCFG.FI_v2_1_LearnerWordSemanticsGold
import LeanCfgProject.MCFG.FI_v2_1_CanonicalLearnerGrammarInterface
import LeanCfgProject.MCFG.FI_v2_1_CanonicalLearnerGrammarExact
import LeanCfgProject.MCFG.FI_v2_1_CanonicalLearnerGrammarGold
```

---

## 3. Layer-by-layer status

| Layer | File | Main role | Status |
|---:|---|---|---|
| 1 | `FI_v2_1_FixedObservation.lean` | Words, tuples, observation evaluation, tuple types, fixed-`h` substitutability, refinement monotonicity | checked |
| 2 | `FI_v2_1_NamedSentenceContext.lean` | Raw and well-formed named sentence contexts, named filling | checked |
| 3 | `FI_v2_1_MCFG_Syntax.lean` | Working binary MCFG syntax: templates, rules, fan-out, nondeleting side conditions | checked |
| 4 | `FI_v2_1_MCFG_Derivation.lean` | First derivation semantics: tuple and string languages | checked |
| 5 | `FI_v2_1_MCFG_ContextualSemantics.lean` | Exposed tuples, grammar/sample named distributions, sample-safe merge soundness | checked |
| 6 | `FI_v2_1_LearnerUnitClosure.lean` | Learner unit edges, unit reachability, soundness of unit-rule closure | checked |
| 7 | `FI_v2_1_LearnerDistribution.lean` | Transported contexts and learner approximate distributions | checked |
| 8 | `FI_v2_1_ReconstructionCertificate.lean` | Distribution-level reconstruction certificates and characteristic-sample skeleton | checked |
| 9 | `FI_v2_1_GoldStabilization.lean` | Texts, prefix samples, eventual containment, Gold-style stabilization | checked |
| 10 | `FI_v2_1_IdentificationSummary.lean` | Class-level identification wrappers from characteristic samples | checked |
| 11 | `FI_v2_1_FiniteSupport.lean` | Finite sample support for tuples, contexts, and listed unit edges | checked |
| 12 | `FI_v2_1_FiniteHypothesis.lean` | Finite learner hypothesis object, soundness, completeness-to-exactness certificate | checked |
| 13 | `FI_v2_1_FiniteHypothesisGold.lean` | Finite-hypothesis Gold wrapper and telltale-style class summaries | checked |
| 14 | `FI_v2_1_OutputTypeRefinement.lean` | Output-type computation for templates and rule applications | checked |
| 15 | `FI_v2_1_RefinedRules.lean` | Refined terminal, binary, and start rule skeletons | checked |
| 16 | `FI_v2_1_OutputTypedDerivationSummary.lean` | Output-typed tuple language and tuple-level conservativity summaries | checked |
| 17 | `FI_v2_1_RefinedGrammar.lean` | Predicate-style output-type refined grammar skeleton and refined derivations | checked |
| 18 | `FI_v2_1_FiniteRefinedGrammar.lean` | Finite refined grammar certificate using explicit finite rule lists | checked |
| 19 | `FI_v2_1_FiniteOutputTypeEnumeration.lean` | Certificate interface for finite enumeration of output-type vectors | checked |
| 20 | `FI_v2_1_FiniteEnumerationSummary.lean` | Bundles finite refined grammar certificates with output-type enumeration support | checked |
| 21 | `FI_v2_1_FintypeOutputEnumeration.lean` | Builds output-type enumeration from `[Fintype M]` via `Fintype.elems` | checked |
| 22 | `FI_v2_1_FintypeEnumerationCertificate.lean` | Finite-monoid output-type refinement certificates | checked |
| 23 | `FI_v2_1_FiniteBaseRuleSupport.lean` | Explicit finite support for ordinary terminal, binary, and start rules | checked |
| 24 | `FI_v2_1_FiniteRuleEnumerationPlan.lean` | Finite rule-enumeration plans from base rules plus output-type lists | checked |
| 25 | `FI_v2_1_FintypeRuleEnumerationPlan.lean` | Canonical rule-enumeration plans when the observation monoid is finite | checked |
| 26 | `FI_v2_1_ConcreteRuleEnumerationSkeleton.lean` | Support predicates for concrete refined terminal/binary/start rules under a finite plan | checked |
| 27 | `FI_v2_1_ConcreteRuleEnumerationCertificate.lean` | Certificate interface for concrete refined rule enumerations | checked |
| 28 | `FI_v2_1_FintypeConcreteRuleEnumeration.lean` | Connects concrete refined rule enumerations to finite-monoid rule-enumeration plans | checked |
| 29 | `FI_v2_1_RelativeSampleExtraction.lean` | Relative sample-extraction certificates linking finite hypotheses and concrete refined enumerations | checked |
| 30 | `FI_v2_1_RelativeSampleExtractionExact.lean` | Exactness interface for relative sample extraction | checked |
| 31 | `FI_v2_1_RelativeSampleExtractionGold.lean` | Gold wrapper for relative sample extraction | checked |
| 32 | `FI_v2_1_ConcreteExtractedSampleData.lean` | Implementation-facing concrete extracted sample data certificates | checked |
| 33 | `FI_v2_1_ConcreteExtractedSampleExact.lean` | Exactness certificate for concrete extracted sample data | checked |
| 34 | `FI_v2_1_ConcreteExtractedSampleGold.lean` | Gold wrapper for concrete extracted sample data | checked |
| 35 | `FI_v2_1_ConcreteSampleConsistency.lean` | Sample-context consistency for concrete extracted samples | checked |
| 36 | `FI_v2_1_ConcreteSampleConsistencyExact.lean` | Exactness plus sample-context consistency | checked |
| 37 | `FI_v2_1_ConcreteSampleConsistencyGold.lean` | Gold wrapper for sample-context consistent extraction | checked |
| 38 | `FI_v2_1_SampleWordConsistencySkeleton.lean` | Target-side sample-word consistency skeleton | checked |
| 39 | `FI_v2_1_SampleWordConsistencyExact.lean` | Exactness plus sample-word consistency | checked |
| 40 | `FI_v2_1_SampleWordConsistencyGold.lean` | Gold wrapper for word-consistent extraction | checked |
| 41 | `FI_v2_1_StartRuleSampleWitness.lean` | Start-symbol derivation witnesses for sample words | checked |
| 42 | `FI_v2_1_StartRuleSampleWitnessExact.lean` | Exactness plus target-side start derivation witnesses | checked |
| 43 | `FI_v2_1_StartRuleSampleWitnessGold.lean` | Gold wrapper for start-witness consistent extraction | checked |
| 44 | `FI_v2_1_LearnerWordConsistencySkeleton.lean` | Learner-side sample-word generation interface | checked |
| 45 | `FI_v2_1_LearnerWordConsistencyExact.lean` | Exactness plus learner-side sample-word generation | checked |
| 46 | `FI_v2_1_LearnerWordConsistencyGold.lean` | Gold wrapper for learner-side sample-word consistency | checked |
| 47 | `FI_v2_1_LearnerWordSemanticsInterface.lean` | Packaged learner word-semantics certificates | checked |
| 48 | `FI_v2_1_LearnerWordSemanticsExact.lean` | Exactness plus packaged learner word semantics | checked |
| 49 | `FI_v2_1_LearnerWordSemanticsGold.lean` | Gold wrapper for packaged learner word semantics | checked |
| 50 | `FI_v2_1_CanonicalLearnerGrammarInterface.lean` | Canonical learner grammar package interface | checked |
| 51 | `FI_v2_1_CanonicalLearnerGrammarExact.lean` | Exactness certificate for canonical learner grammar packages | checked |
| 52 | `FI_v2_1_CanonicalLearnerGrammarGold.lean` | Gold wrapper for canonical learner grammar packages | checked |

The development has grown from a distribution-level skeleton into a broad
formal infrastructure for output-type refined MCFG learning.  It still avoids
claiming a complete machine-checked proof of the final learner grammar theorem.

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
characteristic-sample argument: once a finite witness sample is contained in a
text prefix, the certified approximate distribution stabilizes to the target
distribution.

### 4.3 Finite hypotheses and finite-hypothesis Gold wrappers
Main checked layers: `IdentificationSummary`, `FiniteSupport`,
`FiniteHypothesis`, `FiniteHypothesisGold`.

Representative declarations:

```lean
FiniteLearnerSupport
FiniteLearnerHypothesis
FiniteLearnerHypothesis.ApproxDistribution
FiniteLearnerHypothesis.CompleteForLanguage
FiniteLearnerHypothesis.ExactForLanguage

FiniteHypothesisLearner
FiniteHypothesisCharacteristicSample
FiniteHypothesisIdentifiesInLimit
GrammarFiniteHypothesisCharacteristicSample
```

These layers connect the distributional reconstruction story to finite learner
objects.  They formalize that finite samples can carry finite support data for
nodes, contexts, and safe unit edges, and that a finite-hypothesis learner
identifies in the Gold sense once a finite characteristic sample guarantees
exactness.

### 4.4 Output-type refinement infrastructure
Main checked layers: `OutputTypeRefinement`, `RefinedRules`,
`OutputTypedDerivationSummary`, `RefinedGrammar`.

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
derives_actualRefinedNonterminal
OutputTypeRefinementConservative

OutputTypeRefinedGrammar
RefinedDerivesTuple
OutputTypeRefinedGrammar.TupleLanguage
```

This is the formal substrate for nonterminals refined by componentwise
observation type.  The checked statements show that terminal, binary, and start
rule steps can be given output types, that ordinary tuple derivations are
covered by the actual refined nonterminal determined by their observation type,
and that refined derivations forget to ordinary derivations while preserving the
advertised output type.

### 4.5 Finite refined grammars and finite output-type enumeration
Main checked layers: `FiniteRefinedGrammar`, `FiniteOutputTypeEnumeration`,
`FiniteEnumerationSummary`, `FintypeOutputEnumeration`,
`FintypeEnumerationCertificate`.

Representative declarations:

```lean
FiniteOutputTypeRefinedGrammar
FiniteOutputTypeRefinedGrammar.toOutputTypeRefinedGrammar
FiniteOutputTypeRefinedGrammar.CoversAllOrdinaryRuleRefinements
FiniteOutputTypeRefinementCertificate

OutputTypeEnumeration
OutputTypeEnumeration.complete
GrammarOutputTypeEnumeration

fintypeOutputTypeList
OutputTypeEnumeration.ofFintype
FintypeOutputTypeRefinementCertificate
```

This block replaces predicate-style refined grammars with explicit finite rule
lists and isolates the finite enumeration of output-type vectors.  The important
finite-monoid point is checked: if `M` is represented by `[Fintype M]`, then
each output-type vector type `Fin d → M` can be enumerated using
`Fintype.elems`, giving a Lean certificate for finite output-type support.

### 4.6 Finite rule-enumeration plans and concrete refined-rule certificates
Main checked layers: `FiniteBaseRuleSupport`, `FiniteRuleEnumerationPlan`,
`FintypeRuleEnumerationPlan`, `ConcreteRuleEnumerationSkeleton`,
`ConcreteRuleEnumerationCertificate`, `FintypeConcreteRuleEnumeration`.

Representative declarations:

```lean
FiniteBaseRuleSupport
FiniteRuleEnumerationPlan
FiniteRuleEnumerationPlan.ofFintype

FiniteRuleEnumerationPlan.SupportsRefinedTerminalRule
FiniteRuleEnumerationPlan.SupportsRefinedBinaryRule
FiniteRuleEnumerationPlan.SupportsRefinedStartRule

ConcreteRefinedRuleEnumeration
FintypeConcreteRuleEnumeration
```

The finite base-rule lists of `WorkingMCFG` are bundled as support data, then
combined with finite output-type lists into a rule-enumeration plan.  The later
concrete-rule layers specify the certificate interface that actual refined
rule-list generation must satisfy.  This still does not implement the full
`List.bind` / cartesian-product generation of all refined rules; instead it
formalizes the support and packaging needed by that future implementation.

### 4.7 Relative and concrete sample extraction
Main checked layers: `RelativeSampleExtraction`, `RelativeSampleExtractionExact`,
`RelativeSampleExtractionGold`, `ConcreteExtractedSampleData`,
`ConcreteExtractedSampleExact`, `ConcreteExtractedSampleGold`.

Representative declarations:

```lean
RelativeSampleExtraction
RelativeSampleExtractionExactForLanguage
RelativeSampleExtractionCharacteristicSample

ConcreteExtractedSampleData
ConcreteExtractedSampleExactForLanguage
ConcreteExtractedSampleCharacteristicSample
```

These layers connect finite learner hypotheses, concrete finite-monoid refined
rule enumerations, sample equality, and safe unit edges into sample-extraction
certificates.  They also provide exactness and Gold wrappers, so the route

```text
finite sample
→ relative/concrete extraction certificate
→ finite learner hypothesis
→ concrete refined rule enumeration
→ exactness after characteristic sample
→ Gold identification
```

is available in Lean as a certificate pipeline.

### 4.8 Sample-context, sample-word, and start-witness consistency
Main checked layers: `ConcreteSampleConsistency`,
`ConcreteSampleConsistencyExact`, `ConcreteSampleConsistencyGold`,
`SampleWordConsistencySkeleton`, `SampleWordConsistencyExact`,
`SampleWordConsistencyGold`, `StartRuleSampleWitness`,
`StartRuleSampleWitnessExact`, `StartRuleSampleWitnessGold`.

Representative declarations:

```lean
ConcreteExtractedSampleContextConsistency
ConcreteExtractedSampleExactAndConsistentForLanguage
ConcreteSampleConsistentCharacteristicSample

SampleWordLanguageConsistency
ConcreteExtractedSampleWordConsistencyForLanguage
ConcreteExtractedSampleExactContextWordForGrammar

SampleStartDerivationWitnesses
ConcreteExtractedSampleStartWitnessForGrammar
ConcreteExtractedSampleExactContextWordStartForGrammar
```

These layers make the sample-side obligations explicit.  At the distribution
level, observed sample contexts are required to be licensed by the extracted
approximation.  At the word level, sample words are related to the target
language.  For grammar targets, sample words are further equipped with
start-symbol derivation witnesses.  This is still target-side consistency, not
yet a proof that a fully constructed learner grammar generates every sample
word.

### 4.9 Learner-side word consistency and packaged learner semantics
Main checked layers: `LearnerWordConsistencySkeleton`,
`LearnerWordConsistencyExact`, `LearnerWordConsistencyGold`,
`LearnerWordSemanticsInterface`, `LearnerWordSemanticsExact`,
`LearnerWordSemanticsGold`.

Representative declarations:

```lean
FiniteHypothesisSampleWordConsistent
ConcreteExtractedSampleLearnerWordConsistent
ConcreteExtractedSampleExactStartLearnerWordForGrammar

ConcreteExtractedSampleWordSemanticsCertificate
ConcreteExtractedSampleLearnerWordSemanticsCertificate
ConcreteExtractedSampleExactWithWordSemanticsForGrammar
GrammarConcreteLearnerWordSemanticsCharacteristicSample
```

These layers introduce an abstract learner-side word language interface.  Since
the full canonical grammar's `StringLanguage` is not yet defined, the word
semantics are packaged as certificates associated with extracted sample data.
The checked statements connect exact reconstruction, target-side start
witnesses, learner-side sample-word generation, and Gold-style distributional
identification.

### 4.10 Canonical learner grammar package interface
Main checked layers: `CanonicalLearnerGrammarInterface`,
`CanonicalLearnerGrammarExact`, `CanonicalLearnerGrammarGold`.

Representative declarations:

```lean
CanonicalLearnerGrammarPackage
CanonicalLearnerGrammarPackage.toConcreteExtractedSampleData
CanonicalLearnerGrammarPackage.toFiniteLearnerHypothesis
CanonicalLearnerGrammarPackage.wordLanguage
CanonicalLearnerGrammarPackage.sample_word_generated
CanonicalLearnerGrammarPackage.ApproxDistribution
CanonicalLearnerGrammarPackage.RefinedTupleLanguage

CanonicalLearnerGrammarExactForGrammar
CanonicalLearnerGrammarCharacteristicSample
CanonicalLearnerGrammarLearner
```

This is the current top block of the Lean experiment.  It packages concrete
extracted sample data together with learner-side word semantics as a
sample-indexed canonical learner grammar package.  The exactness layer says that
such a package is exact for a target grammar when its distributions match the
target, sample words have target start-derivation witnesses, and sample words
are generated by the packaged learner-side word semantics.  The Gold layer then
lifts characteristic-sample witnesses to the canonical learner grammar package
level.

This is still an interface layer.  It does not yet define the actual canonical
learner grammar as a concrete `WorkingMCFG` with extracted terminal, binary,
start, and unit rules.


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
| exposed tuple with context | `ExposedWithContext` | formalized abstractly |
| sample-safe merge | `SampleSafeMerge` | formalized |
| unit-rule closure | `LearnerUnitReach` | formalized |
| learner transported distribution | `LearnerApproxDistribution` | formalized |
| reconstruction certificate | `DistributionReconstructionCertificate` | formalized abstractly |
| characteristic sample skeleton | `DistributionCharacteristicSample` | formalized abstractly |
| text and prefix sample | `Text`, `PrefixSample` | formalized |
| eventual containment of finite sample | `text_eventually_contains_finite_sample` | proved |
| distribution-level identification in the limit | `DistributionIdentifiesInLimit` | formalized |
| finite learner support | `FiniteLearnerSupport` | formalized |
| finite learner hypothesis | `FiniteLearnerHypothesis` | formalized |
| finite-hypothesis Gold wrapper | `FiniteHypothesisCharacteristicSample` and related declarations | formalized |
| output-type computation for templates | `templateWordType`, `templateTupleType` | formalized |
| output type of terminal rules | `TerminalRule.outputType` | formalized |
| output type of binary rules | `BinaryRule.outputType` | formalized |
| refined nonterminal | `RefinedNonterminal` | formalized |
| refined terminal/binary/start rules | `RefinedTerminalRule`, `RefinedBinaryRule`, `RefinedStartRule` | formalized |
| refined grammar skeleton | `OutputTypeRefinedGrammar` | formalized |
| refined derivation | `RefinedDerivesTuple` | formalized |
| finite refined grammar certificate | `FiniteOutputTypeRefinedGrammar` | formalized |
| finite output-type enumeration | `OutputTypeEnumeration` | formalized |
| output-type enumeration from finite monoid | `OutputTypeEnumeration.ofFintype` | formalized |
| finite base rule support | `FiniteBaseRuleSupport` | formalized |
| finite rule-enumeration plan | `FiniteRuleEnumerationPlan` | formalized |
| finite-monoid rule-enumeration plan | `FiniteRuleEnumerationPlan.ofFintype` | formalized |
| concrete refined rule enumeration interface | `ConcreteRefinedRuleEnumeration` | formalized as certificate interface |
| relative sample extraction | `RelativeSampleExtraction` | formalized as certificate interface |
| concrete extracted sample data | `ConcreteExtractedSampleData` | formalized as certificate interface |
| sample-context consistency | `ConcreteExtractedSampleContextConsistency` | formalized |
| sample-word consistency | `SampleWordLanguageConsistency` and related packages | formalized |
| target-side start witnesses for sample words | `SampleStartDerivationWitnesses` | formalized |
| learner-side sample-word generation | `FiniteHypothesisSampleWordConsistent` | formalized as interface |
| packaged learner word semantics | `ConcreteExtractedSampleWordSemanticsCertificate` | formalized as interface |
| canonical learner grammar package | `CanonicalLearnerGrammarPackage` | formalized as interface |
| canonical learner grammar exactness package | `CanonicalLearnerGrammarExactForGrammar` | formalized as interface |
| canonical learner grammar Gold wrapper | `CanonicalLearnerGrammarCharacteristicSample` | formalized |
| actual concrete refined rule lists via `List.bind` | not yet formalized | pending |
| actual sample-extracted rule generation algorithm | not yet formalized | pending |
| full concrete canonical learner grammar as `WorkingMCFG` | not yet formalized | pending |
| full exact reconstruction theorem | not yet formalized | pending |
| no-advice non-identifiability | not yet formalized | pending |
| bounded-spine polynomial-data theorem | not yet formalized | pending |

---

## 6. What is not formalized yet

The current Lean development should not be described as a complete
machine-checked proof of the paper.  The following major parts remain outside
the current formalization.

1. **Actual concrete refined rule-list construction.**  
   The development has finite rule-enumeration plans and concrete refined-rule
   certificate interfaces, but it does not yet implement the actual
   `List.bind`/cartesian-product construction of all refined terminal, binary,
   and start rules.

2. **Actual sample-extracted rule generation.**  
   Relative and concrete extraction certificates are formalized, but the
   algorithm that constructs terminal, binary, start, and unit rule lists from a
   finite positive sample is not yet implemented.

3. **Concrete canonical learner grammar as a `WorkingMCFG`.**  
   The current top layer defines a canonical learner grammar package interface.
   It is a disciplined place to plug in a future grammar construction, but it is
   not itself the full concrete learner grammar.

4. **Construction of the presentation-relative characteristic sample.**  
   The certificate layers assume distribution-level, finite-hypothesis, or
   package-level characteristic-sample witnesses.  They do not yet prove that
   the paper's finite characteristic sample can be extracted from every
   witnessing working MCFG presentation.

5. **Occurrence witnesses in derivation trees.**  
   `ExposedWithContext` is currently abstract.  A full derivation-tree
   occurrence notion connecting nonterminal occurrences to named contexts
   remains pending.

6. **The hybrid filling lemma in final grammar form.**  
   Distributional transport is checked, but the full MCFG hybrid replacement
   lemma for arbitrary binary derivation contexts is not yet formalized.

7. **Sample consistency for the fully constructed learner grammar.**  
   The development packages learner-side sample-word generation as an interface,
   but it does not yet prove it from a concrete learner grammar construction.

8. **Full grammar-level exact reconstruction theorem.**  
   The development does not yet combine output-type refinement, characteristic
   sample coverage, extracted rules, unit transport, and hybrid filling into the
   final theorem that the learned grammar has exactly the target language.

9. **Productivity, reachability, and reducedness closure.**  
   The syntax and derivation layers include basic working conditions, but not
   the full reducedness/productivity/reachability infrastructure used in a
   polished paper proof.

10. **No-advice non-identifiability.**  
    The superfinite-chain argument for the union over all finite observations is
    not yet formalized.

11. **Polynomial-time and polynomial-data statements.**  
    Complexity bounds, enumeration size bounds, characteristic-sample size
    bounds, and fixed-parameter polynomiality are not yet formalized.

12. **Compression lower bound and bounded spine width.**  
    The unary singleton compression example, bounded-spine-width definitions,
    and polynomial-data recovery theorem are not yet formalized.

13. **Comparison examples.**  
    The Yoshinaka comparison, ordered-context examples, parallel-agreement
    examples, cross-serial examples, finite-kernel comparison, conservativity
    proposition, and slope counterexample are not yet formalized.

---

## 7. Suggested wording for the paper

A safe current paragraph is:

```latex
A Lean companion formalizes substantial bookkeeping infrastructure for the
fixed-observation MCFG construction.  The checked development includes fixed
monoid observations on words and tuples, named sentence contexts, a working MCFG
syntax and derivation skeleton, sample-safe unit closure, transported learner
distributions, distribution-level reconstruction certificates, Gold-style
stabilization wrappers, finite-hypothesis certificates, output-type refined
rule and grammar skeletons, finite refined-grammar certificates, finite
rule-enumeration plans derived from a finite observation monoid, concrete
sample-extraction certificate interfaces, sample-context and sample-word
consistency wrappers, learner-side word-semantics certificates, and a canonical
learner grammar package interface with exactness and Gold-style wrappers.  The
formalization is not yet a machine-checked proof of the full reconstruction
theorem: the concrete canonical learner grammar, the actual sample-extracted
rule-generation algorithm, the presentation-relative characteristic-sample
construction, the hybrid filling lemma, the no-advice boundary, and the
bounded-spine polynomial-data theorem remain outside the current Lean
development.
```

A shorter footnote version is:

```latex
A Lean companion checks the fixed-observation and distributional bookkeeping
layers of the construction, including named contexts, MCFG syntax and derivation
skeletons, safe unit-rule closure, transported distributions, finite-hypothesis
wrappers, output-type refinement, finite refined-grammar certificates, finite
rule-enumeration plans for finite observation monoids, concrete extraction and
consistency certificate interfaces, learner-side word semantics, and a
canonical learner grammar package interface.  The full concrete
canonical-grammar reconstruction theorem is not yet machine-checked.
```

An even shorter introduction version is:

```latex
A Lean companion is available for the main bookkeeping infrastructure of the
construction.  It currently reaches a canonical learner grammar package
interface with exactness and Gold-style wrappers, while the full concrete
canonical-grammar reconstruction theorem remains future work.
```

These statements are intentionally conservative.  They emphasize what is
checked without implying that the entire paper has been formalized.

---

## 8. Suggested next formalization milestones

The most valuable next milestones are now:

1. **Canonical rule-list specification.**  
   Specify exactly what terminal, binary, start, and unit rule lists inside a
   canonical learner grammar package must contain.

2. **Actual concrete refined rule lists.**  
   Implement refined terminal, binary, and start rule lists using `List.bind` or
   suitable finite-list combinators from the finite rule-enumeration plan.

3. **Finite refined grammar generated from the plan.**  
   Construct an actual `FiniteOutputTypeRefinedGrammar` from the concrete
   refined rule lists and prove that it covers all ordinary rule refinements.

4. **Sample-extracted rule lists.**  
   Formalize terminal, binary, start, and unit rule extraction from a finite
   positive sample.

5. **Concrete canonical learner grammar.**  
   Define the full learner grammar as a concrete grammar object, not only a
   package interface.

6. **Occurrence witnesses in derivation trees.**  
   Strengthen `ExposedWithContext` into a derivation-tree occurrence notion.

7. **Sample consistency for the concrete learner grammar.**  
   Prove that every positive sample word is generated by the learner grammar.

8. **Hybrid filling lemma.**  
   Prove that replacing a tuple by a distribution-equivalent tuple inside a
   derivation context preserves target membership.

9. **Exact reconstruction theorem.**  
   Combine output-type refinement, characteristic-sample coverage, extracted
   rules, unit transport, sample consistency, and hybrid filling into the
   grammar-level exact reconstruction theorem.

10. **No-advice boundary.**  
    Formalize the superfinite chain
    `({a^n b^n | 1 ≤ n ≤ k})_k` converging to `{a^n b^n | n ≥ 1}`.

11. **Polynomial and bounded-spine results.**  
    Formalize enumeration bounds and then the bounded-spine polynomial-data
    theorem.

For the paper's credibility, the highest-value next step is still the concrete
grammar-building part: canonical rule-list specifications, concrete refined
rule lists, sample-extracted rules, occurrence witnesses, and the hybrid filling
lemma.

---

## 9. Current status summary

```text
Checked by CI: yes
Latest CI: Lean CI #408
Latest commit reported by user: 8f598b9
Repository: growupkuriyama-hub/lean_cfg_project
Top checked module: LeanCfgProject.MCFG.FI_v2_1_CanonicalLearnerGrammarGold
Aggregate import: LeanCfgProject.MCFG.Basic

Current scope:
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
  concrete refined-rule enumeration certificate interfaces;
  relative and concrete sample-extraction certificates;
  sample-context consistency;
  sample-word consistency;
  target-side start-symbol derivation witnesses;
  learner-side sample-word generation interfaces;
  packaged learner word semantics;
  canonical learner grammar package interface;
  exactness and Gold-style wrappers for canonical learner packages.

Full concrete canonical learner grammar checked: no
Actual sample-extracted rule-generation algorithm checked: no
Actual concrete refined rule-list construction checked: no
Full grammar-level reconstruction theorem checked: no
Presentation-relative characteristic-sample construction checked: no
Hybrid filling lemma checked: no
No-advice theorem checked: no
Bounded-spine theorem checked: no
```

In one sentence:

> The current Lean development machine-checks the fixed-observation,
> distributional, finite-hypothesis, output-type-refinement, finite-enumeration,
> sample-extraction, consistency, learner-word-semantics, and canonical learner
> package infrastructure of the MCFG learning construction through CI #408 /
> commit `8f598b9`, while leaving the full concrete presentation-relative
> canonical-grammar reconstruction theorem for future formalization.
