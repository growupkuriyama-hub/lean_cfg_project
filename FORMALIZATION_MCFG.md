# Lean formalization companion for the fixed-observation MCFG paper

This note documents the current Lean companion for the paper

> **Fixed-Monoid Tuple Substitution for Positive-Data Learning of Multiple Context-Free Grammars**

The Lean development is a companion formalization of the paper's core
bookkeeping infrastructure around fixed finite observations, named sentence
contexts, MCFG derivations, sample-safe unit closure, transported distributions,
finite-hypothesis certificates, output-type refinement, and finite enumeration
plans.

This document is intended to be self-contained: a reader should be able to
understand the current scope of the Lean experiment, its CI status, and the
remaining formalization gap from this file alone.

---

## 0. Current CI status

```text
Repository: growupkuriyama-hub/lean_cfg_project
Latest checked CI: Lean CI #398
Latest commit reported by user: 83aa08d
Status: succeeded
Top checked module: LeanCfgProject.MCFG.FI_v2_1_FintypeRuleEnumerationPlan
Aggregate import: LeanCfgProject.MCFG.Basic
```

The current CI chain checks all MCFG companion files through Lake.  The top
currently checked layer is no longer merely the Gold-stabilization skeleton; it
now reaches a finite-monoid rule-enumeration plan for output-type refined
grammar infrastructure.

A typical local check is:

```bash
lake build LeanCfgProject.MCFG.FI_v2_1_FintypeRuleEnumerationPlan
lake build LeanCfgProject.MCFG.Basic
lake build LeanCfgProject
```

Warnings about unused section variables or unused simp arguments may remain in
some files.  They are linter warnings, not failed proof obligations.

---

## 1. Scope statement

The current development **does formalize** substantial parts of the
paper's bookkeeping infrastructure:

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
- finite base-rule support and finite-monoid rule-enumeration plans.

The current development **does not yet formalize** the full paper theorem.
In particular, it does not yet prove the full presentation-relative canonical
MCFG learner, the full construction of a characteristic sample from an arbitrary
witnessing presentation, the hybrid filling lemma in its final derivation-tree
form, the no-advice non-identifiability theorem, or the bounded-spine
polynomial-data theorem.

A safe one-sentence summary is:

> The Lean companion currently machine-checks the fixed-observation,
> distributional, finite-hypothesis, output-type-refinement, and finite
> enumeration-plan infrastructure for the MCFG learning construction, while the
> full canonical-grammar reconstruction theorem remains future work.

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

The development has grown from a distribution-level skeleton into a broader
formal infrastructure for output-type refined MCFG bookkeeping.  It still avoids
claiming a complete learner grammar reconstruction theorem.

---

## 4. What is currently formalized

### 4.1 Words, tuples, and fixed observations

Words over an alphabet are represented by lists.

```lean
abbrev Word (α : Type u) := List α
```

A tuple of arity `d` is a `Fin d`-indexed family of words.

```lean
abbrev Tuple (α : Type u) (d : Nat) := Fin d → Word α
```

A letter observation is represented as:

```lean
obs : α → M
```

where `M` is a monoid.  It is extended multiplicatively to words.

```lean
def evalObs (obs : α → M) : Word α → M
```

The append law is checked:

```lean
theorem evalObs_append (obs : α → M) (u v : Word α) :
    evalObs obs (u ++ v) = evalObs obs u * evalObs obs v
```

The componentwise type of a tuple is:

```lean
def tupleType {d : Nat} (obs : α → M) (x : Tuple α d) : Fin d → M
```

This corresponds to the paper's observation vector
`h^{(d)}(w_1,...,w_d)`.

---

### 4.2 Refinement of observations

The formalization uses an explicit refinement structure.

```lean
structure Refines (obs : α → M) (obs' : α → M') where
  map : M' → M
  map_one : map 1 = 1
  map_mul : ∀ x y : M', map (x * y) = map x * map y
  comm : ∀ a : α, map (obs' a) = obs a
```

The key checked compatibility lemmas are:

```lean
theorem evalObs_refines (r : Refines obs obs') (w : Word α) :
    r.map (evalObs obs' w) = evalObs obs w
```

```lean
theorem tupleType_refines_apply {d : Nat} (r : Refines obs obs')
    (x : Tuple α d) (i : Fin d) :
    r.map (tupleType obs' x i) = tupleType obs x i
```

The refinement monotonicity theorem for fixed-observation substitutability is
also checked.

---

### 4.3 Fixed-observation tuple substitutability

At the abstract level, a context family and filling operation are parameters.

```lean
Ctx : Nat → Type
fill : ∀ d : Nat, Ctx d → Tuple α d → Word α
```

The distribution of a tuple is the set of contexts accepting it.

```lean
def Distribution {d : Nat} (L : Set (Word α)) (x : Tuple α d) : Set (Ctx d)
```

The fixed-observation substitutability predicate is:

```lean
def FixedTupleSubstitutable
    (f : Nat) (obs : α → M) (L : Set (Word α)) : Prop
```

It formalizes the implication:

> same componentwise observation type + one shared accepting context
> implies equality of all accepting contexts.

The named-context version is also checked through
`FixedNamedTupleSubstitutable`.

---

### 4.4 Named sentence contexts

The second layer introduces concrete named sentence contexts.

Main declarations include:

```lean
RawNamedSentenceContext
RawNamedSentenceContext.WellFormed
NamedSentenceContext
rawNamedFill
namedFill
NamedDistribution
NamedSharesContext
FixedNamedTupleSubstitutable
fixedNamedTupleSubstitutable_of_refines
```

This supports arity-indexed contexts with named holes and avoids baking in a
fragile concrete encoding too early.

---

### 4.5 Working MCFG syntax

The syntax layer introduces a binary linear MCFG presentation skeleton.

Main declarations include:

```lean
TemplateAtom
TemplateWord
evalTemplateAtom
evalTemplateWord
TemplateTuple
evalTemplateTuple
TemplateTuple.Nondeleting
StartRule
TerminalRule
BinaryRule
BinaryRule.apply
WorkingMCFG
WorkingMCFG.FanoutAtMost
WorkingMCFG.BasicWorkingConditions
```

The point of this layer is to make terminal, binary, and start rules explicit
before reconstruction statements are considered.

---

### 4.6 Derivation semantics

The derivation layer introduces a first semantics for tuple derivability and
string languages.

Main declarations include:

```lean
castTuple
singletonTuple
StartRule.WellTyped
WorkingMCFG.StartRulesWellTyped
WorkingMCFG.SemanticWorkingConditions
DerivesTuple
TupleLanguage
StringLanguage
```

This is not yet a full derivation-tree occurrence formalization, but it gives a
checked inductive semantics for generated tuple languages and the start string
language.

---

### 4.7 Contextual semantics and sample-safe merge

The contextual semantics layer connects derivations with named sentence
contexts and positive samples.

Main declarations include:

```lean
ExposedWithContext
GrammarNamedDistribution
GrammarNamedSharesContext
grammarNamedSharesContext_of_two_exposures
grammarNamedDistribution_eq_of_fixed_substitutable
grammarNamedDistribution_eq_of_two_exposures

PositiveSample
SampleNamedDistribution
SampleNamedSharesContext
ObservedInSampleWithContext
observedInSample_to_exposedWithContext

SampleSafeMerge
sampleSafeMerge_sound_for_grammar
sampleObservedExposures_sound_for_grammar
```

The key checked idea is:

> If two tuples are observed in a positive sample with the same fixed observation
> type and a shared sample context, then the fixed-substitutability promise makes
> the corresponding grammar-level named distributions equal.

---

### 4.8 Learner unit-rule closure

The unit-closure layer formalizes the soundness of repeatedly applying
sample-safe unit edges.

Main declarations include:

```lean
PositiveForLanguage
sampleSafeMerge_sound_for_language

LearnerUnitEdge
LearnerUnitEdge.sound_for_language

LearnerUnitReach
LearnerUnitReach.sound_for_language
LearnerUnitReach.mem_namedDistribution_of_reachable
LearnerUnitReach.mem_namedDistribution_iff_of_reachable

LearnerUnitHypothesis
LearnerUnitHypothesis.reach_sound_for_language
```

The checked content is:

> Sample-safe unit edges preserve target named-context distributions, and this
> preservation remains true after taking reflexive-transitive closure.

---

### 4.9 Learner transported distributions

The learner-distribution layer defines contexts licensed by observation and unit
transport.

Main declarations include:

```lean
LearnerLicensedContext
LearnerApproxDistribution
DistributionComplete

sampleSafeMerge_symm
LearnerUnitEdge.reverse
LearnerUnitReach.symm

learnerApproxDistribution_sound_for_language
learnerApproxDistribution_exact_of_complete

LearnerObservedNode
LearnerObservedNode.transported_context_sound_for_language
```

The key checked statement is:

> A context observed in the sample can be transported along safe unit
> reachability to another tuple without leaving the target distribution.

---

### 4.10 Reconstruction certificates

The reconstruction-certificate layer abstracts the point where the paper's
presentation-relative characteristic sample enters.

Main declarations include:

```lean
DistributionReconstructionCertificate
LearnerDistributionExact
TargetContextsLicensed
TargetContextsTransportWitnessed
DistributionCharacteristicSample
DistributionCharacteristicSample.exact_after_extending
exact_for_grammar_after_characteristic_sample
```

This layer proves a distribution-level certificate statement:

> If a finite sample is rich enough to license all target contexts relevant to
> the tuples under consideration, then the learner's transported distribution
> equals the target distribution.

The layer assumes the relevant reconstruction certificate; it does not yet
construct that certificate from an arbitrary MCFG presentation.

---

### 4.11 Gold-style stabilization

The Gold layer formalizes the finite-characteristic-sample-to-eventual-
stabilization argument.

Main declarations include:

```lean
Text
TextFor
PrefixSample
prefixSample_positive
prefixSample_extends_mono
text_eventually_contains_finite_sample

DistributionIdentifiesInLimit
distributionCharacteristicSample_identifiesInLimit
eventually_licensed_iff_target_context

TextForGrammar
DistributionIdentifiesInLimitForGrammar
distributionCharacteristicSample_identifiesGrammarInLimit
eventually_licensed_iff_grammar_context
```

It proves the standard implication:

> If a finite characteristic sample exists, then every text for the target
> language eventually contains it, and all later prefix samples satisfy the
> reconstruction condition.

---

### 4.12 Class-level and finite-hypothesis wrappers

The identification-summary and finite-hypothesis layers connect the abstract
certificate story to finite learner objects.

Main declarations include:

```lean
DistributionTelltaleClass
DistributionIdentifiesLanguageClass
DistributionTargetWitness

GrammarDistributionTelltaleClass
DistributionIdentifiesGrammarClass
GrammarDistributionTargetWitness
```

and:

```lean
FiniteLearnerSupport
FiniteLearnerHypothesis
FiniteLearnerHypothesis.UnitReach
FiniteLearnerHypothesis.ApproxDistribution
FiniteLearnerHypothesis.LicensedContext
FiniteLearnerHypothesis.CompleteForLanguage
FiniteLearnerHypothesis.ExactForLanguage
```

The finite-hypothesis Gold wrapper adds:

```lean
FiniteHypothesisLearner
FiniteHypothesisIdentifiesInLimit
FiniteHypothesisEventuallyCorrectContexts
FiniteHypothesisCharacteristicSample
FiniteHypothesisTelltaleClass
GrammarFiniteHypothesisCharacteristicSample
GrammarFiniteHypothesisTelltaleClass
```

Together these layers formalize:

> If finite samples give finite hypotheses that become exact after a finite
> characteristic sample, then the finite-hypothesis learner stabilizes in the
> Gold sense.

---

### 4.13 Output-type computation for templates

The output-type refinement layer computes the observation type of rule outputs
from the template and child tuple types.

Main declarations include:

```lean
templateAtomType
templateWordType
templateTupleType

evalTemplateAtom_type
evalTemplateWord_type
evalTemplateTuple_type

TerminalRule.outputType
TerminalRule.outputTuple_type

BinaryRule.outputType
BinaryRule.apply_tupleType
BinaryRule.apply_has_outputType
```

This formalizes the basic bookkeeping behind nonterminals of the form

```text
A^(p_1,...,p_d)
```

in the paper: the parent output type is determined by the rule template and the
child output types.

---

### 4.14 Refined nonterminals and refined rules

The refined-rule layer introduces output-typed nonterminals and refined rule
skeletons.

Main declarations include:

```lean
OutputTypedNonterminal
RefinedNonterminal
OutputTypedNonterminal.AcceptsTuple
OutputTypedNonterminal.TypedTuple

DerivesOutputTypedTuple
binary_step_has_output_type

RefinedTerminalRule
RefinedBinaryRule
RefinedStartRule

TerminalRule.refinedLHS
BinaryRule.refinedLeft
BinaryRule.refinedRight
BinaryRule.refinedLHS
StartRule.refinedChild
StartRule.refinedStart
```

The checked content is:

> Terminal, binary, and start rule steps can be lifted to output-typed rule
> skeletons, and the resulting tuple has the advertised output type.

---

### 4.15 Output-typed derivation summaries

The output-typed derivation summary layer connects ordinary tuple derivations
to actual refined nonterminals determined by their observed tuple type.

Main declarations include:

```lean
OutputTypedTupleLanguage
actualRefinedNonterminal
derives_actualRefinedNonterminal
tupleLanguage_covered_by_outputTypes
OutputTypeRefinementConservative
outputTypeRefinementConservative
```

The checked summary is:

> Every ordinary tuple derivation is covered by the refined nonterminal whose
> output type is the actual observation type of the derived tuple.

This is a tuple-level conservativity statement.  It is not yet a full grammar
transformation theorem.

---

### 4.16 Predicate-style refined grammar skeleton

The refined-grammar layer bundles refined terminal, binary, and start rules into
a predicate-style refined grammar.

Main declarations include:

```lean
OutputTypeRefinedGrammar
OutputTypeRefinedGrammar.all
OutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements

RefinedDerivesTuple
RefinedDerivesTuple.sound
RefinedDerivesTuple.forgets_to_derivation
RefinedDerivesTuple.has_output_type

OutputTypeRefinedGrammar.TupleLanguage
OutputTypeRefinedGrammar.tupleLanguage_sound
OutputTypeRefinedGrammar.tupleLanguage_forgets_to_base
OutputTypeRefinedGrammar.tupleLanguage_has_output_type
```

The checked content is:

> Refined derivations forget to ordinary derivations and preserve the advertised
> output type.

The `OutputTypeRefinedGrammar.all` construction represents the fully inclusive
predicate-style refined grammar skeleton.

---

### 4.17 Finite refined grammar certificates

The finite-refined-grammar layer replaces the predicate-style grammar with
explicit finite lists of refined rules.

Main declarations include:

```lean
FiniteOutputTypeRefinedGrammar
FiniteOutputTypeRefinedGrammar.toOutputTypeRefinedGrammar

FiniteOutputTypeRefinedGrammar.CoversAllOrdinaryRuleRefinements
FiniteOutputTypeRefinedGrammar.coversAll_to_containsAll

FiniteOutputTypeRefinedGrammar.TupleLanguage
FiniteOutputTypeRefinedGrammar.tupleLanguage_sound
FiniteOutputTypeRefinedGrammar.tupleLanguage_forgets_to_base
FiniteOutputTypeRefinedGrammar.tupleLanguage_has_output_type

FiniteOutputTypeRefinementCertificate
```

This layer formalizes a finite certificate interface:

> If explicit finite refined rule lists cover all ordinary rule refinements,
> then they induce the corresponding predicate-style refined grammar behavior.

---

### 4.18 Finite output-type enumeration certificates

The finite output-type enumeration layer isolates the finite enumeration of
output-type vectors.

Main declarations include:

```lean
OutputTypeEnumeration
OutputTypeEnumeration.types
OutputTypeEnumeration.complete
OutputTypeEnumeration.SupportsRefinedNonterminal
OutputTypeEnumeration.SupportsRefinedBinaryRule
OutputTypeEnumeration.SupportsRefinedStartRule

GrammarOutputTypeEnumeration
GrammarOutputTypeEnumeration.supports_refinedNonterminal
GrammarOutputTypeEnumeration.supports_actualRefinedNonterminal
GrammarOutputTypeEnumeration.supports_refinedBinaryRule
GrammarOutputTypeEnumeration.supports_refinedStartRule
```

This expresses the certificate form of:

> For each arity `d`, all output types `Fin d → M` are available from a finite
> list.

---

### 4.19 Fintype-derived output-type enumeration

The `FintypeOutputEnumeration` layer connects the certificate interface to
Lean's finite-type infrastructure.

Main declarations include:

```lean
fintypeOutputTypeList
mem_fintypeOutputTypeList
fintypeOutputTypeCount

OutputTypeEnumeration.ofFintype
OutputTypeEnumeration.ofFintype_complete
OutputTypeEnumeration.ofFintype_supports_refinedNonterminal
OutputTypeEnumeration.ofFintype_supports_refinedBinaryRule
OutputTypeEnumeration.ofFintype_supports_refinedStartRule

GrammarOutputTypeEnumeration.ofFintype
GrammarOutputTypeEnumeration.ofFintype_supports_actualRefinedNonterminal
```

The important checked point is:

> If `M` is finite, represented as `[Fintype M]`, then each output-type vector
> type `Fin d → M` can be enumerated using `Fintype.elems`.

This is one of the Lean points closest to the paper's fixed finite monoid
hypothesis.

---

### 4.20 Finite-monoid enumeration certificates

The `FintypeEnumerationCertificate` layer bundles the output-type enumeration
from `[Fintype M]` with a finite refined grammar certificate.

Main declarations include:

```lean
FintypeOutputTypeRefinementCertificate
FintypeOutputTypeRefinementCertificate.outputTypes
FintypeOutputTypeRefinementCertificate.grammar
FintypeOutputTypeRefinementCertificate.toEnumerationCertificate
FintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar

FintypeOutputTypeRefinementCertificate.containsAllOrdinaryRuleRefinements
FintypeOutputTypeRefinementCertificate.listedBinaryRule_supported
FintypeOutputTypeRefinementCertificate.listedStartRule_supported
FintypeOutputTypeRefinementCertificate.refinedNonterminal_supported

FintypeOutputTypeRefinementCertificate.TupleLanguage
FintypeOutputTypeRefinementCertificate.tupleLanguage_sound
FintypeOutputTypeRefinementCertificate.tupleLanguage_forgets_to_base
FintypeOutputTypeRefinementCertificate.tupleLanguage_has_output_type
```

This says, in certificate form:

> Once the observation monoid is finite, output-type refinement can be supported
> by finite output-type enumeration certificates.

---

### 4.21 Finite base-rule support

The finite base-rule support layer records that the base `WorkingMCFG` already
carries ordinary rules as finite lists.

Main declarations include:

```lean
WorkingMCFG.terminalRuleCount
WorkingMCFG.binaryRuleCount
WorkingMCFG.startRuleCount
WorkingMCFG.ordinaryRuleCount

FiniteBaseRuleSupport
FiniteBaseRuleSupport.canonical

FiniteBaseRuleSupport.SupportsTerminalRule
FiniteBaseRuleSupport.SupportsBinaryRule
FiniteBaseRuleSupport.SupportsStartRule
```

This formalizes the ordinary finite input side of the enumeration story:

> The terminal, binary, and start rules of the base presentation are finite
> listed data.

---

### 4.22 Finite rule-enumeration plans

The finite rule-enumeration plan layer combines base rule support with output
type enumeration.

Main declarations include:

```lean
FiniteRuleEnumerationPlan
FiniteRuleEnumerationPlan.terminalRuleCount
FiniteRuleEnumerationPlan.binaryRuleCount
FiniteRuleEnumerationPlan.startRuleCount
FiniteRuleEnumerationPlan.outputTypeCount

FiniteRuleEnumerationPlan.binaryTypeChoiceCount
FiniteRuleEnumerationPlan.startTypeChoiceCount

FiniteRuleEnumerationPlan.supports_terminal_rule
FiniteRuleEnumerationPlan.supports_binary_rule
FiniteRuleEnumerationPlan.supports_start_rule
FiniteRuleEnumerationPlan.supports_binary_type_choices
FiniteRuleEnumerationPlan.supports_start_type_choice
```

This is not yet the actual `List.bind` construction of all refined rules, but it
formalizes the finite plan:

> Ordinary finite rule lists plus finite output-type lists give finite data
> sufficient to plan the refined rule enumeration.

---

### 4.23 Fintype rule-enumeration plans

The latest layer constructs the canonical finite rule-enumeration plan when the
observation monoid is finite.

Main declarations include:

```lean
FiniteRuleEnumerationPlan.ofFintype

FiniteRuleEnumerationPlan.ofFintype_supports_terminal_rule
FiniteRuleEnumerationPlan.ofFintype_supports_binary_rule
FiniteRuleEnumerationPlan.ofFintype_supports_start_rule
FiniteRuleEnumerationPlan.ofFintype_lists_output_type
FiniteRuleEnumerationPlan.ofFintype_supports_binary_type_choices
FiniteRuleEnumerationPlan.ofFintype_supports_start_type_choice
```

The checked statement is:

> Given a finite observation monoid `[Fintype M]` and the finite rule lists of
> the base working grammar, Lean can build a finite plan that supports the
> output-type choices needed for refined terminal, binary, and start rules.

This is the current top layer of the Lean experiment.

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
| actual concrete refined rule lists via `List.bind` | not yet formalized | pending |
| full canonical learner grammar | not yet formalized | pending |
| full exact reconstruction theorem | not yet formalized | pending |
| no-advice non-identifiability | not yet formalized | pending |
| bounded-spine polynomial-data theorem | not yet formalized | pending |

---

## 6. What is not formalized yet

The current Lean development should not be described as a complete
machine-checked proof of the paper.  The following major parts remain outside
the current formalization.

1. **Concrete refined rule-list construction.**  
   The development now has finite rule-enumeration plans, but it does not yet
   implement the actual `List.bind`/cartesian-product construction of all
   refined terminal, binary, and start rules.

2. **Construction of the presentation-relative characteristic sample.**  
   The certificate layers assume distribution-level or finite-hypothesis
   reconstruction witnesses.  They do not yet prove that the paper's finite
   characteristic sample can be extracted from every witnessing working MCFG
   presentation.

3. **The full canonical learner grammar.**  
   Unit-rule closure, transported distributions, finite hypotheses, and refined
   grammar infrastructure are formalized, but the full canonical learner grammar
   with all extracted terminal, binary, start, and unit rules is not yet
   formalized.

4. **Occurrence witnesses in derivation trees.**  
   `ExposedWithContext` is currently abstract.  A full derivation-tree occurrence
   notion connecting nonterminal occurrences to named contexts remains pending.

5. **The hybrid filling lemma in final grammar form.**  
   Distributional transport is checked, but the full MCFG hybrid replacement
   lemma for arbitrary binary derivation contexts is not yet formalized.

6. **Sample consistency for the full learner grammar.**  
   The development does not yet prove that every word in a positive sample is
   generated by the full canonical learner grammar.

7. **Full grammar-level exact reconstruction theorem.**  
   The development does not yet combine output-type refinement, characteristic
   sample coverage, unit transport, extracted rules, and hybrid filling into the
   final theorem that the learned grammar has exactly the target language.

8. **Productivity, reachability, and reducedness closure.**  
   The syntax and derivation layers include basic working conditions, but not
   the full reducedness/productivity/reachability infrastructure used in a
   polished paper proof.

9. **No-advice non-identifiability.**  
   The superfinite-chain argument for the union over all finite observations is
   not yet formalized.

10. **Polynomial-time and polynomial-data statements.**  
    Complexity bounds, enumeration size bounds, characteristic-sample size
    bounds, and fixed-parameter polynomiality are not yet formalized.

11. **Compression lower bound and bounded spine width.**  
    The unary singleton compression example, bounded-spine-width definitions,
    and polynomial-data recovery theorem are not yet formalized.

12. **Comparison examples.**  
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
rule and grammar skeletons, finite refined-grammar certificates, and finite
rule-enumeration plans derived from a finite observation monoid.  The
formalization is not yet a machine-checked proof of the full reconstruction
theorem: the concrete canonical learner grammar, the presentation-relative
characteristic-sample construction, the hybrid filling lemma, the no-advice
boundary, and the bounded-spine polynomial-data theorem remain outside the
current Lean development.
```

A shorter footnote version is:

```latex
A Lean companion checks the fixed-observation and distributional bookkeeping
layers of the construction, including named contexts, MCFG syntax and
derivation skeletons, safe unit-rule closure, transported distributions,
finite-hypothesis wrappers, output-type refinement, finite refined-grammar
certificates, and finite rule-enumeration plans for finite observation monoids.
The full canonical-grammar reconstruction theorem is not yet machine-checked.
```

An even shorter introduction version is:

```latex
A Lean companion is available for the main bookkeeping infrastructure of the
construction.  It currently reaches finite output-type refinement and
finite-monoid rule-enumeration plans, while the full canonical-grammar
reconstruction theorem remains future work.
```

These statements are intentionally conservative.  They emphasize what is
checked without implying that the entire paper has been formalized.

---

## 8. Suggested next formalization milestones

The most valuable next milestones are now:

1. **Concrete refined rule lists.**  
   Implement refined terminal, binary, and start rule lists using `List.bind`
   or suitable finite-list combinators from the finite rule-enumeration plan.

2. **Finite refined grammar generated from the plan.**  
   Construct an actual `FiniteOutputTypeRefinedGrammar` from the concrete
   refined rule lists and prove that it covers all ordinary rule refinements.

3. **Sample-extracted rule skeleton.**  
   Formalize terminal, binary, start, and unit rule extraction from a finite
   positive sample.

4. **Occurrence witnesses in derivation trees.**  
   Strengthen `ExposedWithContext` into a derivation-tree occurrence notion.

5. **Sample consistency.**  
   Prove that every positive sample word is generated by the learner grammar.

6. **Hybrid filling lemma.**  
   Prove that replacing a tuple by a distribution-equivalent tuple inside a
   derivation context preserves target membership.

7. **Canonical learner grammar.**  
   Define the full learner grammar, not only transported distributions or finite
   hypotheses.

8. **Exact reconstruction theorem.**  
   Combine output-type refinement, characteristic-sample coverage, extracted
   rules, unit transport, and hybrid filling into the grammar-level exact
   reconstruction theorem.

9. **No-advice boundary.**  
   Formalize the superfinite chain
   `({a^n b^n | 1 ≤ n ≤ k})_k` converging to `{a^n b^n | n ≥ 1}`.

10. **Polynomial and bounded-spine results.**  
    Formalize enumeration bounds and then the bounded-spine polynomial-data
    theorem.

For the paper's credibility, the highest-value next step is not the complexity
part but the concrete grammar-building part: concrete refined rule lists,
sample-extracted rules, occurrence witnesses, and the hybrid filling lemma.

---

## 9. Current status summary

```text
Checked by CI: yes
Latest CI: Lean CI #398
Latest commit reported by user: 83aa08d
Repository: growupkuriyama-hub/lean_cfg_project
Top checked module: LeanCfgProject.MCFG.FI_v2_1_FintypeRuleEnumerationPlan
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
  finite-monoid rule-enumeration plans.

Full MCFG canonical learner checked: no
Full grammar-level reconstruction theorem checked: no
Concrete refined rule-list construction checked: no
Presentation-relative characteristic-sample construction checked: no
Hybrid filling lemma checked: no
No-advice theorem checked: no
Bounded-spine theorem checked: no
```

In one sentence:

> The current Lean development machine-checks the fixed-observation,
> distributional, finite-hypothesis, output-type-refinement, and finite
> enumeration-plan infrastructure of the MCFG learning construction through
> CI #398 / commit `83aa08d`, while leaving the full presentation-relative
> canonical-grammar reconstruction theorem for future formalization.
