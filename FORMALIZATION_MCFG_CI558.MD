# FORMALIZATION_MCFG

Lean formalization log and roadmap for the MCFG fixed finite-observation paper.

Last updated: 2026-07-06  
Current confirmed CI point: Lean CI #558, commit `f1bf7fa`, pushed by `growupkuriyama-hub`.

---

## 0. Purpose of this restart

This experiment restarts the Lean verification of the paper

> Positive-Data Learning of Multiple Context-Free Grammars with Fixed Finite-Monoid Observations

from a clean baseline.

The previous zip contained many useful experimental files from an earlier paper version, but the experiment procedure had mistakes and the behavior of the old Lean chain was not fully trustworthy. Therefore, this restart follows a conservative policy:

1. do not import the old terminal mega-file as a foundation;
2. rebuild the formalization in small independently checkable layers;
3. keep every file CI-checkable before moving to the next file;
4. separate what is fully Lean-verified from what is currently an explicit skeleton/bridge assumption;
5. reuse old files only as design references or for small ideas, not as opaque trusted infrastructure.

At the current stage, the development has a verified reachable-model main theorem and a substantially scaffolded trimmed-presentation / characteristic-sample route. It is not yet the fully concrete canonical learner theorem from the paper, but the chain now isolates the remaining semantic transport obligations very cleanly: exposing-context transport, common-context transport, start-word evidence, and named-context splicing.

---

## 1. Current high-level status

The current verified chain is:

```text
Basic.lean ✅
ExactOnce.lean ✅
OutputTypeRefinement.lean ✅
OutputTypeLift.lean ✅
DistributionalEquivalence.lean ✅
FillingIdentity.lean ✅
WitnessedComposition.lean ✅
LearnerSoundnessCore.lean ✅
LearnerDerivationSoundness.lean ✅
ConcreteLearnerEvidence.lean ✅
StartRuleSoundness.lean ✅
CompletenessSkeleton.lean ✅
CharacteristicSampleSkeleton.lean ✅
ExactReconstructionSkeleton.lean ✅
GoldIdentificationSkeleton.lean ✅
FiniteTextCoverage.lean ✅
ReachableStartBridge.lean ✅
ReachableGoldTheorem.lean ✅
CharacteristicDataMonotone.lean ✅
StartAnchorCanonical.lean ✅
PrefixExactReconstruction.lean ✅
MainReachableTheorem.lean ✅
CharacteristicSamplePackage.lean ✅
CharacteristicSampleBuilderSkeleton.lean ✅
BlueprintFiniteSample.lean ✅
FillingIdentityConstructionSkeleton.lean ✅
NamedContextSplicingSkeleton.lean ✅
BinaryRuleSplicingEvidence.lean ✅
NamedContextSplicingConstructor.lean ✅
SplicingMainTheorem.lean ✅
SplicingMainDataMonotone.lean ✅
SplicingCharacteristicPackage.lean ✅
SplicingBlueprint.lean ✅
SplicingBlueprintMainData.lean ✅
SplicingBlueprintMainDataMonotone.lean ✅
FinalReachableTheorem.lean ✅
OutputTypeRefinementPresentation.lean ✅
OutputTypePresentationLanguage.lean ✅
OutputTypePresentationMonotone.lean ✅
OutputTypePresentationCompleteness.lean ✅
OutputTypeTrimmedPresentationSkeleton.lean ✅
TrimmedPresentationPreCore.lean ✅
TrimmedPresentationSample.lean ✅
TrimmedPresentationSampleMonotone.lean ✅
TrimmedPresentationFinalTheorem.lean ✅
CharacteristicSampleFromTrimmedPresentation.lean ✅
CharacteristicSampleWitnessSet.lean ✅
CharacteristicSampleWitnessSetMonotone.lean ✅
CharacteristicSampleFiniteBuilder.lean ✅
CharacteristicSampleFiniteUnionBuilder.lean ✅
CharacteristicSampleFiniteUnionPackage.lean ✅
CharacteristicSampleComponentPackage.lean ✅
CharacteristicSampleComponentEnumeration.lean ✅
CharacteristicSampleRuleEnumeration.lean ✅
CharacteristicSampleRuleCoverage.lean ✅
CharacteristicSampleGrammarRuleBuilder.lean ✅
CharacteristicSampleGrammarRulePositivity.lean ✅
CharacteristicSampleRuleWitnessTransport.lean ✅
CharacteristicSampleRuleTransportFinal.lean ✅
CharacteristicSampleContextTransport.lean ✅
CharacteristicSampleExposingTransport.lean ✅
CharacteristicSampleStartWordEvidence.lean ✅
CharacteristicSampleExposingCoreFinal.lean ✅
CharacteristicSampleStartWordFromSample.lean ✅
CharacteristicSampleSameContextCore.lean ✅
CharacteristicSampleAnchorDistributionTransport.lean ✅
CharacteristicSampleAnchorCommonContext.lean ✅
CharacteristicSampleExposingAsCommonContext.lean ✅
CharacteristicSampleTransportInterfaceDiagram.lean ✅
CharacteristicSampleAnchorCommonContextFinal.lean ✅
```

All files marked ✅ above are user-confirmed as passed.  The latest named CI/commit explicitly recorded in this document is:

```text
Lean CI #558
Commit: f1bf7fa
```

`CharacteristicSampleAnchorCommonContextFinal.lean` is now confirmed passed.

The current state is best described as:

```text
reachable main theorem: stabilized under FinalReachableData
splicing/blueprint layer: packaged up to a flat construction target
context-splicing task: isolated as NamedContextSplicingConstructor
finite typed presentation layer: soundness, monotonicity, and completeness interface are in place
trimmed-presentation layer: skeleton, base representatives, pre-core, and sample data are connected to FinalReachableData
concrete canonical learner enumeration: still not yet formalized
actual construction of G̃₀ / CS(G̃₀): now scaffolded through component/rule enumeration and semantic transport interfaces, but not yet concretely constructed from the refined grammar
```

Most important progress since CI #511:

```text
BlueprintFiniteSample.lean split the finite sample data from the blueprint core.
FillingIdentityConstructionSkeleton.lean separated pre-core data from binary filling witnesses.
NamedContextSplicingSkeleton.lean reduced filling witnesses to named-context splicing.
BinaryRuleSplicingEvidence.lean localized named-context splicing to each binary rule.
NamedContextSplicingConstructor.lean isolated a universal constructor target for all parent contexts/templates.
SplicingMainTheorem.lean packaged pre-core + finite sample + constructor into the reachable theorem.
SplicingMainDataMonotone.lean proved monotonicity of that package under sample extension.
SplicingCharacteristicPackage.lean separated finite splicing data from fanout/promise assumptions.
SplicingBlueprint.lean introduced a flat construction target for the splicing-based characteristic data.
SplicingBlueprintMainData.lean combined that flat blueprint with fanout and substitutability.
SplicingBlueprintMainDataMonotone.lean proved final-interface monotonicity.
FinalReachableTheorem.lean fixed stable final names for the reachable theorem.
OutputTypeRefinementPresentation.lean introduced finite typed presentations.
OutputTypePresentationLanguage.lean attached a sound string language to finite typed presentations.
OutputTypePresentationMonotone.lean proved presentation language monotonicity under extension.
OutputTypePresentationCompleteness.lean packaged the converse presentation-language inclusion as `PresentationCompleteFor`.
OutputTypeTrimmedPresentationSkeleton.lean introduced complete trimmed presentations with anchors/exposing contexts for present typed nonterminals.
TrimmedPresentationPreCore.lean descended from typed representatives to base-indexed anchors/exposes and `ReachableBlueprintPreCore`.
TrimmedPresentationSample.lean packaged finite witness-word membership and connected trimmed sample data to `FinalReachableData`.
TrimmedPresentationSampleMonotone.lean proved monotonicity of trimmed sample data under finite positive sample extension.
TrimmedPresentationFinalTheorem.lean gave stable final theorem names for the trimmed-presentation route.
CharacteristicSampleFromTrimmedPresentation.lean packaged the finite witness-word object attached to trimmed pre-core data.
CharacteristicSampleWitnessSet.lean and CharacteristicSampleWitnessSetMonotone.lean isolated the witness-word set and its monotonicity.
CharacteristicSampleFiniteBuilder.lean through CharacteristicSampleFiniteUnionPackage.lean built finite and componentwise routes to witness samples.
CharacteristicSampleComponentPackage.lean and CharacteristicSampleComponentEnumeration.lean converted component samples and indexed enumerations into characteristic samples.
CharacteristicSampleRuleEnumeration.lean and CharacteristicSampleRuleCoverage.lean moved from abstract indices to grammar-rule-indexed finite coverage.
CharacteristicSampleGrammarRuleBuilder.lean and CharacteristicSampleGrammarRulePositivity.lean used the grammar's finite rule sets and removed redundant anchor-positivity assumptions.
CharacteristicSampleRuleWitnessTransport.lean and CharacteristicSampleRuleTransportFinal.lean isolated the remaining terminal/binary/start witness positivity target and gave it a final route.
CharacteristicSampleContextTransport.lean and CharacteristicSampleExposingTransport.lean reduced rule-witness positivity to same-context or exposing-context transport.
CharacteristicSampleStartWordEvidence.lean, CharacteristicSampleExposingCoreFinal.lean, and CharacteristicSampleStartWordFromSample.lean separated and repackaged start-word positivity.
CharacteristicSampleSameContextCore.lean, CharacteristicSampleAnchorDistributionTransport.lean, and CharacteristicSampleAnchorCommonContext.lean linked same-context, distributional, and common-context transport routes.
CharacteristicSampleExposingAsCommonContext.lean and CharacteristicSampleTransportInterfaceDiagram.lean organized the transport-interface conversion diagram.
CharacteristicSampleAnchorCommonContextFinal.lean gave the common-context route its final theorem wrapper.
```

What has **not** yet been fully formalized:

```text
concrete finite canonical learner enumeration
explicit tuple-occurrence and binary-witness enumeration
actual construction of NamedContextSplicingConstructor
actual construction of CS(G̃₀) from the concrete trimmed presentation
trimmed output-type refinement G̃₀ as a concrete finite presentation/grammar object
proof that the constructed G^h / G̃₀ presentation satisfies the completeness interface
proof of the semantic transport obligations now isolated as ExposingContextTransport / AnchorCommonContextTransport
polynomial-time construction bound
no-advice non-identifiability
copy-language / member-kernel exclusion
```

---

## 2. File-by-file progress

### 2.1 `Basic.lean`

Status: CI passed.

Purpose:

This is the clean base layer. It intentionally does not import the previous experimental MCFG files.

Main contents:

```lean
Word
Tuple
evalObs
tupleType
ExplicitFiniteObservation
Distribution
SharesContext
FixedTupleSubstitutable
Refines
fixedTupleSubstitutable_of_refines
RawNamedSentenceContext
NamedSentenceContext
namedFill
FixedNamedTupleSubstitutable
TemplateAtom
TemplateWord
TemplateTuple
evalTemplateTuple
TemplateTuple.Nondeleting
StartRule
TerminalRule
BinaryRule
WorkingMCFG
DerivesTuple
StringLanguage
PositiveSample
CharacteristicSample
```

Paper correspondence:

- fixed finite monoid observations;
- tuple distributions;
- named sentence contexts;
- basic working MCFG syntax;
- minimal tuple derivation semantics;
- characteristic sample abstraction.

Important design choice:

`TemplateTuple.Nondeleting` is deliberately weak in `Basic.lean`: every child component occurs at least once. Exact-once linearity is added later in `ExactOnce.lean`.

---

### 2.2 `ExactOnce.lean`

Status: CI passed.

Purpose:

Add the paper-style exact-once linearity condition for binary templates without changing `Basic.lean`.

Main contents:

```lean
leftVarCount
rightVarCount
LeftOccursExactlyOnce
RightOccursExactlyOnce
TemplateTuple.ExactlyOnce
TemplateTuple.ExactlyOnce.nondeleting
BinaryRule.ExactlyOnce
WorkingMCFG.BinaryRulesExactlyOnce
WorkingMCFG.ExactWorkingConditions
WorkingMCFG.basicWorkingConditions_of_exact
```

Paper correspondence:

This refines the working MCFG side condition: each variable from the two child tuples occurs exactly once in the whole output tuple.

Current limitation:

Exact-once counting is represented by explicit occurrence-count predicates. It is not yet connected to a finite rule enumerator.

---

### 2.3 `OutputTypeRefinement.lean`

Status: CI passed.

Purpose:

Formalize the stable core of the paper’s output-type refinement `G^h`.

Main contents:

```lean
TypedNonterminal
TypedNonterminal.Matches
TypedNonterminal.ofTuple
TerminalRule.outputType
BinaryRule.outputType
BinaryRule.outputType_sound
TypedTerminalRule
TypedBinaryRule
TypedBinaryRule.apply_matches_lhs
TypedStartRule
OutputTypedDerives
OutputTypedDerives.erase
OutputTypedDerives.tuple_type_eq
OutputTypedDerives.of_derives
OutputTypedDerives.binary
```

Paper correspondence:

This matches the output-type refinement idea:

```text
A_p where p is the componentwise h-type of the tuple derived by A.
```

Verified here:

If child tuples match their stored output types, binary template application produces a parent tuple matching the computed parent output type.

Not yet done:

The actual finite refined grammar `G^h` is not yet constructed as a `WorkingMCFG`.

---

### 2.4 `OutputTypeLift.lean`

Status: CI passed.

Purpose:

Formalize the canonical lift of ordinary derivations to output-typed derivations.

Main contents:

```lean
CanonicalTypedNonterminal
ordinaryDerivation_lifts_canonically
outputType_determined_by_tuple
matches_of_outputTypedDerives
typedTerminalRule_lifts
TypedBinaryRule.ofChildTuples
binaryDerivation_lifts_to_computed_lhs
typedStartRule_erases_to_start_derivation
mem_stringLanguage_of_typedStartRule
```

Paper correspondence:

This is the Lean-friendly form of:

> Every ordinary derivation tree lifts uniquely to the output-type refinement by labeling each node with the componentwise output type of the tuple derived at that node.

What is verified:

- every ordinary derivation has a canonical typed wrapper;
- typed derivations erase to ordinary derivations;
- output type is determined by the derived tuple.

What is postponed:

Full uniqueness as equality of dependent typed derivation trees.

---

### 2.5 `DistributionalEquivalence.lean`

Status: CI passed.

Purpose:

Isolate the semantic equivalence relation used in learner soundness.

Main contents:

```lean
FixedDistributionalEquivalent
FixedDistributionalEquivalent.refl
FixedDistributionalEquivalent.symm
FixedDistributionalEquivalent.trans
FixedDistributionalEquivalent.fill_mem_iff
fixedDistributionalEquivalent_of_sharedContext
fixedDistributionalEquivalent_of_common_context

FixedNamedDistributionalEquivalent
fixedNamedDistributionalEquivalent_of_sharedContext
fixedNamedDistributionalEquivalent_of_common_context

GrammarNamedDistributionalEquivalent
grammarNamedDistributionalEquivalent_of_sharedContext
grammarNamedDistributionalEquivalent_of_common_context
grammarNamedDistributionalEquivalent_of_two_exposures
```

Paper correspondence:

This corresponds to the paper’s notation:

```text
u ≡_L^d x
```

and the lemma:

```text
same h-type + one shared accepting context
⇒ equal tuple distributions
```

This is one of the key semantic steps in learner soundness.

---

### 2.6 `FillingIdentity.lean`

Status: CI passed.

Purpose:

Prepare the filling-identity layer for binary-composition soundness.

Main contents:

```lean
tupleType_evalTemplateTuple_congr
tupleType_evalTemplateTuple_left_congr
tupleType_evalTemplateTuple_right_congr

LeftFillingIdentity
RightFillingIdentity

parent_mem_of_left_equiv
parent_mem_of_right_equiv
named_parent_mem_of_left_equiv
named_parent_mem_of_right_equiv
```

Paper correspondence:

This abstracts the statement:

```text
E_B[x] = E[ρ(x,y)]
E_C[y] = E[ρ(x,y)]
```

Design choice:

Concrete construction of the named child contexts is postponed. Instead, this file introduces witness records:

```lean
LeftFillingIdentity
RightFillingIdentity
```

This keeps the semantic proof stable while leaving the bookkeeping-heavy concrete construction for later.

---

### 2.7 `WitnessedComposition.lean`

Status: CI passed.

Purpose:

Formalize the core binary-composition preservation lemma.

Main contents:

```lean
witnessedComposition_accepts_left_replacement
witnessedComposition_accepts_right_replacement
witnessedComposition_accepts
witnessedComposition_preserves_equivalence

named_witnessedComposition_accepts
named_witnessedComposition_preserves_equivalence

grammar_witnessedComposition_preserves_equivalence
```

Paper correspondence:

This formalizes the soundness core:

```text
u ≡ x
v ≡ y
E[ρ(x,y)] ∈ L
⇒ E[ρ(u,v)] ∈ L
⇒ ρ(u,v) ≡ ρ(x,y)
```

Remaining abstraction:

The construction of `E_B` and `E_C` remains represented by `LeftFillingIdentity` and `RightFillingIdentity`.

---

### 2.8 `LearnerSoundnessCore.lean`

Status: CI passed.

Purpose:

Extract rule-by-rule soundness for learner rules.

Main contents:

```lean
NamedUnitEvidence
NamedUnitEvidence.sound
NamedUnitEvidence.symm
sampleUnitEvidence_sound_for_grammar

NamedBinaryEvidence
NamedBinaryEvidence.accepts
NamedBinaryEvidence.sound
NamedBinaryEvidence.sound_self
grammarBinaryEvidence_sound

terminalTuple_sound_self
observedTuple_sound_self
```

Paper correspondence:

This corresponds to the rule cases in learner soundness:

```text
terminal/base case
unit rule case
binary witness rule case
```

This file does not yet define a concrete canonical learner. It proves that the semantic evidence used by the learner is valid.

---

### 2.9 `LearnerDerivationSoundness.lean`

Status: CI passed.

Purpose:

Prove the induction principle behind learner soundness.

Main contents:

```lean
AbstractLearnerDerives
AbstractLearnerDerives.sound
AbstractLearnerDerives.tupleType_eq_of_derives
AbstractLearnerDerives.mem_right_of_derives
AbstractLearnerDerives.mem_left_of_derives
AbstractLearnerDerives.sound_unit_step
AbstractLearnerDerives.sound_binary_step

grammarAbstractLearnerDerives_sound
grammarAbstractLearnerDerives_tupleType_eq
grammarAbstractLearnerDerives_mem_right
```

Paper correspondence:

This gives:

```text
each learner rule is sound
⇒ every learner derivation is sound
```

This is the core induction of `L(learner(K)) ⊆ L`, but still at the abstract tuple-derivation level.

---

### 2.10 `ConcreteLearnerEvidence.lean`

Status: CI passed.

Purpose:

Connect finite positive samples to the abstract semantic evidence.

Main contents:

```lean
SampleUnitEvidence
SampleUnitEvidence.toNamedUnitEvidence
SampleUnitEvidence.sound_for_grammar

SampleBinaryEvidence
SampleBinaryEvidence.toNamedBinaryEvidence
SampleBinaryEvidence.accepts_for_grammar
SampleBinaryEvidence.sound_for_grammar

SampleLearnerDerives
SampleLearnerDerives.toAbstract
SampleLearnerDerives.sound_for_grammar
SampleLearnerDerives.tupleType_eq_for_grammar
SampleLearnerDerives.mem_right_for_grammar
```

Paper correspondence:

This is the bridge:

```text
evidence visible in finite sample K
+
K ⊆ L
⇒ target-language evidence
```

This brings the soundness argument closer to the actual canonical learner.

Still abstracted:

Actual enumeration of all tuple occurrences and binary witnesses in `K`.

---

### 2.11 `StartRuleSoundness.lean`

Status: CI passed.

Purpose:

Move soundness from tuple derivations to string derivations.

Main contents:

```lean
unaryIdentityContext
namedFill_unaryIdentityContext
SampleStringDerives
SampleStringDerives.of_sample_word
SampleStringDerives.sound_for_grammar
SampleStringDerives.singleton_tupleType_eq_for_grammar
sample_string_soundness
```

Paper correspondence:

This proves the string-level soundness skeleton:

```text
K ⊆ L
and sample-level learner derives word w
⇒ w ∈ L
```

This corresponds to the inclusion:

```text
L(learner(K)) ⊆ L
```

under the current abstract learner model.

---

### 2.12 `CompletenessSkeleton.lean`

Status: CI passed.

Purpose:

Start the completeness side by proving a rule-simulation induction principle.

Main contents:

```lean
SampleLearnerReachable
SampleLearnerReachable.of_derives
SampleLearnerReachable.trans'
SampleLearnerReachable.arityCast
SampleLearnerReachable.sound_for_grammar
SampleLearnerReachable.tupleType_eq_for_grammar
SampleLearnerReachable.mem_right_for_grammar

AnchorSimulation
AnchorSimulation.simulates_derivation
```

Paper correspondence:

This proves:

```text
if every target rule is simulated from chosen anchors,
then every target derivation is simulated from the corresponding anchor.
```

This is the main induction behind completeness.

Important note:

`SampleLearnerReachable` adds explicit transitive closure, because completeness requires concatenating many rule simulations.

---

### 2.13 `CharacteristicSampleSkeleton.lean`

Status: CI passed.

Purpose:

Package the sample data needed to build `AnchorSimulation`.

Main contents:

```lean
CharacteristicSampleData
CharacteristicSampleData.terminalUnitEvidence
CharacteristicSampleData.binaryUnitEvidence
CharacteristicSampleData.binaryEvidence
CharacteristicSampleData.startUnitEvidence
CharacteristicSampleData.toAnchorSimulation
CharacteristicSampleData.simulates_derivation
CharacteristicSampleData.reaches_of_string_mem
CharacteristicSampleData.simulated_derivation_sound
```

Paper correspondence:

This is the skeleton of:

```text
CS(G̃₀) ⊆ K
⇒ anchor/exposure examples are present in K
⇒ every target rule is simulated
⇒ every target derivation is simulated
```

Still not done:

- constructing `CS(G̃₀)`;
- proving that the constructed sample satisfies `CharacteristicSampleData`;
- extracting anchors from the trimmed output-type refinement.

---

### 2.14 `ExactReconstructionSkeleton.lean`

Status: CI passed.

Purpose:

Package soundness and completeness skeletons into an exact-reconstruction statement.

Main contents:

```lean
SampleStringLanguage
sampleStringLanguage_sound
sample_mem_sampleStringLanguage

CharacteristicReachableLanguage
target_subset_characteristicReachableLanguage

ReconstructionBridge
ReconstructionBridge.characteristicReachable_sound
ReconstructionBridge.exact_reconstruction
ReconstructionBridge.exact_reconstruction_inclusions
```

Paper correspondence:

This gives the first outer exact reconstruction form:

```text
SampleStringLanguage K obs f = G.StringLanguage
```

provided a remaining `ReconstructionBridge`.

This bridge is later replaced by the more natural reachable-language bridge in `ReachableStartBridge.lean`.

---

### 2.15 `GoldIdentificationSkeleton.lean`

Status: CI passed.

Purpose:

Formalize the general Gold-identification step after exact reconstruction.

Main contents:

```lean
TextFor
TextFor.prefixSample
TextFor.prefixSample_subset
TextFor.prefixSample_mono
TextFor.EventuallyContains
EventuallyCorrectOnText
characteristicSample_eventual_correct_on_text
characteristicSample_correct_after_stage
characteristicSample_identifies_target
exactReconstruction_characteristicSample_identifies
```

Paper correspondence:

This formalizes:

```text
finite characteristic sample S
+
eventually S appears in every positive text
⇒ learner stabilizes to the target language
```

At this file’s level, `TextFor.EventuallyContains S` was still an explicit assumption. That is discharged later in `FiniteTextCoverage.lean`.

---

### 2.16 `FiniteTextCoverage.lean`

Status: CI passed.

Purpose:

Discharge the finite-coverage assumption used by the Gold identification skeleton.

Main contents:

```lean
TextFor.eventuallyContains_of_subset
TextFor.eventuallyContains_finite_subset

characteristicSample_eventual_correct_on_every_text
characteristicSample_correct_after_finite_coverage
finiteCharacteristicSample_identifies_target
```

Paper correspondence:

This proves the standard Gold-learning finite-coverage lemma:

```text
S finite
S ⊆ L
T is a positive text for L
⇒ S is eventually contained in the prefix samples of T
```

This removes the earlier explicit `EventuallyContains` assumption.

---

### 2.17 `ReachableStartBridge.lean`

Status: CI passed.

Purpose:

Replace the earlier abstract `ReconstructionBridge` by a more natural reachable-language bridge.

Main contents:

```lean
ReachableSampleStringDerives
ReachableSampleStringLanguage
reachableSampleStringLanguage_sound
sampleStringLanguage_subset_reachableSampleStringLanguage

StartAnchorAsSampleWord
StartAnchorAsSampleWord.characteristic_subset_reachableSample
StartAnchorAsSampleWord.exact_reconstruction_reachable
StartAnchorAsSampleWord.exact_reconstruction_reachable_inclusions
```

Paper correspondence:

This formalizes the reachable version:

```text
characteristic start anchor is the singleton tuple of a sample word
⇒ characteristic reachable language ⊆ reachable sample string language
⇒ reachable exact reconstruction
```

This is now the main route for exact reconstruction.

---

### 2.18 `ReachableGoldTheorem.lean`

Status: CI passed.

Purpose:

Connect reachable exact reconstruction with Gold identification.

Main contents:

```lean
ReachableSampleHyp
reachableSampleLearner
reachableHypLanguage

ReachableCharacteristicCondition
reachable_characteristicSample
reachable_identifies_from_positive_text
reachable_identifies_after_some_stage
```

Paper correspondence:

This proves:

```text
if a finite S is positive
and every positive finite K ⊇ S supplies characteristic data plus start-anchor bridge,
then the reachable learner identifies the target from every positive text.
```

This is a major packaging step toward the main theorem.

---

### 2.19 `CharacteristicDataMonotone.lean`

Status: CI passed.

Purpose:

Show that characteristic data over a finite sample `S` can be transported to any larger sample `K`.

Main contents:

```lean
CharacteristicSampleData.mono
StartAnchorAsSampleWord.mono

reachableCharacteristicCondition_of_data
reachable_characteristicSample_of_data
reachable_identifies_from_characteristic_data
reachable_correct_after_some_stage_from_characteristic_data
```

Paper correspondence:

This is the monotonicity principle:

```text
CS(G̃₀) works at S
⇒ the same witnesses work at every finite K with S ⊆ K
```

This eliminates the need to separately construct characteristic data for every later prefix sample.

---

### 2.20 `StartAnchorCanonical.lean`

Status: CI passed.

Purpose:

Make the start-anchor bridge easier to construct.

Main contents:

```lean
StartAnchorCanonical
StartAnchorCanonical.toStartAnchorAsSampleWord
StartAnchorCanonical.toStartAnchorAsSampleWord_of_eq
StartAnchorCanonical.mono
StartAnchorCanonical.exact_reconstruction_reachable
StartAnchorCanonical.exact_reconstruction_reachable_inclusions

reachable_characteristicSample_of_canonical_data
reachable_identifies_from_canonical_characteristic_data
reachable_correct_after_some_stage_from_canonical_data
```

Paper correspondence:

Instead of requiring an equality for every proof of the start arity equality, this file allows construction from one proof:

```text
startWord ∈ S
1 = arity start
anchor start = castTuple hstart (singletonTuple startWord)
```

This is closer to the way the paper’s start convention should be used.

---

### 2.21 `PrefixExactReconstruction.lean`

Status: CI passed.

Purpose:

State exact reconstruction directly for prefix samples of a positive text.

Main contents:

```lean
exact_reconstruction_at_prefix_after_seen
eventually_exact_reconstruction_at_prefixes
eventually_reachable_hypothesis_correct_at_prefixes
reachable_hypothesis_correct_after_seen
```

Paper correspondence:

This proves:

```text
finite characteristic sample S has appeared in T.prefixSample n
⇒ reachable learner on T.prefixSample n reconstructs L(G) exactly.
```

Together with finite-text coverage, this gives eventual exact reconstruction along every positive text.

---

### 2.22 `MainReachableTheorem.lean`

Status: CI passed.

Purpose:

Package the current verified development into a single reachable-model main theorem.

Main contents:

```lean
ReachableMainData

ReachableMainData.exact_at_seen_prefix
ReachableMainData.eventually_exact_at_prefixes
ReachableMainData.eventually_hypothesis_correct_at_prefixes
ReachableMainData.eventually_correct_on_text
ReachableMainData.characteristic_sample
ReachableMainData.identifies_from_positive_text
ReachableMainData.prefix_exact_eventually

main_reachable_identification
main_reachable_prefix_exact
```

Paper correspondence:

This is the clean current main theorem for the reachable learner model:

```text
ReachableMainData G S obs f
⇒ for every positive text T for L(G),
   eventually the reachable learner hypothesis on T.prefixSample n is exactly L(G).
```

The record `ReachableMainData` still assumes the finite characteristic data and start-anchor witness, but the theorem chain from those assumptions to Gold identification is now fully Lean-checked.

---

### 2.23 `CharacteristicSamplePackage.lean`

Status: CI passed.

Purpose:

Separate finite characteristic-sample data from global target assumptions.

Main contents:

```lean
ReachableCharacteristicPackage

ReachableCharacteristicPackage.toMainData
ReachableCharacteristicPackage.characteristic_sample
ReachableCharacteristicPackage.eventually_correct_on_text
ReachableCharacteristicPackage.identifies_from_positive_text
ReachableCharacteristicPackage.exact_at_seen_prefix
ReachableCharacteristicPackage.prefix_exact_eventually
ReachableCharacteristicPackage.mono
ReachableCharacteristicPackage.exact_for_positive_superset
ReachableCharacteristicPackage.toReachableCharacteristicCondition

main_reachable_identification_from_package
main_reachable_prefix_exact_from_package
```

Paper correspondence:

This separates:

```text
finite sample side:
  positivity of S
  CharacteristicSampleData
  StartAnchorCanonical

global target side:
  fanout ≤ f
  fixed-observation substitutability promise
```

This is useful because the future `CS(G̃₀)` construction should produce the finite package, while the theorem statement supplies the global target assumptions.

---

### 2.24 `CharacteristicSampleBuilderSkeleton.lean`

Status: CI passed.

Purpose:

Introduce a flat construction blueprint for the finite characteristic package.

Main contents:

```lean
ReachableCharacteristicBlueprint

ReachableCharacteristicBlueprint.toData
ReachableCharacteristicBlueprint.toStartAnchorCanonical
ReachableCharacteristicBlueprint.toPackage
ReachableCharacteristicBlueprint.toMainData

ReachableCharacteristicBlueprint.exact_at_seen_prefix
ReachableCharacteristicBlueprint.prefix_exact_eventually
ReachableCharacteristicBlueprint.identifies_from_positive_text
ReachableCharacteristicBlueprint.characteristic_sample
ReachableCharacteristicBlueprint.exact_for_positive_superset

main_reachable_identification_from_blueprint
main_reachable_prefix_exact_from_blueprint
```

Paper correspondence:

This is now the target shape for the actual characteristic-sample construction:

```text
construct ReachableCharacteristicBlueprint from CS(G̃₀)
⇒ get ReachableCharacteristicPackage
⇒ get ReachableMainData
⇒ get reachable exact reconstruction and Gold identification
```

This file is a major interface improvement: future construction work can focus on filling one flat record rather than juggling dependent packages.

---

### 2.25 `BlueprintFiniteSample.lean`

Status: CI passed.

Purpose:

Separate the sample-independent blueprint core from the finite sample membership data.

Main contents:

```lean
ReachableBlueprintCore
ReachableBlueprintFiniteSample
ReachableBlueprintFiniteSample.toBlueprint
ReachableBlueprintFiniteSample.toPackage
ReachableBlueprintFiniteSample.toMainData
ReachableBlueprintFiniteSample.mono
main_reachable_identification_from_finite_sample_blueprint
main_reachable_prefix_exact_from_finite_sample_blueprint
```

Paper correspondence:

This clarifies the role of the finite characteristic set:

```text
core choices: anchors, exposures, type equalities, filling identities, start anchor
finite sample facts: the required words are actually contained in S
```

This is closer to a future construction from `CS(G̃₀)`.

---

### 2.26 `FillingIdentityConstructionSkeleton.lean`

Status: CI passed.

Purpose:

Separate the pre-core from the binary filling identity witnesses.

Main contents:

```lean
ReachableBlueprintPreCore
BinaryFillingWitnessFamily
ReachableBlueprintPreCore.withFillingWitnesses
ReachablePreCoreFiniteSample
ReachablePreCoreFiniteSample.toFiniteSample
main_reachable_identification_from_precore
main_reachable_prefix_exact_from_precore
```

Paper correspondence:

This isolates the remaining context-splicing/filling task:

```text
pre-core data + binary filling witnesses
⇒ full reachable blueprint core
```

So the hard bookkeeping around child contexts is no longer mixed with the rest of the main theorem.

---

### 2.27 `NamedContextSplicingSkeleton.lean`

Status: CI passed.

Purpose:

Reduce binary filling identities to named-context splicing data.

Main contents:

```lean
BinaryNamedContextSplicing
BinaryNamedContextSplicing.leftIdentity
BinaryNamedContextSplicing.rightIdentity
BinaryNamedSplicingFamily
BinaryNamedSplicingFamily.toFillingWitnessFamily
BinaryNamedSplicingFamily.toBlueprintCore
BinaryNamedSplicingFamily.toFiniteSample
BinaryNamedSplicingFamily.toBlueprint
main_reachable_identification_from_named_splicing
main_reachable_prefix_exact_from_named_splicing
```

Paper correspondence:

This gives a cleaner target for constructing child contexts:

```text
parent named context E
binary template ρ
⇒ left and right named child contexts satisfying exact filling equations
```

---

### 2.28 `BinaryRuleSplicingEvidence.lean`

Status: CI passed.

Purpose:

Localize named-context splicing evidence to individual binary rules.

Main contents:

```lean
BinaryRuleSplicingEvidence
BinaryRuleSplicingEvidence.leftIdentity
BinaryRuleSplicingEvidence.rightIdentity
BinaryRuleSplicingProvider
BinaryRuleSplicingProvider.toNamedSplicingFamily
BinaryRuleSplicingProvider.toFillingWitnessFamily
BinaryRuleSplicingProvider.toBlueprintCore
main_reachable_identification_from_rule_splicing
main_reachable_prefix_exact_from_rule_splicing
```

Paper correspondence:

This says:

```text
if every binary rule has local splicing evidence,
then the whole grammar has the filling witnesses needed for the reachable theorem.
```

---

### 2.29 `NamedContextSplicingConstructor.lean`

Status: CI passed.

Purpose:

Isolate a universal named-context splicing constructor.

Main contents:

```lean
NamedContextSplicingConstructor
NamedContextSplicingConstructor.toRuleSplicingEvidence
NamedContextSplicingConstructor.toRuleSplicingProvider
NamedContextSplicingConstructor.toNamedSplicingFamily
NamedContextSplicingConstructor.toFillingWitnessFamily
NamedContextSplicingConstructor.toBlueprintCore
main_reachable_identification_from_splicing_constructor
main_reachable_prefix_exact_from_splicing_constructor
```

Paper correspondence:

This is now the clean construction target for the filling-identity problem:

```text
for every parent named context and every binary template,
construct BinaryNamedContextSplicing
```

Once this constructor exists, the entire binary filling side follows.

---

### 2.30 `SplicingMainTheorem.lean`

Status: CI passed.

Purpose:

Package the reachable theorem using the universal splicing constructor.

Main contents:

```lean
ReachableSplicingMainData
ReachableSplicingMainData.ruleSplicingProvider
ReachableSplicingMainData.namedSplicingFamily
ReachableSplicingMainData.fillingWitnessFamily
ReachableSplicingMainData.blueprintCore
ReachableSplicingMainData.toBlueprint
ReachableSplicingMainData.toPackage
ReachableSplicingMainData.toMainData
ReachableSplicingMainData.identifies_from_positive_text
ReachableSplicingMainData.prefix_exact_eventually
main_reachable_identification_from_splicing_data
main_reachable_prefix_exact_from_splicing_data
```

Paper correspondence:

This theorem interface says:

```text
fanout + promise + pre-core + finite sample + universal splicing constructor
⇒ reachable exact reconstruction and Gold identification.
```

---

### 2.31 `SplicingMainDataMonotone.lean`

Status: CI passed.

Purpose:

Prove monotonicity of `ReachableSplicingMainData` under finite sample extension.

Main contents:

```lean
ReachablePreCoreFiniteSample.mono
ReachablePreCoreFiniteSample.toFiniteSample_mono
ReachableSplicingMainData.mono
ReachableSplicingMainData.exact_after_mono
ReachableSplicingMainData.exact_at_prefix_via_mono
ReachableSplicingMainData.prefix_exact_eventually_via_mono
main_reachable_prefix_exact_from_splicing_data_mono
main_reachable_identification_from_splicing_data_mono
```

Paper correspondence:

This is the prefix-text mechanism in the splicing package:

```text
S has all witnesses
S ⊆ K ⊆ L(G)
⇒ the same data works over K
```

---

### 2.32 `SplicingCharacteristicPackage.lean`

Status: CI passed.

Purpose:

Separate finite splicing construction data from the global target assumptions.

Main contents:

```lean
ReachableSplicingPackage
ReachableSplicingPackage.toMainData
ReachableSplicingPackage.ruleSplicingProvider
ReachableSplicingPackage.namedSplicingFamily
ReachableSplicingPackage.fillingWitnessFamily
ReachableSplicingPackage.blueprintCore
ReachableSplicingPackage.toBlueprint
ReachableSplicingPackage.toCharacteristicPackage
ReachableSplicingPackage.mono
ReachableSplicingPackage.identifies_from_positive_text
main_reachable_identification_from_splicing_package
main_reachable_prefix_exact_from_splicing_package
```

Paper correspondence:

This makes the finite construction target independent of:

```text
fanout bound
fixed-observation substitutability promise
```

Those are supplied later by the theorem statement.

---

### 2.33 `SplicingBlueprint.lean`

Status: CI passed.

Purpose:

Introduce the flat construction target for the splicing-based characteristic package.

Main contents:

```lean
ReachableSplicingBlueprint
ReachableSplicingBlueprint.toPreCore
ReachableSplicingBlueprint.toFiniteSample
ReachableSplicingBlueprint.toPackage
ReachableSplicingBlueprint.toMainData
ReachableSplicingBlueprint.mono
ReachableSplicingBlueprint.characteristic_sample
ReachableSplicingBlueprint.identifies_from_positive_text
main_reachable_identification_from_splicing_blueprint
main_reachable_prefix_exact_from_splicing_blueprint
```

Paper correspondence:

This is now the most natural target for a future `CS(G̃₀)` construction:

```text
anchors + exposing contexts + type equalities
+ finite sample membership facts
+ start anchor
+ NamedContextSplicingConstructor
⇒ reachable identification
```

---

### 2.34 `SplicingBlueprintMainData.lean`

Status: CI passed.

Purpose:

Package the flat blueprint together with the global target assumptions.

Main contents:

```lean
ReachableSplicingBlueprintMainData
ReachableSplicingBlueprintMainData.toPackage
ReachableSplicingBlueprintMainData.toSplicingMainData
ReachableSplicingBlueprintMainData.toReachableMainData
ReachableSplicingBlueprintMainData.characteristic_sample
ReachableSplicingBlueprintMainData.exact_for_positive_superset
ReachableSplicingBlueprintMainData.prefix_exact_eventually
ReachableSplicingBlueprintMainData.identifies_from_positive_text
main_reachable_identification_from_splicing_blueprint_data
main_reachable_prefix_exact_from_splicing_blueprint_data
```

Paper correspondence:

This gives the compact main-theorem interface:

```text
ReachableSplicingBlueprint
+
fanout
+
fixed-observation promise
⇒ reachable exact reconstruction and Gold identification
```

---

### 2.35 `SplicingBlueprintMainDataMonotone.lean`

Status: CI passed.

Purpose:

Prove monotonicity of the flat blueprint main-data interface.

Main contents:

```lean
ReachableSplicingBlueprintMainData.mono
ReachableSplicingBlueprintMainData.exact_after_mono
ReachableSplicingBlueprintMainData.characteristic_sample_after_mono
ReachableSplicingBlueprintMainData.exact_at_prefix_via_mono
ReachableSplicingBlueprintMainData.prefix_exact_eventually_via_mono
ReachableSplicingBlueprintMainData.identifies_from_positive_text_via_mono
main_reachable_prefix_exact_from_splicing_blueprint_data_mono
main_reachable_identification_from_splicing_blueprint_data_mono
```

Paper correspondence:

This is the final-interface version of:

```text
once S appears in a positive text prefix,
every later prefix inherits the same characteristic blueprint data.
```

---

### 2.36 `FinalReachableTheorem.lean`

Status: CI passed.

Purpose:

Fix stable final names for the current reachable-model theorem.

Main contents:

```lean
FinalReachableData
FinalReachableData.blueprint
FinalReachableData.fanout
FinalReachableData.promise
FinalReachableData.toBlueprintMainData
FinalReachableData.toSplicingMainData
FinalReachableData.toReachableMainData
FinalReachableData.characteristic_sample
FinalReachableData.exact_for_positive_superset
FinalReachableData.prefix_exact_eventually
FinalReachableData.identifies_from_positive_text
FinalReachableData.mono
final_reachable_identification
final_reachable_prefix_exact
final_reachable_exact_for_positive_superset
```

Paper correspondence:

This is the current formal endpoint:

```text
FinalReachableData
⇒ reachable Gold identification
⇒ eventual prefix-exact reconstruction.
```

Important limitation:

This is still the reachable sample-language theorem, not yet the fully enumerated concrete canonical learner theorem.

---

### 2.37 `OutputTypeRefinementPresentation.lean`

Status: CI passed.

Purpose:

Start the finite typed-presentation layer for output-type refinements.

Main contents:

```lean
OutputTypeRefinementPresentation
OutputTypeRefinementPresentation.HasNonterminal
OutputTypeRefinementPresentation.HasTerminalRule
OutputTypeRefinementPresentation.HasBinaryRule
OutputTypeRefinementPresentation.HasStartRule
OutputTypeRefinementPresentation.terminal_lhs_present
OutputTypeRefinementPresentation.binary_nodes_present
PresentationDerives
PresentationDerives.toOutputTypedDerives
PresentationDerives.erase
PresentationDerives.tuple_type_eq
```

Paper correspondence:

This starts representing finite pieces of `G^h` / `G̃₀` as a finite typed presentation:

```text
finite typed nonterminals
finite typed terminal rules
finite typed binary rules
finite typed start rules
```

Verified here:

```text
a presentation derivation erases to an ordinary derivation of the original grammar
and has the output type stored in its typed nonterminal.
```

---

### 2.38 `OutputTypePresentationLanguage.lean`

Status: CI passed.

Purpose:

Attach a string language to finite output-type presentations.

Main contents:

```lean
PresentationStringDerives
PresentationStringDerives.child_present
PresentationStringDerives.child_erases
PresentationStringDerives.child_output_typed_derives
PresentationStringDerives.child_tuple_type_eq
PresentationStringDerives.sound
PresentationStringLanguage
presentationStringLanguage_sound
mem_original_of_mem_presentationStringLanguage
mem_presentationStringLanguage_of_start
mem_original_of_presentation_start
```

Paper correspondence:

This proves the soundness inclusion for finite typed presentations:

```text
PresentationStringLanguage P ⊆ G.StringLanguage
```

This is the presentation-level soundness half for `G^h` / `G̃₀`.

---

### 2.39 `OutputTypePresentationMonotone.lean`

Status: CI passed.

Purpose:

Prove monotonicity of finite typed presentations.

Main contents:

```lean
PresentationExtends
PresentationExtends.refl
PresentationExtends.trans
PresentationExtends.hasNonterminal
PresentationExtends.hasTerminalRule
PresentationExtends.hasBinaryRule
PresentationExtends.hasStartRule
PresentationExtends.derives
PresentationExtends.stringDerives
PresentationExtends.language_subset
PresentationExtends.mem_language
PresentationExtends.language_eq_of_mutual
PresentationExtends.sound_after_extension
```

Paper correspondence:

This verifies:

```text
P's typed nonterminals and typed rules are included in Q
⇒ every P derivation is a Q derivation
⇒ PresentationStringLanguage P ⊆ PresentationStringLanguage Q
```

This is useful for moving between a trimmed core presentation and a larger saturated/reachable presentation.

---

### 2.40 `OutputTypePresentationCompleteness.lean`

Status: CI passed / user-confirmed.

Purpose:

Package the missing converse inclusion for finite output-type presentations.

Main contents:

```lean
PresentationCompleteFor
PresentationCompleteFor.mem_presentation
PresentationCompleteFor.sound
PresentationCompleteFor.language_eq
PresentationCompleteFor.mem_iff
PresentationCompleteFor.extend
PresentationCompleteFor.language_eq_after_extension
PresentationCompleteFor.of_mutual_extension
PresentationCompleteFor.language_eq_of_mutual_extension

presentationCompleteFor_of_subset
presentationStringLanguage_eq_original_of_subset
presentationCompleteFor_of_language_eq
presentation_language_inclusions
presentation_language_exact

CompleteOutputTypePresentation
CompleteOutputTypePresentation.language
CompleteOutputTypePresentation.sound
CompleteOutputTypePresentation.complete_subset
CompleteOutputTypePresentation.language_eq
CompleteOutputTypePresentation.mem_iff
CompleteOutputTypePresentation.extend
CompleteOutputTypePresentation.extend_language_eq
```

Paper correspondence:

The already verified soundness inclusion is:

```text
PresentationStringLanguage P ⊆ G.StringLanguage
```

This file isolates the converse as an explicit interface:

```text
PresentationCompleteFor P
:= G.StringLanguage ⊆ PresentationStringLanguage P
```

and proves:

```text
PresentationCompleteFor P
⇒ PresentationStringLanguage P = G.StringLanguage
```

This does not yet prove that the actual `G^h` or `G̃₀` presentation is complete; it fixes the exact theorem target.

---

### 2.41 `OutputTypeTrimmedPresentationSkeleton.lean`

Status: CI passed / user-confirmed.

Purpose:

Introduce a skeleton for a complete trimmed finite output-type presentation.

Main contents:

```lean
PresentTypedNonterminal
PresentTypedNonterminal.base
PresentTypedNonterminal.arity
PresentTypedNonterminal.out
PresentTypedNonterminal.mkOfMem

TrimmedNonterminalWitnesses
TrimmedNonterminalWitnesses.exposedWord
TrimmedNonterminalWitnesses.exposedWord_mem
TrimmedNonterminalWitnesses.anchor_tupleType

TrimmedOutputTypePresentation
TrimmedOutputTypePresentation.presentation
TrimmedOutputTypePresentation.language
TrimmedOutputTypePresentation.ofComplete
TrimmedOutputTypePresentation.sound
TrimmedOutputTypePresentation.complete_subset
TrimmedOutputTypePresentation.language_eq
TrimmedOutputTypePresentation.mem_language_iff
TrimmedOutputTypePresentation.anchor
TrimmedOutputTypePresentation.expose
TrimmedOutputTypePresentation.exposedWord
TrimmedOutputTypePresentation.anchor_tupleType
TrimmedOutputTypePresentation.exposedWord_mem
TrimmedOutputTypePresentation.terminalLHS
TrimmedOutputTypePresentation.binaryLHS
TrimmedOutputTypePresentation.binaryLeft
TrimmedOutputTypePresentation.binaryRight
TrimmedOutputTypePresentation.startChild
```

Paper correspondence:

This starts representing `G̃₀`-like data:

```text
complete finite typed presentation
+
for every present typed nonterminal, an anchor tuple
+
for every present typed nonterminal, an exposing named context
```

This is not yet the concrete construction of `G̃₀`, but it is the right shape for trimmed/productive/reachable witnesses.

---

### 2.42 `TrimmedPresentationPreCore.lean`

Status: CI passed / user-confirmed.

Purpose:

Descend from typed nonterminal witnesses to base-nonterminal data.

Main contents:

```lean
TrimmedBaseRepresentatives
TrimmedBaseRepresentatives.repArityEq
TrimmedBaseRepresentatives.transportedRepOutput
TrimmedBaseRepresentatives.exposedWord
TrimmedBaseRepresentatives.anchor_tupleType
TrimmedBaseRepresentatives.exposedWord_mem
TrimmedBaseRepresentatives.rep_present

TrimmedPresentationPreCoreData
TrimmedPresentationPreCoreData.anchor
TrimmedPresentationPreCoreData.expose
TrimmedPresentationPreCoreData.toReachablePreCore
TrimmedPresentationPreCoreData.exposedWord
TrimmedPresentationPreCoreData.exposedWord_mem
TrimmedPresentationPreCoreData.anchor_tupleType_rep
TrimmedPresentationPreCoreData.terminal_type
TrimmedPresentationPreCoreData.binary_type
TrimmedPresentationPreCoreData.start_type
```

Paper correspondence:

`ReachableSplicingBlueprint` is indexed by base nonterminals `A : N`, while the trimmed presentation is typed.  This file adds the bridge:

```text
typed present nonterminal representatives
⇒ base-indexed anchor/expose data
⇒ ReachableBlueprintPreCore
```

It also records the terminal, binary, and start type equalities needed by the pre-core.

---

### 2.43 `TrimmedPresentationSample.lean`

Status: CI passed / user-confirmed.

Purpose:

Add the finite sample membership layer on top of trimmed-presentation pre-core data.

Main contents:

```lean
TrimmedPresentationPreCoreData.anchorWitnessWord
TrimmedPresentationPreCoreData.terminalWitnessWord
TrimmedPresentationPreCoreData.binaryWitnessWord
TrimmedPresentationPreCoreData.startWitnessWord

TrimmedPresentationSampleData
TrimmedPresentationSampleData.anchor_mem_target
TrimmedPresentationSampleData.terminal_mem_target
TrimmedPresentationSampleData.binary_mem_target
TrimmedPresentationSampleData.start_mem_target
TrimmedPresentationSampleData.startWord_mem_target
TrimmedPresentationSampleData.toReachablePreCoreFiniteSample
TrimmedPresentationSampleData.toSplicingPackage
TrimmedPresentationSampleData.toSplicingBlueprint
TrimmedPresentationSampleData.toSplicingBlueprintMainData
TrimmedPresentationSampleData.toFinalReachableData
TrimmedPresentationSampleData.identifies_from_trimmed_sample
TrimmedPresentationSampleData.prefix_exact_from_trimmed_sample
```

Paper correspondence:

This makes the future characteristic sample role concrete:

```text
CS(G̃₀) should contain:
  anchorWitnessWord
  terminalWitnessWord
  binaryWitnessWord
  startWitnessWord
  startWord
```

Given those membership facts, plus `NamedContextSplicingConstructor`, fanout, and the substitutability promise, the file constructs:

```lean
FinalReachableData G S obs f
```

and therefore obtains reachable identification and prefix-exact reconstruction.

---

### 2.44 `TrimmedPresentationSampleMonotone.lean`

Status: CI passed / user-confirmed.

Purpose:

Prove monotonicity of `TrimmedPresentationSampleData` under finite sample extension.

Main contents:

```lean
TrimmedPresentationSampleData.mono
TrimmedPresentationSampleData.toReachablePreCoreFiniteSample_mono
TrimmedPresentationSampleData.toSplicingPackage_mono
TrimmedPresentationSampleData.exact_after_mono
TrimmedPresentationSampleData.exact_at_prefix_via_mono
TrimmedPresentationSampleData.prefix_exact_via_mono
TrimmedPresentationSampleData.identifies_via_mono

main_reachable_identification_from_trimmed_sample_mono
main_reachable_prefix_exact_from_trimmed_sample_mono
```

Paper correspondence:

The intended theorem is:

```text
S contains the trimmed-presentation witness words
S ⊆ K
K ⊆ G.StringLanguage
⇒ the same trimmed sample data works over K
```

This gives the direct positive-text flow:

```text
S appears in a prefix sample
⇒ transport trimmed sample data to that prefix
⇒ exact reconstruction
⇒ Gold identification
```

---


### 2.45 `TrimmedPresentationFinalTheorem.lean`

Status: CI passed / user-confirmed.

Purpose:

Give stable final theorem names for the trimmed-presentation route.

Main contents:

```lean
TrimmedPresentationFinalData
TrimmedPresentationFinalData.toFinalReachableData
TrimmedPresentationFinalData.characteristic_sample
TrimmedPresentationFinalData.exact_for_positive_superset
TrimmedPresentationFinalData.exact_at_seen_prefix
TrimmedPresentationFinalData.prefix_exact_eventually
TrimmedPresentationFinalData.identifies_from_positive_text
trimmed_presentation_reachable_identification
trimmed_presentation_reachable_prefix_exact
trimmed_presentation_exact_for_positive_superset
```

Paper correspondence:

This makes the route

```text
TrimmedPresentationSampleData
+
NamedContextSplicingConstructor
+
fanout
+
fixed-observation promise
⇒ FinalReachableData
```

available under stable top-level theorem names.

---

### 2.46 `CharacteristicSampleFromTrimmedPresentation.lean`

Status: CI passed / user-confirmed.

Purpose:

Package the finite characteristic-sample object attached to trimmed pre-core data.

Main contents:

```lean
TrimmedPresentationCharacteristicSample
TrimmedPresentationCharacteristicSample.toSampleData
TrimmedPresentationCharacteristicSample.toWitnessSample
TrimmedPresentationCharacteristicSample.toFinalData
TrimmedPresentationCharacteristicSample.toFinalReachableData
TrimmedPresentationCharacteristicSample.characteristic_sample
TrimmedPresentationCharacteristicSample.exact_for_positive_superset
TrimmedPresentationCharacteristicSample.prefix_exact_eventually
TrimmedPresentationCharacteristicSample.identifies_from_positive_text
```

Paper correspondence:

This names the future `CS(G̃₀)`-like sample: it must contain anchor, terminal, binary, start, and distinguished start-word witnesses.

---

### 2.47 `CharacteristicSampleWitnessSet.lean`

Status: CI passed / user-confirmed.

Purpose:

Separate the set of required witness words from any particular finite sample.

Main contents:

```lean
TrimmedPresentationWitnessWordSet
TrimmedPresentationWitnessWordSet.anchor_mem
TrimmedPresentationWitnessWordSet.terminal_mem
TrimmedPresentationWitnessWordSet.binary_mem
TrimmedPresentationWitnessWordSet.start_mem
TrimmedPresentationWitnessWordSet.startWord_mem
TrimmedPresentationWitnessSample
TrimmedPresentationWitnessSample.toSampleData
TrimmedPresentationWitnessSample.toCharacteristicSample
trimmed_witness_sample_reachable_identification
trimmed_witness_sample_reachable_prefix_exact
```

Paper correspondence:

The future characteristic sample only has to be a finite positive set containing this witness set.

---

### 2.48 `CharacteristicSampleWitnessSetMonotone.lean`

Status: CI passed / user-confirmed.

Purpose:

Prove monotonicity of witness-sample data under positive finite sample extension.

Main contents:

```lean
TrimmedPresentationWitnessSample.mono
TrimmedPresentationWitnessSample.exact_after_mono
TrimmedPresentationWitnessSample.exact_at_prefix_via_mono
TrimmedPresentationWitnessSample.prefix_exact_via_mono
TrimmedPresentationWitnessSample.identifies_via_mono
main_reachable_identification_from_witness_sample_mono
main_reachable_prefix_exact_from_witness_sample_mono
```

Paper correspondence:

Once a prefix sample contains the witness words, every later positive prefix inherits the same reconstruction data.

---

### 2.49 `CharacteristicSampleFiniteBuilder.lean`

Status: CI passed / user-confirmed.

Purpose:

Introduce a finite-sample builder whose only construction obligation is containment of the witness-word set.

Main contents:

```lean
TrimmedPresentationFiniteSampleBuilder
TrimmedPresentationFiniteSampleBuilder.toWitnessSample
TrimmedPresentationFiniteSampleBuilder.toSampleData
TrimmedPresentationFiniteSampleBuilder.toCharacteristicSample
TrimmedPresentationFiniteSampleBuilder.anchor_mem
TrimmedPresentationFiniteSampleBuilder.terminal_mem
TrimmedPresentationFiniteSampleBuilder.binary_mem
TrimmedPresentationFiniteSampleBuilder.start_mem
TrimmedPresentationFiniteSampleBuilder.startWord_mem
```

Paper correspondence:

This is a compact interface for building `CS(G̃₀)` from a finite set.

---

### 2.50 `CharacteristicSampleFiniteUnionBuilder.lean`

Status: CI passed / user-confirmed.

Purpose:

Build the characteristic finite sample as a union of anchor, terminal, binary, start, and start-word components.

Main contents:

```lean
TrimmedPresentationFiniteUnionBuilder
TrimmedPresentationFiniteUnionBuilder.sample
TrimmedPresentationFiniteUnionBuilder.contains_witnesses
TrimmedPresentationFiniteUnionBuilder.toFiniteSampleBuilder
TrimmedPresentationFiniteUnionBuilder.Positive
TrimmedPresentationFiniteUnionBuilder.Positive.toWitnessSample
```

Paper correspondence:

This matches the paper-level picture of `CS(G̃₀)` as a union of finite witness families.

---

### 2.51 `CharacteristicSampleFiniteUnionPackage.lean`

Status: CI passed / user-confirmed.

Purpose:

Package a finite union builder together with positivity.

Main contents:

```lean
TrimmedPresentationPositiveFiniteUnionBuilder
TrimmedPresentationPositiveFiniteUnionBuilder.sample
TrimmedPresentationPositiveFiniteUnionBuilder.sample_positive
TrimmedPresentationPositiveFiniteUnionBuilder.contains_witnesses
TrimmedPresentationPositiveFiniteUnionBuilder.toFinalReachableData
TrimmedPresentationPositiveFiniteUnionBuilder.characteristic_sample
```

Paper correspondence:

This is the positive finite-union route to the final reachable theorem.

---

### 2.52 `CharacteristicSampleComponentPackage.lean`

Status: CI passed / user-confirmed.

Purpose:

Introduce component records for anchor, terminal, binary, and start witness families.

Main contents:

```lean
AnchorWitnessComponent
TerminalWitnessComponent
BinaryWitnessComponent
StartWitnessComponent
TrimmedPresentationComponentPackage
TrimmedPresentationComponentPackage.toPositiveFiniteUnionBuilder
TrimmedPresentationComponentPackage.toFinalReachableData
TrimmedPresentationComponentPackage.characteristic_sample
```

Paper correspondence:

This provides a modular way to prove each witness family separately.

---

### 2.53 `CharacteristicSampleComponentEnumeration.lean`

Status: CI passed / user-confirmed.

Purpose:

Build component packages from abstract finite indexed enumerations.

Main contents:

```lean
AnchorWitnessEnumeration
TerminalWitnessEnumeration
BinaryWitnessEnumeration
StartWitnessEnumeration
TrimmedPresentationComponentEnumeration
TrimmedPresentationComponentEnumeration.toComponentPackage
TrimmedPresentationComponentEnumeration.toFinalReachableData
trimmed_component_enumeration_reachable_identification
trimmed_component_enumeration_reachable_prefix_exact
```

Paper correspondence:

This reduces finite witness construction to supplying finite index sets and word functions.

---

### 2.54 `CharacteristicSampleRuleEnumeration.lean`

Status: CI passed / user-confirmed.

Purpose:

Specialize abstract indexed enumeration to grammar-rule-indexed witness families.

Main contents:

```lean
TerminalWitnessIndex
StartWitnessIndex
AnchorRuleEnumeration
TerminalRuleWitnessEnumeration
BinaryRuleWitnessEnumeration
StartRuleWitnessEnumeration
TrimmedPresentationRuleEnumeration
trimmed_rule_enumeration_reachable_identification
trimmed_rule_enumeration_reachable_prefix_exact
```

Paper correspondence:

This starts moving from abstract finite indices toward the actual rules of the grammar.

---

### 2.55 `CharacteristicSampleRuleCoverage.lean`

Status: CI passed / user-confirmed.

Purpose:

Separate finite coverage data from positivity data for rule-indexed enumeration.

Main contents:

```lean
AnchorRuleCoverage
TerminalRuleCoverage
BinaryRuleCoverage
StartRuleCoverage
AnchorRulePositivity
TerminalRulePositivity
BinaryRulePositivity
StartRulePositivity
TrimmedPresentationRuleCoveragePackage
```

Paper correspondence:

This isolates two tasks:

```text
finite rule/nonterminal coverage
positivity of the selected witness words
```

---

### 2.56 `CharacteristicSampleGrammarRuleBuilder.lean`

Status: CI passed / user-confirmed.

Purpose:

Use the grammar's own finite rule sets to build terminal, binary, and start witness components.

Main contents:

```lean
TrimmedPresentationGrammarRuleBuilder
TrimmedPresentationGrammarRuleBuilder.anchorSample
TrimmedPresentationGrammarRuleBuilder.terminalSample
TrimmedPresentationGrammarRuleBuilder.binarySample
TrimmedPresentationGrammarRuleBuilder.startSample
TrimmedPresentationGrammarRuleBuilder.toComponentPackage
trimmed_grammar_rule_builder_reachable_identification
trimmed_grammar_rule_builder_reachable_prefix_exact
```

Paper correspondence:

This is close to the actual finite construction: terminal, binary, and start samples come from `G.terminalRules`, `G.binaryRules`, and `G.startRules`.

---

### 2.57 `CharacteristicSampleGrammarRulePositivity.lean`

Status: CI passed / user-confirmed.

Purpose:

Remove redundant anchor-positivity assumptions from the grammar-rule builder.

Main contents:

```lean
TrimmedPresentationGrammarRuleData
TrimmedPresentationGrammarRuleData.anchor_positive
TrimmedPresentationGrammarRuleData.toGrammarRuleBuilder
trimmed_grammar_rule_data_reachable_identification
trimmed_grammar_rule_data_reachable_prefix_exact
```

Paper correspondence:

Anchor witness positivity follows from the trimmed pre-core itself, leaving only terminal/binary/start/startWord positivity as semantic obligations.

---

### 2.58 `CharacteristicSampleRuleWitnessTransport.lean`

Status: CI passed / user-confirmed.

Purpose:

Isolate the remaining semantic witness-positivity obligations.

Main contents:

```lean
TrimmedPresentationRuleAritySelectors
TrimmedPresentationRuleWitnessTransport
TrimmedPresentationGrammarRuleTransportData
trimmed_rule_transport_reachable_identification
trimmed_rule_transport_reachable_prefix_exact
```

Paper correspondence:

This collects the remaining semantic facts needed to prove terminal, binary, and start witness words are positive.

---

### 2.59 `CharacteristicSampleRuleTransportFinal.lean`

Status: CI passed / user-confirmed.

Purpose:

Give the rule-witness-transport route a final-data wrapper.

Main contents:

```lean
TrimmedPresentationRuleTransportFinalData
TrimmedPresentationRuleTransportFinalData.toFinalReachableData
TrimmedPresentationRuleTransportFinalData.characteristic_sample
TrimmedPresentationRuleTransportFinalData.exact_for_positive_superset
TrimmedPresentationRuleTransportFinalData.prefix_exact_eventually
TrimmedPresentationRuleTransportFinalData.identifies_from_positive_text
```

Paper correspondence:

This is the final endpoint for the route:

```text
base cover + arity selectors + witness transport + splicing/fanout/promise
⇒ reachable identification
```

---

### 2.60 `CharacteristicSampleContextTransport.lean`

Status: CI passed / user-confirmed.

Purpose:

Prove rule-witness transport from a strong same-context transport principle.

Main contents:

```lean
TrimmedPresentationSameContextTransport
TrimmedPresentationSameContextTransport.terminal_positive
TrimmedPresentationSameContextTransport.binary_positive
TrimmedPresentationSameContextTransport.start_positive
TrimmedPresentationContextTransportData
trimmed_context_transport_reachable_identification
trimmed_context_transport_reachable_prefix_exact
```

Paper correspondence:

This introduces the semantic principle:

```text
same named context + same observed type + one tuple accepted
⇒ the other tuple accepted
```

and shows it suffices for the characteristic-sample route.

---

### 2.61 `CharacteristicSampleExposingTransport.lean`

Status: CI passed / user-confirmed.

Purpose:

Weaken same-context transport to transport only through the exposing contexts `D.expose A`.

Main contents:

```lean
TrimmedPresentationExposingContextTransport
TrimmedPresentationExposingContextTransport.ofSameContextTransport
TrimmedPresentationExposingContextTransport.terminal_positive
TrimmedPresentationExposingContextTransport.binary_positive
TrimmedPresentationExposingContextTransport.start_positive
TrimmedPresentationExposingTransportData
trimmed_exposing_transport_reachable_identification
trimmed_exposing_transport_reachable_prefix_exact
```

Paper correspondence:

This identifies a much sharper remaining semantic target: transport only through the trimmed exposing contexts.

---

### 2.62 `CharacteristicSampleStartWordEvidence.lean`

Status: CI passed / user-confirmed.

Purpose:

Separate positivity of the distinguished start word from exposing-context transport.

Main contents:

```lean
TrimmedPresentationStartWordEvidence
TrimmedPresentationExposingTransportCoreData
TrimmedPresentationExposingTransportCoreData.withStartWord
trimmed_exposing_core_reachable_identification
trimmed_exposing_core_reachable_prefix_exact
```

Paper correspondence:

This splits the remaining semantic tasks into:

```text
exposing-context transport
startWord ∈ G.StringLanguage
```

---

### 2.63 `CharacteristicSampleExposingCoreFinal.lean`

Status: CI passed / user-confirmed.

Purpose:

Give the separated exposing-core route its final wrapper.

Main contents:

```lean
TrimmedPresentationExposingCoreFinalData
TrimmedPresentationExposingCoreFinalData.toExposingTransportData
TrimmedPresentationExposingCoreFinalData.toFinalReachableData
TrimmedPresentationExposingCoreFinalData.characteristic_sample
TrimmedPresentationExposingCoreFinalData.exact_for_positive_superset
TrimmedPresentationExposingCoreFinalData.prefix_exact_eventually
TrimmedPresentationExposingCoreFinalData.identifies_from_positive_text
```

Paper correspondence:

This is the stable endpoint for:

```text
exposing-context transport + start-word evidence + splicing/fanout/promise
⇒ reachable identification
```

---

### 2.64 `CharacteristicSampleStartWordFromSample.lean`

Status: CI passed / user-confirmed.

Purpose:

Extract start-word evidence from any positive finite sample containing `D.startWord`.

Main contents:

```lean
TrimmedPresentationStartWordSampleEvidence
TrimmedPresentationStartWordSampleEvidence.toStartWordEvidence
TrimmedPresentationSampleData.toStartWordEvidence
TrimmedPresentationWitnessSample.toStartWordEvidence
TrimmedPresentationCharacteristicSample.toStartWordEvidence
TrimmedPresentationFiniteSampleBuilder.toStartWordEvidence
```

Paper correspondence:

This makes the start-word obligation easy to discharge whenever the finite characteristic sample already contains `D.startWord`.

---

### 2.65 `CharacteristicSampleSameContextCore.lean`

Status: CI passed / user-confirmed.

Purpose:

Connect the stronger same-context transport principle to the separated exposing-core route.

Main contents:

```lean
TrimmedPresentationSameContextCoreData
TrimmedPresentationSameContextCoreData.toExposingTransportCoreData
TrimmedPresentationSameContextCoreData.toExposingCoreFinalData
TrimmedPresentationSameContextCoreData.exact_for_positive_superset
TrimmedPresentationSameContextCoreData.prefix_exact_eventually
TrimmedPresentationSameContextCoreData.identifies_from_positive_text
```

Paper correspondence:

This gives a stable entry point if same-context transport is proved first.

---

### 2.66 `CharacteristicSampleAnchorDistributionTransport.lean`

Status: CI passed / user-confirmed.

Purpose:

Bridge anchor distributional equivalence to exposing-context transport.

Main contents:

```lean
TrimmedPresentationAnchorDistributionTransport
TrimmedPresentationAnchorDistributionTransport.exposing_accepts
TrimmedPresentationAnchorDistributionTransport.toExposingContextTransport
TrimmedPresentationAnchorDistributionCoreData
trimmed_anchor_distribution_core_reachable_identification
trimmed_anchor_distribution_core_reachable_prefix_exact
```

Paper correspondence:

This expresses the target:

```text
D.anchor A and x are distributionally equivalent
⇒ D.expose A accepts x
```

which is close to the paper's distribution-based semantics.

---

### 2.67 `CharacteristicSampleAnchorCommonContext.lean`

Status: CI passed / user-confirmed.

Purpose:

Build anchor distributional equivalence from common accepting contexts.

Main contents:

```lean
TrimmedPresentationAnchorCommonContextEvidence
TrimmedPresentationAnchorCommonContextEvidence.toDistributionalEquivalent
TrimmedPresentationAnchorCommonContextTransport
TrimmedPresentationAnchorCommonContextTransport.toAnchorDistributionTransport
TrimmedPresentationAnchorCommonContextCoreData
trimmed_anchor_common_context_core_reachable_identification
trimmed_anchor_common_context_core_reachable_prefix_exact
```

Paper correspondence:

This uses the existing lemma:

```lean
fixedNamedDistributionalEquivalent_of_common_context
```

to connect common accepting contexts with distributional equivalence under fixed-observation substitutability.

---

### 2.68 `CharacteristicSampleExposingAsCommonContext.lean`

Status: CI passed / user-confirmed.

Purpose:

Show that exposing-context transport supplies common-context evidence by using `D.expose A` itself as the common context.

Main contents:

```lean
TrimmedPresentationExposingAsCommonContext
TrimmedPresentationExposingAsCommonContext.commonEvidence
TrimmedPresentationExposingAsCommonContext.toAnchorCommonContextTransport
TrimmedPresentationExposingCommonCoreData
trimmed_exposing_common_core_reachable_identification
trimmed_exposing_common_core_reachable_prefix_exact
```

Paper correspondence:

This connects the direct exposing-transport route and the common-context/distribution route.

---

### 2.69 `CharacteristicSampleTransportInterfaceDiagram.lean`

Status: CI passed / user-confirmed.

Purpose:

Record the conversion diagram among transport interfaces.

Main contents:

```lean
TrimmedPresentationTransportDiagram.sameContext_to_exposing
TrimmedPresentationTransportDiagram.exposing_to_exposingAsCommon
TrimmedPresentationTransportDiagram.exposingAsCommon_to_common
TrimmedPresentationTransportDiagram.common_to_anchorDistribution
TrimmedPresentationTransportDiagram.anchorDistribution_to_exposing
TrimmedPresentationTransportDiagram.exposing_roundTrip
TrimmedPresentationTransportDiagram.sameContext_roundTrip_to_exposing
```

Paper correspondence:

This records the transport-interface map:

```text
SameContextTransport
⇒ ExposingContextTransport
⇒ ExposingAsCommonContext
⇒ AnchorCommonContextTransport
⇒ AnchorDistributionTransport
⇒ ExposingContextTransport
```

---

### 2.70 `CharacteristicSampleAnchorCommonContextFinal.lean`

Status: CI passed / user-confirmed. Latest named CI point: Lean CI #558, commit `f1bf7fa`.

Purpose:

Give the common-context route its own final-data wrapper.

Main contents:

```lean
TrimmedPresentationAnchorCommonContextFinalData
TrimmedPresentationAnchorCommonContextFinalData.toAnchorDistributionCoreData
TrimmedPresentationAnchorCommonContextFinalData.toExposingTransportCoreData
TrimmedPresentationAnchorCommonContextFinalData.toExposingCoreFinalData
TrimmedPresentationAnchorCommonContextFinalData.toFinalReachableData
TrimmedPresentationAnchorCommonContextFinalData.characteristic_sample
TrimmedPresentationAnchorCommonContextFinalData.exact_for_positive_superset
TrimmedPresentationAnchorCommonContextFinalData.prefix_exact_eventually
TrimmedPresentationAnchorCommonContextFinalData.identifies_from_positive_text
trimmed_anchor_common_context_final_reachable_identification
trimmed_anchor_common_context_final_reachable_prefix_exact
trimmed_anchor_common_context_final_exact_for_positive_superset
```

Paper correspondence:

This is the stable endpoint for:

```text
common accepting context evidence
+
start-word evidence
+
NamedContextSplicingConstructor
+
fanout
+
fixed-observation substitutability
⇒ reachable identification / prefix exactness / positive-superset exactness
```

---

## 3. Overall dependency chain

Current import chain:

```text
Basic
  ↓
ExactOnce
  ↓
OutputTypeRefinement
  ↓
OutputTypeLift
  ↓
DistributionalEquivalence
  ↓
FillingIdentity
  ↓
WitnessedComposition
  ↓
LearnerSoundnessCore
  ↓
LearnerDerivationSoundness
  ↓
ConcreteLearnerEvidence
  ↓
StartRuleSoundness
  ↓
CompletenessSkeleton
  ↓
CharacteristicSampleSkeleton
  ↓
ExactReconstructionSkeleton
  ↓
GoldIdentificationSkeleton
  ↓
FiniteTextCoverage
  ↓
ReachableStartBridge
  ↓
ReachableGoldTheorem
  ↓
CharacteristicDataMonotone
  ↓
StartAnchorCanonical
  ↓
PrefixExactReconstruction
  ↓
MainReachableTheorem
  ↓
CharacteristicSamplePackage
  ↓
CharacteristicSampleBuilderSkeleton
  ↓
BlueprintFiniteSample
  ↓
FillingIdentityConstructionSkeleton
  ↓
NamedContextSplicingSkeleton
  ↓
BinaryRuleSplicingEvidence
  ↓
NamedContextSplicingConstructor
  ↓
SplicingMainTheorem
  ↓
SplicingMainDataMonotone
  ↓
SplicingCharacteristicPackage
  ↓
SplicingBlueprint
  ↓
SplicingBlueprintMainData
  ↓
SplicingBlueprintMainDataMonotone
  ↓
FinalReachableTheorem
  ↓
OutputTypeRefinementPresentation
  ↓
OutputTypePresentationLanguage
  ↓
OutputTypePresentationMonotone
  ↓
OutputTypePresentationCompleteness
  ↓
OutputTypeTrimmedPresentationSkeleton
  ↓
TrimmedPresentationPreCore
  ↓
TrimmedPresentationSample
  ↓
TrimmedPresentationSampleMonotone
  ↓
TrimmedPresentationFinalTheorem
  ↓
CharacteristicSampleFromTrimmedPresentation
  ↓
CharacteristicSampleWitnessSet
  ↓
CharacteristicSampleWitnessSetMonotone
  ↓
CharacteristicSampleFiniteBuilder
  ↓
CharacteristicSampleFiniteUnionBuilder
  ↓
CharacteristicSampleFiniteUnionPackage
  ↓
CharacteristicSampleComponentPackage
  ↓
CharacteristicSampleComponentEnumeration
  ↓
CharacteristicSampleRuleEnumeration
  ↓
CharacteristicSampleRuleCoverage
  ↓
CharacteristicSampleGrammarRuleBuilder
  ↓
CharacteristicSampleGrammarRulePositivity
  ↓
CharacteristicSampleRuleWitnessTransport
  ↓
CharacteristicSampleRuleTransportFinal
  ↓
CharacteristicSampleContextTransport
  ↓
CharacteristicSampleExposingTransport
  ↓
CharacteristicSampleStartWordEvidence
  ↓
CharacteristicSampleExposingCoreFinal
  ↓
CharacteristicSampleStartWordFromSample
  ↓
CharacteristicSampleSameContextCore
  ↓
CharacteristicSampleAnchorDistributionTransport
  ↓
CharacteristicSampleAnchorCommonContext
  ↓
CharacteristicSampleExposingAsCommonContext
  ↓
CharacteristicSampleTransportInterfaceDiagram
  ↓
CharacteristicSampleAnchorCommonContextFinal
```

This linear chain is intentional. It keeps CI failures local and makes the experiment traceable.

---

## 4. What is genuinely verified so far?

The following are genuinely Lean-checked:

### 4.1 Fixed-observation refinement

```text
If obs' refines obs, then fixed tuple-substitutability for obs implies fixed tuple-substitutability for obs'.
```

### 4.2 Output-type invariants

```text
Template evaluation preserves output types.
Binary rules compute parent output types from child output types.
Ordinary derivations lift canonically to output-typed wrappers.
```

### 4.3 Distributional equivalence

```text
same output type + shared accepting context
⇒ distributional equivalence
```

under the fixed-observation substitutability promise.

### 4.4 Witnessed composition

```text
child equivalence + filling identities + parent acceptance
⇒ parent equivalence
```

### 4.5 Learner soundness skeleton

```text
sample-level unit/binary evidence
+
positive sample
+
target promise
⇒ sample-level learner derivations are sound
⇒ sample-level string derivations generate only target strings.
```

### 4.6 Completeness induction skeleton

```text
if characteristic sample data gives rule-by-rule anchor simulation,
then target derivations are learner-reachable from anchors.
```

### 4.7 Finite text coverage

```text
finite S ⊆ L
+
T is a positive text for L
⇒ S appears in all sufficiently late prefix samples of T.
```

### 4.8 Reachable exact reconstruction

```text
CharacteristicSampleData
+
StartAnchorCanonical
+
positive finite sample
+
target promise
⇒ ReachableSampleStringLanguage K obs f = G.StringLanguage.
```

### 4.9 Reachable Gold identification

```text
ReachableCharacteristicPackage
+
global target assumptions
⇒ reachable learner identifies the target from every positive text.
```

### 4.10 Blueprint-to-main theorem bridge

```text
ReachableCharacteristicBlueprint
⇒ ReachableCharacteristicPackage
⇒ ReachableMainData
⇒ main reachable identification theorem.
```


### 4.11 Splicing-constructor reduction

```text
binary filling witnesses
⇐ named-context splicing families
⇐ binary-rule splicing evidence
⇐ universal NamedContextSplicingConstructor
```

The remaining context-splicing construction is now isolated in one clean interface.

### 4.12 Final reachable theorem names

```text
FinalReachableData
⇒ final_reachable_identification
⇒ final_reachable_prefix_exact
⇒ final_reachable_exact_for_positive_superset
```

The reachable-model endpoint now has stable names suitable for paper/roadmap references.

### 4.13 Finite typed presentation soundness

```text
PresentationDerives P X x
⇒ OutputTypedDerives X x
⇒ DerivesTuple G X.base x
```

and at string level:

```text
PresentationStringLanguage P ⊆ G.StringLanguage
```

### 4.14 Finite typed presentation monotonicity

```text
PresentationExtends P Q
⇒ PresentationStringLanguage P ⊆ PresentationStringLanguage Q
```

This is verified for typed nonterminals, terminal rules, binary rules, and start rules.


### 4.15 Finite typed presentation completeness interface

```text
PresentationCompleteFor P
:= G.StringLanguage ⊆ PresentationStringLanguage P
```

and therefore:

```text
PresentationCompleteFor P
⇒ PresentationStringLanguage P = G.StringLanguage
```

This is an interface theorem; the actual proof that a constructed `G^h` / `G̃₀` satisfies it remains future work.

### 4.16 Trimmed-presentation witness skeleton

```text
CompleteOutputTypePresentation
+
anchor/expose witnesses for present typed nonterminals
⇒ TrimmedOutputTypePresentation
```

The skeleton now carries accepted exposed words and typed output matching for anchors.

### 4.17 Descent from typed representatives to base pre-core

```text
TrimmedBaseRepresentatives
+
terminal/binary/start type equalities
⇒ TrimmedPresentationPreCoreData
⇒ ReachableBlueprintPreCore
```

This is the first bridge from typed presentation data to the base-indexed interface used by the reachable theorem.

### 4.18 Trimmed sample data to final reachable data

```text
TrimmedPresentationSampleData
+
NamedContextSplicingConstructor
+
fanout
+
fixed-observation promise
⇒ FinalReachableData
⇒ reachable Gold identification
```

This is a major narrowing of the remaining `CS(G̃₀)` construction task.




### 4.19 Characteristic witness set and finite-builder route

```text
TrimmedPresentationWitnessWordSet
+
positive finite sample containing it
⇒ TrimmedPresentationWitnessSample
⇒ TrimmedPresentationCharacteristicSample
⇒ FinalReachableData
```

This verifies the abstract `CS(G̃₀)` route up to the point where a concrete finite set still has to be constructed.

### 4.20 Componentwise and rule-indexed characteristic sample construction

```text
component packages
+
indexed enumerations
+
rule-indexed finite coverage
⇒ positive finite witness sample
⇒ reachable Gold identification
```

This is verified as plumbing.  The actual concrete enumeration of the refined/trimmed grammar is still future work.

### 4.21 Grammar-rule sample builder

```text
finite base-nonterminal cover
+
G.terminalRules / G.binaryRules / G.startRules
+
arity selectors
+
witness positivity
⇒ characteristic sample route
```

Anchor witness positivity is now discharged from the trimmed pre-core itself.

### 4.22 Semantic witness-transport interfaces

The following routes are verified as interfaces:

```text
SameContextTransport
⇒ ExposingContextTransport
⇒ RuleWitnessTransport
⇒ FinalReachableData
```

and

```text
AnchorCommonContextTransport
⇒ AnchorDistributionTransport
⇒ ExposingContextTransport
⇒ RuleWitnessTransport
⇒ FinalReachableData
```

The files do not yet prove the semantic transport facts from the concrete `G̃₀`; they isolate exactly what must be proved.

### 4.23 Common-context final route

```text
TrimmedPresentationAnchorCommonContextFinalData
⇒ characteristic sample
⇒ exact reconstruction on positive supersets
⇒ eventual prefix-exact reconstruction
⇒ reachable Gold identification
```

This is the latest verified endpoint as of Lean CI #558.


---

## 5. What remains as explicit assumptions or skeleton fields?

The main explicit assumptions/skeleton records are now:

### 5.1 `NamedContextSplicingConstructor`

This remains the cleanest abstraction around filling identities.

It currently assumes:

```text
for every parent named context E and binary template ρ,
there is a BinaryNamedContextSplicing E ρ
```

Need later:

```text
Concrete construction of the left and right child named contexts,
including component order, empty components, and cast bookkeeping.
```

This still supersedes direct manipulation of `LeftFillingIdentity` / `RightFillingIdentity`.

---

### 5.2 `PresentationCompleteFor` for the actual refined/trimmed presentation

The completeness interface now exists, but the actual construction theorem is not yet proved.

Need later:

```text
construct G^h or G̃₀ as a finite typed presentation P
prove PresentationCompleteFor P
```

The current file proves:

```text
PresentationCompleteFor P
⇒ PresentationStringLanguage P = G.StringLanguage
```

but not that the concrete presentation satisfies `PresentationCompleteFor`.

---

### 5.3 `TrimmedOutputTypePresentation`

The skeleton now exists.

Need later:

```text
derive the complete finite presentation from the actual output-type refinement
prove present typed nonterminals have the required anchor/expose witnesses
connect trimming/productivity/reachability to those witnesses
```

---

### 5.4 `TrimmedPresentationPreCoreData`

This bridges typed representatives to base-indexed pre-core data.

Need later:

```text
derive the base representatives systematically from the trimmed presentation
prove terminal/binary/start type equalities from typed rule data rather than assuming them as fields
```

---

### 5.5 `TrimmedPresentationSampleData`

This narrows the future characteristic sample construction.

Need later:

```text
define CS(G̃₀) as a finite set of witness words
prove it contains:
  anchorWitnessWord
  terminalWitnessWord
  binaryWitnessWord
  startWitnessWord
  startWord
prove positivity of that finite set
```

Once this is available, the current pipeline already gives `FinalReachableData`.

---

### 5.6 Semantic transport obligations

The characteristic-sample construction has now isolated the main semantic transport tasks.

Important interfaces:

```lean
TrimmedPresentationExposingContextTransport
TrimmedPresentationAnchorCommonContextTransport
TrimmedPresentationAnchorDistributionTransport
TrimmedPresentationSameContextTransport
```

The most concrete current targets are:

```text
ExposingContextTransport:
  for every A and tuple x of the same observed type as D.anchor A,
  D.expose A accepts x.

AnchorCommonContextTransport:
  for every A and same-type tuple x,
  find one common named context accepting both D.anchor A and x.
```

The files through CI #558 prove that any of these routes is enough to obtain the final reachable theorem, but the concrete derivation of these transport facts from the constructed trimmed presentation remains future work.

---

### 5.7 Concrete learner equivalence

The current theorem is still for:

```lean
ReachableSampleStringLanguage K obs f
```

Need later:

```text
Define the actual finite canonical learner grammar/relation and prove its language equals,
or is at least extensionally equivalent to, ReachableSampleStringLanguage K obs f.
```

---

### 5.8 Polynomial and boundary results

Still not verified:

```text
polynomial-time construction bound
no-advice non-identifiability
copy-language / member-kernel exclusion
```

These are separate from the core reachable identification proof.

---

## 6. Immediate next files

Current immediate status:

```text
CharacteristicSampleAnchorCommonContextFinal.lean has passed Lean CI #558. Commit: f1bf7fa.
```

Current useful CI/local command:

```bash
lake build LeanCfgProject.MCFG.CharacteristicSampleAnchorCommonContextFinal
```

Recommended next file:

### 6.1 `TrimmedPresentationFinalTheorem.lean`

Goal:

Give stable final names for the current trimmed-presentation route.

Expected theorem shape:

```lean
TrimmedPresentationSampleData D S
+
NamedContextSplicingConstructor α
+
G.FanoutAtMost f
+
FixedNamedTupleSubstitutable f obs G.StringLanguage
⇒ final_reachable_identification
```

This would be a naming/package file analogous to `FinalReachableTheorem.lean`, but starting from the trimmed-presentation data.

---

### 6.2 `CharacteristicSampleFromTrimmedPresentation.lean`

Goal:

Define a finite set of witness words associated to `TrimmedPresentationPreCoreData`.

Expected first construction:

```lean
anchorWitnessWord
terminalWitnessWord
binaryWitnessWord
startWitnessWord
startWord
```

collected into a finite set, probably requiring finite lists/enumerations of base nonterminals and grammar rules.

This starts the real `CS(G̃₀)` construction.

---

### 6.3 `NamedContextSplicingConstruction.lean`

Goal:

Start proving the actual `NamedContextSplicingConstructor`.

Expected first move:

```text
define raw operations for substituting a binary template into one hole
construct left and right child contexts
prove the corresponding namedFill equations
```

This remains bookkeeping-heavy and should be split into small files.

---

### 6.4 `ConcreteCanonicalLearnerRelation.lean`

Goal:

Define the actual learner relation generated by enumerated sample evidence.

Recommended order:

```text
1. relation first
2. grammar object later
3. prove equivalence with ReachableSampleStringLanguage
```

---

## 7. Medium-term roadmap toward the paper theorem

### Stage A: Reachable main theorem

Status: verified under final blueprint/data assumptions.

Endpoint:

```lean
final_reachable_identification
final_reachable_prefix_exact
final_reachable_exact_for_positive_superset
```

Current theorem shape:

```lean
FinalReachableData G S obs f
⇒ reachable learner identifies G.StringLanguage from every positive text.
```

This stage is the strongest verified result so far.

---

### Stage B: Presentation-level output-type refinement

Status: interface layer mostly in place.

Verified:

```text
finite typed presentation derivations erase to original grammar derivations
presentation string language is sound
presentation extension is monotone
presentation completeness interface gives language equality
```

Still needed:

```text
actual construction of G^h / G̃₀ as a finite typed presentation
proof that the constructed presentation satisfies PresentationCompleteFor
```

---

### Stage C: Trimmed-presentation route to the final reachable theorem

Status: substantially scaffolded.

Verified / scaffolded:

```text
TrimmedOutputTypePresentation
TrimmedBaseRepresentatives
TrimmedPresentationPreCoreData
TrimmedPresentationSampleData
TrimmedPresentationSampleData ⇒ FinalReachableData
component/rule-indexed characteristic sample routes ⇒ FinalReachableData
common-context transport route ⇒ FinalReachableData
```

Pending:

```text
stable final trimmed theorem names
concrete construction of the finite sample CS(G̃₀)
concrete proof of exposing/common-context transport facts
```

---

### Stage D: Construct the blueprint from `CS(G̃₀)`

Files to create or continue:

```text
CharacteristicSampleFromTrimmedPresentation.lean
SplicingBlueprintFromPresentation.lean
FinalDataFromCharacteristicSample.lean
```

Target theorem shape:

```lean
CS(G̃₀) constructed from the trimmed output-type presentation
⇒ TrimmedPresentationSampleData
⇒ FinalReachableData
```

---

### Stage E: Concrete learner equivalence

Files to create:

```text
TupleOccurrences.lean
BinaryWitnesses.lean
CanonicalLearnerRelation.lean
CanonicalLearnerSoundComplete.lean
```

Target theorem shape:

```lean
language of the concrete canonical learner relation
=
ReachableSampleStringLanguage K obs f
```

or a pair of inclusions if equality is too strict at first.

---

### Stage F: Polynomial bound

Files to create:

```text
OccurrenceCounting.lean
WitnessCounting.lean
PolynomialConstructionBound.lean
```

Target theorem shape:

```lean
for fixed f and fixed h,
learner hypothesis from K is constructible in ||K||_+^{O(f)}
```

This may remain partially informal unless a complexity framework is introduced.

---

### Stage G: Boundary results

Files to create:

```text
ObservationAdviceBoundary.lean
MemberKernelExclusion.lean
CopyLanguageBoundary.lean
```

Target theorem directions:

```text
bounded observation families compile by product morphism
unbounded union over all finite observations is not identifiable
member-kernel criterion excludes copy language from finite-observation fibers
```

These are mathematically separate from the learner construction and can be formalized later.

---

## 8. Trust map

### Strongly verified now

```text
typed observation algebra
output-type local invariants
distributional equivalence lemmas
witnessed composition semantic core
sample-level soundness
completeness induction skeleton
finite text coverage
reachable exact reconstruction
reachable Gold identification
splicing/blueprint/main theorem plumbing
FinalReachableData endpoint
finite typed-presentation soundness
finite typed-presentation monotonicity
finite typed-presentation completeness interface
trimmed-presentation witness skeleton
typed-to-base pre-core bridge
trimmed sample data to FinalReachableData
```

### Verified but intentionally abstract

```text
universal named-context splicing constructor
sample binary evidence
start-anchor canonical bridge
reachable splicing blueprint
reachable sample language model
actual completeness of the constructed G^h / G̃₀ presentation
concrete CS(G̃₀) membership proofs
```

### Not yet verified

```text
actual concrete learner enumeration
actual characteristic sample construction as a concrete finite set from G̃₀
trimmed output-type refinement as a concrete finite grammar/presentation
concrete exposing/common-context transport proof for the trimmed presentation
concrete named-context splicing construction
concrete filling-identity construction as a theorem
polynomial bound
boundary examples and non-identifiability
```

---

## 9. Notes on the old zip experiment

The old zip was useful as a source of design ideas, especially for:

```text
fixed observation definitions
named sentence contexts
MCFG syntax and derivations
output-type refinement
learner distribution/unit closure ideas
```

However, the new experiment should not directly trust or import the old terminal chain, because:

```text
old Basic.lean was a large import endpoint
some files corresponded to older paper versions
some later files encoded experimental assumptions too early
CI success of a mega-import does not isolate which proof layer is reliable
```

Recommended policy:

```text
Use old files as references.
Copy only small ideas.
Re-prove every layer in the new chain.
Keep each new file small and CI-confirmed.
```

---

## 10. Current recommended next command

Latest confirmed command/CI target:

```bash
lake build LeanCfgProject.MCFG.CharacteristicSampleAnchorCommonContextFinal
```

Latest confirmed CI point:

```text
Lean CI #558
Commit: f1bf7fa
```

Recommended next file:

### 10.1 `CharacteristicSampleTransportObligations.lean`

Goal:

Collect the current remaining semantic obligations in one theorem-facing package.

Expected contents:

```lean
TrimmedPresentationTransportObligations
  exposingTransport : TrimmedPresentationExposingContextTransport D
  startEvidence : TrimmedPresentationStartWordEvidence D
```

or alternatively:

```lean
TrimmedPresentationCommonContextObligations
  commonContext : TrimmedPresentationAnchorCommonContextTransport D
  startEvidence : TrimmedPresentationStartWordEvidence D
```

Expected purpose:

```text
state the cleanest remaining theorem target:
transport obligations + splicing constructor + fanout + promise
⇒ final reachable identification.
```

This would be mostly a naming/roadmap file, but useful before attempting the harder semantic proof.

---

### 10.2 `CharacteristicSampleStartWordFromStartAnchor.lean`

Goal:

Try to derive `TrimmedPresentationStartWordEvidence` from existing start-anchor / start-word fields.

Expected purpose:

```text
reduce or eliminate the separate startWord positivity obligation
when it is already carried by a sample package or by a start derivation witness.
```

This may be safer than attacking exposing-context transport directly.

---

### 10.3 `CharacteristicSampleExposingTransportConstruction.lean`

Goal:

Start the actual semantic proof of `TrimmedPresentationExposingContextTransport`.

Expected first move:

```text
for fixed A and x with tupleType obs (D.anchor A) = tupleType obs x,
identify the common/exposing context and invoke fixed-observation substitutability.
```

This is the mathematical hard point now isolated by the CI #558 chain.

---

### 10.4 `NamedContextSplicingConstruction.lean`

Goal:

Start proving the actual `NamedContextSplicingConstructor`.

Expected first move:

```text
define raw operations for substituting a binary template into one hole
construct left and right child contexts
prove the corresponding namedFill equations
```

This remains bookkeeping-heavy and should be split into small files.

---

Recommended order:

```text
1. CharacteristicSampleTransportObligations.lean
2. CharacteristicSampleStartWordFromStartAnchor.lean
3. CharacteristicSampleExposingTransportConstruction.lean
4. NamedContextSplicingConstruction.lean
5. ConcreteCanonicalLearnerRelation.lean
```
