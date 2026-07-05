# FORMALIZATION_MCFG

Lean formalization log and roadmap for the MCFG fixed finite-observation paper.

Last updated: 2026-07-05  
Current confirmed CI point: Lean CI #527, commit `c83ea95`, pushed by `growupkuriyama-hub`.

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

At the current stage, the development has a verified reachable-model main theorem. It is not yet the fully concrete canonical learner theorem from the paper, but it is now much closer than the earlier skeleton: soundness, reachable exact reconstruction, finite-text coverage, and Gold identification have all been connected.

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
```

All of the above files have passed Lean CI up to:

```text
Lean CI #527
Commit: c83ea95
```

The current state is best described as:

```text
reachable main theorem: stabilized under FinalReachableData
splicing/blueprint layer: packaged up to a flat construction target
context-splicing task: isolated as NamedContextSplicingConstructor
finite typed presentation layer: introduced, with language soundness and monotonicity
concrete canonical learner enumeration: still not yet formalized
actual construction from G̃₀ / CS(G̃₀): still not yet formalized
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
```

What has **not** yet been fully formalized:

```text
concrete finite canonical learner enumeration
explicit tuple-occurrence and binary-witness enumeration
actual construction of NamedContextSplicingConstructor
actual construction of CS(G̃₀)
trimmed output-type refinement G̃₀ as a concrete finite presentation/grammar object
proof that CS(G̃₀) gives ReachableSplicingBlueprint / FinalReachableData
completeness of finite output-type presentations for the original grammar language
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


---

## 5. What remains as explicit assumptions or skeleton fields?

The main explicit assumptions/skeleton records are now:

### 5.1 `NamedContextSplicingConstructor`

This is the cleanest remaining abstraction around filling identities.

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

This now supersedes the older direct focus on `LeftFillingIdentity` / `RightFillingIdentity`.

---

### 5.2 `ReachableSplicingBlueprint`

This is now the preferred finite construction target.

Need later:

```text
Build its fields from the actual trimmed output-type presentation G̃₀ and CS(G̃₀):
  anchor
  expose
  terminal_type_eq
  binary_type_eq
  start_type_eq
  sample membership facts
  startWord
  start_arity
  start_anchor_eq
  splicingConstructor
```

---

### 5.3 `FinalReachableData`

This is the stable wrapper for the current reachable theorem.

It is verified that:

```text
FinalReachableData
⇒ final_reachable_identification
⇒ final_reachable_prefix_exact
```

Need later:

```text
construct FinalReachableData from the actual finite characteristic sample.
```

---

### 5.4 Finite output-type presentation completeness

The presentation layer currently verifies soundness and monotonicity:

```text
PresentationStringLanguage P ⊆ G.StringLanguage
PresentationExtends P Q ⇒ PresentationStringLanguage P ⊆ PresentationStringLanguage Q
```

Need later:

```text
conditions ensuring G.StringLanguage ⊆ PresentationStringLanguage P
```

Probably this should be packaged as a completeness/lift assumption first, then connected to `G^h` / `G̃₀`.

---

### 5.5 Concrete learner equivalence

The current theorem is for:

```lean
ReachableSampleStringLanguage K obs f
```

Need later:

```text
Define the actual finite canonical learner grammar/relation and prove its language equals,
or is at least extensionally equivalent to, ReachableSampleStringLanguage K obs f.
```

---

### 5.6 Concrete characteristic sample construction

Still not done:

```text
tuple occurrences in sample words
binary witness segmentation
presentation-relative CS(G̃₀)
proof that CS(G̃₀) supplies the fields of ReachableSplicingBlueprint
```

---

## 6. Immediate next files

Recommended next step:

### 6.1 `OutputTypePresentationCompleteness.lean`

Goal:

Package the missing completeness direction for a finite typed presentation.

Expected theorem shape:

```lean
PresentationCompleteFor G P
⇒ G.StringLanguage ⊆ PresentationStringLanguage P
```

and therefore, together with already verified soundness:

```lean
PresentationStringLanguage P = G.StringLanguage
```

This should initially be an assumption/record interface, not the full construction of `G^h`.

---

### 6.2 `OutputTypeTrimmedPresentationSkeleton.lean`

Goal:

Represent a trimmed finite presentation `G̃₀`.

Possible fields:

```text
presentation P
productive witnesses / anchors
reachable or exposing witnesses / contexts
start coverage
presentation completeness
```

This should eventually connect the finite typed-presentation layer to `ReachableSplicingBlueprint`.

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

This is bookkeeping-heavy and should probably be split into several small files.

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

Status: started.

Verified:

```text
finite typed presentation derivations erase to original grammar derivations
presentation string language is sound
presentation extension is monotone
```

Next target:

```text
presentation completeness interface
trimmed presentation skeleton
```

---

### Stage C: Construct the blueprint from `CS(G̃₀)`

Files to create or continue:

```text
OutputTypePresentationCompleteness.lean
OutputTypeTrimmedPresentationSkeleton.lean
CharacteristicSampleConstruction.lean
SplicingBlueprintFromPresentation.lean
```

Target theorem shape:

```lean
CS(G̃₀) constructed from the trimmed output-type presentation
⇒ ReachableSplicingBlueprint G CS obs f
⇒ FinalReachableData G CS obs f
```

---

### Stage D: Concrete learner equivalence

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

### Stage E: Polynomial bound

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

### Stage F: Boundary results

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
```

### Verified but intentionally abstract

```text
universal named-context splicing constructor
sample binary evidence
start-anchor canonical bridge
reachable splicing blueprint
reachable sample language model
finite typed-presentation completeness
```

### Not yet verified

```text
actual concrete learner enumeration
actual characteristic sample construction
trimmed output-type refinement as finite presentation/grammar
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

After the latest confirmed file, the useful CI/local command is:

```bash
lake build LeanCfgProject.MCFG.OutputTypePresentationMonotone
```

Next proposed file:

```text
OutputTypePresentationCompleteness.lean
```

Expected purpose:

```text
package the assumption that a finite typed presentation is complete for G,
then prove PresentationStringLanguage P = G.StringLanguage from completeness + soundness.
```

Alternative next file:

```text
OutputTypeTrimmedPresentationSkeleton.lean
```

Expected purpose:

```text
start representing the trimmed output-type presentation G̃₀,
with anchors/productivity/exposing-context data separated from global assumptions.
```

Recommended order:

```text
1. OutputTypePresentationCompleteness.lean
2. OutputTypeTrimmedPresentationSkeleton.lean
3. NamedContextSplicingConstruction.lean
4. SplicingBlueprintFromPresentation.lean
```
