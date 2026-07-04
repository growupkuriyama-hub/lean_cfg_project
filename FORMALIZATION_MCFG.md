# FORMALIZATION_MCFG

Lean formalization log and roadmap for the MCFG fixed finite-observation paper.

Last updated: 2026-07-04  
Current confirmed CI point: Lean CI #511, commit `ad9754b`, pushed by `growupkuriyama-hub`.

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
```

All of the above files have passed Lean CI up to:

```text
Lean CI #511
Commit: ad9754b
```

The current state is best described as:

```text
soundness side: strong skeleton, largely formalized
completeness side: rule-simulation skeleton formalized
reachable exact reconstruction: packaged as a main theorem
Gold identification: finite characteristic package ⇒ eventual correctness verified
characteristic sample construction: now has a blueprint target, but not yet constructed from G̃₀
concrete canonical learner enumeration: still not yet formalized
```

Most important progress since CI #502:

```text
FiniteTextCoverage.lean removed the explicit EventuallyContains assumption.
ReachableStartBridge.lean replaced the old ReconstructionBridge by a natural reachable-language bridge.
ReachableGoldTheorem.lean connected reachable exact reconstruction to Gold identification.
CharacteristicDataMonotone.lean proved finite characteristic data is monotone under sample extension.
StartAnchorCanonical.lean made the start-anchor bridge easier to construct.
PrefixExactReconstruction.lean stated exact reconstruction directly for text prefix samples.
MainReachableTheorem.lean packaged the current reachable main theorem.
CharacteristicSamplePackage.lean separated finite characteristic data from global target assumptions.
CharacteristicSampleBuilderSkeleton.lean introduced a flat blueprint for constructing the finite package.
```

What has **not** yet been fully formalized:

```text
concrete finite canonical learner enumeration
explicit tuple-occurrence and binary-witness enumeration
actual construction of CS(G̃₀)
trimmed output-type refinement G̃₀ as a finite grammar object
proof that CS(G̃₀) gives ReachableCharacteristicBlueprint
concrete construction of LeftFillingIdentity / RightFillingIdentity
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

---

## 5. What remains as explicit assumptions or skeleton fields?

The main explicit assumptions/skeleton records are now:

### 5.1 `LeftFillingIdentity` / `RightFillingIdentity`

These abstract the construction of child contexts from a parent context and a binary template.

Need later:

```text
Concrete construction for named sentence contexts, including empty components and tie-order bookkeeping.
```

### 5.2 `SampleBinaryEvidence`

This assumes the existence of filling-identity witnesses for binary sample witnesses.

Need later:

```text
Derive this from concrete tuple occurrences and binary witnesses in sample words.
```

### 5.3 `CharacteristicSampleData`

This packages the data that `CS(G̃₀) ⊆ K` should provide.

Partly superseded by:

```lean
ReachableCharacteristicBlueprint
ReachableCharacteristicPackage
```

Need later:

```text
Construct these records from the actual presentation-relative characteristic sample.
```

### 5.4 `StartAnchorCanonical`

This is now the preferred start-anchor bridge.

Need later:

```text
Derive it from the actual start convention of CS(G̃₀), probably using an identity exposing context for the start.
```

### 5.5 `ReachableCharacteristicBlueprint`

This is the new target for construction.

Need later:

```text
Build its fields:
  anchor
  expose
  anchor_mem
  terminal_mem
  terminal_type_eq
  binary_mem
  binary_type_eq
  binary_leftIdentity
  binary_rightIdentity
  start_mem
  start_type_eq
  startWord
  start_arity
  start_anchor_eq
```

### 5.6 Concrete learner equivalence

The current theorem is for:

```lean
ReachableSampleStringLanguage K obs f
```

Need later:

```text
Define the actual finite canonical learner grammar/relation and prove its language equals, or is equivalent to, the reachable model.
```

---

## 6. Immediate next files

Recommended next steps:

### 6.1 `BlueprintFiniteSample.lean`

Goal:

Define a canonical finite sample associated to a blueprint.

Possible content:

```lean
def ReachableCharacteristicBlueprint.sampleWords : Finset (Word α)
```

or, more realistically, define a separate record that stores the finite set of words used by the blueprint and proves all membership fields.

This may clarify how `CS(G̃₀)` is represented.

---

### 6.2 `ExposingContextSkeleton.lean`

Goal:

Start isolating the construction of exposing contexts.

Need ingredients:

```text
for each surviving typed nonterminal X:
  anchor tuple ω(X)
  named context χ(X)
  namedFill χ(X) ω(X) ∈ L(G)
```

This is where the “trimmed” condition of `G̃₀` enters.

---

### 6.3 `FillingIdentityConstructionSkeleton.lean`

Goal:

Reduce the abstraction around `LeftFillingIdentity` and `RightFillingIdentity`.

Possible first theorem shape:

```lean
Given a parent named context E and a binary template ρ,
there exist child named contexts E_left and E_right satisfying
LeftFillingIdentity and RightFillingIdentity.
```

This will likely require more concrete definitions for template holes and component order.

---

### 6.4 `OutputTypeRefinementGrammar.lean`

Goal:

Construct the actual finite output-type refined grammar object.

Need ingredients:

```text
typed nonterminals as base nonterminal + componentwise observation type
typed terminal rules
typed binary rules
typed start rules
erasure and lifting theorems
```

Some pieces already exist in `OutputTypeRefinement.lean` and `OutputTypeLift.lean`, but not yet as a finite `WorkingMCFG`.

---

### 6.5 `TrimmedRefinementSkeleton.lean`

Goal:

Represent surviving nonterminals of `G̃₀`.

Need ingredients:

```text
reachable from start
productive to terminal strings
anchor tuple
exposing context
```

This is likely prerequisite for constructing `ReachableCharacteristicBlueprint`.

---

### 6.6 `ConcreteTupleOccurrences.lean`

Goal:

Define concrete tuple occurrences in finite sample words.

Need ingredients:

```text
intervals or cut positions
named holes
empty component bookkeeping
binary witness segmentation
induced template
```

This file is likely bookkeeping-heavy and should be done carefully.

---

### 6.7 `ConcreteCanonicalLearner.lean`

Goal:

Define the actual finite learner object from a finite sample.

Possible options:

1. define it as an inductive relation generated by enumerated evidence;
2. define an actual grammar object;
3. prove equivalence between the grammar object and the inductive relation.

Recommended order:

```text
first relation,
then grammar object later.
```

---

## 7. Medium-term roadmap toward the paper theorem

### Stage A: Reachable main theorem

Status: essentially complete under blueprint/package assumptions.

Files:

```text
FiniteTextCoverage.lean
ReachableStartBridge.lean
ReachableGoldTheorem.lean
CharacteristicDataMonotone.lean
StartAnchorCanonical.lean
PrefixExactReconstruction.lean
MainReachableTheorem.lean
CharacteristicSamplePackage.lean
CharacteristicSampleBuilderSkeleton.lean
```

Current theorem shape:

```lean
ReachableCharacteristicBlueprint G S obs f
+
G.FanoutAtMost f
+
FixedNamedTupleSubstitutable f obs G.StringLanguage
⇒ reachable learner identifies G.StringLanguage from every positive text.
```

This stage is the strongest verified result so far.

---

### Stage B: Construct the blueprint from `CS(G̃₀)`

Files to create:

```text
OutputTypeRefinementGrammar.lean
TrimmedRefinementSkeleton.lean
ExposingContextSkeleton.lean
CharacteristicSampleConstruction.lean
CharacteristicBlueprintTheorem.lean
```

Target theorem shape:

```lean
CS(G̃₀) constructed from the trimmed output-type refinement
⇒ ReachableCharacteristicBlueprint G CS obs f
```

This is the main remaining completeness-construction work.

---

### Stage C: Concrete learner equivalence

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

### Stage D: Polynomial bound

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

### Stage E: Boundary results

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
distributional equivalence lemmas
witnessed composition semantic core
sample-level soundness
completeness induction skeleton
finite text coverage
reachable exact reconstruction
reachable Gold identification
blueprint/package/main-theorem plumbing
```

### Verified but intentionally abstract

```text
filling identities
sample binary evidence
characteristic sample data
start-anchor canonical bridge
reachable characteristic blueprint
reachable sample language model
```

### Not yet verified

```text
actual concrete learner enumeration
actual characteristic sample construction
trimmed output-type refinement as finite grammar
concrete filling-identity construction
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

After adding the current latest file, the useful CI/local command is:

```bash
lake build LeanCfgProject.MCFG.CharacteristicSampleBuilderSkeleton
```

Next proposed file:

```text
BlueprintFiniteSample.lean
```

Expected purpose:

```text
start making the blueprint construction more concrete by separating
the finite set of characteristic words from the proofs that those words
supply anchor, terminal, binary, and start witnesses.
```

Alternative next file:

```text
FillingIdentityConstructionSkeleton.lean
```

Expected purpose:

```text
start reducing the remaining abstraction around LeftFillingIdentity and
RightFillingIdentity.
```

Recommended order:

```text
1. BlueprintFiniteSample.lean
2. FillingIdentityConstructionSkeleton.lean
3. OutputTypeRefinementGrammar.lean
4. TrimmedRefinementSkeleton.lean
```
