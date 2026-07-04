# FORMALIZATION_MCFG

Lean formalization log and roadmap for the MCFG fixed finite-observation paper.

Last updated: 2026-07-04  
Current confirmed CI point: Lean CI #502, commit `1ac7d43`, pushed by `growupkuriyama-hub`.

---

## 0. Purpose of this restart

This experiment restarts the Lean verification of the paper

> Positive-Data Learning of Multiple Context-Free Grammars with Fixed Finite-Monoid Observations

from a clean baseline.

The previous zip contained many useful experimental files from an earlier paper version, but the experiment procedure had mistakes and the behavior of the old Lean chain was not fully trustworthy.  Therefore, this restart follows a conservative policy:

1. do not import the old terminal mega-file as a foundation;
2. rebuild the formalization in small independently checkable layers;
3. keep every file CI-checkable before moving to the next file;
4. separate what is fully Lean-verified from what is currently an explicit skeleton/bridge assumption;
5. reuse old files only as design references or for small ideas, not as opaque trusted infrastructure.

At the current stage, the goal is not yet to prove the full main theorem of the paper.  The goal is to build a reliable, modular Lean foundation for the soundness and completeness proof.

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
```

All of the above files have passed Lean CI up to:

```text
Lean CI #502
Commit: 1ac7d43
```

The current state is best described as:

```text
soundness side: strong skeleton, largely formalized
completeness side: rule-simulation skeleton formalized
exact reconstruction: outer skeleton formalized, one bridge remains explicit
Gold identification: finite characteristic sample ⇒ eventual correctness skeleton formalized
```

What has **not** yet been fully formalized:

```text
concrete finite canonical learner enumeration
explicit tuple-occurrence and binary-witness enumeration
actual construction of CS(G̃₀)
trimmed output-type refinement G̃₀ as a finite grammar object
proof that CS(G̃₀) gives CharacteristicSampleData
ReconstructionBridge from characteristic start anchor to actual sample-start derivations
finite-text coverage from finite S without explicit EventuallyContains assumption
polynomial-time construction bound
no-advice non-identifiability
copy-language / member-kernel exclusion
```

---

## 2. File-by-file progress

### 2.1 `Basic.lean`

Status: CI passed.

Purpose:

This is the clean base layer.  It intentionally does not import the previous experimental MCFG files.

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

`TemplateTuple.Nondeleting` is deliberately weak in `Basic.lean`: every child component occurs at least once.  Exact-once linearity is added later in `ExactOnce.lean`.

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

Exact-once counting is represented by explicit occurrence-count predicates.  It is not yet connected to a finite rule enumerator.

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

Concrete construction of the named child contexts is postponed.  Instead, this file introduces witness records:

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

This file does not yet define a concrete canonical learner.  It proves that the semantic evidence used by the learner is valid.

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

This gives the outer exact reconstruction form:

```text
SampleStringLanguage K obs f = G.StringLanguage
```

provided a remaining `ReconstructionBridge`.

Current bridge assumption:

```lean
ReconstructionBridge.toSampleString :
  CharacteristicReachableLanguage D ⊆ SampleStringLanguage K obs f
```

This corresponds to connecting the characteristic start anchor to actual sample start rules.

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

Current abstraction:

`TextFor.EventuallyContains S` is assumed explicitly.  The next step should prove this from finiteness of `S` and coverage of the text.

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
```

This linear chain is intentional.  It keeps CI failures local and makes the experiment traceable.

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

### 4.6 Completeness skeleton

```text
if characteristic sample data gives rule-by-rule anchor simulation,
then target derivations are learner-reachable from anchors.
```

### 4.7 Exact reconstruction outer form

```text
soundness inclusion
+
completeness inclusion
+
ReconstructionBridge
⇒ exact reconstruction.
```

### 4.8 Gold identification skeleton

```text
finite characteristic sample condition
+
eventual appearance in text
⇒ eventual correctness of hypotheses.
```

---

## 5. What remains as explicit assumptions or skeleton fields?

The main explicit assumptions/skeleton records are:

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

Need later:

```text
Construct CharacteristicSampleData from the actual presentation-relative characteristic sample.
```

### 5.4 `ReconstructionBridge`

This bridges characteristic-anchor reachability to actual sample-start derivations.

Need later:

```text
Use the start-child convention / expose-start identity context to prove this.
```

### 5.5 `TextFor.EventuallyContains`

Currently assumed in `GoldIdentificationSkeleton`.

Need later:

```text
Prove every finite S ⊆ L is eventually contained in every text for L.
```

---

## 6. Immediate next files

Recommended next steps:

### 6.1 `FiniteTextCoverage.lean`

Goal:

Remove the explicit `EventuallyContains` assumption for finite characteristic samples.

Expected theorem:

```lean
theorem finiteSample_eventuallyContained
    (T : TextFor L) (S : Finset (Word α))
    (hS : (S : Set (Word α)) ⊆ L) :
    T.EventuallyContains S
```

Idea:

For each `s ∈ S`, use `T.covers s`.  Take a maximum stage over the finite set.

This should be a relatively safe next file.

---

### 6.2 `ReachableStartBridge.lean`

Goal:

Fill or reduce `ReconstructionBridge`.

Possible approach:

Define a reachable string language that starts from `D.anchor G.start`, and prove that if the start anchor itself occurs as a sample start word, then characteristic reachability is included in `SampleStringLanguage`.

Expected data:

```lean
startAnchorAsSampleWord :
  ∃ w ∈ K, D.anchor G.start = singletonTuple w
```

or a variant using arity transport and identity context.

This corresponds to the paper’s convention that for start children the exposing context is `□`.

---

### 6.3 `CharacteristicSampleFromRefinement.lean`

Goal:

Connect actual output-type refinement data to `CharacteristicSampleData`.

This is harder.

Need ingredients:

```text
surviving typed nonterminals
anchor tuple ω(X)
exposing context χ(X)
terminal and binary rule sample words
output-type equality for anchors and rule outputs
filling identities for binary witnesses
```

This is where the paper’s `CS(G̃₀)` construction enters Lean.

---

### 6.4 `ConcreteTupleOccurrences.lean`

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

### 6.5 `ConcreteCanonicalLearner.lean`

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

### 6.6 `PolynomialBoundSkeleton.lean`

Goal:

Formalize or at least structure the fixed-parameter polynomial construction bound.

This can initially be a skeleton:

```text
number of tuple occurrences ≤ |K|^{O(f)}
number of binary witnesses ≤ |K|^{O(f)}
rule generation is polynomial for fixed f and fixed h
```

This is likely better after concrete tuple occurrence enumeration is defined.

---

## 7. Medium-term roadmap toward the paper theorem

### Stage A: Finish Gold identification skeleton

Files:

```text
FiniteTextCoverage.lean
GoldIdentification.lean
```

Target theorem shape:

```lean
finite characteristic sample
⇒ identifies in the limit from positive data
```

This is probably the nearest fully completable part.

---

### Stage B: Fill exact reconstruction bridge

Files:

```text
ReachableStartBridge.lean
ExactReconstruction.lean
```

Target theorem shape:

```lean
CharacteristicSampleData
+ start bridge
⇒ SampleStringLanguage K obs f = G.StringLanguage
```

This should be feasible soon.

---

### Stage C: Construct characteristic sample data

Files:

```text
OutputTypeRefinementGrammar.lean
ExposingContexts.lean
CharacteristicSampleConstruction.lean
CharacteristicSampleDataTheorem.lean
```

Target theorem shape:

```lean
CS(G̃₀) ⊆ K ⊆ L(G)
⇒ CharacteristicSampleData G K obs f
```

This is the main completeness construction.

---

### Stage D: Concrete learner

Files:

```text
TupleOccurrences.lean
BinaryWitnesses.lean
CanonicalLearnerRelation.lean
CanonicalLearnerSoundComplete.lean
```

Target theorem shape:

```lean
language of concrete learner relation = SampleStringLanguage
```

or

```lean
concrete learner derivation implies SampleStringDerives
```

and the reverse if needed.

---

### Stage E: Polynomial bound

Files:

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

Files:

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
Gold finite-sample skeleton
```

### Verified but intentionally abstract

```text
filling identities
sample binary evidence
characteristic sample data
reconstruction bridge
eventual containment of finite samples
```

### Not yet verified

```text
actual concrete learner enumeration
actual characteristic sample construction
trimmed output-type refinement as finite grammar
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
lake build LeanCfgProject.MCFG.GoldIdentificationSkeleton
```

Next proposed file:

```text
FiniteTextCoverage.lean
```

Expected purpose:

```text
prove finite S ⊆ L eventually appears in every positive text for L
```

This will remove one explicit assumption from the Gold identification skeleton.
