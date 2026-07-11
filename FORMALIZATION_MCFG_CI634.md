# FORMALIZATION_MCFG

Lean formalization log and roadmap for the MCFG fixed finite-observation paper.

Last updated: 2026-07-11  
Current confirmed CI point: Lean CI #634, commit `168022f`, pushed by `growupkuriyama-hub`.

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

At the current stage, the development has a verified reachable-model main theorem, a scaffolded trimmed-presentation / characteristic-sample route, a paper-facing existential theorem, and a stable constructive paper-facing facade.  The major named-context splicing obligation has now been solved for the paper's exact-once working grammars by an explicit Lean construction.  The unrestricted universal `NamedContextSplicingConstructor` was shown to be false in general, and the corrected exact-once constructor has been connected through characteristic samples, prefix-exact reconstruction, and Gold identification.  The development is still not the fully concrete canonical learner theorem from the paper: the main remaining obligations are the concrete construction of the complete finite output-type presentation and its productive/reachable trim, extraction of successful occurrence/representative data from that construction, exact language equivalence for the concrete presentation grammar, and equivalence with the fully enumerated canonical learner.

The CI-confirmed phase from CI #583 to CI #603 did not pretend to discharge those remaining mathematical construction obligations.  Instead, it reorganized them into clean construction layers and then wrapped them in stable final names suitable for the paper and blueprint.

The phase from CI #603 to CI #620 decomposed the preferred anchor-common route down to an explicit all-pieces checklist and opened the splicing obligation down to concrete child-context functions and `namedFill` equations.  The CI #621--#624 phase then crossed the important line from interface decomposition to actual construction: it proved that the old unrestricted constructor is not inhabitable, built explicit left/right named contexts under exact-once linearity, integrated the resulting filling witnesses into the reachable theorem chain, removed unnecessary common-transport assumptions from a minimal route, and connected the existing exposing-transport route to the concrete exact-once splicing construction.

The CI #625--#634 phase moved beyond the exposing-transport interface.  It replaced the unconditional transport assumption by the paper-faithful derivational-exposure invariant, constructed that invariant from explicit successful derivation spines and successful occurrences, used those occurrences to build the witness component of a trimmed typed presentation, descended to base-nonterminal representatives and pre-core data, derived rule-output compatibility from actual typed-rule realizations and then from canonical typed-rule closure, and finally converted every finite output-type presentation into an actual `WorkingMCFG` with a fresh start symbol.  Presentation derivations now embed into this concrete grammar, and exact working conditions and fan-out bounds are preserved.

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
CharacteristicSampleTransportObligations.lean ✅
CharacteristicSampleTransportObligationsFromSample.lean ✅
CharacteristicSampleTransportObligationsFromExistingSamples.lean ✅
CharacteristicSampleTransportObligationsFromBuilders.lean ✅
CharacteristicSampleTransportObligationsFromComponents.lean ✅
CharacteristicSampleTransportObligationsFromRules.lean ✅
CharacteristicSampleTransportObligationsFromRuleData.lean ✅
CharacteristicSampleTransportObligationsFromCoreData.lean ✅
CharacteristicSampleTransportObligationsFromAnchorData.lean ✅
CharacteristicSampleSemanticConstructionTargets.lean ✅
CharacteristicSampleSemanticConstructionTargetLevels.lean ✅
CharacteristicSampleSemanticTransportTargets.lean ✅
CharacteristicSampleSemanticTransportTargetLevels.lean ✅
CharacteristicSampleSameContextTransportTargets.lean ✅
CharacteristicSampleSameContextTransportTargetLevels.lean ✅
CharacteristicSampleSemanticTransportTargetDiagram.lean ✅
CharacteristicSampleCommonToExposingTargetDiagram.lean ✅
CharacteristicSampleSemanticMainTheorems.lean ✅
CharacteristicSamplePaperMainTheorem.lean ✅
CharacteristicSamplePaperMainVariants.lean ✅
CharacteristicSamplePaperAssumptionDiagram.lean ✅
CharacteristicSamplePaperWitnessTheorem.lean ✅
CharacteristicSampleGlobalPaperWitnessTheorem.lean ✅
CharacteristicSampleBoundedGlobalPaperTheorem.lean ✅
CharacteristicSampleExistentialPaperTheorem.lean ✅
CharacteristicSampleExposingTransportConstruction.lean ✅
CharacteristicSampleAnchorCommonTransportConstruction.lean ✅
CharacteristicSampleSameContextTransportConstruction.lean ✅
CharacteristicSampleTransportConstructionDiagram.lean ✅
CharacteristicSampleTransportConstructionChoice.lean ✅
CharacteristicSampleTransportConstructionBase.lean ✅
CharacteristicSampleTransportConstructionExistential.lean ✅
CharacteristicSampleBaseConstructionLayers.lean ✅
CharacteristicSampleCoreConstructionLayers.lean ✅
CharacteristicSampleCoreConstructionExistential.lean ✅
CharacteristicSampleSplitCoreGlobalLayer.lean ✅
CharacteristicSampleGlobalAssumptionLayers.lean ✅
CharacteristicSampleTargetAssumptionLayers.lean ✅
CharacteristicSampleFlatConstructionData.lean ✅
CharacteristicSampleFlatConstructionChoice.lean ✅
CharacteristicSampleFlatConstructionDisjunction.lean ✅
CharacteristicSampleFinalConstructionFacade.lean ✅
CharacteristicSampleConstructiveLearningTheorem.lean ✅
CharacteristicSampleConstructiveLearnabilityFacade.lean ✅
CharacteristicSamplePaperConstructiveStatement.lean ✅
CharacteristicSamplePaperConstructiveRouteCorollaries.lean ✅
CharacteristicSamplePreferredAnchorCommonConstruction.lean ✅
CharacteristicSamplePreferredAnchorCommonTargets.lean ✅
CharacteristicSamplePreferredAnchorCommonTargetPieces.lean ✅
CharacteristicSamplePreferredSplitCorePieces.lean ✅
CharacteristicSamplePreferredGlobalPieces.lean ✅
CharacteristicSamplePreferredAllPieces.lean ✅
CharacteristicSampleNamedContextSplicingConstruction.lean ✅
CharacteristicSampleNamedContextSplicingPieces.lean ✅
CharacteristicSampleNamedContextSplicingLeftRightConstructors.lean ✅
CharacteristicSampleNamedContextSplicingLocalTargets.lean ✅
CharacteristicSampleNamedContextSplicingTemplateTargets.lean ✅
CharacteristicSampleNamedContextSplicingTemplateChoices.lean ✅
CharacteristicSampleNamedContextSplicingParentChoices.lean ✅
CharacteristicSampleNamedContextSplicingContextFamilies.lean ✅
CharacteristicSampleNamedContextSplicingContextEquations.lean ✅
CharacteristicSampleNamedContextSplicingExactOnceConstruction.lean ✅
CharacteristicSampleNamedContextSplicingExactOnceIntegration.lean ✅
CharacteristicSampleExactOnceMinimalPaperRoute.lean ✅
CharacteristicSampleExactOnceExposingTransportRoute.lean ✅
CharacteristicSampleExactOnceDerivationalExposureRoute.lean ✅
CharacteristicSampleExactOnceFiniteDerivationalExposureRoute.lean ✅
CharacteristicSampleExactOnceFiniteNonterminalDerivationalExposureRoute.lean ✅
CharacteristicSampleExactOnceSuccessfulDerivationSpineRoute.lean ✅
CharacteristicSampleExactOnceSuccessfulOccurrenceRoute.lean ✅
OutputTypeTrimmedPresentationSuccessfulOccurrenceConstruction.lean ✅
CharacteristicSampleExactOnceSuccessfulPresentationRoute.lean ✅
CharacteristicSampleExactOnceSuccessfulRuleRealizationRoute.lean ✅
CharacteristicSampleExactOnceCanonicalRuleClosureRoute.lean ✅
OutputTypePresentationWorkingGrammar.lean ✅
```

All files marked ✅ above are user-confirmed as passed.  The latest named CI/commit explicitly recorded in this document is:

```text
Lean CI #634
Commit: 168022f
```

`OutputTypePresentationWorkingGrammar.lean` is now confirmed passed.

The current state is best described as:

```text
reachable main theorem: stabilized under FinalReachableData
exact-once named-context splicing: concretely constructed and CI-confirmed
unrestricted universal splicing constructor: formally refuted and absent from the corrected route
unconditional exposing transport: no longer needed by the strongest corrected route
derivational exposure: constructed from explicit successful derivation spines and occurrences
trimmed witness layer: constructed from successful typed occurrences
typed-to-base pre-core layer: constructed from representative selection and rule compatibility
rule compatibility: derived from actual typed-rule realization and canonical typed-rule closure
finite positive characteristic sample: constructed from the successful-presentation package
current strongest identification endpoint:
  trimmed_successful_canonical_rule_closure_exact_working_conclusion_package
concrete presentation grammar:
  OutputTypeRefinementPresentation.toWorkingMCFG
presentation derivations embed into the concrete WorkingMCFG
exact working conditions and fan-out bounds transfer to the concrete WorkingMCFG
actual finite complete G^h / trimmed G̃₀ construction from G and h: still not complete
successful occurrence family and representative/canonical-closure existence: still construction obligations
concrete canonical learner enumeration: still not yet formalized
```


Most important progress since CI #624:

```text
CharacteristicSampleExactOnceDerivationalExposureRoute.lean replaced the overly strong unconditional exposing-transport assumption by TrimmedPresentationDerivationalExposure.
Terminal, binary, and start witness positivity is now proved directly from genuine grammar derivations and exposing contexts that accept every derivable tuple.
CharacteristicSampleExactOnceFiniteDerivationalExposureRoute.lean generated the finite base-nonterminal cover and rule-arity selectors automatically from finite nonterminals and BasicWorkingConditions.
CharacteristicSampleExactOnceFiniteNonterminalDerivationalExposureRoute.lean weakened the public enumeration requirement from [Fintype N] to the natural proposition [Finite N].
CharacteristicSampleExactOnceSuccessfulDerivationSpineRoute.lean defined ExactSuccessfulDerivationSpine and proved acceptsDerives by induction through root, start, left-binary, and right-binary steps.
CharacteristicSampleExactOnceSuccessfulOccurrenceRoute.lean combined anchor derivability and exposing spines into one ExactSuccessfulDerivationOccurrence witness.
OutputTypeTrimmedPresentationSuccessfulOccurrenceConstruction.lean constructed TrimmedNonterminalWitnesses and a TrimmedOutputTypePresentation from successful typed occurrences.
CharacteristicSampleExactOnceSuccessfulPresentationRoute.lean transported typed occurrences to base representatives and constructed TrimmedPresentationPreCoreData from rule-output compatibility.
CharacteristicSampleExactOnceSuccessfulRuleRealizationRoute.lean derived output compatibility from actual typed rules present in the finite presentation.
CharacteristicSampleExactOnceCanonicalRuleClosureRoute.lean removed arbitrary typed-rule choices by defining canonical terminal/binary/start typed rules from representative output types.
OutputTypePresentationWorkingGrammar.lean converted an OutputTypeRefinementPresentation into an actual WorkingMCFG with a fresh start symbol, embedded presentation derivations, and transferred exact working conditions and fan-out bounds.
```

Current strongest corrected identification route:

```text
complete finite typed presentation
+
successful typed occurrences
+
one present typed representative for each base nonterminal
+
closure under the canonical typed terminal/binary/start rules
+
G.ExactWorkingConditions
+
fan-out bound
+
fixed-observation tuple substitutability
⇒ concrete finite positive characteristic sample
⇒ exact reconstruction on every positive finite superset
⇒ eventual prefix-exact reconstruction
⇒ reachable Gold identification.
```

Stable endpoint:

```lean
trimmed_successful_canonical_rule_closure_exact_working_conclusion_package
```

New concrete grammar construction:

```lean
OutputTypeRefinementPresentation.toWorkingMCFG
PresentationDerives.toWorkingMCFG
PresentationStringDerives.toWorkingMCFG
presentationStringLanguage_subset_workingGrammar
CompleteOutputTypePresentation.original_subset_workingGrammar
```

This is the first CI-confirmed point where a finite output-type presentation is
turned into an actual `WorkingMCFG`, rather than remaining only a presentation
record.

Current progress estimate:

```text
logical theorem plumbing and reachable-model reasoning: 95%+
exact-once named-context splicing: completed
derivational exposure and successful-occurrence semantics: completed conditionally on occurrence witnesses
conditional characteristic-sample / Gold theorem from a successful typed presentation: about 95%
concrete end-to-end theorem from G and h to a learned grammar: about 78--82%
fully enumerated canonical learner and equivalence proof: about 58--62%
whole paper including complexity and boundary/non-identifiability results: about 50--55%
```

The remaining positive-learning work is now concentrated in constructing the
finite complete output-type presentation and its successful occurrence /
representative closure data directly from `G` and `obs`, plus proving the
concrete presentation grammar has exactly the intended presentation language.

Most important progress since CI #620:

```text
CharacteristicSampleNamedContextSplicingExactOnceConstruction.lean proved that the old unrestricted universal constructor is false using the square-template counterexample.
The same file implemented tokenization/normalization of named contexts and concrete leftContextNSC/rightContextNSC functions.
It proved leftContext_fill_eq and rightContext_fill_eq under componentwise exact-once hypotheses.
It constructed exact_namedContextSplicingConstructor for every alphabet.
It connected the constructor to BinaryRuleSplicingEvidence, BinaryRuleSplicingProvider, and BinaryFillingWitnessFamily using G.BinaryRulesExactlyOnce.
CharacteristicSampleNamedContextSplicingExactOnceIntegration.lean bypassed the false legacy constructor and connected exact-once filling witnesses to reachable characteristic samples, exact reconstruction, prefix exactness, and Gold identification.
CharacteristicSampleExactOnceMinimalPaperRoute.lean removed the unused commonTransport premise from the minimal paper-facing route.
CharacteristicSampleExactOnceExposingTransportRoute.lean removed the need to assume a pre-built positive grammar-rule builder: exposing-context transport now supplies rule-witness positivity, and concrete exact-once splicing completes the route.
```

Current corrected exact-once endpoints:

```lean
trimmed_paper_preferred_anchor_common_exact_once_main_theorem
trimmed_paper_preferred_anchor_common_exact_working_main_theorem
trimmed_paper_exact_once_minimal_main_theorem
trimmed_paper_exact_working_minimal_main_theorem
trimmed_exposing_transport_exact_once_main_theorem
trimmed_exposing_transport_exact_working_main_theorem
trimmed_exposing_transport_exact_working_conclusion_package
```

Historical CI #624 corrected route, expanded:

```text
trimmed output-type presentation/pre-core data
+
finite base-nonterminal coverage and rule arity selectors
+
exposing-context transport
+
positive distinguished start word
+
G.ExactWorkingConditions
+
fanout bound
+
fixed-observation tuple substitutability
⇒ finite positive characteristic sample
⇒ exact reconstruction on every positive finite superset
⇒ eventual prefix-exact reconstruction
⇒ Gold identification for the reachable learner.
```

This route remains verified, but CI #625--#634 supersedes its unconditional
transport premise by derivational exposure and then by explicit successful
occurrences.

Critical mathematical correction:

```text
The old NamedContextSplicingConstructor quantified over arbitrary templates and
is not generally inhabitable.  Exact-once linearity is essential: a template
using the same child variable twice cannot be represented by a well-formed named
context containing that hole exactly once.  The corrected theorem chain now uses
G.BinaryRulesExactlyOnce, already contained in G.ExactWorkingConditions.
```

Most important progress since CI #603:

```text
CharacteristicSamplePaperConstructiveRouteCorollaries.lean made the route-specific paper corollaries explicit, especially the preferred anchor-common route.
CharacteristicSamplePreferredAnchorCommonConstruction.lean introduced PaperPreferredAnchorCommonConstructionData as the paper-facing preferred anchor-common data record.
CharacteristicSamplePreferredAnchorCommonTargets.lean split the preferred route into split core, fully split global assumptions, and anchor-common transport.
CharacteristicSamplePreferredAnchorCommonTargetPieces.lean named the split core target, fully split global target, and anchor-common transport target separately.
CharacteristicSamplePreferredSplitCorePieces.lean split the split core into fanout bound, trimmed presentation, pre-core data, and grammar-rule builder.
CharacteristicSamplePreferredGlobalPieces.lean split global assumptions into splicing constructor, fanout, and substitutability promise.
CharacteristicSamplePreferredAllPieces.lean introduced PaperPreferredAnchorCommonAllPieces, the complete eight-item checklist for the preferred route.
CharacteristicSampleNamedContextSplicingConstruction.lean isolated the named-context splicing constructor as an independent construction datum.
CharacteristicSampleNamedContextSplicingPieces.lean split BinaryNamedContextSplicing into left and right splicing pieces.
CharacteristicSampleNamedContextSplicingLeftRightConstructors.lean separated the universal left and right splicing constructors.
CharacteristicSampleNamedContextSplicingLocalTargets.lean introduced local parent/body splicing targets.
CharacteristicSampleNamedContextSplicingTemplateTargets.lean lifted local targets to template-level constructors.
CharacteristicSampleNamedContextSplicingTemplateChoices.lean separated template-by-template existence from universal choice.
CharacteristicSampleNamedContextSplicingParentChoices.lean reduced template-level construction to parentwise local target existence.
CharacteristicSampleNamedContextSplicingContextFamilies.lean exposed the actual child-context families and their namedFill equations.
CharacteristicSampleNamedContextSplicingContextEquations.lean split those context families into context functions plus namedFill equation proofs.
```

Historical CI #620 preferred-route endpoints:

```lean
trimmed_paper_preferred_anchor_common_all_pieces_main_theorem
trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_context_functions_equations
```

These remain Lean-checked conditional theorems, but the first route contains the
unrestricted `NamedContextSplicingConstructor`, which is now known not to be
inhabitable in general.  They should therefore be treated as historical
decomposition results rather than current constructive endpoints.

The corrected CI #624 route replaces them by:

```lean
trimmed_paper_preferred_anchor_common_exact_once_main_theorem
trimmed_paper_preferred_anchor_common_exact_working_main_theorem
trimmed_paper_exact_working_minimal_main_theorem
trimmed_exposing_transport_exact_working_conclusion_package
```

In these corrected endpoints, named-context splicing is constructed internally
from exact-once linearity; it is no longer supplied as an external premise.

Most important progress since CI #583:

```text
CharacteristicSampleExposingTransportConstruction.lean introduced direct exposing-context construction data.
CharacteristicSampleAnchorCommonTransportConstruction.lean introduced the preferred anchor-common construction route.
CharacteristicSampleSameContextTransportConstruction.lean introduced the stronger same-context construction route.
CharacteristicSampleTransportConstructionDiagram.lean recorded Same/Common ⇒ Exposing construction diagrams.
CharacteristicSampleTransportConstructionChoice.lean packaged exposing/anchor-common/same-context construction routes into one choice.
CharacteristicSampleTransportConstructionBase.lean factored the common base data away from the transport witness.
CharacteristicSampleTransportConstructionExistential.lean introduced the ∃ base + transport-witness interface.
CharacteristicSampleBaseConstructionLayers.lean split construction data into core construction data and global assumptions.
CharacteristicSampleCoreConstructionLayers.lean split the core into presentation, pre-core, and grammar-rule-builder layers.
CharacteristicSampleCoreConstructionExistential.lean exposed the direct targets f, T, D, and builder.
CharacteristicSampleSplitCoreGlobalLayer.lean separated split core + global assumptions from the transport witness.
CharacteristicSampleGlobalAssumptionLayers.lean split global assumptions into splicing and target assumptions.
CharacteristicSampleTargetAssumptionLayers.lean split target assumptions into fanout and substitutability assumptions.
CharacteristicSampleFlatConstructionData.lean introduced flat route-specific construction records.
CharacteristicSampleFlatConstructionChoice.lean packaged the flat route alternatives into one choice.
CharacteristicSampleFlatConstructionDisjunction.lean introduced the paper-readable route disjunction.
CharacteristicSampleFinalConstructionFacade.lean introduced TrimmedPresentationConstructiveMainAssumptions.
CharacteristicSampleConstructiveLearningTheorem.lean packaged characteristic-sample, prefix-exact, and Gold-identification consequences.
CharacteristicSampleConstructiveLearnabilityFacade.lean introduced short constructive-learnability names.
CharacteristicSamplePaperConstructiveStatement.lean introduced the stable paper-facing constructive statement
preferred anchor-common all-pieces checklist
splicing decomposition to context functions and namedFill equations.
```

Current strongest paper-facing constructive endpoint:

```lean
trimmed_paper_constructive_main_theorem
```

Current meaning:

```text
PaperConstructiveRouteAssumption G obs
⇒ PaperConstructiveIdentificationConclusion G obs
```

Expanded meaning:

```text
if one of the verified flat construction routes exists
(exposing, anchor-common, or same-context),
then there exists a finite fanout bound such that
the reachable learner using obs identifies G.StringLanguage
from every positive text.
```

Most important progress since CI #558:

```text
CharacteristicSampleTransportObligations*.lean created endpoint wrappers from transport obligations, sample evidence, existing samples, finite builders, components, rules, rule data, core data, and anchor data.
CharacteristicSampleSemanticConstructionTargets*.lean named semantic construction targets at grammar-builder, rule-coverage, component-package, and component-enumeration levels.
CharacteristicSampleSemanticTransportTargets*.lean reduced target records so common/exposing/same-context transport evidence can be supplied directly rather than as pre-built final data.
CharacteristicSampleSameContextTransportTargets*.lean added same-context variants and connected them to exposing transport.
CharacteristicSampleSemanticTransportTargetDiagram.lean and CharacteristicSampleCommonToExposingTargetDiagram.lean made Same ⇒ Exposing and Common ⇒ Exposing target diagrams explicit.
CharacteristicSampleSemanticMainTheorems.lean collected theorem-facing names for common/exposing/same-context target routes.
CharacteristicSamplePaperMainTheorem.lean introduced the paper-facing `TrimmedPresentationPaperMainAssumptions` facade.
CharacteristicSamplePaperMainVariants.lean added paper-facing exposing and same-context variants.
CharacteristicSamplePaperAssumptionDiagram.lean connected paper-facing common/same assumptions to exposing variants.
CharacteristicSamplePaperWitnessTheorem.lean hid the concrete pre-core datum `D`.
CharacteristicSampleGlobalPaperWitnessTheorem.lean hid the trimmed presentation `T`.
CharacteristicSampleBoundedGlobalPaperTheorem.lean hid the fanout bound `f`.
CharacteristicSampleExistentialPaperTheorem.lean reached the current paper-level existential statement:
  Nonempty BoundedGlobalPaperMainWitness
  ⇒ ∃ f, reachable learner at f identifies the target language.
```

Current best theorem-facing endpoint:

```lean
trimmed_paper_constructive_main_theorem
```

Current meaning:

```text
PaperConstructiveRouteAssumption G obs
⇒ PaperConstructiveIdentificationConclusion G obs
```

Expanded meaning:

```text
if one of the flat constructive routes exists,
then there exists a finite fanout bound f such that
the reachable learner using obs and f identifies G.StringLanguage
from every positive text.
```

Current strongest corrected endpoint:

```lean
trimmed_successful_canonical_rule_closure_exact_working_conclusion_package
```

Current meaning:

```text
successful complete typed presentation
+
base representative selection
+
canonical typed-rule closure
+
G.ExactWorkingConditions
+
fanout
+
fixed-observation substitutability
⇒ finite characteristic sample, prefix exactness, and Gold identification.
```

The earlier exposing-transport, all-pieces, and context-equation endpoints are
retained as historical decomposition milestones.  The strongest route no
longer assumes unconditional exposing transport.

Older still-valid existential endpoint:

```lean
trimmed_existential_paper_main_theorem
```

Older meaning:

```text
Nonempty TrimmedPresentationBoundedGlobalPaperMainWitness
⇒ ∃ f, reachable learner at f identifies G.StringLanguage.
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
actual finite enumeration/construction of the complete output-type presentation G^h from G and obs
construction of the reachable/productive trimmed core G̃₀ from that full presentation
automatic extraction of one successful typed occurrence for every present typed nonterminal
automatic choice/existence of one compatible present typed representative for every base nonterminal
proof that the concrete presentation WorkingMCFG has no extra derivations beyond the presentation relation
language equality between OutputTypeRefinementPresentation.toWorkingMCFG and PresentationStringLanguage
concrete finite canonical learner enumeration
explicit tuple-occurrence and binary-witness enumeration
equivalence between the reachable learner language and the fully enumerated canonical learner object
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


### 2.71 `CharacteristicSampleTransportObligations.lean`

Status: CI passed.

Purpose:

Collect the current remaining semantic obligations in theorem-facing transport-obligation packages.

Main contents:

```lean
TrimmedPresentationExposingTransportObligations
TrimmedPresentationCommonContextTransportObligations
```

Paper correspondence:

This packages the route:

```text
exposing/common-context transport
+
start-word evidence
+
NamedContextSplicingConstructor
+
fanout/promise
⇒ FinalReachableData
⇒ reachable identification.
```

---

### 2.72 `CharacteristicSampleTransportObligationsFromSample.lean`

Status: CI passed.

Purpose:

Build transport obligations when start-word evidence is supplied by a positive finite sample.

Main contents:

```lean
TrimmedPresentationExposingTransportObligationsFromSample
TrimmedPresentationCommonContextTransportObligationsFromSample
```

Paper correspondence:

This says the start-word obligation can be discharged from sample membership and positivity.

---

### 2.73 `CharacteristicSampleTransportObligationsFromExistingSamples.lean`

Status: CI passed.

Purpose:

Connect already existing witness-sample and characteristic-sample packages to the transport-obligation route.

Main contents:

```lean
TrimmedPresentationExposingTransportFromWitnessSample
TrimmedPresentationCommonContextFromWitnessSample
TrimmedPresentationExposingTransportFromCharacteristicSample
TrimmedPresentationCommonContextFromCharacteristicSample
```

Paper correspondence:

This bridges old sample packages to the newer transport-obligation endpoint.

---

### 2.74 `CharacteristicSampleTransportObligationsFromBuilders.lean`

Status: CI passed.

Purpose:

Connect finite builders and positive finite-union builders to transport obligations.

Main contents:

```lean
TrimmedPresentationExposingTransportFromFiniteBuilder
TrimmedPresentationCommonContextFromFiniteBuilder
TrimmedPresentationExposingTransportFromPositiveFiniteUnionBuilder
TrimmedPresentationCommonContextFromPositiveFiniteUnionBuilder
```

Paper correspondence:

This makes the finite-builder route compatible with the final transport theorem.

---

### 2.75 `CharacteristicSampleTransportObligationsFromComponents.lean`

Status: CI passed.

Purpose:

Connect component packages and component enumerations to exposing/common-context transport obligations.

Main contents:

```lean
TrimmedPresentationExposingTransportFromComponentPackage
TrimmedPresentationCommonContextFromComponentPackage
TrimmedPresentationExposingTransportFromComponentEnumeration
TrimmedPresentationCommonContextFromComponentEnumeration
```

Paper correspondence:

This lifts anchor/terminal/binary/start component data into the final transport route.

---

### 2.76 `CharacteristicSampleTransportObligationsFromRules.lean`

Status: CI passed.

Purpose:

Connect rule enumerations, rule coverage, and grammar-rule builders to exposing/common-context transport obligations.

Main contents:

```lean
TrimmedPresentationExposingTransportFromRuleEnumeration
TrimmedPresentationCommonContextFromRuleEnumeration
TrimmedPresentationExposingTransportFromRuleCoverage
TrimmedPresentationCommonContextFromRuleCoverage
TrimmedPresentationExposingTransportFromGrammarRuleBuilder
TrimmedPresentationCommonContextFromGrammarRuleBuilder
```

Paper correspondence:

This is the main bridge from grammar-rule-indexed witness construction into semantic transport endpoints.

---

### 2.77 `CharacteristicSampleTransportObligationsFromRuleData.lean`

Status: CI passed.

Purpose:

Introduce endpoint wrappers for grammar-rule data and rule-transport final data.

Main contents:

```lean
TrimmedPresentationGrammarRuleDataEndpoint
TrimmedPresentationGrammarRuleTransportEndpoint
TrimmedPresentationRuleTransportEndpoint
```

Paper correspondence:

This gives stable endpoints for rule-data, grammar-rule-transport data, and final rule-transport data.

---

### 2.78 `CharacteristicSampleTransportObligationsFromCoreData.lean`

Status: CI passed.

Purpose:

Add endpoint wrappers for exposing-core-final data and same-context-core data.

Main contents:

```lean
TrimmedPresentationExposingCoreFinalEndpoint
TrimmedPresentationSameContextCoreEndpoint
TrimmedPresentationSameContextCoreEndpointFromSample
```

Paper correspondence:

This exposes the route:

```text
SameContextCoreData
⇒ ExposingCoreFinalData
⇒ FinalReachableData.
```

---

### 2.79 `CharacteristicSampleTransportObligationsFromAnchorData.lean`

Status: CI passed.

Purpose:

Add endpoint wrappers for anchor-distribution and anchor-common-context core data.

Main contents:

```lean
TrimmedPresentationAnchorDistributionCoreEndpoint
TrimmedPresentationAnchorDistributionCoreEndpointFromSample
TrimmedPresentationAnchorCommonContextCoreEndpoint
TrimmedPresentationAnchorCommonContextCoreEndpointFromSample
```

Paper correspondence:

This packages the route:

```text
AnchorCommonContextCoreData
⇒ AnchorDistributionCoreData
⇒ ExposingTransportCoreData
⇒ ExposingCoreFinalData
⇒ FinalReachableData.
```

---

### 2.80 `CharacteristicSampleSemanticConstructionTargets.lean`

Status: CI passed.

Purpose:

Name the semantic construction targets at grammar-rule-builder and rule-coverage levels.

Main contents:

```lean
TrimmedPresentationGrammarBuilderCommonContextTarget
TrimmedPresentationGrammarBuilderExposingTarget
TrimmedPresentationRuleCoverageCommonContextTarget
TrimmedPresentationRuleCoverageExposingTarget
```

Paper correspondence:

This identifies a natural proof target:

```text
GrammarRuleBuilder
+
AnchorCommonContextCoreData
+
splicing/fanout/promise
⇒ reachable identification.
```

---

### 2.81 `CharacteristicSampleSemanticConstructionTargetLevels.lean`

Status: CI passed.

Purpose:

Extend semantic construction targets to component-package and component-enumeration levels.

Main contents:

```lean
TrimmedPresentationComponentPackageCommonContextTarget
TrimmedPresentationComponentPackageExposingTarget
TrimmedPresentationComponentEnumerationCommonContextTarget
TrimmedPresentationComponentEnumerationExposingTarget
```

Paper correspondence:

This makes the construction hierarchy explicit:

```text
component enumeration
⇒ component package
⇒ positive finite-union builder
⇒ witness sample
⇒ transport obligations
⇒ reachable identification.
```

---

### 2.82 `CharacteristicSampleSemanticTransportTargets.lean`

Status: CI passed.

Purpose:

Move from pre-built core data to direct transport evidence at grammar-rule-builder level.

Main contents:

```lean
TrimmedPresentationGrammarBuilderCommonTransportTarget
TrimmedPresentationGrammarBuilderExposingTransportTarget
```

Paper correspondence:

This reduces the common-context target to:

```text
GrammarRuleBuilder
+
AnchorCommonContextTransport
+
splicing/fanout/promise
⇒ reachable identification.
```

---

### 2.83 `CharacteristicSampleSemanticTransportTargetLevels.lean`

Status: CI passed.

Purpose:

Extend direct common-transport targets to rule-coverage, component-package, and component-enumeration levels.

Main contents:

```lean
TrimmedPresentationRuleCoverageCommonTransportTarget
TrimmedPresentationComponentPackageCommonTransportTarget
TrimmedPresentationComponentEnumerationCommonTransportTarget
```

Paper correspondence:

This lets lower-level constructions supply only `AnchorCommonContextTransport` plus finite cover and arity selectors.

---

### 2.84 `CharacteristicSampleSameContextTransportTargets.lean`

Status: CI passed.

Purpose:

Add the stronger same-context-transport target at grammar-rule-builder level.

Main contents:

```lean
TrimmedPresentationGrammarBuilderSameContextTransportTarget
```

Paper correspondence:

This gives a debugging route:

```text
GrammarRuleBuilder
+
SameContextTransport
+
splicing/fanout/promise
⇒ reachable identification.
```

---

### 2.85 `CharacteristicSampleSameContextTransportTargetLevels.lean`

Status: CI passed.

Purpose:

Extend same-context transport targets to rule-coverage, component-package, and component-enumeration levels.

Main contents:

```lean
TrimmedPresentationRuleCoverageSameContextTransportTarget
TrimmedPresentationComponentPackageSameContextTransportTarget
TrimmedPresentationComponentEnumerationSameContextTransportTarget
```

Paper correspondence:

This records that same-context transport can be used at every finite-sample construction level.

---

### 2.86 `CharacteristicSampleSemanticTransportTargetDiagram.lean`

Status: CI passed.

Purpose:

Record the diagram from same-context transport to exposing transport.

Main contents:

```lean
toGrammarBuilderExposingTransportTarget
toRuleCoverageExposingTransportTarget
toComponentPackageExposingTransportTarget
toComponentEnumerationExposingTransportTarget
```

Paper correspondence:

This formalizes the target-level conversion:

```text
SameContextTransport ⇒ ExposingContextTransport.
```

---

### 2.87 `CharacteristicSampleCommonToExposingTargetDiagram.lean`

Status: CI passed.

Purpose:

Record the diagram from anchor common-context transport to exposing transport.

Main contents:

```lean
toGrammarBuilderExposingTransportTarget
toRuleCoverageExposingTransportTarget
toComponentPackageExposingTransportTarget
toComponentEnumerationExposingTransportTarget
```

Paper correspondence:

This formalizes:

```text
AnchorCommonContextTransport ⇒ ExposingContextTransport
```

at every target level.

---

### 2.88 `CharacteristicSampleSemanticMainTheorems.lean`

Status: CI passed.

Purpose:

Collect theorem-facing names for the semantic target hierarchy.

Main contents:

```lean
trimmed_main_grammar_builder_common_transport_identifies
trimmed_main_grammar_builder_exposing_transport_identifies
trimmed_main_grammar_builder_same_context_transport_identifies
```

Paper correspondence:

This is the first theorem-name index for common/exposing/same-context target routes.

---

### 2.89 `CharacteristicSamplePaperMainTheorem.lean`

Status: CI passed.

Purpose:

Introduce the preferred paper-facing assumption package.

Main contents:

```lean
TrimmedPresentationPaperMainAssumptions
trimmed_paper_main_theorem
trimmed_paper_main_exists_positive_characteristic_sample
```

Paper correspondence:

This packages:

```text
GrammarRuleBuilder
+
AnchorCommonContextTransport
+
NamedContextSplicingConstructor
+
fanout/promise
⇒ identification in the limit.
```

---

### 2.90 `CharacteristicSamplePaperMainVariants.lean`

Status: CI passed.

Purpose:

Add paper-facing variants for exposing-context transport and same-context transport.

Main contents:

```lean
TrimmedPresentationPaperExposingAssumptions
TrimmedPresentationPaperSameContextAssumptions
trimmed_paper_exposing_main_theorem
trimmed_paper_same_context_main_theorem
```

Paper correspondence:

This records direct and stronger semantic routes under stable paper-facing names.

---

### 2.91 `CharacteristicSamplePaperAssumptionDiagram.lean`

Status: CI passed.

Purpose:

Connect paper-facing common/same-context assumptions to the exposing variant.

Main contents:

```lean
TrimmedPresentationPaperMainAssumptions.toPaperExposingAssumptions
TrimmedPresentationPaperSameContextAssumptions.identifies_from_positive_text_via_exposing
```

Paper correspondence:

This makes the paper-level assumption diagram explicit.

---

### 2.92 `CharacteristicSamplePaperWitnessTheorem.lean`

Status: CI passed.

Purpose:

Hide the concrete pre-core datum `D` inside paper witness packages.

Main contents:

```lean
TrimmedPresentationPaperMainWitness
TrimmedPresentationPaperExposingWitness
TrimmedPresentationPaperSameContextWitness
trimmed_paper_witness_main_theorem
```

Paper correspondence:

This supports the statement:

```text
if a trimmed presentation witness exists,
then the reachable learner identifies the target language.
```

---

### 2.93 `CharacteristicSampleGlobalPaperWitnessTheorem.lean`

Status: CI passed.

Purpose:

Hide the trimmed output-type presentation `T` inside global witness packages.

Main contents:

```lean
TrimmedPresentationGlobalPaperMainWitness
TrimmedPresentationGlobalPaperExposingWitness
TrimmedPresentationGlobalPaperSameContextWitness
trimmed_global_paper_witness_main_theorem
```

Paper correspondence:

This supports:

```text
if a global trimmed presentation witness exists,
then identification follows.
```

---

### 2.94 `CharacteristicSampleBoundedGlobalPaperTheorem.lean`

Status: CI passed.

Purpose:

Hide the fanout bound `f` inside bounded global witness packages.

Main contents:

```lean
TrimmedPresentationBoundedGlobalPaperMainWitness
TrimmedPresentationBoundedGlobalPaperExposingWitness
TrimmedPresentationBoundedGlobalPaperSameContextWitness
trimmed_bounded_global_paper_main_theorem
trimmed_bounded_global_paper_exists_bound_and_characteristic_sample
```

Paper correspondence:

This gives:

```text
some finite bound and its global witness
⇒ identification at that bound.
```

---

### 2.95 `CharacteristicSampleExistentialPaperTheorem.lean`

Status: CI passed. Latest named CI point: Lean CI #583, commit `8025962`.

Purpose:

State the final paper-facing existential form from a mere `Nonempty` bounded global witness.

Main contents:

```lean
ExistsBoundedPositiveCharacteristicSample
ExistsBoundedReachableIdentification
ExistsBoundedPrefixExactIdentification

trimmed_existential_paper_exists_characteristic_sample
trimmed_existential_paper_main_theorem
trimmed_existential_paper_prefix_exact_theorem
```

Paper correspondence:

This is the current strongest theorem-facing endpoint:

```text
Nonempty BoundedGlobalPaperMainWitness
⇒ ∃ f, reachable learner at f identifies the target language.
```

It is still conditional on existence of the bounded global witness, but the chain from that package to Gold-style identification is Lean-verified.


### 2.96 `CharacteristicSampleExposingTransportConstruction.lean`

Status: CI passed / user-confirmed.

Purpose:

Introduce a construction-facing package for the direct exposing-context route.

Main contents:

```lean
TrimmedPresentationExposingTransportConstructionData
trimmed_exposing_transport_construction_main_theorem
```

Paper correspondence:

This packages the route:

```text
split trimmed presentation data
+
grammar-rule builder
+
exposing-context transport
+
splicing/fanout/substitutability
⇒ reachable identification.
```

---

### 2.97 `CharacteristicSampleAnchorCommonTransportConstruction.lean`

Status: CI passed / user-confirmed.

Purpose:

Introduce the preferred construction-facing package for anchor common-context transport.

Main contents:

```lean
TrimmedPresentationAnchorCommonTransportConstructionData
trimmed_anchor_common_transport_construction_main_theorem
trimmed_anchor_common_transport_construction_main_theorem_via_exposing
```

Paper correspondence:

This is the preferred semantic route:

```text
anchor common context evidence
⇒ anchor distribution transport
⇒ exposing transport
⇒ reachable identification.
```

---

### 2.98 `CharacteristicSampleSameContextTransportConstruction.lean`

Status: CI passed / user-confirmed.

Purpose:

Introduce the stronger same-context construction package.

Main contents:

```lean
TrimmedPresentationSameContextTransportConstructionData
trimmed_same_context_transport_construction_main_theorem
trimmed_same_context_transport_construction_main_theorem_via_exposing
```

Paper correspondence:

This gives a useful debug route:

```text
same-context transport
⇒ exposing-context transport
⇒ reachable identification.
```

---

### 2.99 `CharacteristicSampleTransportConstructionDiagram.lean`

Status: CI passed / user-confirmed.

Purpose:

Record construction-level conversions among the transport packages.

Main contents:

```lean
exposingConstruction_of_anchorCommonConstruction
exposingConstruction_of_sameContextConstruction
trimmed_transport_construction_diagram_anchor_common_to_exposing
trimmed_transport_construction_diagram_same_context_to_exposing
```

Paper correspondence:

This proves that stronger/common construction routes can be funneled through the direct exposing construction route.

---

### 2.100 `CharacteristicSampleTransportConstructionChoice.lean`

Status: CI passed / user-confirmed.

Purpose:

Package the exposing, anchor-common, and same-context construction routes into one choice.

Main contents:

```lean
TrimmedPresentationTransportConstructionChoice
trimmed_transport_construction_choice_main_theorem
```

Paper correspondence:

This gives one theorem interface for all three transport construction routes.

---

### 2.101 `CharacteristicSampleTransportConstructionBase.lean`

Status: CI passed / user-confirmed.

Purpose:

Factor common base construction data away from the transport witness.

Main contents:

```lean
TrimmedPresentationBaseConstructionData
TrimmedPresentationTransportWitnessChoice
TrimmedPresentationStructuredTransportConstructionData
trimmed_structured_transport_construction_main_theorem
```

Paper correspondence:

This splits the task into:

```text
base construction data
+
one transport witness
⇒ reachable identification.
```

---

### 2.102 `CharacteristicSampleTransportConstructionExistential.lean`

Status: CI passed / user-confirmed.

Purpose:

Introduce the existential interface:

```text
∃ base, Nonempty (TransportWitnessChoice base)
```

Main contents:

```lean
ExistsBaseWithTransportWitnessChoice
ExistsBaseWithExposingTransport
ExistsBaseWithAnchorCommonTransport
ExistsBaseWithSameContextTransport
trimmed_exists_base_transport_choice_main_theorem
```

Paper correspondence:

This lets the proof construct the base and transport witness separately.

---

### 2.103 `CharacteristicSampleBaseConstructionLayers.lean`

Status: CI passed / user-confirmed.

Purpose:

Split base construction into core data and global assumptions.

Main contents:

```lean
TrimmedPresentationCoreConstructionData
TrimmedPresentationGlobalConstructionAssumptions
TrimmedPresentationLayeredTransportConstructionData
trimmed_exists_layered_transport_construction_main_theorem
```

Paper correspondence:

This separates:

```text
T, D, builder
```

from:

```text
splicingConstructor, fanout, promise.
```

---

### 2.104 `CharacteristicSampleCoreConstructionLayers.lean`

Status: CI passed / user-confirmed.

Purpose:

Split the core into presentation, pre-core, and rule-builder layers.

Main contents:

```lean
TrimmedPresentationPresentationConstructionData
TrimmedPresentationPreCoreConstructionData
TrimmedPresentationRuleBuilderConstructionData
TrimmedPresentationFullyLayeredConstructionData
```

Paper correspondence:

This isolates the future concrete construction targets:

```text
T : TrimmedOutputTypePresentation
D : TrimmedPresentationPreCoreData T f
builder : TrimmedPresentationGrammarRuleBuilder D
```

---

### 2.105 `CharacteristicSampleCoreConstructionExistential.lean`

Status: CI passed / user-confirmed.

Purpose:

Expose the split core as a direct flat record.

Main contents:

```lean
TrimmedPresentationSplitCoreConstructionData
TrimmedPresentationSplitLayeredTransportConstructionData
TrimmedPresentationSplitLayeredExposingConstructionData
TrimmedPresentationSplitLayeredAnchorCommonConstructionData
TrimmedPresentationSplitLayeredSameContextConstructionData
```

Paper correspondence:

This makes the core construction target visibly:

```text
f, T, D, builder.
```

---

### 2.106 `CharacteristicSampleSplitCoreGlobalLayer.lean`

Status: CI passed / user-confirmed.

Purpose:

Put split core and global assumptions together, while leaving transport out.

Main contents:

```lean
TrimmedPresentationSplitCoreWithGlobalAssumptions
ExistsSplitCoreGlobalWithTransportChoice
ExistsSplitCoreGlobalWithAnchorCommonTransport
```

Paper correspondence:

This organizes the proof as:

```text
construct split core
construct global assumptions
construct one transport witness.
```

---

### 2.107 `CharacteristicSampleGlobalAssumptionLayers.lean`

Status: CI passed / user-confirmed.

Purpose:

Split global assumptions into splicing and target assumptions.

Main contents:

```lean
TrimmedPresentationSplicingConstructionAssumption
TrimmedPresentationTargetConstructionAssumptions
TrimmedPresentationSplitGlobalConstructionAssumptions
```

Paper correspondence:

This separates context algebra from the target-language assumptions.

---

### 2.108 `CharacteristicSampleTargetAssumptionLayers.lean`

Status: CI passed / user-confirmed.

Purpose:

Split target assumptions into fanout and substitutability.

Main contents:

```lean
TrimmedPresentationFanoutConstructionAssumption
TrimmedPresentationSubstitutabilityConstructionAssumption
TrimmedPresentationFullySplitGlobalConstructionAssumptions
```

Paper correspondence:

This isolates:

```text
G.FanoutAtMost f
FixedNamedTupleSubstitutable f obs G.StringLanguage
```

as independent assumptions.

---

### 2.109 `CharacteristicSampleFlatConstructionData.lean`

Status: CI passed / user-confirmed.

Purpose:

Introduce flat route-specific construction records.

Main contents:

```lean
TrimmedPresentationFlatExposingConstructionData
TrimmedPresentationFlatAnchorCommonConstructionData
TrimmedPresentationFlatSameContextConstructionData
```

Paper correspondence:

These records put all construction ingredients at top level:

```text
f, T, D, builder, splicing, fanout, promise, transport.
```

---

### 2.110 `CharacteristicSampleFlatConstructionChoice.lean`

Status: CI passed / user-confirmed.

Purpose:

Package the flat exposing, anchor-common, and same-context routes into one choice.

Main contents:

```lean
TrimmedPresentationFlatConstructionChoice
ExistsFlatConstructionChoice
trimmed_flat_construction_choice_main_theorem
```

Paper correspondence:

This gives one flat construction theorem interface for all routes.

---

### 2.111 `CharacteristicSampleFlatConstructionDisjunction.lean`

Status: CI passed / user-confirmed.

Purpose:

Introduce a paper-readable disjunction of flat construction routes.

Main contents:

```lean
ExistsFlatConstructionRouteDisjunction
ExistsAnyFlatConstruction
trimmed_flat_construction_route_disjunction_main_theorem
trimmed_any_flat_construction_main_theorem
```

Paper correspondence:

This gives the paper-friendly hypothesis:

```text
flat exposing ∨ flat anchor-common ∨ flat same-context.
```

---

### 2.112 `CharacteristicSampleFinalConstructionFacade.lean`

Status: CI passed / user-confirmed.

Purpose:

Introduce the final construction-facing facade.

Main contents:

```lean
TrimmedPresentationConstructiveMainAssumptions
trimmed_constructive_main_theorem
trimmed_constructive_characteristic_sample_theorem
trimmed_constructive_prefix_exact_theorem
```

Paper correspondence:

This is the stable internal theorem-facing facade for constructive assumptions.

---

### 2.113 `CharacteristicSampleConstructiveLearningTheorem.lean`

Status: CI passed / user-confirmed.

Purpose:

Package characteristic sample, prefix exactness, and Gold identification together.

Main contents:

```lean
ExistsConstructiveFlatRoute
ExistsConstructiveBoundedIdentification
ConstructiveLearningConsequences
trimmed_constructive_learning_consequences
```

Paper correspondence:

This packages the three main consequences of the constructive route.

---

### 2.114 `CharacteristicSampleConstructiveLearnabilityFacade.lean`

Status: CI passed / user-confirmed.

Purpose:

Introduce short constructive-learnability names.

Main contents:

```lean
ConstructivelyLearnableByFlatRoutes
ConstructivelyIdentifiedByReachableLearner
ConstructiveLearnabilitySummary
trimmed_constructively_learnable_identified
```

Paper correspondence:

This gives the compact statement:

```text
ConstructivelyLearnableByFlatRoutes G obs
⇒ ConstructivelyIdentifiedByReachableLearner G obs.
```

---

### 2.115 `CharacteristicSamplePaperConstructiveStatement.lean`

Status: CI passed / user-confirmed. Latest named CI point: Lean CI #603, commit `eca688f`.

Purpose:

Give the stable paper-facing constructive theorem names.

Main contents:

```lean
PaperConstructiveRouteAssumption
PaperConstructiveCharacteristicSampleConclusion
PaperConstructivePrefixExactConclusion
PaperConstructiveIdentificationConclusion
PaperConstructiveLearningConclusionPackage

paper_constructive_learnability_main_theorem
trimmed_paper_constructive_main_theorem
trimmed_paper_constructive_conclusion_package
```

Paper correspondence:

This is the current strongest paper-facing constructive statement
preferred anchor-common all-pieces checklist
splicing decomposition to context functions and namedFill equations:

```text
PaperConstructiveRouteAssumption G obs
⇒ PaperConstructiveIdentificationConclusion G obs.
```

Expanded:

```text
if one verified flat constructive route exists,
then the reachable learner identifies the target language for some finite bound.
```

---



### 2.116 `CharacteristicSamplePaperConstructiveRouteCorollaries.lean`

Status: CI passed / user-confirmed.

Purpose:

Add route-specific paper-facing corollaries from the final constructive statement.

Main contents:

```lean
PaperExposingConstructiveRouteAssumption
PaperAnchorCommonConstructiveRouteAssumption
PaperSameContextConstructiveRouteAssumption
PaperPreferredConstructiveRouteAssumption

trimmed_paper_preferred_constructive_main_theorem
trimmed_paper_anchor_common_constructive_main_theorem
trimmed_paper_exposing_constructive_main_theorem
trimmed_paper_same_context_constructive_main_theorem
```

Paper correspondence:

This identifies the anchor-common flat construction as the preferred paper route.

---

### 2.117 `CharacteristicSamplePreferredAnchorCommonConstruction.lean`

Status: CI passed / user-confirmed.

Purpose:

Introduce a stable paper-facing data record for the preferred anchor-common construction route.

Main contents:

```lean
PaperPreferredAnchorCommonConstructionData
ExistsPaperPreferredAnchorCommonConstruction
trimmed_paper_preferred_anchor_common_construction_main_theorem
```

Paper correspondence:

This record has the fields:

```text
fanoutBound
presentation
data
builder
splicingConstructor
fanout
promise
commonTransport
```

and implies the paper-facing identification conclusion.

---

### 2.118 `CharacteristicSamplePreferredAnchorCommonTargets.lean`

Status: CI passed / user-confirmed.

Purpose:

Split the preferred anchor-common construction target into three major pieces.

Main contents:

```lean
PaperPreferredAnchorCommonLayeredConstructionData
ExistsPaperPreferredAnchorCommonLayeredConstruction
ExistsPaperPreferredAnchorCommonConstructionTargets
trimmed_paper_preferred_anchor_common_targets_main_theorem
```

Paper correspondence:

This isolates:

```text
split core
fully split global assumptions
anchor-common transport.
```

---

### 2.119 `CharacteristicSamplePreferredAnchorCommonTargetPieces.lean`

Status: CI passed / user-confirmed.

Purpose:

Name each of the three preferred anchor-common target pieces separately.

Main contents:

```lean
PaperPreferredSplitCoreTarget
PaperPreferredFullySplitGlobalTarget
PaperPreferredAnchorCommonTransportTarget
PaperPreferredAnchorCommonSeparatedTargets
```

Paper correspondence:

This makes it possible to construct split core, global assumptions, and transport separately.

---

### 2.120 `CharacteristicSamplePreferredSplitCorePieces.lean`

Status: CI passed / user-confirmed.

Purpose:

Split the preferred split core into four construction pieces.

Main contents:

```lean
PaperPreferredFanoutBoundTarget
PaperPreferredPresentationTarget
PaperPreferredPreCoreTarget
PaperPreferredRuleBuilderTarget
ExistsPaperPreferredAnchorCommonPiecewiseTargets
```

Paper correspondence:

This exposes the concrete core construction path:

```text
fanout bound
⇒ trimmed output-type presentation
⇒ pre-core data
⇒ grammar-rule builder.
```

---

### 2.121 `CharacteristicSamplePreferredGlobalPieces.lean`

Status: CI passed / user-confirmed.

Purpose:

Split fully split global assumptions into their three sources.

Main contents:

```lean
PaperPreferredSplicingConstructorTarget
PaperPreferredFanoutAssumptionTarget
PaperPreferredSubstitutabilityAssumptionTarget
PaperPreferredFullySplitGlobalSeparatedTarget
PaperPreferredAnchorCommonPiecewiseSeparatedGlobalTargets
```

Paper correspondence:

This isolates:

```text
NamedContextSplicingConstructor
G.FanoutAtMost f
FixedNamedTupleSubstitutable f obs G.StringLanguage.
```

---

### 2.122 `CharacteristicSamplePreferredAllPieces.lean`

Status: CI passed / user-confirmed.

Purpose:

Introduce the complete preferred anchor-common route checklist.

Main contents:

```lean
PaperPreferredAnchorCommonAllPieces
ExistsPaperPreferredAnchorCommonAllPieces
trimmed_paper_preferred_anchor_common_all_pieces_main_theorem
```

Paper correspondence:

This is the clean all-pieces target.  Once all eight fields are supplied, the paper-facing identification conclusion follows.

---

### 2.123 `CharacteristicSampleNamedContextSplicingConstruction.lean`

Status: CI passed / user-confirmed.

Purpose:

Isolate the named-context splicing constructor as an independent construction datum.

Main contents:

```lean
NamedContextSplicingConstructionData
ExistsNamedContextSplicingConstruction
PaperPreferredAnchorCommonAllPiecesWithoutSplicing
trimmed_paper_preferred_anchor_common_without_splicing_main_theorem
```

Paper correspondence:

This separates the preferred all-pieces target into:

```text
all preferred pieces except splicing
+
NamedContextSplicingConstructor.
```

---

### 2.124 `CharacteristicSampleNamedContextSplicingPieces.lean`

Status: CI passed / user-confirmed.

Purpose:

Split one binary named-context splicing object into left and right pieces.

Main contents:

```lean
LeftNamedContextSplicingPiece
RightNamedContextSplicingPiece
NamedContextSplicingPiecewiseConstructor
```

Paper correspondence:

This reduces `BinaryNamedContextSplicing parent body` to left and right child-context constructions.

---

### 2.125 `CharacteristicSampleNamedContextSplicingLeftRightConstructors.lean`

Status: CI passed / user-confirmed.

Purpose:

Split the universal splicing constructor into independent left and right universal constructors.

Main contents:

```lean
NamedContextLeftSplicingConstructor
NamedContextRightSplicingConstructor
NamedContextLeftRightSplicingConstructors
```

Paper correspondence:

This allows the left-child and right-child context constructions to be attacked separately.

---

### 2.126 `CharacteristicSampleNamedContextSplicingLocalTargets.lean`

Status: CI passed / user-confirmed.

Purpose:

Introduce local splicing targets for a fixed parent context and a fixed binary template.

Main contents:

```lean
LeftNamedContextSplicingLocalTarget
RightNamedContextSplicingLocalTarget
BinaryNamedContextSplicingLocalTarget
NamedContextLeftSplicingLocalConstructor
NamedContextRightSplicingLocalConstructor
NamedContextBinarySplicingLocalConstructor
```

Paper correspondence:

This makes the most local target visible:

```text
fixed parent context
+
fixed binary template
⇒ local left/right splicing target.
```

---

### 2.127 `CharacteristicSampleNamedContextSplicingTemplateTargets.lean`

Status: CI passed / user-confirmed.

Purpose:

Move one level outward: fix a binary template and let the parent context vary.

Main contents:

```lean
TemplateLeftNamedContextSplicingConstructor
TemplateRightNamedContextSplicingConstructor
TemplateBinaryNamedContextSplicingConstructor
NamedContextTemplateLeftSplicingConstructor
NamedContextTemplateRightSplicingConstructor
NamedContextTemplateBinarySplicingConstructor
```

Paper correspondence:

This sets up a template-by-template construction strategy.

---

### 2.128 `CharacteristicSampleNamedContextSplicingTemplateChoices.lean`

Status: CI passed / user-confirmed.

Purpose:

Separate template-by-template existence from a universal template-level constructor.

Main contents:

```lean
ExistsTemplateLeftNamedContextSplicingConstructor
ExistsTemplateRightNamedContextSplicingConstructor
ExistsTemplateBinaryNamedContextSplicingConstructor
ForallTemplateLeftNamedContextSplicingConstructor
ForallTemplateRightNamedContextSplicingConstructor
ForallTemplateBinaryNamedContextSplicingConstructor
```

Paper correspondence:

This uses `Classical.choice` as packaging: pointwise `Nonempty` template data can be assembled into a universal constructor.

---

### 2.129 `CharacteristicSampleNamedContextSplicingParentChoices.lean`

Status: CI passed / user-confirmed.

Purpose:

Reduce template-level construction to parentwise local target existence.

Main contents:

```lean
ForallParentLeftNamedContextSplicingLocalTarget
ForallParentRightNamedContextSplicingLocalTarget
ForallParentBinaryNamedContextSplicingLocalTarget
ForallTemplateParentLeftNamedContextSplicingLocalTarget
ForallTemplateParentRightNamedContextSplicingLocalTarget
ForallTemplateParentBinaryNamedContextSplicingLocalTarget
```

Paper correspondence:

This shows:

```text
∀ body parent, local target
⇒ template-level constructor
⇒ NamedContextSplicingConstructor.
```

---

### 2.130 `CharacteristicSampleNamedContextSplicingContextFamilies.lean`

Status: CI passed / user-confirmed.

Purpose:

Expose local splicing targets as explicit context families and namedFill equations.

Main contents:

```lean
ParentwiseLeftSplicingContextFamily
ParentwiseRightSplicingContextFamily
ParentwiseBinarySplicingContextFamily
ForallTemplateParentwiseLeftSplicingContextFamily
ForallTemplateParentwiseRightSplicingContextFamily
ForallTemplateParentwiseBinarySplicingContextFamily
```

Paper correspondence:

This displays the actual splicing construction shape:

```text
leftContext parent y
rightContext parent u
namedFill equations.
```

---

### 2.131 `CharacteristicSampleNamedContextSplicingContextEquations.lean`

Status: CI passed / user-confirmed. Latest named CI point: Lean CI #620, commit `8ff8cfb`.

Purpose:

Split parentwise context families into context functions and equation proofs.

Main contents:

```lean
ParentwiseLeftSplicingContextFunctions
ParentwiseRightSplicingContextFunctions
ParentwiseBinarySplicingContextFunctions

ParentwiseLeftSplicingContextEquations
ParentwiseRightSplicingContextEquations
ParentwiseBinarySplicingContextEquations

ForallTemplateParentwiseBinarySplicingContextFunctionsWithEquations
existsNamedContextSplicingConstruction_of_context_functions_equations
trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_context_functions_equations
```

Paper correspondence:

This is the current most explicit named-context splicing target:

```text
define leftContext and rightContext
+
prove the two namedFill equations
⇒ NamedContextSplicingConstructor
⇒ preferred paper theorem.
```

---



### 2.132 `CharacteristicSampleNamedContextSplicingExactOnceConstruction.lean`

Status: CI passed / user-confirmed.

Purpose:

Replace the false unrestricted named-context splicing premise by a concrete
constructor for exact-once templates.

Main contents:

```lean
squareBody_not_exactlyOnce
square_template_no_splicing

Tok
realizeTokens
holeSeq
NF
build

bodyLeftTokens
leftTokens
leftContextNSC
leftContext_fill_eq

bodyRightTokens
rightTokens
rightContextNSC
rightContext_fill_eq

ExactNamedContextSplicingConstructor
exactSplice
exact_namedContextSplicingConstructor

ExactNamedContextSplicingConstructor.toRuleSplicingEvidence
ExactNamedContextSplicingConstructor.toRuleSplicingProvider
ExactNamedContextSplicingConstructor.toFillingWitnessFamily
```

Paper correspondence:

This is the concrete Lean proof of the filling-identity construction used in the
paper.  Parent contexts and binary templates are flattened to terminal/hole
tokens, normalized back into named contexts, and proved well formed using the
exact-once variable-count hypotheses.

Important correction:

```text
NamedContextSplicingConstructor α
```

without exact-once hypotheses is false in general.  The square template using
one child component twice gives a formal counterexample.  The corrected
constructor is:

```lean
ExactNamedContextSplicingConstructor α
```

and is applied only to grammar rules through:

```lean
G.BinaryRulesExactlyOnce.
```

---

### 2.133 `CharacteristicSampleNamedContextSplicingExactOnceIntegration.lean`

Status: CI passed / user-confirmed.

Purpose:

Integrate concrete exact-once filling witnesses into the already verified
characteristic-sample and Gold-identification chain without using the false
legacy constructor.

Main contents:

```lean
TrimmedPresentationSampleData.exactFillingWitnessFamily
TrimmedPresentationSampleData.toExactReachableBlueprint
TrimmedPresentationSampleData.exact_characteristic_sample
TrimmedPresentationSampleData.exact_reconstruction_for_positive_superset
TrimmedPresentationSampleData.exact_prefix_reconstruction
TrimmedPresentationSampleData.exact_identifies_from_positive_text

PaperPreferredAnchorCommonAllPiecesWithoutSplicing.exactSample
PaperPreferredAnchorCommonAllPiecesWithoutSplicing.exactSampleData
PaperPreferredAnchorCommonAllPiecesWithoutSplicing.toExactReachableBlueprint
PaperPreferredAnchorCommonAllPiecesWithoutSplicing.exact_paper_main_theorem
PaperPreferredAnchorCommonAllPiecesWithoutSplicing.exact_working_paper_main_theorem

trimmed_paper_preferred_anchor_common_exact_once_main_theorem
trimmed_paper_preferred_anchor_common_exact_working_main_theorem
```

Paper correspondence:

```text
finite trimmed sample data
+
exact-once binary rules
+
fanout
+
fixed-observation substitutability
⇒ characteristic sample
⇒ exact reconstruction
⇒ Gold identification.
```

The splicing constructor is no longer a paper-facing assumption; it is an
internally constructed object.

---

### 2.134 `CharacteristicSampleExactOnceMinimalPaperRoute.lean`

Status: CI passed / user-confirmed.

Purpose:

Provide a smaller corrected paper route and remove an unused
`AnchorCommonContextTransport` premise from the builder-based route.

Main contents:

```lean
PaperExactOnceMinimalPieces
PaperExactOnceMinimalPieces.sample
PaperExactOnceMinimalPieces.sampleData
PaperExactOnceMinimalPieces.toExactReachableBlueprint
PaperExactOnceMinimalPieces.characteristic_sample
PaperExactOnceMinimalPieces.exact_for_positive_superset
PaperExactOnceMinimalPieces.prefix_exact_eventually
PaperExactOnceMinimalPieces.identifies_from_positive_text
PaperExactOnceMinimalPieces.paper_main_theorem
PaperExactOnceMinimalPieces.exact_working_paper_main_theorem

ExistsPaperExactOnceMinimalPieces
trimmed_paper_exact_once_minimal_main_theorem
trimmed_paper_exact_working_minimal_main_theorem
```

Current assumptions of this route:

```text
fanout bound
trimmed output-type presentation
pre-core data
positive grammar-rule builder
fanout condition
fixed-observation substitutability
exact-once binary rules / exact working conditions
```

No common-context transport and no unrestricted splicing constructor are
required.

---

### 2.135 `CharacteristicSampleExactOnceExposingTransportRoute.lean`

Status: CI passed.

Latest confirmed point:

```text
Lean CI #624
Commit: c60dbd3
```

Purpose:

Connect the existing exposing-context transport mechanism to the concrete
exact-once splicing construction.

Main contents:

```lean
TrimmedPresentationExposingTransportData.exactSampleData
TrimmedPresentationExposingTransportData.toExactReachableBlueprint
TrimmedPresentationExposingTransportData.exact_characteristic_sample
TrimmedPresentationExposingTransportData.exact_for_positive_superset
TrimmedPresentationExposingTransportData.exact_prefix_reconstruction
TrimmedPresentationExposingTransportData.exact_identifies_from_positive_text
TrimmedPresentationExposingTransportData.exact_paper_main_theorem
TrimmedPresentationExposingTransportData.exact_working_paper_main_theorem

trimmed_exposing_transport_exact_once_main_theorem
trimmed_exposing_transport_exact_once_conclusion_package
trimmed_exposing_transport_exact_working_main_theorem
trimmed_exposing_transport_exact_working_conclusion_package
```

Paper correspondence:

```text
exposing-context transport
⇒ positivity of terminal/binary/start witness words
⇒ finite positive characteristic sample
+
concrete exact-once splicing
⇒ exact reconstruction and Gold identification.
```

This is currently the strongest corrected paper-facing route because it no
longer assumes a fully pre-built positive grammar-rule builder.  The remaining
semantic obligation is to construct the exposing-transport data itself from the
concrete trimmed presentation and the target substitutability promise.

---



### 2.136 `CharacteristicSampleExactOnceDerivationalExposureRoute.lean`

Status: CI passed / user-confirmed.

Purpose:

Replace the unconditional `TrimmedPresentationExposingContextTransport` premise
by the paper-faithful derivational invariant:

```lean
TrimmedPresentationDerivationalExposure D
```

Main semantic fields:

```lean
anchor_derives
expose_accepts_derives
```

Verified route:

```text
derivational exposure
⇒ terminal/binary/start witness positivity
⇒ finite characteristic sample
⇒ concrete exact-once filling witnesses
⇒ exact reconstruction and Gold identification.
```

---

### 2.137 `CharacteristicSampleExactOnceFiniteDerivationalExposureRoute.lean`

Status: CI passed / user-confirmed.

Purpose:

Construct the finite base-nonterminal cover and terminal/start arity selectors
from `Finset.univ` and `G.BasicWorkingConditions`.

This removes hand-supplied finite-cover and arity-selector data from the
derivational-exposure route.

---

### 2.138 `CharacteristicSampleExactOnceFiniteNonterminalDerivationalExposureRoute.lean`

Status: CI passed / user-confirmed.

Confirmed point:

```text
Lean CI #627
Commit: 9b6f7ec
```

Purpose:

Weaken the public nonterminal enumeration assumption from

```lean
[Fintype N] [DecidableEq N]
```

to the natural proposition

```lean
[Finite N].
```

A `Fintype` and decidable equality are installed internally by classical
choice.  The resulting sample, prefix-exact theorem, and Gold theorem do not
depend on a caller-selected enumeration.

---

### 2.139 `CharacteristicSampleExactOnceSuccessfulDerivationSpineRoute.lean`

Status: CI passed / user-confirmed.

Purpose:

Construct derivational exposure from explicit successful paths to the grammar
start.

Main object:

```lean
ExactSuccessfulDerivationSpine G A c
```

Constructors:

```lean
root
throughStart
throughLeft
throughRight
```

Key theorem:

```lean
ExactSuccessfulDerivationSpine.acceptsDerives
```

An explicit spine context accepts every tuple derivable from its hole
nonterminal.  Binary descent uses the already verified exact-once child-context
constructors.

---

### 2.140 `CharacteristicSampleExactOnceSuccessfulOccurrenceRoute.lean`

Status: CI passed / user-confirmed.

Purpose:

Combine anchor derivability and the surrounding successful spine into one
inductively generated occurrence witness:

```lean
ExactSuccessfulDerivationOccurrence G A x c
```

Main consequences:

```lean
ExactSuccessfulDerivationOccurrence.derives
ExactSuccessfulDerivationOccurrence.spine
ExactSuccessfulDerivationOccurrence.accepts
ExactSuccessfulDerivationOccurrence.exposedWithContext
```

A family of such occurrences constructs
`TrimmedPresentationDerivationalExposure`.

---

### 2.141 `OutputTypeTrimmedPresentationSuccessfulOccurrenceConstruction.lean`

Status: CI passed / user-confirmed.

Purpose:

Construct the abstract typed anchor/exposure witness layer from explicit
successful typed occurrences.

Main objects:

```lean
PresentTypedSuccessfulOccurrence X
TypedSuccessfulOccurrenceFamily P
SuccessfulOccurrenceCompletePresentation G obs
```

Main constructions:

```lean
TypedSuccessfulOccurrenceFamily.toTrimmedNonterminalWitnesses
CompleteOutputTypePresentation.withSuccessfulOccurrences
```

Verified consequences include typed-anchor derivability, stored output-type
correctness, universal acceptance of derivable tuples, explicit successful
occurrence witnesses, and preservation of presentation language.

---

### 2.142 `CharacteristicSampleExactOnceSuccessfulPresentationRoute.lean`

Status: CI passed / user-confirmed.

Purpose:

Descend from typed successful occurrences to the base-indexed pre-core.

Main objects:

```lean
SuccessfulOccurrenceBaseRepresentativeSelection
SuccessfulOccurrenceRepresentativeOutputCompatibility
SuccessfulOccurrencePreCoreConstruction
```

Main constructions:

```lean
SuccessfulOccurrencePreCoreConstruction.toPreCoreData
SuccessfulOccurrencePreCoreConstruction.toSuccessfulOccurrenceData
```

Terminal, binary, and start tuple-type equations are derived from
representative output compatibility.  The start word is extracted canonically
from the selected start anchor.

---

### 2.143 `CharacteristicSampleExactOnceSuccessfulRuleRealizationRoute.lean`

Status: CI passed / user-confirmed.

Purpose:

Replace direct rule-output equations by actual typed terminal, binary, and
start rules present in the finite presentation.

Main object:

```lean
SuccessfulOccurrenceRepresentativeRuleRealization
```

Main construction:

```lean
SuccessfulOccurrenceRepresentativeRuleRealization.toOutputCompatibility
```

Thus present typed-rule realization implies all pre-core output equations and
the full characteristic-sample / Gold route.

---

### 2.144 `CharacteristicSampleExactOnceCanonicalRuleClosureRoute.lean`

Status: CI passed / user-confirmed.

Purpose:

Remove arbitrary choices of typed rules.  Define canonical typed terminal,
binary, and start rules from the original rule and the selected representative
output types.

Main definitions:

```lean
SuccessfulOccurrenceBaseRepresentativeSelection.canonicalTerminalRule
SuccessfulOccurrenceBaseRepresentativeSelection.canonicalBinaryRule
SuccessfulOccurrenceBaseRepresentativeSelection.canonicalStartRule
SuccessfulOccurrenceRepresentativeCanonicalRuleClosure
```

Main bridge:

```lean
SuccessfulOccurrenceRepresentativeCanonicalRuleClosure.toRuleRealization
```

Strongest current paper-facing endpoint:

```lean
trimmed_successful_canonical_rule_closure_exact_working_conclusion_package
```

---

### 2.145 `OutputTypePresentationWorkingGrammar.lean`

Status: CI passed / user-confirmed.

Latest confirmed point:

```text
Lean CI #634
Commit: 168022f
```

Purpose:

Turn every finite output-type presentation into an actual `WorkingMCFG`.

Main syntax and construction:

```lean
PresentationGrammarNonterminal
presentationGrammarArity
liftPresentationStartRule
liftPresentationTerminalRule
liftPresentationBinaryRule
OutputTypeRefinementPresentation.toWorkingMCFG
```

Main verified properties:

```lean
OutputTypeRefinementPresentation.toWorkingMCFG_basicWorkingConditions
OutputTypeRefinementPresentation.toWorkingMCFG_exactWorkingConditions
OutputTypeRefinementPresentation.toWorkingMCFG_fanoutAtMost
PresentationDerives.toWorkingMCFG
PresentationStringDerives.toWorkingMCFG
presentationStringLanguage_subset_workingGrammar
CompleteOutputTypePresentation.original_subset_workingGrammar
CompleteOutputTypePresentation.workingGrammar_conditions
```

Paper correspondence:

A finite typed presentation is now represented by a genuine grammar with one
fresh start symbol and one nonterminal for each typed node.  Present typed
rules are lifted to actual finite grammar rules.  Presentation derivations
embed into this grammar, and the original exact-once/fan-out conditions are
preserved.

Remaining converse:

The file currently proves that presentation derivations embed into the new
grammar.  A converse erasure theorem for arbitrary derivations of
`P.toWorkingMCFG`, and hence exact language equality with
`PresentationStringLanguage P`, remains to be proved.

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
  ↓
CharacteristicSampleTransportObligations
  ↓
CharacteristicSampleTransportObligationsFromSample
  ↓
CharacteristicSampleTransportObligationsFromExistingSamples
  ↓
CharacteristicSampleTransportObligationsFromBuilders
  ↓
CharacteristicSampleTransportObligationsFromComponents
  ↓
CharacteristicSampleTransportObligationsFromRules
  ↓
CharacteristicSampleTransportObligationsFromRuleData
  ↓
CharacteristicSampleTransportObligationsFromCoreData
  ↓
CharacteristicSampleTransportObligationsFromAnchorData
  ↓
CharacteristicSampleSemanticConstructionTargets
  ↓
CharacteristicSampleSemanticConstructionTargetLevels
  ↓
CharacteristicSampleSemanticTransportTargets
  ↓
CharacteristicSampleSemanticTransportTargetLevels
  ↓
CharacteristicSampleSameContextTransportTargets
  ↓
CharacteristicSampleSameContextTransportTargetLevels
  ↓
CharacteristicSampleSemanticTransportTargetDiagram
  ↓
CharacteristicSampleCommonToExposingTargetDiagram
  ↓
CharacteristicSampleSemanticMainTheorems
  ↓
CharacteristicSamplePaperMainTheorem
  ↓
CharacteristicSamplePaperMainVariants
  ↓
CharacteristicSamplePaperAssumptionDiagram
  ↓
CharacteristicSamplePaperWitnessTheorem
  ↓
CharacteristicSampleGlobalPaperWitnessTheorem
  ↓
CharacteristicSampleBoundedGlobalPaperTheorem
  ↓
CharacteristicSampleExistentialPaperTheorem
  ↓
CharacteristicSampleExposingTransportConstruction
  ↓
CharacteristicSampleAnchorCommonTransportConstruction
  ↓
CharacteristicSampleSameContextTransportConstruction
  ↓
CharacteristicSampleTransportConstructionDiagram
  ↓
CharacteristicSampleTransportConstructionChoice
  ↓
CharacteristicSampleTransportConstructionBase
  ↓
CharacteristicSampleTransportConstructionExistential
  ↓
CharacteristicSampleBaseConstructionLayers
  ↓
CharacteristicSampleCoreConstructionLayers
  ↓
CharacteristicSampleCoreConstructionExistential
  ↓
CharacteristicSampleSplitCoreGlobalLayer
  ↓
CharacteristicSampleGlobalAssumptionLayers
  ↓
CharacteristicSampleTargetAssumptionLayers
  ↓
CharacteristicSampleFlatConstructionData
  ↓
CharacteristicSampleFlatConstructionChoice
  ↓
CharacteristicSampleFlatConstructionDisjunction
  ↓
CharacteristicSampleFinalConstructionFacade
  ↓
CharacteristicSampleConstructiveLearningTheorem
  ↓
CharacteristicSampleConstructiveLearnabilityFacade
  ↓
CharacteristicSamplePaperConstructiveStatement
  ↓
CharacteristicSamplePaperConstructiveRouteCorollaries
  ↓
CharacteristicSamplePreferredAnchorCommonConstruction
  ↓
CharacteristicSamplePreferredAnchorCommonTargets
  ↓
CharacteristicSamplePreferredAnchorCommonTargetPieces
  ↓
CharacteristicSamplePreferredSplitCorePieces
  ↓
CharacteristicSamplePreferredGlobalPieces
  ↓
CharacteristicSamplePreferredAllPieces
  ↓
CharacteristicSampleNamedContextSplicingConstruction
  ↓
CharacteristicSampleNamedContextSplicingPieces
  ↓
CharacteristicSampleNamedContextSplicingLeftRightConstructors
  ↓
CharacteristicSampleNamedContextSplicingLocalTargets
  ↓
CharacteristicSampleNamedContextSplicingTemplateTargets
  ↓
CharacteristicSampleNamedContextSplicingTemplateChoices
  ↓
CharacteristicSampleNamedContextSplicingParentChoices
  ↓
CharacteristicSampleNamedContextSplicingContextFamilies
  ↓
CharacteristicSampleNamedContextSplicingContextEquations
  ↓
CharacteristicSampleNamedContextSplicingExactOnceConstruction
  ↓
CharacteristicSampleNamedContextSplicingExactOnceIntegration
  ↓
CharacteristicSampleExactOnceMinimalPaperRoute
  ↓
CharacteristicSampleExactOnceExposingTransportRoute
  ↓
CharacteristicSampleExactOnceDerivationalExposureRoute
  ↓
CharacteristicSampleExactOnceFiniteDerivationalExposureRoute
  ↓
CharacteristicSampleExactOnceFiniteNonterminalDerivationalExposureRoute
  ↓
CharacteristicSampleExactOnceSuccessfulDerivationSpineRoute
  ↓
CharacteristicSampleExactOnceSuccessfulOccurrenceRoute
  ↓
OutputTypeTrimmedPresentationSuccessfulOccurrenceConstruction
  ↓
CharacteristicSampleExactOnceSuccessfulPresentationRoute
  ↓
CharacteristicSampleExactOnceSuccessfulRuleRealizationRoute
  ↓
CharacteristicSampleExactOnceCanonicalRuleClosureRoute
  ↓
OutputTypePresentationWorkingGrammar
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


### 4.11 Splicing-constructor reduction and correction

The older interface decomposition remains verified:

```text
binary filling witnesses
⇐ named-context splicing families
⇐ binary-rule splicing evidence.
```

However, the final unrestricted universal-constructor step was too strong.  CI
#624 replaces it with the corrected chain:

```text
G.BinaryRulesExactlyOnce
+
ExactNamedContextSplicingConstructor
⇒ BinaryRuleSplicingEvidence
⇒ BinaryRuleSplicingProvider
⇒ BinaryFillingWitnessFamily.
```

The exact constructor is now concrete rather than assumed.

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

### 4.18 Trimmed sample data to the corrected exact-once reachable route

```text
TrimmedPresentationSampleData
+
G.BinaryRulesExactlyOnce
+
fanout
+
fixed-observation promise
⇒ ReachableCharacteristicBlueprint
⇒ reachable Gold identification.
```

The false unrestricted splicing premise has been removed from this route.




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

This is the verified historical endpoint as of Lean CI #558.


---


### 4.24 Transport-obligation endpoint tower

```text
transport obligations
+
start evidence from sample/builders/components/rules/rule data/core data/anchor data
⇒ FinalReachableData
⇒ reachable identification
```

This entire endpoint tower is now Lean-checked through CI #583.

### 4.25 Semantic construction targets

```text
GrammarRuleBuilder / RuleCoverage / ComponentPackage / ComponentEnumeration
+
CommonContext / Exposing / SameContext transport targets
⇒ reachable identification
```

The target hierarchy is verified as plumbing.  It does not yet construct the semantic transport witnesses.

### 4.26 Transport target diagrams

```text
SameContextTransport ⇒ ExposingContextTransport
AnchorCommonContextTransport ⇒ ExposingContextTransport
```

These diagrams are verified at the grammar-builder, rule-coverage, component-package, and component-enumeration levels.

### 4.27 Paper-facing assumption facades

```text
TrimmedPresentationPaperMainAssumptions
TrimmedPresentationPaperExposingAssumptions
TrimmedPresentationPaperSameContextAssumptions
```

All three packages now have stable theorem names for characteristic samples, prefix exactness, and Gold-style identification.

### 4.28 Paper witness packages

```text
PaperMainWitness hides D
GlobalPaperMainWitness hides T
BoundedGlobalPaperMainWitness hides f
```

The theorem chain remains verified after each layer of dependent data is hidden inside a package.

### 4.29 Existential paper theorem

```text
Nonempty BoundedGlobalPaperMainWitness
⇒ ExistsBoundedReachableIdentification G obs
```

This is the current strongest Lean-checked paper-level facade:

```lean
trimmed_existential_paper_main_theorem
```



### 4.30 Constructive paper facade

The CI #603 chain adds a final constructive facade.  The following path is now Lean-checked:

```text
flat exposing / flat anchor-common / flat same-context construction
⇒ flat construction choice
⇒ route disjunction
⇒ final constructive assumptions
⇒ constructive learning consequences
⇒ paper constructive statement.
```

Stable endpoint:

```lean
trimmed_paper_constructive_main_theorem
```

Meaning:

```text
PaperConstructiveRouteAssumption G obs
⇒ PaperConstructiveIdentificationConclusion G obs.
```

This is a packaging and facade result.  It does not by itself construct the flat route; it makes the remaining construction target paper-readable and stable.



### 4.31 Preferred anchor-common all-pieces checklist

The CI #620 chain introduces a preferred anchor-common checklist:

```lean
PaperPreferredAnchorCommonAllPieces
```

with eight explicit fields:

```text
fanoutBound
presentation
data
builder
splicingConstructor
fanout
promise
commonTransport
```

and proves:

```lean
trimmed_paper_preferred_anchor_common_all_pieces_main_theorem
```

meaning:

```text
ExistsPaperPreferredAnchorCommonAllPieces G obs
⇒ PaperConstructiveIdentificationConclusion G obs.
```

This is now the cleanest preferred route target.

### 4.32 Named-context splicing reduced to context functions and equations

The CI #620 chain also opens the old `NamedContextSplicingConstructor` obligation.  The current endpoint is:

```lean
trimmed_paper_preferred_anchor_common_without_splicing_main_theorem_of_context_functions_equations
```

meaning:

```text
splicing-free preferred pieces
+
ForallTemplateParentwiseBinarySplicingContextFunctionsWithEquations α
⇒ PaperConstructiveIdentificationConclusion G obs.
```

The splicing construction task is now explicit:

```text
for every binary template body,
define parent-indexed leftContext and rightContext functions,
then prove the two namedFill equations.
```

This is still not the completed splicing construction, but it is no longer opaque.



### 4.33 Unrestricted splicing counterexample

The old universal premise is now formally known to be too strong:

```lean
square_template_no_splicing :
  ¬ Nonempty (BinaryNamedContextSplicing trivParent squareBody)
```

The square template uses the same left child variable twice.  A well-formed
arity-one named context contains its sole hole exactly once, so it cannot realize
the required duplicated filling for every input word.

### 4.34 Concrete exact-once splicing construction

For exact-once templates, the left and right child contexts are now explicit
Lean functions:

```lean
leftContextNSC
rightContextNSC
```

with verified equations:

```lean
leftContext_fill_eq
rightContext_fill_eq
```

and a global constructor:

```lean
exact_namedContextSplicingConstructor :
  ExactNamedContextSplicingConstructor α.
```

This discharges the former filling-identity bookkeeping obligation for all
listed binary rules satisfying `G.BinaryRulesExactlyOnce`.

### 4.35 Exact-once route to characteristic samples and identification

The following corrected chain is Lean-checked:

```text
TrimmedPresentationSampleData
+
G.BinaryRulesExactlyOnce
+
fanout
+
fixed-observation substitutability
⇒ ReachableCharacteristicBlueprint
⇒ finite characteristic sample
⇒ exact reconstruction on positive supersets
⇒ eventual prefix exactness
⇒ Gold identification.
```

### 4.36 Exposing-transport exact-once route

This historical CI #624 route is verified:

```text
TrimmedPresentationExposingTransportData
+
G.ExactWorkingConditions
+
fanout
+
fixed-observation substitutability
⇒ PaperConstructiveLearningConclusionPackage.
```

Endpoint:

```lean
trimmed_exposing_transport_exact_working_conclusion_package
```

CI #625--#634 replaces the unconditional exposing-transport premise by
derivational exposure and explicit successful occurrence semantics.  The
exposing-transport endpoint is therefore retained as a verified historical
route rather than the current strongest construction.



### 4.37 Derivational exposure replaces unconditional transport

The strongest corrected route no longer needs

```lean
TrimmedPresentationExposingContextTransport D.
```

Instead it uses the semantically justified invariant:

```lean
TrimmedPresentationDerivationalExposure D
```

with anchor derivability and acceptance of every genuinely derivable tuple by
the selected exposing context.

### 4.38 Successful derivation spines and occurrences

The following concrete inductive semantics is verified:

```text
successful root/start/binary path
⇒ explicit named exposing context
⇒ acceptance of every tuple derivable at the hole nonterminal.
```

A single `ExactSuccessfulDerivationOccurrence` simultaneously gives the
anchor derivation and its surrounding successful context.

### 4.39 Successful occurrences construct trimmed witnesses

For every present typed nonterminal, an explicit successful occurrence
constructs:

```text
typed anchor
typed exposing context
stored observation-type equation
positive exposed anchor word
universal derivational exposure.
```

This produces `TrimmedNonterminalWitnesses` and therefore a
`TrimmedOutputTypePresentation` from a complete presentation.

### 4.40 Typed successful presentations construct pre-core data

A base-representative selection transports typed anchors, contexts, and
successful occurrences to the original base nonterminals.  Rule-output
compatibility then constructs `TrimmedPresentationPreCoreData`, including all
terminal, binary, start, and canonical start-word equations.

### 4.41 Rule realization and canonical closure

Output compatibility is no longer a primitive premise.  It follows from actual
present typed rules realizing the original grammar rules, and those rule
choices are further replaced by canonical typed rule instances determined by
the selected representative output types.

### 4.42 Finite typed presentations become actual working grammars

Every `OutputTypeRefinementPresentation P` now has a concrete grammar:

```lean
P.toWorkingMCFG
```

with a fresh start symbol and typed nonterminals.  Presentation derivations
embed into grammar derivations, and exact working conditions and fan-out bounds
are inherited from the original grammar.


## 5. What remains as explicit assumptions or skeleton fields?

CI #634 has eliminated the old splicing and unconditional-transport
obligations from the strongest route.  The remaining positive-learning
assumptions now concern construction of the finite typed presentation itself
and extraction of successful data from it.

### 5.1 Concrete finite complete output-type presentation

Still explicit.

The current strongest route begins with a

```lean
CompleteOutputTypePresentation G obs
```

inside `SuccessfulOccurrenceCompletePresentation`.

What remains is to construct its finite sets of:

```text
typed nonterminals
typed terminal rules
typed binary rules
typed start rules
```

directly from the finite grammar `G` and finite observation monoid, and prove
`PresentationCompleteFor` for that concrete presentation.

### 5.2 Successful occurrence family

Still explicit.

For each present typed nonterminal, the current construction assumes a

```lean
PresentTypedSuccessfulOccurrence X.
```

The next semantic construction must extract such an occurrence from a
successful presentation derivation, or define the trimmed presentation so that
being present already carries this successful occurrence witness.

### 5.3 Base representative selection

Still explicit.

The current route assumes one present typed representative for every original
base nonterminal:

```lean
SuccessfulOccurrenceBaseRepresentativeSelection.
```

This is appropriate only for reduced grammars.  A concrete reducedness /
productive-and-reachable construction must prove that every relevant base
nonterminal has such a present typed representative.

### 5.4 Canonical typed-rule closure

Still explicit.

The current strongest package assumes the selected finite presentation contains
the canonical typed terminal, binary, and start rules determined by the chosen
representative output types.

The full output-type refinement should make this closure automatic.  A trimmed
presentation may require a proof that only productive/reachable canonical rules
needed by the selected successful occurrences are retained.

### 5.5 Converse for the concrete presentation grammar

Still explicit.

CI #634 proves:

```text
PresentationStringLanguage P
⊆ P.toWorkingMCFG.StringLanguage.
```

It does not yet prove that arbitrary derivations of `P.toWorkingMCFG` decode
back to `PresentationDerives P`.  This converse is needed for:

```text
P.toWorkingMCFG.StringLanguage
= PresentationStringLanguage P.
```

### 5.6 Concrete canonical learner

Still explicit.

The verified endpoint continues to use `ReachableSampleStringLanguage`.
Finite enumeration of tuple occurrences, empty-slot tie orders, binary
witnesses, unit rules, and the actual learner grammar is not yet implemented.

### 5.7 Complexity and boundary results

Still explicit:

```text
fixed-(f,h) polynomial construction bound
bounded observation-family product compilation
unbounded no-advice non-identifiability
member-kernel exclusion
copy-language exclusion
```

## 6. Immediate next files

The current CI #634 endpoint is:

```lean
OutputTypePresentationWorkingGrammar.lean
```

The next work should stay on the concrete presentation grammar rather than add
another paper-facing wrapper.

### 6.1 `OutputTypePresentationWorkingGrammarEquivalence.lean`

Recommended next.

Goal:

```lean
WorkingGrammarDerives.toPresentationDerives
```

for derivations whose nonterminal is `.typed X`, followed by:

```lean
P.toWorkingMCFG.StringLanguage
  ⊆ PresentationStringLanguage P
```

and therefore:

```lean
P.toWorkingMCFG.StringLanguage
  = PresentationStringLanguage P.
```

The proof should invert membership in the three mapped finite rule lists and
recover the corresponding present typed rule.

For complete presentations, conclude:

```lean
P.toWorkingMCFG.StringLanguage = G.StringLanguage.
```

### 6.2 `ConcreteOutputTypeRefinementPresentation.lean`

Construct the full finite output-type presentation from `G` and `obs`.

Expected finite data:

```text
all base nonterminals relevant to the finite grammar
all componentwise monoid output tuples of the appropriate arity
all canonical typed terminal rules
all canonical typed binary rules for child output pairs
all canonical typed start rules
```

Prove closure and `PresentationCompleteFor`.

### 6.3 `ConcreteTrimmedSuccessfulPresentation.lean`

Define the productive/reachable successful core.  Presence should carry or
generate an explicit `PresentTypedSuccessfulOccurrence`, so that the witness
family from CI #634 is constructed rather than assumed.

### 6.4 `ConcreteReducedRepresentativeSelection.lean`

From reducedness, choose one successful present typed representative for every
base nonterminal and prove canonical rule closure for the selected
representatives.

### 6.5 Concrete learner enumeration

After the concrete presentation route is closed:

```text
TupleOccurrences.lean
BinaryWitnesses.lean
ConcreteCanonicalLearner.lean
CanonicalLearnerReachableEquivalence.lean
```

## 7. Medium-term roadmap toward the paper theorem

### Stage A: Reachable learner theorem

Status: essentially complete.

Verified endpoints:

```lean
final_reachable_identification
final_reachable_prefix_exact
final_reachable_exact_for_positive_superset
```

The remaining work is no longer in the Gold-learning logic.

---

### Stage B: Exact-once context and successful-occurrence semantics

Status: complete at the conditional construction level.

Verified:

```text
unrestricted splicing is false
exact-once child contexts and filling equations
derivational exposure
successful derivation spines
successful derivation occurrences
successful occurrences ⇒ typed trimmed witnesses
```

Remaining task:

```text
extract successful occurrences automatically from the concrete productive/reachable trim
```

---

### Stage C: Concrete output-type presentation grammar

Status: actively under construction.

Verified:

```text
finite typed presentation interfaces
presentation soundness and completeness interface
canonical typed-rule closure route
OutputTypeRefinementPresentation.toWorkingMCFG
presentation derivations embed into the concrete grammar
exact working conditions and fan-out bounds transfer
```

Next:

```text
reverse concrete-grammar derivations back to PresentationDerives
language equality for P.toWorkingMCFG
actual finite full G^h construction from G and obs
```

---

### Stage D: Concrete productive/reachable trimmed core

Status: not yet constructed from the full presentation.

Targets:

```text
define present typed nodes/rules by successful occurrences
construct TypedSuccessfulOccurrenceFamily automatically
prove language preservation
construct base representatives from reducedness
prove canonical rule closure
```

Once this stage is complete, the CI #634 characteristic-sample route should
produce the finite positive sample and Gold theorem with no presentation-side
construction package left as an assumption.

---

### Stage E: Concrete learner equivalence

Files to create:

```text
TupleOccurrences.lean
BinaryWitnesses.lean
CanonicalLearnerRelation.lean
CanonicalLearnerSoundComplete.lean
```

Target:

```lean
ConcreteCanonicalLearnerLanguage K obs f
=
ReachableSampleStringLanguage K obs f.
```

---

### Stage F: Polynomial bound

Targets:

```text
finite tuple-occurrence code count
finite binary-witness code count
learner-rule count
fixed-(f,h) construction bound ||K||₊^{O(f)}
```

---

### Stage G: Boundary results

Targets:

```text
bounded observation families compile by product morphism
unbounded union over all finite observations is not identifiable
member-kernel exclusion
copy-language exclusion from every finite-observation fiber
```

## 8. Trust map

### Strongly verified now

```text
typed observation algebra
output-type local invariants
distributional equivalence and witnessed composition
sample-level soundness and completeness induction
finite text coverage, exact reconstruction, and reachable Gold identification
formal counterexample to unrestricted splicing
concrete exact-once left/right context construction and filling equations
derivational exposure route without unconditional transport
successful derivation spines and successful occurrences
successful occurrences to typed trimmed witnesses
typed witnesses to base representatives and pre-core data
typed-rule realization to output compatibility
canonical typed-rule closure to characteristic sample and Gold identification
finite output-type presentation to actual WorkingMCFG
embedding of presentation derivations into the concrete WorkingMCFG
preservation of exact working conditions and fan-out bounds
```

### Verified but intentionally abstract

```text
CompleteOutputTypePresentation supplied as data
TypedSuccessfulOccurrenceFamily supplied as data
one present typed representative for each base nonterminal
canonical typed-rule closure of the selected presentation
reachable sample-language learner model
legacy exposing-transport and unrestricted-splicing routes as historical conditional interfaces
```

### Not yet verified

```text
actual finite full G^h presentation constructed from G and obs
productive/reachable trimmed G̃₀ constructed from the full presentation
automatic extraction of successful typed occurrences
automatic reduced base-representative selection
reverse derivation translation from P.toWorkingMCFG to PresentationDerives
exact language equality for the concrete presentation WorkingMCFG
actual concrete learner enumeration
reachable/concrete learner equivalence
polynomial bound
boundary examples and non-identifiability
```

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
lake build LeanCfgProject.MCFG.OutputTypePresentationWorkingGrammar
```

Latest confirmed CI point:

```text
Lean CI #634
Commit: 168022f
```

Current strongest corrected identification endpoint:

```lean
trimmed_successful_canonical_rule_closure_exact_working_conclusion_package
```

Current concrete grammar endpoint:

```lean
OutputTypeRefinementPresentation.toWorkingMCFG
```

Confirmed implications:

```text
PresentationStringLanguage P
⊆ P.toWorkingMCFG.StringLanguage

G.ExactWorkingConditions
⇒ P.toWorkingMCFG.ExactWorkingConditions

G.FanoutAtMost f
⇒ P.toWorkingMCFG.FanoutAtMost f.
```

Recommended next file:

```text
OutputTypePresentationWorkingGrammarEquivalence.lean
```

Reason:

CI #634 constructs the actual grammar and proves the forward embedding.  The
next smallest genuine mathematical obligation is the converse: invert lifted
rules in an arbitrary derivation of `P.toWorkingMCFG` and recover a
`PresentationDerives P` object.  This will turn the current inclusion into
language equality and, for a complete presentation, establish that the
concrete working grammar generates exactly `G.StringLanguage`.

Parallel major target after that:

```text
ConcreteOutputTypeRefinementPresentation.lean
```

This will eliminate the largest remaining positive-learning assumption:
supplying the complete finite typed presentation itself.

