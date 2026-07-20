# FORMALIZATION_MCFG

Lean formalization log and roadmap for the MCFG fixed finite-observation paper.

Last updated: 2026-07-20  
Current confirmed CI point: Lean CI #751, commit `b7e0d5a`, pushed by `growupkuriyama-hub`.

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

At the current stage, the positive-learning route is no longer merely a reachable-model or presentation-level scaffold.  The development now constructs the full finite output-type presentation from `G` and `obs`, proves exact language equivalence for its concrete working grammar, builds the successful typed trim and extracts successful occurrences, constructs a typed-indexed finite characteristic sample, explicitly enumerates finite tuple occurrences, unit rules, exact-once binary witnesses, and a target-independent concrete canonical learner, and proves exact reconstruction and Gold identification for that finite learner.  The final CI-confirmed class theorem states that one corrected concrete learner identifies every language represented by a finite exact working MCFG satisfying semantic start-rooted normality, the fixed fan-out bound, and the fixed-observation substitutability promise.  The main remaining work is no longer the positive-learning existence theorem; it is executable/complexity refinement, removal or normalization of the start-rooted assumption if desired, and the paper's boundary and non-identifiability results.

The CI-confirmed phase from CI #583 to CI #603 did not pretend to discharge those remaining mathematical construction obligations.  Instead, it reorganized them into clean construction layers and then wrapped them in stable final names suitable for the paper and blueprint.

The phase from CI #603 to CI #620 decomposed the preferred anchor-common route down to an explicit all-pieces checklist and opened the splicing obligation down to concrete child-context functions and `namedFill` equations.  The CI #621--#624 phase then crossed the important line from interface decomposition to actual construction: it proved that the old unrestricted constructor is not inhabitable, built explicit left/right named contexts under exact-once linearity, integrated the resulting filling witnesses into the reachable theorem chain, removed unnecessary common-transport assumptions from a minimal route, and connected the existing exposing-transport route to the concrete exact-once splicing construction.

The CI #625--#634 phase moved beyond the exposing-transport interface.  It replaced the unconditional transport assumption by the paper-faithful derivational-exposure invariant, constructed that invariant from explicit successful derivation spines and successful occurrences, used those occurrences to build the witness component of a trimmed typed presentation, descended to base-nonterminal representatives and pre-core data, derived rule-output compatibility from actual typed-rule realizations and then from canonical typed-rule closure, and finally converted every finite output-type presentation into an actual `WorkingMCFG` with a fresh start symbol.  Presentation derivations now embed into this concrete grammar, and exact working conditions and fan-out bounds are preserved.

The CI #635--#651 phase closes the concrete positive-learning route.  It proves the converse derivation translation and exact presentation-grammar language equality; constructs the full finite output-type refinement and its successful trim directly from `G` and `obs`; replaces the incompatible one-representative-per-base route by a typed-indexed characteristic sample; enumerates finite tuple occurrences, contexts, unit rules, exact-once template tuples, and binary witnesses; proves completeness of those enumerations with a corrected binary-template bound; defines an exact-once reachable relation and a corrected finite concrete learner and proves them equivalent; transfers exact reconstruction and Gold identification to the concrete learner; packages the result for an entire language class; selects finite characteristic samples and stabilization stages; and weakens syntactic `StartSeparated` to semantic `StartRootedNormal`.

The CI #652--#665 phase turns that qualitative concrete learner into an explicit finite hypothesis pipeline and then into an actual `WorkingMCFG`-valued learner.  It proves cardinality bounds for every brute-force finite enumerator, eliminates the sample alphabet in favor of sample length, compresses the bounds to one common power and then to a paper-facing quadratic exponent, packages the dependent unit/binary rule codes as an actual finite hypothesis object, proves its language equal to the corrected learner and exact reachable semantics, gives rule-level simulations under sample extension, and organizes prefix hypotheses as a coherent directed system.  It then identifies a genuine empty-alphabet obstruction for the present `WorkingMCFG` syntax, constructs a finite control/cut saturation, compiles the finite object into an actual working grammar, proves both-direction derivation translation and exact language equality, characterizes the exact compilation domain, and finally proves class-level Gold identification for a learner whose outputs are actual finite `WorkingMCFG` objects whenever the terminal alphabet is nonempty.

The CI #666--#674 phase quantifies and classifies those actual grammar outputs.  It proves exact formulas and quadratic upper bounds for the compiler's control nodes, saturated cut rules, total grammar-rule count, nonterminal enumeration, and complete top-level presentation item count.  It then formalizes the precise structural boundary: the outputs preserve start/terminal typing and bounded fan-out, but nonempty-sample outputs provably fail the paper's nondeleting and exact-working conditions because constant control rules erase dummy children.  On the positive side, it defines the correct cut-compiled representation class, proves that every start-rooted target has an exact finite grammar representation obtained from a finite positive characteristic sample, stratifies those representations by sample-length budget, and introduces minimum representation, exact-output, and characteristic-sample ranks.  Finally it formalizes semantic mind changes along texts, proves that every language change strictly increases the observed prefix-sample cardinality, and proves stabilization with no later language changes after coverage of a minimum-budget characteristic sample.

The CI #675--#695 phase closes a substantial part of the previously open
encoded-description-size layer.  It begins with an abstract entry-cost
interface, specializes it to natural-number, unary, binary, dense, and tagged
dense encodings, and proves collision-free top-level codes with checked
decoding.  It then serializes dependent template atoms, template words,
component-framed template tuples, and complete binary rules.  Terminals are
densely encoded over the finite augmented alphabet
`insert dummy (sampleAlphabet K)`, and the external terminal-support premise is
discharged for every binary rule actually stored in the cut-compiled grammar.
The whole finite grammar presentation is subsequently serialized as one checked
`List Nat`, then as prefix-free unary and logarithmic-structure bit streams.
Exact round-trip theorems and exact length formulas are proved at every layer.
Finally, the common natural-field bit width is selected automatically and
reduced to the binary length of one maximum serialized field-value bound.  At
CI #695 the remaining encoded-size task was sharply localized to bounding that
maximum value and the natural-field count by sample length, fan-out,
presentation size, and template-size parameters; CI #696--#706 subsequently
closed that task.

The CI #696--#718 phase closes that quantitative gap and then builds a new
certified-description and observation-comparison layer.  Every natural field in
the complete grammar serialization is classified, every binary-rule token
payload is bounded, and the maximum field value and field count are reduced to
sample length and fan-out.  The resulting checked logarithmic serialization is
bounded first by a closed sample-parametric expression, then by one paper-facing
envelope, and finally by the single power

```text
(4 * (sampleLengthBudget K + f + 1)) ^
  ((64 *
      (sampleLengthBudget K + f + 1) *
      (sampleLengthBudget K + f + 1)) * 13).
```

That bit representation is then promoted to a checked bounded representation,
a finite Boolean-code universe, a finite exhaustive decoded search, a canonical
decode/re-encode search, and an exact code-indexed selector.  The learner output
itself is lifted to a certified record carrying its actual grammar,
presentation, checked bit code, decoder, re-encoder, finite canonical search,
selector result, and all verification and size proofs.  Semantic mind-change
theory and characteristic-sample ranks transfer to this certified learner.

The same phase defines attained minimum certified bit complexity, attained
minimum canonical-search complexity, a simultaneous two-dimensional
description profile, its minimum profile rank, exact-rank shells, and
profile/complexity obstruction theorems that imply characteristic-rank lower
bounds.  Finally, observation refinement is formalized at the semantic target
class level: target classes grow, failure classes shrink, gain classes compose
disjointly along refinement chains, mutual refinement gives semantic
equivalence, and interface ablation is redundant exactly when the target class
is unchanged.  An essential refinement is shown to yield a genuinely new
fine-observation target with a certified minimum-rank description.  What remains
is no longer the positive-learning theorem or the closed bit-size theorem; it is
chiefly executable polynomial construction, concrete strict-gain/observation
separation examples, observation-design optimization complexity, and the final
negative/exclusion results.

The CI #719--#738 phase builds the semantic observation-design optimization
theory on top of ablation.  It constructs paired and arbitrary finite selected
observation products, proves target/failure monotonicity and synergy
decompositions, defines minimum-cardinality and general weighted selection,
derives irredundancy and coordinate essentiality, introduces two-objective
Pareto fronts and positive additive costs, and turns the semantic optimization
problems into explicit finite feasible/minimum/Pareto candidate sets with actual
classical selectors and certified selected-product learners.  It then organizes
cost-bounded candidates into a monotone filtration and language-class rank
hierarchy, proves exact rank-shell decomposition, comparison, perturbation
sensitivity, and fixed-overhead normalization, identifies the rank-zero,
rank-one, arbitrary-cardinality, and arbitrary-positive-additive layers, and
finally reconstructs positive additive rank as the minimum scalar envelope of
the finite Pareto frontier with an actual Pareto-rank selector.  The remaining
observation-design gap is now chiefly computational complexity and concrete
strict separation, not semantic optimization existence.

The CI #739--#751 phase resolves the internal geometry of the
positive-additive-rank-minimizing Pareto frontier.  It defines the finite set of
rank-minimizing profiles, selects the minimum-cardinality and minimum-additive
endpoints, and proves that every profile lies on one affine rank line.  The
endpoint distance becomes an exact tradeoff width.  Profiles are normalized by
their cardinality offsets, reconstructed exactly from those offsets, and put in
an explicit finite equivalence with the realized offset set.  Actual selected
observation interfaces are then chosen for every realized offset, with exact
cardinality/additive-cost formulas, order equivalence, difference preservation,
Pareto optimality, irredundancy, coordinate essentiality, and certified
selected-product learners.

The same phase distinguishes gap-free spectra from spectra with missing
intermediate profiles.  It proves exact interval and cardinality
characterizations of gap-freeness, defines the finite gap set and the exact
defect formula
`profiles.card + gaps.card = width + 1`, selects and bounds the first missing
offset, and constructs a finite Boolean checker relative to the semantic
offset table together with a canonical least-gap certificate.  Finally it
packages the positive and negative branches as proof-carrying alternatives and
as finite offset-indexed families of actual certified selected interfaces.
This substantially closes the semantic profile/gap theory.  It does not yet
replace semantic target-membership filters by an executable encoded
optimization problem, so the main remaining observation-design task is still
computational complexity and concrete strict separation.

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
OutputTypePresentationWorkingGrammarEquivalence.lean ✅
ConcreteOutputTypeRefinementPresentation.lean ✅
StartSeparatedOutputTypeRefinementCompleteness.lean ✅
ConcreteTrimmedSuccessfulPresentation.lean ✅
ConcreteReducedRepresentativeSelection.lean ✅
ConcreteObservationDeterministicClosure.lean ✅
ConcreteTypedCharacteristicSample.lean ✅
TupleOccurrences.lean ✅
BinaryWitnesses.lean ✅
ConcreteCanonicalLearner.lean ✅
TupleOccurrenceEnumerationCompleteness.lean ✅
NamedFillEnumerationBounds.lean ✅
BinaryWitnessEnumerationCompleteness.lean ✅
ExactConcreteCanonicalLearnerEquivalence.lean ✅
ConcreteCanonicalLearnerIdentification.lean ✅
ConcreteCanonicalLearnerClassTheorem.lean ✅
ConcreteCanonicalLearnerStabilization.lean ✅
StartRootedConcreteCanonicalLearnerIdentification.lean ✅
StartRootedConcreteCanonicalLearnerClassTheorem.lean ✅
ConcreteCanonicalLearnerFiniteEnumerationBounds.lean ✅
ConcreteCanonicalLearnerLengthOnlyBounds.lean ✅
ConcreteCanonicalLearnerSinglePowerBounds.lean ✅
ConcreteCanonicalLearnerPolynomialExponentBounds.lean ✅
ConcreteCanonicalLearnerFiniteHypothesis.lean ✅
ConcreteCanonicalLearnerFiniteHypothesisSize.lean ✅
ConcreteCanonicalLearnerFiniteObjectIdentification.lean ✅
ConcreteCanonicalLearnerFiniteObjectMonotone.lean ✅
ConcreteCanonicalLearnerFiniteObjectDirectedSystem.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObstruction.lean ✅
ConcreteCanonicalLearnerWorkingGrammarCutSaturation.lean ✅
ConcreteCanonicalLearnerWorkingGrammarConstruction.lean ✅
ConcreteCanonicalLearnerWorkingGrammarEquivalence.lean ✅
ConcreteCanonicalLearnerWorkingGrammarIdentification.lean ✅
ConcreteCanonicalLearnerWorkingGrammarSize.lean ✅
ConcreteCanonicalLearnerWorkingGrammarPresentationSize.lean ✅
ConcreteCanonicalLearnerWorkingGrammarStructuralConditions.lean ✅
ConcreteCanonicalLearnerWorkingGrammarRepresentation.lean ✅
ConcreteCanonicalLearnerWorkingGrammarBoundedRepresentation.lean ✅
ConcreteCanonicalLearnerWorkingGrammarRepresentationRank.lean ✅
ConcreteCanonicalLearnerWorkingGrammarCharacteristicRank.lean ✅
ConcreteCanonicalLearnerWorkingGrammarMindChanges.lean ✅
ConcreteCanonicalLearnerWorkingGrammarDescriptionSize.lean ✅
ConcreteCanonicalLearnerWorkingGrammarNaturalEncoding.lean ✅
ConcreteCanonicalLearnerWorkingGrammarBinaryEncoding.lean ✅
ConcreteCanonicalLearnerWorkingGrammarAutomaticBitWidth.lean ✅
ConcreteCanonicalLearnerWorkingGrammarDenseEncoding.lean ✅
ConcreteCanonicalLearnerWorkingGrammarTaggedDenseEncoding.lean ✅
ConcreteCanonicalLearnerWorkingGrammarTaggedDenseDecoding.lean ✅
ConcreteCanonicalLearnerWorkingGrammarTemplateSerialization.lean ✅
ConcreteCanonicalLearnerWorkingGrammarTemplateTupleFraming.lean ✅
ConcreteCanonicalLearnerWorkingGrammarBinaryRuleSerialization.lean ✅
ConcreteCanonicalLearnerWorkingGrammarTerminalAlphabetEncoding.lean ✅
ConcreteCanonicalLearnerWorkingGrammarBinaryRuleNaturalSerialization.lean ✅
ConcreteCanonicalLearnerWorkingGrammarBinaryRuleTerminalClosure.lean ✅
ConcreteCanonicalLearnerWorkingGrammarPresentationNaturalSerialization.lean ✅
ConcreteCanonicalLearnerWorkingGrammarUnaryBitSerialization.lean ✅
ConcreteCanonicalLearnerWorkingGrammarLogarithmicBitSerialization.lean ✅
ConcreteCanonicalLearnerWorkingGrammarLogarithmicBitBounds.lean ✅
ConcreteCanonicalLearnerWorkingGrammarAutomaticNaturalFieldBitWidth.lean ✅
ConcreteCanonicalLearnerWorkingGrammarNaturalFieldMaximum.lean ✅
ConcreteCanonicalLearnerWorkingGrammarNaturalFieldClassification.lean ✅
ConcreteCanonicalLearnerWorkingGrammarNaturalFieldEntryBounds.lean ✅
ConcreteCanonicalLearnerWorkingGrammarBinaryRuleNaturalFieldClassification.lean ✅
ConcreteCanonicalLearnerWorkingGrammarBinaryRuleTokenPayloadBounds.lean ✅
ConcreteCanonicalLearnerWorkingGrammarNaturalFieldFullyExplicitBound.lean ✅
ConcreteCanonicalLearnerWorkingGrammarUniformNaturalFieldBound.lean ✅
ConcreteCanonicalLearnerWorkingGrammarBinaryRuleFamilyBodyBounds.lean ✅
ConcreteCanonicalLearnerWorkingGrammarSampleParametricBitBound.lean ✅
ConcreteCanonicalLearnerWorkingGrammarPaperBitEnvelope.lean ✅
ConcreteCanonicalLearnerWorkingGrammarPaperPowerBitBound.lean ✅
ConcreteCanonicalLearnerWorkingGrammarFinalDescriptionPackage.lean ✅
ConcreteCanonicalLearnerWorkingGrammarCheckedBitRepresentation.lean ✅
ConcreteCanonicalLearnerWorkingGrammarFiniteCodeUniverse.lean ✅
ConcreteCanonicalLearnerWorkingGrammarFiniteDecodedSearch.lean ✅
ConcreteCanonicalLearnerWorkingGrammarCanonicalDecodedSearch.lean ✅
ConcreteCanonicalLearnerWorkingGrammarCanonicalSearchSelector.lean ✅
ConcreteCanonicalLearnerWorkingGrammarCertifiedOutputLearner.lean ✅
ConcreteCanonicalLearnerWorkingGrammarCertifiedOutputMindChanges.lean ✅
ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionComplexity.lean ✅
ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionProfile.lean ✅
ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionRank.lean ✅
ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionRankObstructions.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationRefinementFailure.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationEquivalenceChain.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationAblation.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationProduct.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelection.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionIrredundancy.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationWeightedSelection.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationParetoSelection.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationAdditiveWeights.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationFiniteOptimization.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationOptimizationSelector.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationBudgetFiltration.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRank.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankComparison.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankSensitivity.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionCostOverhead.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankZero.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankOne.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionCardinalityRank.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionPositiveAdditiveRank.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankEnvelope.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankSelector.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfiles.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileExtremes.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileWidth.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsets.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetSelector.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetOrder.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetBijection.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapFree.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGaps.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetFirstGapBounds.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapDecision.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapAlternative.lean ✅
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapSelectionFamily.lean ✅
```

All files marked ✅ above are user-confirmed as passed.  The latest named CI/commit explicitly recorded in this document is:

```text
Lean CI #751
Commit: b7e0d5a
```

`ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapSelectionFamily.lean`
is now confirmed passed at Lean CI #751.  The verified chain listed above
contains 262 CI-confirmed files.

The current state is best described as:

```text
reachable-model soundness/completeness and Gold logic: complete
exact-once named-context splicing: concretely constructed and CI-confirmed
unrestricted universal splicing constructor: formally refuted
finite full output-type presentation G^h from G and obs: constructed
presentation WorkingMCFG language equivalence: proved in both directions
successful typed trim and typed characteristic sample: constructed
finite tuple/context/unit/exact-binary enumeration and completeness: proved
corrected finite concrete canonical learner: constructed and equivalent to exact reachable semantics
uniform start-rooted language-class theorem: proved
actual dependent finite hypothesis object: constructed
actual finite hypothesis language = corrected learner = exact reachable language: proved
actual finite hypothesis rule count: explicitly bounded
sample-extension rule simulations and finite-object language monotonicity: proved
prefix finite hypotheses form a coherent directed system: proved
unconditional compilation into present WorkingMCFG syntax: formally shown false over the empty alphabet with sample {ε}
exact compilation domain: sample empty or terminal alphabet nonempty
finite control/cut saturation compiler to an actual WorkingMCFG: constructed
compiled WorkingMCFG language = finite-object language: proved in both directions
actual WorkingMCFG-valued learner: constructed for Nonempty α
actual WorkingMCFG-valued learner identifies the start-rooted target class: proved
compiled grammar control/cut cardinality and actual rule count: explicitly bounded
all compiled nonterminals: explicitly enumerated
nonterminal-plus-rule presentation item count: explicitly bounded
preserved output conditions: start/terminal typing and fan-out max 1 f
nondeleting/exact-working output condition for nonempty samples: formally refuted
cut-compiled representation class and exact target representations: constructed
bounded representation hierarchy: constructed and monotone
minimum bounded-representation rank: defined and attained
minimum exact-output rank: defined and attained
minimum characteristic-sample rank: defined and attained
rank chain representation ≤ exact-output ≤ characteristic ≤ selected-sample length: proved
semantic language mind changes: bounded by observed prefix-sample cardinality
minimum-characteristic-sample coverage implies permanent target exactness and no later mind changes
abstract entry-cost and natural/unary/binary description-size layers: constructed
dense and tagged-dense top-level presentation codes: injective and decodable
dependent template atoms/words/tuples: structurally serialized with checked round trips
stored binary rules: serialized to pure List Nat with unconditional stored-rule round trip
complete cut-compiled grammar presentation: serialized to one checked List Nat
complete grammar: serialized to prefix-free unary and logarithmic-structure List Bool streams
automatic least positive common natural-field bit width: constructed
every natural serialization field and every stored binary-token payload: classified and bounded
natural-field count and maximum field value: bounded by sample length and fan-out
closed sample-parametric checked logarithmic bit bound: proved
single-power paper bit bound with linear base and quadratic exponent times 13: proved
checked bit-bounded representation hierarchy: constructed
finite Boolean-code universe at each sample/fan-out budget: explicitly enumerated
finite exhaustive decoder search and canonical decode/re-encode search: constructed
exact code-indexed selector recovering the actual presentation: proved
certified learner output carrying grammar, code, presentation, search, selector, and proofs: constructed
certified semantic mind-change theory and minimum-characteristic output bounds: proved
minimum certified bit and search complexities: defined, attained, and rank-bounded
simultaneous certified description profile and minimum profile rank: defined and attained
profile obstructions imply characteristic-rank lower bounds: proved
observation refinement target/failure/gain monotonicity: proved
mutual observation refinement and refinement-chain gain decomposition: proved
interface ablation redundancy/essentiality criterion: proved
paired and finite selected observation products: constructed
minimum-cardinality, weighted, positive-additive, and Pareto selection semantics: proved
minimum selections are irredundant and selected coordinates are essential: proved
finite feasible/minimum/Pareto candidate sets and actual selectors: constructed
cost-budget filtration and exact language-class rank hierarchy: constructed
cost-model comparison, perturbation sensitivity, and fixed-overhead normalization: proved
rank-zero, rank-one, arbitrary-cardinality, and arbitrary-positive-additive shell theorems: proved
positive-additive rank = minimum scalar value on the finite additive Pareto frontier: proved
actual rank-minimizing Pareto selector with certified selected-product learner: constructed
rank-minimizing Pareto profile set, endpoint profiles, and exact tradeoff width: constructed
profile/offset reconstruction, finite bijection, and exact order/difference correspondence: proved
gap-free interval characterization and exact profile-count theorem: proved
finite gap set and exact defect formula profiles.card + gaps.card = width + 1: proved
least missing offset, strict interior/rank bounds, and certified realized prefix: constructed
finite semantic-table Boolean decision and canonical least-gap certificate: constructed
complete or first-gap-prefix offset-indexed families of actual certified selected products: constructed
current strongest certified identification/rank endpoint:
  correctedConcreteCertifiedWorkingGrammarLearner_identification_descriptionRankObstruction_package
current strongest observation endpoint:
  correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankProfileOffsetGapSelectionFamily_package
current strongest checked-description endpoint:
  correctedConcreteWorkingGrammarLearner_finalDescriptionConclusion_package
current strongest finite-search endpoint:
  correctedConcreteWorkingGrammarLearner_identification_canonicalSelector_package
```


Most important progress since CI #738:

```text
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfiles.lean
constructs the finite set of positive-additive-rank-minimizing Pareto profiles,
proves exact rank-line equations and antichain/order properties, bounds the
profile count by rank + 1, and selects the actual selector's profile.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileExtremes.lean
selects the minimum-cardinality and minimum-additive endpoint profiles, proves
their extremal inequalities and rank equations, and attaches certified
selected-product witnesses to both endpoints.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileWidth.lean
defines the exact endpoint tradeoff width, proves equality of the cardinality
and additive-coordinate widths, bounds width by positive-additive rank, embeds
all profiles in the finite endpoint interval, and characterizes width zero as
profile rigidity.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsets.lean
normalizes profiles to cardinality offsets, reconstructs each profile exactly
as `(c_min + d, a_max - d)`, proves offset injectivity, realizes offsets 0 and
width, and gives certified selected-product witnesses for every realized
offset.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetSelector.lean
chooses one actual selected subset for every realized offset and proves exact
profile formulas, Pareto optimality, exact rank, global minimum cost,
irredundancy, coordinate essentiality, endpoint behavior, and certified
learning.  It deliberately asserts profile uniqueness rather than subset
uniqueness.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetOrder.lean
proves that offset order is exactly cardinality order and reverse
additive-coordinate order.  Ordered offset differences are preserved exactly
as both cardinality increase and additive-cost decrease.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetBijection.lean
constructs an explicit equivalence between realized offsets and
rank-minimizing profiles, proves both round trips and unique correspondence,
derives exact finite-cardinality equality, and transports every profile to an
actual certified offset selection.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapFree.lean
defines gap-freeness, characterizes it by equality with
`range (width + 1)` and by attaining the maximal profile count, identifies the
profile set with the full tradeoff interval, constructs all-offset selectors,
and proves exact one-step exchanges.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGaps.lean
defines the finite missing-offset set and gap count, proves disjoint
offset/gap decomposition of the width interval, establishes
`profiles.card + gaps.card = width + 1`, and selects the least missing offset
with a certified realized prefix before it.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetFirstGapBounds.lean
proves that every first gap is a strict interior offset, so non-gap-freeness
forces width and rank at least two.  It bounds profile count below by
`firstGap + 1`, bounds gap count above by `width - firstGap`, and constructs
certified selectors for the realized prefix and maximum endpoint.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapDecision.lean
defines a Boolean gap-free decision and missing-offset verifier relative to
the finite semantic table, proves their correctness, identifies the accepted
candidate set with the semantic gap set, and constructs a canonical least-gap
certificate.  This is not yet an external polynomial-time decision theorem.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapAlternative.lean
packages the Boolean result as a proof-carrying dichotomy: the positive branch
provides all offsets, while the negative branch returns the least verified gap,
its rank/width bounds, and certified selectors for every smaller offset.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapSelectionFamily.lean
lifts single-offset selectors to finite indexed families.  The gap-free branch
has a complete family of width + 1 certified selected products; the negative
branch has a first-gap-prefix-plus-maximum family of firstGap + 1 certified
selected products, with exact profile and tradeoff-order guarantees at every
index.
```

Most important progress since CI #718:

```text
ConcreteCanonicalLearnerWorkingGrammarObservationProduct.lean constructs paired
observations, factor refinements, target/failure comparisons, semantic synergy,
and the decomposition of the paired target class into factor targets plus
genuinely joint-observation targets.

ConcreteCanonicalLearnerWorkingGrammarObservationSelection.lean generalizes
pairing to arbitrary finite selected products and defines minimum-cardinality
observation selection for every full-product target.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionIrredundancy.lean
proves that minimum-cardinality selections are inclusion-irredundant and that
every retained coordinate is essential.

ConcreteCanonicalLearnerWorkingGrammarObservationWeightedSelection.lean
introduces arbitrary natural-valued selection costs, exact attained minima,
strictly monotone cost irredundancy, and exact bounded-cost obstruction
theorems.

ConcreteCanonicalLearnerWorkingGrammarObservationParetoSelection.lean introduces
the two-objective profile (selected cardinality, selection cost), weak/strict
dominance, Pareto fronts, Pareto profiles, existence, irredundancy, coordinate
essentiality, and certified Pareto-selected learners.

ConcreteCanonicalLearnerWorkingGrammarObservationAdditiveWeights.lean
specializes the cost theory to additive and positive-additive coordinate
weights and proves strict monotonicity of the positive-additive model.

ConcreteCanonicalLearnerWorkingGrammarObservationFiniteOptimization.lean turns
semantic feasibility, minimum cost, Pareto fronts, and Pareto profiles into
explicit finite Finset searches bounded by 2^|U|.

ConcreteCanonicalLearnerWorkingGrammarObservationOptimizationSelector.lean
selects actual minimum-cost and Pareto candidates from those finite nonempty
sets and attaches certified selected-product learners.

ConcreteCanonicalLearnerWorkingGrammarObservationBudgetFiltration.lean organizes
all feasible candidates by cost budget, proves filtration monotonicity, and
identifies the semantic minimum as the first nonempty layer.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRank.lean lifts the
budget filtration to cumulative language classes, exact rank shells, unique
rank decomposition, exact profile thresholds, and certified rank-minimum
selection.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankComparison.lean
proves profile/filtration inclusion and rank monotonicity under pointwise cost
order, including cardinality versus positive-additive rank and monotonicity
under coordinate-weight increases.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankSensitivity.lean
proves additive perturbation bounds for profiles, filtrations, exact shells, and
ranks; coordinatewise weight error d changes positive-additive rank by at most
d * |U| in the controlled direction.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionCostOverhead.lean
proves exact translation under a fixed setup cost: ranks shift by the overhead,
minimum subsets and Pareto fronts remain unchanged, and the same selected-product
certified learner applies.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankZero.lean and
ObservationSelectionRankOne.lean identify the bottom two shells: rank zero is
exactly empty-interface representability; cardinality rank one is exactly
one-coordinate representability but not empty-interface representability; the
positive-additive rank-one witness additionally has zero extra weight.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionCardinalityRank.lean
and ObservationSelectionPositiveAdditiveRank.lean give arbitrary-rank witness
theorems, bounded shell decompositions, exact lower-bound obstructions, and
irredundant certified exact-rank selections.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankEnvelope.lean
proves that positive-additive rank is exactly the minimum scalar total on the
finite additive Pareto frontier and that rank lower bounds can be checked only
against Pareto scalar values.

ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankSelector.lean
filters the finite Pareto frontier to the exact rank-minimizing candidates,
selects one actual candidate, proves global optimality, irredundancy and
coordinate essentiality, and attaches its certified learner.
```


Most important progress since CI #695:

```text
ConcreteCanonicalLearnerWorkingGrammarNaturalFieldClassification.lean classified
every natural field in each top-level entry, framed entry stream, and complete
grammar stream, reducing the global maximum to entry-local structural cases.

ConcreteCanonicalLearnerWorkingGrammarNaturalFieldEntryBounds.lean bounded
nonterminal, start, terminal, and binary entry fields by presentation-item,
terminal-alphabet, and binary-payload quantities.

ConcreteCanonicalLearnerWorkingGrammarBinaryRuleNaturalFieldClassification.lean
opened the complete binary-rule payload into dense nonterminal codes, body-token
count, token tags, and token payloads.

ConcreteCanonicalLearnerWorkingGrammarBinaryRuleTokenPayloadBounds.lean bounded
component lengths, terminal codes, and child-variable indices for every stored
compiled binary rule.

ConcreteCanonicalLearnerWorkingGrammarNaturalFieldFullyExplicitBound.lean and
ConcreteCanonicalLearnerWorkingGrammarUniformNaturalFieldBound.lean propagated
those local bounds to the complete natural stream and logarithmic bit codec.

ConcreteCanonicalLearnerWorkingGrammarBinaryRuleFamilyBodyBounds.lean bounded
the three compiler rule families—constant, lifted, and saturated—by one
sample-length/fan-out body-token bound.

ConcreteCanonicalLearnerWorkingGrammarSampleParametricBitBound.lean eliminated
presentation count, terminal-alphabet cardinality, field count, field maximum,
and body-token maximum from the canonical checked bit theorem.

ConcreteCanonicalLearnerWorkingGrammarPaperBitEnvelope.lean compressed the
closed structural formula to one paper description scale and natural-field
envelope.

ConcreteCanonicalLearnerWorkingGrammarPaperPowerBitBound.lean absorbed the
envelope into one power of the existing learner-rule-count base, obtaining the
final exponent multiplier 13.

ConcreteCanonicalLearnerWorkingGrammarFinalDescriptionPackage.lean attached the
checked bit list and decoder directly to the actual WorkingMCFG-valued learner
and combined the bit theorem with consistency, monotonicity, identification,
and selected-stage target exactness.

ConcreteCanonicalLearnerWorkingGrammarCheckedBitRepresentation.lean packaged
each output as a checked bounded code/presentation representation and built the
corresponding representation hierarchy.

ConcreteCanonicalLearnerWorkingGrammarFiniteCodeUniverse.lean explicitly
enumerated every Boolean list within the paper-power bit budget and proved the
finite universe has at most 2^(bound+1) members.

ConcreteCanonicalLearnerWorkingGrammarFiniteDecodedSearch.lean filtered that
universe through the checked decoder, producing a finite exhaustive search whose
successful values include the actual learner presentation.

ConcreteCanonicalLearnerWorkingGrammarCanonicalDecodedSearch.lean added the
decode/re-encode fixed-point filter, removing noncanonical aliases while
retaining the actual learner pair and code/value uniqueness.

ConcreteCanonicalLearnerWorkingGrammarCanonicalSearchSelector.lean defined an
exact finite code-indexed selector and proved that lookup by the emitted learner
code returns exactly the complete actual presentation.

ConcreteCanonicalLearnerWorkingGrammarCertifiedOutputLearner.lean changed the
hypothesis type itself: every learner output now stores the actual grammar,
presentation, checked bits, decoder, re-encoder, finite search, exact selector,
and all size and correctness proofs.

ConcreteCanonicalLearnerWorkingGrammarCertifiedOutputMindChanges.lean transferred
Gold identification, semantic mind-change counting, minimum-characteristic
stabilization, and minimum-rank checked-description bounds to that certified
learner.

ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionComplexity.lean
defined and attained the minimum checked bit complexity and minimum finite-search
complexity of a semantic target.

ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionProfile.lean required
one and the same certificate to satisfy bit and search budgets simultaneously
and built an increasing rank-indexed profile hierarchy.

ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionRank.lean defined the
first occupied profile level, proved its exact threshold characterization, and
showed it is no larger than the characteristic rank.

ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionRankObstructions.lean
turned profile nonmembership and bit/search lower bounds into strict
characteristic-rank lower bounds and partitioned the target class into disjoint
exact-rank shells.

ConcreteCanonicalLearnerWorkingGrammarObservationRefinementFailure.lean transported
target witnesses along observation refinement, proved target growth and failure
shrinkage, and introduced strict gain and empty loss classes.

ConcreteCanonicalLearnerWorkingGrammarObservationEquivalenceChain.lean added
refinement identity/composition, mutual-refinement equivalence, disjoint
incremental gain decomposition, and finest-observation certified learning along
a refinement chain.

ConcreteCanonicalLearnerWorkingGrammarObservationAblation.lean proved the exact
interface-ablation criterion:
  redundant refinement
    ↔ empty gain
    ↔ equal target classes
    ↔ equal failure classes,
while essential refinement yields a genuinely new fine-observation target with
an exact minimum-rank certified description.
```

Current strongest quantitative endpoints:

```lean
correctedConcreteFiniteHypothesis_logarithmicBitCount_le_sampleParametric
correctedConcreteFiniteHypothesis_logarithmicBitCount_le_paperPower
correctedConcreteWorkingGrammarLearner_checkedDescription_semantic_package
correctedConcreteWorkingGrammarLearner_finalDescriptionConclusion_package
```

Current strongest finite-search/certification endpoints:

```lean
correctedConcreteWorkingGrammarLearner_identification_finiteCodeUniverse_package
correctedConcreteWorkingGrammarLearner_identification_finiteDecodedSearch_package
correctedConcreteWorkingGrammarLearner_identification_canonicalDecodedSearch_package
correctedConcreteWorkingGrammarLearner_identification_canonicalSelector_package
correctedConcreteCertifiedWorkingGrammarLearner_identification_package
correctedConcreteCertifiedWorkingGrammarLearner_identification_mindChange_package
correctedConcreteCertifiedWorkingGrammarLearner_identification_descriptionComplexity_package
correctedConcreteCertifiedWorkingGrammarLearner_identification_descriptionProfile_package
correctedConcreteCertifiedWorkingGrammarLearner_identification_descriptionRank_package
correctedConcreteCertifiedWorkingGrammarLearner_identification_descriptionRankObstruction_package
```

Current strongest observation endpoints:

```lean
correctedConcreteCertifiedWorkingGrammar_observationRefinementFailure_package
correctedConcreteCertifiedWorkingGrammar_observationRefinementChain_package
correctedConcreteCertifiedWorkingGrammar_observationAblation_package
```

Most important progress since CI #674:

```text
ConcreteCanonicalLearnerWorkingGrammarDescriptionSize.lean introduced an abstract
entry-cost model for nonterminals and all rule classes and bounded total
description size by presentationItemCount times a common entry cost.
ConcreteCanonicalLearnerWorkingGrammarNaturalEncoding.lean specialized entries
to natural-number codes and gave unary-size bounds from a common code bound.
ConcreteCanonicalLearnerWorkingGrammarBinaryEncoding.lean introduced standard
binary payload lengths and proved total binary-size bounds from CodesFitInBits.
ConcreteCanonicalLearnerWorkingGrammarAutomaticBitWidth.lean selected the least
positive fitting width automatically from the finite used-code family.
ConcreteCanonicalLearnerWorkingGrammarDenseEncoding.lean encoded entries by
their positions inside the finite category lists and obtained logarithmic width
in presentation item count.
ConcreteCanonicalLearnerWorkingGrammarTaggedDenseEncoding.lean combined all four
entry classes into one tagged list, proved global code injectivity on stored
entries, and retained the item-count-times-log-width bound.
ConcreteCanonicalLearnerWorkingGrammarTaggedDenseDecoding.lean added a checked
decoder, exact stored-entry round trips, range completeness, and out-of-range
failure.
ConcreteCanonicalLearnerWorkingGrammarTemplateSerialization.lean serialized
dependent TemplateAtom values to nondependent tagged tokens and proved atom,
word, tuple-component, and binary-body round trips with variable-bound checks.
ConcreteCanonicalLearnerWorkingGrammarTemplateTupleFraming.lean added
length-prefix framing for output components and proved flatten/unflatten
round trips and exact token-count formulas.
ConcreteCanonicalLearnerWorkingGrammarBinaryRuleSerialization.lean combined
lhs/left/right nonterminal codes with framed template bodies and reconstructed
dependent BinaryRule objects with checked arities.
ConcreteCanonicalLearnerWorkingGrammarTerminalAlphabetEncoding.lean densely
encoded terminals over insert dummy (sampleAlphabet K) and naturalized complete
framed template-body token streams.
ConcreteCanonicalLearnerWorkingGrammarBinaryRuleNaturalSerialization.lean
serialized a complete binary rule as one pure List Nat and proved a checked
round trip under the precise terminal-support condition.
ConcreteCanonicalLearnerWorkingGrammarBinaryRuleTerminalClosure.lean proved that
every actually stored constant, lifted, or saturated binary rule satisfies that
terminal-support condition, making stored-rule round trips unconditional.
ConcreteCanonicalLearnerWorkingGrammarPresentationNaturalSerialization.lean
serialized every nonterminal/start/terminal/binary presentation entry and then
the complete compiled grammar as one length-framed List Nat with exact decoding
and field-count formulas.
ConcreteCanonicalLearnerWorkingGrammarUnaryBitSerialization.lean converted the
whole natural stream to a prefix-free List Bool codec using unary natural codes,
with exact round trip and exact bit-count formula.
ConcreteCanonicalLearnerWorkingGrammarLogarithmicBitSerialization.lean replaced
unary natural payloads by a recursively half-sized self-delimiting binary-tree
codec and bounded total size by field count times maximum recursive field cost.
ConcreteCanonicalLearnerWorkingGrammarLogarithmicBitBounds.lean proved
binaryTreeNatBitCost n ≤ 2 * binaryNatCodeLength n + 1 and lifted this to a
whole-grammar fieldCount-times-bitWidth theorem.
ConcreteCanonicalLearnerWorkingGrammarAutomaticNaturalFieldBitWidth.lean
selected the least positive common width from the complete natural stream and
removed the external NaturalFieldsFitInBits premise.
ConcreteCanonicalLearnerWorkingGrammarNaturalFieldMaximum.lean reduced the
automatic width and total grammar bit count to one quantity:
max(naturalFieldCount, maximum serialized natural field value).
```

Current strongest encoding endpoints:

```lean
decodeCompiledWorkingGrammarNaturalList_encode
decodeCompiledWorkingGrammarUnaryBitList_encode
decodeCompiledWorkingGrammarLogarithmicBitList_encode
compiledWorkingGrammarAutomaticNaturalFieldBitWidth_package
compiledWorkingGrammarNaturalFieldMaximum_package
```

Most important progress since CI #665:

```text
ConcreteCanonicalLearnerWorkingGrammarSize.lean counted the actual compiled grammar rules, proving
  controlCodes.card ≤ K.card + 3 * sourceRuleCount,
  cutPairs.card ≤ controlCodes.card²,
and the structural bound
  grammarRuleCount ≤ (K.card + 3 * sourceRuleCount + 2)².
It then substituted the paper-facing source-rule bound into an explicit actual-grammar rule bound.
ConcreteCanonicalLearnerWorkingGrammarPresentationSize.lean explicitly enumerated every compiled nonterminal, proved the enumeration length is controlCodes.card + 2, and bounded the complete nonterminal-plus-rule presentation item count by
  (K.card + 3 * sourceRuleCount + 3)²,
with a fully expanded sample-length-only bound.
ConcreteCanonicalLearnerWorkingGrammarStructuralConditions.lean proved bounded fan-out and start/terminal typing for every output and introduced CutCompiledConditions.  It also proved that every nonempty-sample output fails BinaryRulesNondeleting, BasicWorkingConditions, and ExactWorkingConditions because constant rules erase both dummy children.
ConcreteCanonicalLearnerWorkingGrammarRepresentation.lean defined the cut-compiled representation class and proved every start-rooted target has an exact actual finite WorkingMCFG representation obtained from a finite positive characteristic sample, together with all size bounds.
ConcreteCanonicalLearnerWorkingGrammarBoundedRepresentation.lean stratified exact representations by sample-length budget, proved bound monotonicity and hierarchy monotonicity, and placed every target at some finite level.
ConcreteCanonicalLearnerWorkingGrammarRepresentationRank.lean defined the minimum bounded-representation rank and minimum exact learner-output rank, proved both minima are attained, and proved representation rank ≤ exact-output rank.
ConcreteCanonicalLearnerWorkingGrammarCharacteristicRank.lean defined the minimum characteristic-sample rank, proved it is attained, and established
  representation rank ≤ exact-output rank ≤ characteristic rank ≤ selected characteristic-sample length.
ConcreteCanonicalLearnerWorkingGrammarMindChanges.lean defined semantic prefix hypotheses and language mind changes, proved every semantic change strictly increases prefix-sample cardinality, bounded finite-prefix mind changes by the number of distinct observed words, selected a minimum-budget characteristic sample, and proved permanent target exactness and constant cumulative mind-change count after its coverage stage.
```

Most important progress since CI #651:

```text
ConcreteCanonicalLearnerFiniteEnumerationBounds.lean proved cardinality bounds for the actual word, context, tuple-occurrence, unit-rule, exact-template, and binary-witness enumerators.
ConcreteCanonicalLearnerLengthOnlyBounds.lean eliminated the sample-alphabet cardinality in favor of sampleLengthBudget.
ConcreteCanonicalLearnerSinglePowerBounds.lean absorbed all finite families into one common base and exponent.
ConcreteCanonicalLearnerPolynomialExponentBounds.lean expanded the exponent and proved the paper-facing bound
  (4 * (sampleLengthBudget K + f + 1)) ^
    (64 * (sampleLengthBudget K + f + 1)^2).
ConcreteCanonicalLearnerFiniteHypothesis.lean packaged dependent unit and binary rule codes into an actual finite hypothesis object and proved its listed semantics equivalent to the corrected concrete and exact reachable semantics.
ConcreteCanonicalLearnerFiniteHypothesisSize.lean applied the quantitative bound to the ruleCount of the actual finite hypothesis object.
ConcreteCanonicalLearnerFiniteObjectIdentification.lean made the finite object the learner output type and transferred characteristic samples and class-level Gold identification.
ConcreteCanonicalLearnerFiniteObjectMonotone.lean constructed rule-level sample-extension transports and structurally transported listed derivations.
ConcreteCanonicalLearnerFiniteObjectDirectedSystem.lean added identity, composition, and prefix-directed-system coherence for finite hypothesis simulations.
ConcreteCanonicalLearnerWorkingGrammarObstruction.lean proved that every nonempty WorkingMCFG language forces Nonempty α, and exhibited the empty-alphabet sample {ε} as a counterexample to unconditional compilation.
ConcreteCanonicalLearnerWorkingGrammarCutSaturation.lean normalized listed derivations using a finite control set and finite saturated cut relation.
ConcreteCanonicalLearnerWorkingGrammarConstruction.lean compiled finite controls, corrected binary rules, cut pairs, and sample starts into an actual finite WorkingMCFG and proved the forward language inclusion.
ConcreteCanonicalLearnerWorkingGrammarEquivalence.lean inverted every compiled grammar derivation, proved exact language equality, and characterized realizability by K = ∅ ∨ Nonempty α.
ConcreteCanonicalLearnerWorkingGrammarIdentification.lean made actual compiled WorkingMCFG objects the learner outputs and proved consistency, monotonicity, characteristic samples, start-rooted class identification, selected-stage exactness, and retained source-rule bounds.
```

Most important progress since CI #634:

```text
OutputTypePresentationWorkingGrammarEquivalence.lean proved the reverse derivation translation and exact language equality between a finite typed presentation and its concrete WorkingMCFG.
ConcreteOutputTypeRefinementPresentation.lean constructed the full finite output-type presentation from finite N, finite M, G, and obs.
StartSeparatedOutputTypeRefinementCompleteness.lean replaced an opaque semantic completeness premise by a local syntactic start-separation criterion.
ConcreteTrimmedSuccessfulPresentation.lean defined the successful typed trim by Finset.filter, proved language preservation, and extracted the successful occurrence family automatically.
ConcreteReducedRepresentativeSelection.lean formalized reducedness and representative selection and isolated the parent-output coherence obstruction of the one-base-representative route.
ConcreteObservationDeterministicClosure.lean closed that base-indexed route under the precise TupleTypeDeterministic assumption.
ConcreteTypedCharacteristicSample.lean removed TupleTypeDeterministic and all base representatives by indexing anchors directly by successful typed nonterminals; it proved exact reconstruction and Gold identification for the reachable semantics.
TupleOccurrences.lean and BinaryWitnesses.lean constructed finite sample-dependent enumerations of words, tuples, named contexts, unit rules, exact-once templates, and binary witnesses.
ConcreteCanonicalLearner.lean assembled the first target-independent finite-rule learner and proved its sound inclusion into reachable semantics.
TupleOccurrenceEnumerationCompleteness.lean and NamedFillEnumerationBounds.lean proved completeness of the word/context/tuple/unit-rule enumeration and removed all manually supplied bounds.
BinaryWitnessEnumerationCompleteness.lean corrected the binary template budget to sampleLengthBudget K + dB + dC and proved exact-once binary enumeration completeness.
ExactConcreteCanonicalLearnerEquivalence.lean defined ExactSampleLearnerReachable and proved two-way equivalence with the corrected finite concrete learner.
ConcreteCanonicalLearnerIdentification.lean transferred the typed characteristic-sample reconstruction to the corrected finite learner and proved exact reconstruction, positive-superset exactness, prefix exactness, and Gold identification.
ConcreteCanonicalLearnerClassTheorem.lean proved that one target-independent learner identifies the whole represented language class and supplies finite characteristic samples/tell-tales.
ConcreteCanonicalLearnerStabilization.lean selected a characteristic sample and a concrete coverage/stabilization stage for every target text.
StartRootedConcreteCanonicalLearnerIdentification.lean weakened StartSeparated to semantic StartRootedNormal throughout the grammar-level theorem.
StartRootedConcreteCanonicalLearnerClassTheorem.lean lifted the weaker condition to a uniform class theorem and proved inclusion of the old syntactic class into the new semantic class.
```

Current strongest constructive route:

```text
finite N and finite observation monoid M
+
G.ExactWorkingConditions
+
G.StartRootedNormal
+
G.FanoutAtMost f
+
FixedNamedTupleSubstitutable f obs G.StringLanguage
⇒ full finite typed output presentation
⇒ successful typed trim and concrete typed characteristic sample
⇒ corrected finite exact-once canonical learner
⇒ actual dependent finite hypothesis object
⇒ explicit source-rule cardinality bound
⇒ finite control/cut saturation
⇒ actual finite WorkingMCFG compilation, assuming Nonempty α
⇒ exact grammar-language equivalence
⇒ exact reconstruction on every positive finite superset
⇒ eventual prefix exactness on every positive text
⇒ Gold identification by one target-independent WorkingMCFG-valued learner.
```

Stable finite-rule endpoint:

```lean
correctedConcreteFiniteObjectLearner_class_size_semantic_package
```

Stable actual-grammar endpoints:

```lean
correctedConcreteFiniteHypothesis_cutWorkingGrammar_language_eq
workingGrammarRealization_iff_emptySample_or_nonemptyAlphabet
correctedConcreteWorkingGrammarLearner_identifies_startRootedTargetClass
correctedConcreteWorkingGrammarLearner_presentationSize_semantic_package
correctedConcreteWorkingGrammarLearner_class_structuralBoundary_package
correctedConcreteWorkingGrammarLearner_targetRepresentation_package
correctedConcreteWorkingGrammarLearner_identification_boundedRepresentation_package
correctedConcreteWorkingGrammarLearner_identification_characteristicRank_package
correctedConcreteWorkingGrammarLearner_class_mindChange_package
```

Current actual-grammar quantitative endpoints include:

```lean
grammarRuleCount ≤
  (K.card + 3 * sourceRuleCount + 2) ^ 2

presentationItemCount ≤
  (K.card + 3 * sourceRuleCount + 3) ^ 2

mindChangeCount T N ≤
  (T.prefixSample N).card

logarithmicGrammarBitCount ≤
  (naturalFieldCount + 1) *
    (2 * binaryNatCodeLength naturalFieldValueBound + 1)
```

The natural-field count, every natural-field value, the complete checked
logarithmic bit count, and the final single-power paper bound are now all closed
in `sampleLengthBudget K` and `f`; no serialization-local maximum remains in the
canonical theorem.

The fully expanded presentation-item bound is:

```lean
presentationItemCount ≤
  (sampleLengthBudget K +
      3 *
        ((4 * (sampleLengthBudget K + f + 1)) ^
          (64 *
            (sampleLengthBudget K + f + 1) *
            (sampleLengthBudget K + f + 1))) +
      4) ^ 2.
```

Current progress estimate:

```text
logical theorem plumbing and reachable-model reasoning: complete
exact-once splicing, full presentation, successful trim, and typed characteristic sample: complete
finite corrected canonical learner and exact semantic equivalence: complete
actual finite hypothesis and actual WorkingMCFG-valued learner: complete on the exact alphabet domain
rule/nonterminal/presentation quantitative bounds: complete
checked natural/bit codec and closed sample/fan-out bit bound: complete
single-power paper description-size bound: complete
finite checked code universe, exhaustive decoder search, canonical selector: complete
certificate-carrying learner and certified mind-change transfer: complete
minimum bit/search complexity and simultaneous description-rank framework: complete semantically
description-rank obstruction framework: complete semantically
observation refinement/equivalence/gain/ablation framework: complete abstractly
finite observation products and semantic selection optimization: complete
cardinality/weighted/Pareto/rank hierarchy and selectors: complete semantically
Pareto rank-profile geometry, endpoint width, offset equivalence, and exact order theory: complete semantically
gap-free/gap/first-gap/defect/certificate/selection-family theory: complete semantically
concrete strict observation-separation examples: not yet constructed
executable polynomial learner implementation: about 60--70%
observation-selection encoded decision/optimization complexity: about 35--45%
negative/no-advice and copy/member-kernel boundary results: about 25--35%
positive-learning plus quantitative/certification half: about 95--98%
observation-design mathematical framework: about 98--99% semantically
whole intended paper formalization: about 89--93%
```

The principal remaining work is still divided into three tracks.  On the
executable side: replace brute-force bounded-word enumeration by actual sample
factorization, remove remaining `noncomputable` finite selections, and verify
construction time.  On the observation side, the semantic optimization and
profile/gap theory is now essentially closed; the remaining work is to
construct concrete strict-gain witnesses, replace semantic target-membership
filters by a decidable encoded selection problem, and prove the intended
decision/optimization complexity bounds, including NP-hardness or
NP-completeness if valid.  The new Boolean gap checker is only a finite checker
relative to the already constructed semantic table and does not discharge this
complexity obligation.  On the boundary side: prove no-advice
non-identifiability and the proposed copy/member-kernel exclusions, and decide
whether strict output/start normalization is required by the final paper
statement.

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

Historical CI #634 strongest corrected identification route:

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

Historical CI #634 endpoint:

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

Historical paper-facing constructive endpoint at that phase:

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

Historical best theorem-facing endpoint at that phase:

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

Historical corrected endpoint at that phase:

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

What remains after the CI #738 progress:

```text
executable decidable construction equivalent to the current noncomputable learner
replacement of all-bounded-word enumeration by polynomial sample factorization
verified end-to-end construction-time bound
sharper target-parametric characteristic-sample and total mind-change bounds
exact lower bounds for concrete certified-description-rank families
optional normalization removing semantic StartRootedNormal
strict output compiler preserving paper-side exact-working conditions, if required
one concrete strict observation-gain witness
decidable encoding of semantic observation-selection feasibility
observation-selection decision and optimization complexity
NP-hardness or NP-completeness of observation design, if the intended reduction works
no-advice non-identifiability
copy-language / member-kernel exclusion
```

The previously listed full-presentation, successful-trim, occurrence-extraction,
concrete-grammar-equivalence, tuple/binary enumeration, and concrete-learner
equivalence tasks are now CI-confirmed.

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



### 2.146 `OutputTypePresentationWorkingGrammarEquivalence.lean`

Status: CI passed / user-confirmed.

Purpose:

Prove the converse translation from derivations of the concrete presentation
`WorkingMCFG` back to presentation derivations.

Main verified results:

```lean
presentationStringLanguage_workingGrammar_eq
CompleteOutputTypePresentation.workingGrammar_stringLanguage_eq_original
```

This closes the previously missing reverse inclusion and proves exact language
equality for the concrete presentation grammar.

---

### 2.147 `ConcreteOutputTypeRefinementPresentation.lean`

Status: CI passed / user-confirmed.

Purpose:

Construct the full finite output-type presentation directly from finite `N`,
finite observation monoid `M`, `G`, and `obs`.

Main contents:

```text
all typed nonterminals of compatible arity
all canonical typed terminal rules
all canonical typed binary rules
all canonical typed start rules
finite presentation and completeness for the start-rooted language
```

This eliminates the former external `CompleteOutputTypePresentation` premise at
the full-presentation level.

---

### 2.148 `StartSeparatedOutputTypeRefinementCompleteness.lean`

Status: CI passed / user-confirmed.

Purpose:

Introduce the syntactic condition `WorkingMCFG.StartSeparated` and prove that it
implies ordinary string derivations are start-rooted.

Main results:

```lean
stringLanguage_subset_startRooted_of_startSeparated
concreteCompleteOutputTypePresentation_of_startSeparated
concreteWorkingGrammar_stringLanguage_eq_original_of_startSeparated
```

---

### 2.149 `ConcreteTrimmedSuccessfulPresentation.lean`

Status: CI passed / user-confirmed.

Purpose:

Construct the successful typed trim by finite filtering rather than assuming a
trimmed presentation.

Main contents:

```lean
TypedNonterminal.HasSuccessfulOccurrence
ConcreteSuccessfulOutputTypeRefinement.presentation
StartFreeDerives.toConcreteSuccessfulPresentation
concreteSuccessfulPresentation_stringLanguage_eq_original
concreteTypedSuccessfulOccurrenceFamily
concreteSuccessfulOccurrenceCompletePresentation
```

This automatically extracts the successful occurrence family from trim
membership.

---

### 2.150 `ConcreteReducedRepresentativeSelection.lean`

Status: CI passed / user-confirmed.

Purpose:

Formalize productive/reachable reducedness, successful occurrences, and
base-representative selection.

Main contents:

```lean
WorkingMCFG.SuccessfullyReduced
occurrence_iff_derives_and_spine
concreteReducedBaseRepresentativeSelection
```

The file also isolates the genuine obstruction to a single representative per
base nonterminal: parent output types need not be coherent when one base derives
several observation types.

---

### 2.151 `ConcreteObservationDeterministicClosure.lean`

Status: CI passed / user-confirmed.

Purpose:

Close the base-indexed representative route under the precise semantic
condition `WorkingMCFG.TupleTypeDeterministic`.

Main endpoint:

```lean
concreteObservationDeterministic_paper_conclusion_package
```

This is a valid special case, but it is superseded for the general theorem by
the typed-indexed route.

---

### 2.152 `ConcreteTypedCharacteristicSample.lean`

Status: CI passed / user-confirmed.

Purpose:

Construct the characteristic sample directly over successful typed
nonterminals, avoiding base representatives and tuple-type determinism.

Main contents:

```lean
typedAnchorSample
typedTerminalSample
typedBinarySample
typedStartSample
typedCharacteristicSample
typedCharacteristicSample_positive
presentationDerives_reachable_from_typed_anchor
typedCharacteristicSample_exact_reconstruction
concreteTypedCharacteristicSample_identifies_from_positive_text
```

---

### 2.153 `TupleOccurrences.lean`

Status: CI passed / user-confirmed.

Purpose:

Construct finite sample-dependent enumerations of bounded words, tuples, named
contexts, tuple occurrences, and unit-rule pairs.

Main contents:

```lean
finiteWordsUpTo
sampleAlphabet
finiteTupleCodes
namedContextCandidates
tupleOccurrences
concreteUnitRules
sampleUnitEvidenceOfConcreteRule
```

---

### 2.154 `BinaryWitnesses.lean`

Status: CI passed / user-confirmed.

Purpose:

Enumerate finite exact-once template tuples and sample binary witnesses.

Main contents:

```lean
finiteExactTemplateTupleCodesUpTo
FiniteBinaryWitnessCandidate
concreteBinaryWitnesses
sampleBinaryEvidenceOfConcreteWitness
```

---

### 2.155 `ConcreteCanonicalLearner.lean`

Status: CI passed / user-confirmed at Lean CI #643, commit `ef81a10`.

Purpose:

Assemble finite unit and binary rule sets into a target-independent concrete
learner.

Main contents:

```lean
ConcreteCanonicalLearnerDerives
ConcreteCanonicalStringDerives
ConcreteCanonicalLearnerLanguage
concreteCanonicalLearner
```

Verified here:

```lean
ConcreteCanonicalLearnerLanguage K obs f
  ⊆ ReachableSampleStringLanguage K obs f
```

---

### 2.156 `TupleOccurrenceEnumerationCompleteness.lean`

Status: CI passed / user-confirmed.

Purpose:

Prove completeness of fixed-length list, bounded-word, tuple-code,
named-context, tuple-occurrence, and bounded unit-rule enumeration.

Main endpoint:

```lean
concreteUnitRuleOfEvidenceUpTo
```

---

### 2.157 `NamedFillEnumerationBounds.lean`

Status: CI passed / user-confirmed.

Purpose:

Derive all default occurrence bounds automatically from `namedFill` membership
in the finite sample.

Main results:

```lean
wellFormed_holes_length
namedFill_chunk_mem_sampleBoundedWords
namedFill_component_mem_sampleBoundedWords
concreteUnitRuleOfEvidence
concreteCanonicalLearnerDerives_unit_of_evidence
```

---

### 2.158 `BinaryWitnessEnumerationCompleteness.lean`

Status: CI passed / user-confirmed.

Purpose:

Correct the finite binary-template bound and prove exact-once binary witness
enumeration completeness.

Corrected bound:

```lean
sampleLengthBudget K + dB + dC
```

Main endpoint:

```lean
correctedConcreteBinaryRuleOfEvidence
```

---

### 2.159 `ExactConcreteCanonicalLearnerEquivalence.lean`

Status: CI passed / user-confirmed.

Purpose:

Define the exact-once reachable semantics and prove it equivalent to the
corrected finite concrete learner.

Main contents:

```lean
ExactSampleLearnerReachable
CorrectedConcreteCanonicalLearnerDerives
correctedConcreteCanonicalLearnerDerives_iff_exactReachable
correctedConcreteCanonicalLearnerLanguage_eq_exactReachable
```

---

### 2.160 `ConcreteCanonicalLearnerIdentification.lean`

Status: CI passed / user-confirmed.

Purpose:

Transfer the typed characteristic-sample simulation to exact-once reachability
and then to the corrected finite concrete learner.

Main endpoints:

```lean
concreteTypedCharacteristicSample_correctedConcrete_exact
concreteTypedCharacteristicSample_correctedConcrete_exact_for_positive_superset
correctedConcreteCanonicalLearner_identifies_from_positive_text
correctedConcreteCanonicalLearner_paper_main_theorem
correctedConcreteCanonicalLearner_conclusion_package
```

---

### 2.161 `ConcreteCanonicalLearnerClassTheorem.lean`

Status: CI passed / user-confirmed.

Purpose:

Package the grammar-level theorem as a uniform language-class theorem for one
target-independent learner.

Main contents:

```lean
CorrectedConcreteTargetWitness
CorrectedConcreteTargetClass
correctedConcreteCanonicalLearner_identifies_targetClass
correctedConcreteCanonicalLearner_class_conclusion_package
```

---

### 2.162 `ConcreteCanonicalLearnerStabilization.lean`

Status: CI passed / user-confirmed.

Purpose:

Select a finite characteristic sample for each target language and a concrete
coverage/stabilization stage for each positive text.

Main contents:

```lean
correctedConcreteTargetCharacteristicSample
correctedConcreteTargetCoverageStage
correctedConcreteCanonicalLearner_correct_after_coverageStage
correctedConcreteCanonicalLearner_eventually_language_constant
```

---

### 2.163 `StartRootedConcreteCanonicalLearnerIdentification.lean`

Status: CI passed / user-confirmed.

Purpose:

Replace syntactic `StartSeparated` by the weaker semantic condition
`WorkingMCFG.StartRootedNormal` throughout the grammar-level theorem.

Main endpoint:

```lean
correctedConcreteCanonicalLearner_conclusion_package_of_startRooted
```

---

### 2.164 `StartRootedConcreteCanonicalLearnerClassTheorem.lean`

Status: CI passed / user-confirmed at Lean CI #651, commit `a628798`.

Purpose:

Lift the semantic start-rooted theorem to a uniform class theorem and selected
stabilization package.

Main contents:

```lean
StartRootedCorrectedConcreteTargetWitness
StartRootedCorrectedConcreteTargetClass
correctedConcreteTargetClass_subset_startRooted
correctedConcreteCanonicalLearner_identifies_startRootedTargetClass
startRootedCorrectedConcreteTargetCharacteristicSample
startRootedCorrectedConcreteTargetCoverageStage
correctedConcreteCanonicalLearner_startRooted_stabilization_conclusion_package
```

This is the current strongest class-level endpoint.

---


### 2.165 `ConcreteCanonicalLearnerFiniteEnumerationBounds.lean`

Status: CI passed / confirmed by the CI #665 chain.

Purpose:

Prove cardinality bounds for the actual finite brute-force enumerators.

Main contents:

```lean
finiteWordEnumerationBound
namedContextEnumerationBound
tupleOccurrenceEnumerationBound
unitRuleEnumerationBound
exactTemplateTupleEnumerationBound
correctedBinaryWitnessEnumerationBound
correctedConcreteRuleCountUpToFanout
correctedConcreteRuleCountUpToFanout_le
```

This is the first quantitative layer for the concrete learner.

---

### 2.166 `ConcreteCanonicalLearnerLengthOnlyBounds.lean`

Status: CI passed / confirmed by the CI #665 chain.

Purpose:

Replace sample-alphabet cardinality by the total sample-length budget.

Main contents:

```lean
card_sampleAlphabet_le_sampleLengthBudget
finiteWordEnumerationBound_mono_alphabet
sampleLengthOnlyUnitRuleCountBound
sampleLengthOnlyCorrectedBinaryRuleCountBound
sampleLengthOnlyCorrectedRuleCountBound
correctedConcreteRuleCountUpToFanout_le_lengthOnly
```

---

### 2.167 `ConcreteCanonicalLearnerSinglePowerBounds.lean`

Status: CI passed / confirmed by the CI #665 chain.

Purpose:

Absorb all rule-family bounds into one common base and one exponent.

Main contents:

```lean
uniformEnumerationBase
uniformUnitRuleExponent
uniformBinaryRuleExponent
uniformRuleExponent
singlePowerCorrectedRuleCountBound
correctedConcreteRuleCountUpToFanout_le_singlePower
```

---

### 2.168 `ConcreteCanonicalLearnerPolynomialExponentBounds.lean`

Status: CI passed / confirmed by the CI #665 chain.

Purpose:

Expand the common exponent and derive a simpler paper-facing quadratic
exponent.

Main contents:

```lean
expandedUniformRuleExponent
expandedSinglePowerCorrectedRuleCountBound
correctedLearnerPaperRuleCountBound
correctedConcreteRuleCountUpToFanout_le_paperBound
correctedConcreteRuleCountUpToFanout_le_explicit_paperPower
```

Verified explicit bound:

```lean
correctedConcreteRuleCountUpToFanout K obs f ≤
  (4 * (sampleLengthBudget K + f + 1)) ^
    (64 *
      (sampleLengthBudget K + f + 1) *
      (sampleLengthBudget K + f + 1)).
```

---

### 2.169 `ConcreteCanonicalLearnerFiniteHypothesis.lean`

Status: CI passed / confirmed by the CI #665 chain.

Purpose:

Package the arity-indexed finite rule families into an actual dependent finite
hypothesis object.

Main contents:

```lean
CorrectedConcreteUnitRuleCode
CorrectedConcreteBinaryRuleCode
CorrectedConcreteFiniteHypothesis
correctedConcreteFiniteHypothesis
FiniteCorrectedConcreteLearnerDerives
FiniteCorrectedConcreteLearnerLanguage
finiteCorrectedConcreteLearnerLanguage_eq
finiteCorrectedConcreteLearnerLanguage_eq_exactReachable
```

This is the first actual finite hypothesis object, rather than a language-valued
facade.

---

### 2.170 `ConcreteCanonicalLearnerFiniteHypothesisSize.lean`

Status: CI passed / confirmed by the CI #665 chain.

Purpose:

Apply the quantitative bounds to the actual dependent finite hypothesis.

Main contents:

```lean
card_positiveArities
card_finset_sigma_le_card_mul
card_finiteCorrectedConcreteUnitRuleCodes_le_uniform
card_finiteCorrectedConcreteBinaryRuleCodes_le_uniform
correctedConcreteFiniteHypothesis_ruleCount_le_singlePower
correctedConcreteFiniteHypothesis_ruleCount_le_explicit_paperPower
correctedConcreteFiniteHypothesis_size_semantic_package
```

---

### 2.171 `ConcreteCanonicalLearnerFiniteObjectIdentification.lean`

Status: CI passed / confirmed by the CI #665 chain.

Purpose:

Make the actual finite rule object the fixed hypothesis type of the learner.

Main contents:

```lean
ListedFiniteCorrectedConcreteLearnerDerives
CorrectedConcreteFiniteHypothesis.Language
CorrectedConcreteFiniteHypothesisObject
correctedConcreteFiniteObjectLearner
correctedConcreteFiniteObjectHypLanguage
correctedConcreteFiniteObjectLearner_identifies_startRootedTargetClass
correctedConcreteFiniteObjectLearner_class_size_semantic_package
```

The listed semantics explicitly carries membership proofs in the stored rule
lists.

---

### 2.172 `ConcreteCanonicalLearnerFiniteObjectMonotone.lean`

Status: CI passed / confirmed by the CI #665 chain.

Purpose:

Construct rule-level sample-extension transports and structurally transport
listed derivation trees.

Main contents:

```lean
CorrectedConcreteUnitRuleCode.mono
CorrectedConcreteBinaryRuleCode.mono
CorrectedConcreteFiniteHypothesisSimulation
CorrectedConcreteFiniteHypothesisSimulation.ofSampleSubset
CorrectedConcreteFiniteHypothesisSimulation.derives
correctedConcreteFiniteHypothesis_language_mono
correctedConcreteFiniteObjectLearner_language_mono
```

---

### 2.173 `ConcreteCanonicalLearnerFiniteObjectDirectedSystem.lean`

Status: CI passed / included in the confirmed CI #665 project chain.

Purpose:

Give finite-hypothesis simulations identity, composition, and coherent
prefix-directed-system structure.

Main contents:

```lean
CorrectedConcreteFiniteHypothesisSimulation.refl
CorrectedConcreteFiniteHypothesisSimulation.comp
correctedConcreteTextFiniteHypothesis
correctedConcreteTextSimulation
correctedConcreteTextSimulation_refl
correctedConcreteTextSimulation_trans
correctedConcreteFiniteObject_directedStabilization_package
```

---

### 2.174 `ConcreteCanonicalLearnerWorkingGrammarObstruction.lean`

Status: CI passed / dependency of the CI #665 endpoint.

Purpose:

Identify the exact obstruction to unconditional compilation into the current
`WorkingMCFG` syntax.

Main contents:

```lean
DerivesTuple.alphabet_nonempty
WorkingMCFG.stringLanguage_eq_empty_of_isEmpty
CorrectedConcreteFiniteObjectWorkingGrammarRealization
emptySampleWorkingGrammarRealization
emptyAlphabet_epsilonSample_not_represented
workingGrammarRealization_implies_compilationDomain
```

Key correction:

```text
nonempty WorkingMCFG language ⇒ Nonempty α,
```

whereas the finite learner over the empty alphabet and sample `{ε}` generates
`ε`.  Thus unconditional compilation is false.

---

### 2.175 `ConcreteCanonicalLearnerWorkingGrammarCutSaturation.lean`

Status: CI passed / dependency of the CI #665 endpoint.

Purpose:

Normalize transitive listed derivations through a finite control set and a
finite saturated cut relation.

Main contents:

```lean
FiniteObjectTupleCode
CorrectedConcreteFiniteHypothesis.controlCodes
CutNormalizedListedFiniteDerives
ListedFiniteCorrectedConcreteLearnerDerives.toCutNormalized
CorrectedConcreteFiniteHypothesis.cutPairs
correctedConcreteFiniteHypothesis_language_iff_cutNormalized
```

---

### 2.176 `ConcreteCanonicalLearnerWorkingGrammarConstruction.lean`

Status: CI passed / dependency of the CI #665 endpoint.

Purpose:

Compile the finite controls, corrected binary rules, saturated cuts, and sample
starts into an actual finite `WorkingMCFG`.

Main contents:

```lean
CorrectedConcreteCutGrammarNonterminal
correctedConcreteCutConstantRule
correctedConcreteCutLiftedBinaryRule
correctedConcreteCutSaturationRule
CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG
CutNormalizedListedFiniteDerives.toCutWorkingMCFG
correctedConcreteFiniteHypothesis_language_subset_cutWorkingGrammar
```

The construction uses a dummy terminal seed.  Its constant and cut rules are
not asserted to satisfy the paper-side nondeleting/exact-once conditions.

---

### 2.177 `ConcreteCanonicalLearnerWorkingGrammarEquivalence.lean`

Status: CI passed / user-confirmed before CI #665.

Purpose:

Invert every derivation of the compiled grammar and prove exact language
equality.

Main contents:

```lean
CorrectedConcreteCutWorkingGrammarDerivationView
CorrectedConcreteCutWorkingGrammarDerivationView.ofDerives
cutWorkingGrammar_control_derives_iff
cutWorkingGrammar_start_derives_iff
correctedConcreteFiniteHypothesis_cutWorkingGrammar_language_eq
workingGrammarRealization_iff_emptySample_or_nonemptyAlphabet
```

Exact domain theorem:

```lean
Nonempty CorrectedConcreteFiniteObjectWorkingGrammarRealization ↔
  K = ∅ ∨ Nonempty α.
```

---

### 2.178 `ConcreteCanonicalLearnerWorkingGrammarIdentification.lean`

Status: CI passed / user-confirmed at Lean CI #665, commit `1ef3ea8`.

Purpose:

Make actual compiled finite `WorkingMCFG` objects the learner output type and
transfer the complete Gold-identification theorem.

Main contents:

```lean
CorrectedConcreteWorkingGrammarHypothesis
correctedConcreteWorkingGrammarLearner
correctedConcreteWorkingGrammarHypLanguage
correctedConcreteWorkingGrammarLearner_consistent
correctedConcreteWorkingGrammarLearner_language_mono
correctedConcreteWorkingGrammarLearner_identifies_startRootedTargetClass
correctedConcreteWorkingGrammarLearner_correct_after_startRootedCoverageStage
correctedConcreteWorkingGrammarLearner_class_conclusion_package
correctedConcreteWorkingGrammarLearner_selectedStage_package
```

This is the current strongest actual-grammar-valued endpoint.

---


### 2.179 `ConcreteCanonicalLearnerWorkingGrammarSize.lean`

Status: CI passed / user-confirmed.

Purpose:

Count every rule stored by the actual cut-saturated `WorkingMCFG` and connect
the compiler overhead to the existing source finite-rule bound.

Main contents:

```lean
card_sample_le_lengthBudget_add_one
CorrectedConcreteFiniteHypothesis.controlCodes_card_le_sample_add_three_ruleCount
CorrectedConcreteFiniteHypothesis.cutPairs_card_le_controlCodes_square
CorrectedConcreteFiniteHypothesis.compiledGrammarRuleCount
CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_totalRuleCount_eq
CorrectedConcreteFiniteHypothesis.compiledGrammarRuleCount_le_quadratic
correctedConcreteCompiledGrammarRuleCountBound
correctedConcreteWorkingGrammarLearner_grammarRuleCount_le_explicit
correctedConcreteWorkingGrammarLearner_size_semantic_package
```

Central structural estimate:

```lean
H.compiledGrammarRuleCount ≤
  (K.card + 3 * H.ruleCount + 2) ^ 2.
```

---

### 2.180 `ConcreteCanonicalLearnerWorkingGrammarPresentationSize.lean`

Status: CI passed / user-confirmed.

Purpose:

Explicitly enumerate every nonterminal of the compiled grammar and bound the
complete top-level presentation size.

Main contents:

```lean
CorrectedConcreteFiniteHypothesis.compiledGrammarNonterminals
CorrectedConcreteFiniteHypothesis.mem_compiledGrammarNonterminals
CorrectedConcreteFiniteHypothesis.compiledGrammarNonterminalCount
CorrectedConcreteFiniteHypothesis.compiledGrammarPresentationItemCount
CorrectedConcreteFiniteHypothesis.compiledGrammarPresentationItemCount_le_structuralSquare
correctedConcreteCompiledGrammarPresentationItemBound
correctedConcreteWorkingGrammarLearner_presentationItemCount_le_explicit
correctedConcreteWorkingGrammarLearner_presentationSize_semantic_package
```

Exact nonterminal count and structural presentation bound:

```lean
nonterminalCount = controlCodes.card + 2

presentationItemCount ≤
  (K.card + 3 * sourceRuleCount + 3) ^ 2.
```

---

### 2.181 `ConcreteCanonicalLearnerWorkingGrammarStructuralConditions.lean`

Status: CI passed / user-confirmed.

Purpose:

Identify exactly which syntactic conditions are preserved by the compiler and
which paper-side conditions fail.

Main contents:

```lean
CorrectedConcreteFiniteHypothesis.controlCode_arity_le_max
CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_fanoutAtMost_max
WorkingMCFG.CutCompiledConditions
CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_cutCompiledConditions
constantTupleTemplate_not_nondeleting
correctedConcreteCutConstantRule_not_nondeleting
CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_not_basicWorkingConditions_of_sample_nonempty
CorrectedConcreteFiniteHypothesis.toCutWorkingMCFG_not_exactWorkingConditions_of_sample_nonempty
correctedConcreteWorkingGrammarLearner_class_structuralBoundary_package
```

Verified positive conditions:

```text
start arity one
well-typed start rules
well-typed terminal rules
fan-out at most max 1 f.
```

Verified boundary:

```lean
K.Nonempty →
  ¬ (H.toCutWorkingMCFG dummy).ExactWorkingConditions.
```

---

### 2.182 `ConcreteCanonicalLearnerWorkingGrammarRepresentation.lean`

Status: CI passed / user-confirmed.

Purpose:

Define the correct class of languages represented by actual cut-compiled
grammars and prove exact representation of every start-rooted target.

Main contents:

```lean
CutCompiledWorkingGrammarRepresentation
CutCompiledWorkingGrammarLanguageClass
CorrectedConcreteWorkingGrammarTargetRepresentationWitness
correctedConcreteWorkingGrammarTargetRepresentation_of_characteristicSample
correctedConcreteWorkingGrammarLearner_exists_targetRepresentation
startRootedTargetClass_subset_cutCompiledWorkingGrammarLanguageClass
correctedConcreteWorkingGrammarLearner_targetRepresentation_package
correctedConcreteWorkingGrammarLearner_representation_identification_package
```

Each target representation carries a finite positive construction sample,
actual grammar, exact language equality, compiler conditions, and all verified
size bounds.

---

### 2.183 `ConcreteCanonicalLearnerWorkingGrammarBoundedRepresentation.lean`

Status: CI passed / user-confirmed.

Purpose:

Stratify exact grammar representations by the total length of the finite
positive construction sample.

Main contents:

```lean
correctedLearnerPaperRuleCountBound_mono_sampleLength
correctedConcreteCompiledGrammarPresentationItemBound_mono_sampleLength
BoundedCutCompiledWorkingGrammarRepresentation
BoundedCutCompiledWorkingGrammarLanguageClass
boundedCutCompiledWorkingGrammarLanguageClass_mono
correctedConcreteWorkingGrammarLearner_boundedRepresentation
CorrectedConcreteBoundedWorkingGrammarTargetWitness
startRootedTarget_mem_some_boundedCutCompiledClass
correctedConcreteWorkingGrammarLearner_boundedRepresentation_package
```

The bounded classes form an increasing hierarchy, and every semantic
start-rooted target belongs to some finite level.

---

### 2.184 `ConcreteCanonicalLearnerWorkingGrammarRepresentationRank.lean`

Status: CI passed / user-confirmed.

Purpose:

Define least sample-length budgets for bounded representation and for exact
output by the canonical grammar-valued learner.

Main contents:

```lean
HasBoundedCutCompiledWorkingGrammarRepresentation
boundedCutCompiledWorkingGrammarRepresentationRank
CorrectedConcreteWorkingGrammarExactOutputAtBudget
HasCorrectedConcreteWorkingGrammarExactOutputBudget
correctedConcreteWorkingGrammarExactOutputRank
boundedRepresentationRank_le_exactOutputRank
startRootedTargetExactOutputRank
startRootedTargetExactOutputRank_le_selectedCharacteristicSampleLength
correctedConcreteWorkingGrammarLearner_representationRank_package
```

Verified inequality:

```text
minimum bounded-representation budget
≤ minimum exact learner-output budget.
```

---

### 2.185 `ConcreteCanonicalLearnerWorkingGrammarCharacteristicRank.lean`

Status: CI passed / user-confirmed.

Purpose:

Define the minimum total word length of a characteristic sample for the actual
grammar-valued learner.

Main contents:

```lean
CorrectedConcreteWorkingGrammarCharacteristicAtBudget
HasCorrectedConcreteWorkingGrammarCharacteristicBudget
correctedConcreteWorkingGrammarCharacteristicRank
exactOutputRank_le_characteristicRank
boundedRepresentationRank_le_characteristicRank
startRootedTargetCharacteristicRank
startRootedTarget_exists_characteristicSample_at_rank
startRootedTarget_fullRankChain
correctedConcreteWorkingGrammarLearner_identification_characteristicRank_package
```

Full target-level rank chain:

```text
representation rank
≤ exact-output rank
≤ characteristic rank
≤ selected characteristic-sample total length.
```

---

### 2.186 `ConcreteCanonicalLearnerWorkingGrammarMindChanges.lean`

Status: CI passed / user-confirmed at Lean CI #674, commit `94d1590`.

Purpose:

Formalize semantic language changes along positive texts and connect them to
minimum characteristic-sample coverage.

Main contents:

```lean
correctedConcreteWorkingGrammarTextLanguage
CorrectedConcreteWorkingGrammarLanguageChangesAt
correctedConcreteWorkingGrammarMindChangeCount
correctedConcreteWorkingGrammarLanguageChangesAt_implies_prefixSample_card_lt
correctedConcreteWorkingGrammarMindChangeCount_le_prefixSample_card
correctedConcreteWorkingGrammarCharacteristicCoverageStage
startRootedTargetMinimalCharacteristicSample
correctedConcreteWorkingGrammar_correct_after_minimalCharacteristicCoverage
correctedConcreteWorkingGrammar_no_mindChanges_after_minimalCharacteristicCoverage
correctedConcreteWorkingGrammarLearner_class_mindChange_package
```

Every semantic language change strictly increases the prefix-sample
cardinality, and after minimum-characteristic-sample coverage the output
language is permanently equal to the target and the cumulative mind-change
count is constant.

---


### 2.187 `ConcreteCanonicalLearnerWorkingGrammarDescriptionSize.lean`

Status: CI passed.

Purpose:

Introduce an abstract encoded-entry cost model for the complete cut-compiled
grammar.

Main results:

```lean
descriptionSize_le_presentationItemCount_mul
descriptionSize_le_structuralSquare_mul
correctedConcreteFiniteHypothesis_descriptionSize_le_paperBound
correctedConcreteFiniteHypothesis_descriptionSize_le_explicit
```

This is the first bridge from top-level item count to the amount of data stored
inside items.

---

### 2.188 `ConcreteCanonicalLearnerWorkingGrammarNaturalEncoding.lean`

Status: CI passed.

Purpose:

Specialize abstract entry costs to natural-number codes and unary
self-delimiting costs.

Main results:

```lean
boundedBy_maxEntryCost
descriptionSize_le_presentationItemCount_mul_maxEntryCost
CorrectedConcreteCompiledGrammarNaturalEncoding.unaryDescriptionSize_le_presentationItemCount_mul
correctedConcreteFiniteHypothesis_unaryDescriptionSize_le_paperBound
```

---

### 2.189 `ConcreteCanonicalLearnerWorkingGrammarBinaryEncoding.lean`

Status: CI passed.

Purpose:

Replace unary code length by a standard binary payload length and derive total
binary-size bounds from a common fitting bit width.

Main results:

```lean
binaryNatCodeLength_le_succ_of_lt_two_pow
CorrectedConcreteCompiledGrammarNaturalEncoding.CodesFitInBits
CorrectedConcreteCompiledGrammarNaturalEncoding.binaryDescriptionSize_le_presentationItemCount_mul
correctedConcreteFiniteHypothesis_binaryDescriptionSize_le_explicit
```

---

### 2.190 `ConcreteCanonicalLearnerWorkingGrammarAutomaticBitWidth.lean`

Status: CI passed.

Purpose:

Select the least positive fitting width from the finite set of actually used
entry codes.

Main results:

```lean
natCode_lt_two_pow_binaryNatCodeLength
CorrectedConcreteCompiledGrammarNaturalEncoding.codesFitInBits_automaticBitWidth
CorrectedConcreteCompiledGrammarNaturalEncoding.automaticBitWidth_isLeastPositiveFitting
correctedConcreteFiniteHypothesis_binaryDescriptionSize_le_automatic_explicit
```

---

### 2.191 `ConcreteCanonicalLearnerWorkingGrammarDenseEncoding.lean`

Status: CI passed.

Purpose:

Encode each entry by its position in the corresponding finite presentation
list, obtaining logarithmic width in the number of stored items.

Main results:

```lean
denseNaturalEncoding_codesBelow_presentationItemCount
denseNaturalEncoding_automaticBitWidth_le_presentationItemLength
denseNaturalEncoding_binaryDescriptionSize_le_itemCount_mul_logWidth
correctedConcreteFiniteHypothesis_denseBinaryDescriptionSize_le_explicit
```

---

### 2.192 `ConcreteCanonicalLearnerWorkingGrammarTaggedDenseEncoding.lean`

Status: CI passed.

Purpose:

Combine nonterminal, start-rule, terminal-rule, and binary-rule entries into one
tagged finite presentation list and assign globally collision-free dense codes.

Main results:

```lean
compiledGrammarPresentationEntries_length
compiledGrammarGlobalDenseCode_lt_presentationItemCount
compiledGrammarGlobalDenseCode_injective_on_storedEntries
taggedDenseNaturalEncoding_binaryDescriptionSize_le_itemCount_mul_logWidth
```

---

### 2.193 `ConcreteCanonicalLearnerWorkingGrammarTaggedDenseDecoding.lean`

Status: CI passed.

Purpose:

Turn the tagged dense numbering into a checked finite codec.

Main results:

```lean
compiledGrammarGlobalDenseDecode_encode_of_mem
compiledGrammarGlobalDenseDecode_sound
compiledGrammarGlobalDenseDecode_complete
compiledGrammarGlobalDenseDecode_eq_none_of_presentationItemCount_le
compiledGrammarTaggedDenseCodec_package
```

---

### 2.194 `ConcreteCanonicalLearnerWorkingGrammarTemplateSerialization.lean`

Status: CI passed.

Purpose:

Serialize dependent template atoms to nondependent tagged structural tokens and
decode them with explicit left/right arity checks.

Main results:

```lean
decodeTemplateAtomStructural_encode
decodeTemplateWordStructural_encode
decodeTemplateTupleStructural_component
BinaryRule.decode_structuralBodyTokens_component
BinaryRule.structuralBodyTokens_roundTrip_package
```

---

### 2.195 `ConcreteCanonicalLearnerWorkingGrammarTemplateTupleFraming.lean`

Status: CI passed.

Purpose:

Flatten a template tuple into a single length-prefixed token stream while
preserving output-component boundaries.

Main results:

```lean
decodeFramedTemplateWords_encode
encodeFramedTemplateWords_length
decodeTemplateTupleFramed_encode
BinaryRule.framedStructuralBodyTokens_roundTrip_package
```

The exact flat-token count equals the lhs fan-out plus the total number of
template atoms.

---

### 2.196 `ConcreteCanonicalLearnerWorkingGrammarBinaryRuleSerialization.lean`

Status: CI passed.

Purpose:

Combine lhs, left-child, and right-child global nonterminal codes with the
framed template body and reconstruct a dependent `BinaryRule`.

Main results:

```lean
decodeCompiledNonterminalCode_encode
decodeCompiledBinaryRuleStructuralPacket_encode
compiledBinaryRuleStructuralFieldCount_eq
compiledBinaryRuleStructuralCodec_package
```

---

### 2.197 `ConcreteCanonicalLearnerWorkingGrammarTerminalAlphabetEncoding.lean`

Status: CI passed.

Purpose:

Densely encode terminal symbols over the finite augmented alphabet

```lean
insert dummy (sampleAlphabet K)
```

and naturalize all framed template-body tokens.

Main results:

```lean
compiledTerminalDenseDecode_encode_of_mem
compiledTerminalDenseCode_lt_card
decodeTemplateAtomNatural_encode
decodeFramedTemplateBodyNatural_encode
framedTemplateBodyNaturalCodec_package
```

---

### 2.198 `ConcreteCanonicalLearnerWorkingGrammarBinaryRuleNaturalSerialization.lean`

Status: CI passed.

Purpose:

Serialize a complete binary rule as a pure `List Nat`.

Encoding shape:

```text
[lhsCode, leftCode, rightCode, bodyTokenCount] ++ encodedBody
```

Main results:

```lean
decodeCompiledBinaryRuleNaturalPacket_encode
decodeCompiledBinaryRuleNaturalList_encode
encodeCompiledBinaryRuleNaturalList_length
compiledBinaryRuleNaturalListCodec_package
```

---

### 2.199 `ConcreteCanonicalLearnerWorkingGrammarBinaryRuleTerminalClosure.lean`

Status: CI passed.

Purpose:

Remove the external terminal-support premise from the natural binary-rule codec
for every rule actually stored in the compiled grammar.

Verified separately for:

```text
control constant rules
lifted corrected sample rules
saturated cut rules
```

Main results:

```lean
controlCode_tuple_terminalsIn_sampleAlphabet
cutWorkingGrammar_binaryRule_framedTokens_terminalsIn
decodeCompiledBinaryRuleNaturalList_encode_of_mem
compiledBinaryRuleNaturalListCodec_of_mem_package
```

---

### 2.200 `ConcreteCanonicalLearnerWorkingGrammarPresentationNaturalSerialization.lean`

Status: CI passed.

Purpose:

Serialize all top-level presentation entries and then the complete cut-compiled
grammar as one checked `List Nat`.

Entry tags:

```text
0 = nonterminal
1 = start rule
2 = terminal rule
3 = binary rule
```

The complete stream stores the entry count and a length prefix for every entry.

Main results:

```lean
decodeCompiledGrammarPresentationEntryNaturalList_encode_of_mem
decodeCompiledGrammarPresentationEntryStreamExact_encode
decodeCompiledWorkingGrammarNaturalList_encode
encodeCompiledWorkingGrammarNaturalList_length
compiledWorkingGrammarNaturalCodec_package
```

---

### 2.201 `ConcreteCanonicalLearnerWorkingGrammarUnaryBitSerialization.lean`

Status: CI passed.

Purpose:

Convert the complete natural grammar stream to a genuine prefix-free
`List Bool` serialization using unary natural codes.

Main results:

```lean
decodeUnaryNatBits_encode_append
decodeUnaryNatListBits_encode
encodeUnaryNatListBits_length_closed
decodeCompiledWorkingGrammarUnaryBitList_encode
compiledWorkingGrammarUnaryBitCodec_package
```

Exact bit length for natural fields `fields`:

```text
1 + 2 * fields.length + fields.sum
```

---

### 2.202 `ConcreteCanonicalLearnerWorkingGrammarLogarithmicBitSerialization.lean`

Status: CI passed.

Purpose:

Replace unary field payloads by a recursively half-sized self-delimiting
binary-tree natural code.

Cost recurrence:

```text
L(0) = 1
L(n + 1) = L(n / 2) + 2
```

Main results:

```lean
decodeBinaryTreeNatBits_encode_append
encodeBinaryTreeNatBits_length
decodeBinaryTreeNatListBits_encode
compiledWorkingGrammarLogarithmicBitCount_le_fieldCount_mul_maximum
compiledWorkingGrammarLogarithmicBitCodec_package
```

---

### 2.203 `ConcreteCanonicalLearnerWorkingGrammarLogarithmicBitBounds.lean`

Status: CI passed.

Purpose:

Connect recursive binary-tree code cost to the standard binary payload length.

Main bounds:

```lean
n < 2 ^ b →
  binaryTreeNatBitCost n ≤ 2 * b + 1

binaryTreeNatBitCost n ≤
  2 * binaryNatCodeLength n + 1
```

Whole-stream and whole-grammar endpoints:

```lean
encodeBinaryTreeNatListBits_length_le_of_fieldsFitInBits
compiledWorkingGrammarLogarithmicBitCount_le_of_naturalFieldsFitInBits
compiledWorkingGrammarExplicitLogarithmicBitBound_package
```

---

### 2.204 `ConcreteCanonicalLearnerWorkingGrammarAutomaticNaturalFieldBitWidth.lean`

Status: CI passed.

Purpose:

Remove the externally supplied common width for the complete natural stream.

Definition:

```lean
automaticNaturalFieldBitWidth fields :=
  maximumBinaryNatCodeLength (fields.length :: fields)
```

Main results:

```lean
automaticNaturalFieldBitWidth_fits
naturalFieldStreamFitsInBits_iff
automaticNaturalFieldBitWidth_isLeastPositiveFitting
compiledWorkingGrammarNaturalFieldsFitInBits_automatic
compiledWorkingGrammarAutomaticNaturalFieldBitWidth_package
```

---

### 2.205 `ConcreteCanonicalLearnerWorkingGrammarNaturalFieldMaximum.lean`

Status: CI passed at Lean CI #695, commit `01c31b5`.

Purpose:

Reduce the automatically selected width and complete grammar bit count to one
ordinary natural-value bound.

Definition:

```lean
naturalFieldValueBound fields :=
  max fields.length (maximumNaturalFieldValue fields)
```

Main results:

```lean
naturalFieldValueBound_le_iff
naturalFieldStreamFitsInBits_binaryNatCodeLength_valueBound
automaticNaturalFieldBitWidth_le_binaryNatCodeLength_valueBound
compiledWorkingGrammarNaturalFieldValueBound
compiledWorkingGrammarLogarithmicBitCount_le_binaryNatCodeLength_valueBound
compiledWorkingGrammarNaturalFieldMaximum_package
```

Current exact bound:

```text
grammarBitCount
≤
(naturalFieldCount + 1) *
  (2 * binaryNatCodeLength naturalFieldValueBound + 1)
```

The next missing quantitative theorem is a sample/fan-out/presentation bound on
`compiledWorkingGrammarNaturalFieldValueBound` and
`compiledWorkingGrammarNaturalFieldCount`.

---


### 2.206 `ConcreteCanonicalLearnerWorkingGrammarNaturalFieldClassification.lean`

Status: CI passed.

Purpose:

Classifies every natural field in the complete checked grammar serialization, in both directions, and reduces the global maximum to entry-local structural maxima.

Main contents:

```lean
CompiledGrammarPresentationEntryNaturalFieldClass
CompiledWorkingGrammarNaturalFieldClass
compiledWorkingGrammarNaturalField_classification
compiledWorkingGrammarClassifiedNaturalFieldBound
```


### 2.207 `ConcreteCanonicalLearnerWorkingGrammarNaturalFieldEntryBounds.lean`

Status: CI passed.

Purpose:

Evaluates top-level entry bounds using presentation-item count, augmented terminal-alphabet size, and the remaining binary-rule payload bound.

Main contents:

```lean
compiledBinaryRuleNaturalValueBound
compiledGrammarPresentationEntryExplicitNaturalValueBound
compiledWorkingGrammarEntryExplicitNaturalFieldBound
```


### 2.208 `ConcreteCanonicalLearnerWorkingGrammarBinaryRuleNaturalFieldClassification.lean`

Status: CI passed.

Purpose:

Opens a complete binary-rule natural packet into dense nonterminal codes, body-token count, token tags, and token payloads.

Main contents:

```lean
FramedTemplateBodyNaturalToken.NaturalFieldClass
CompiledBinaryRuleNaturalFieldClass
compiledBinaryRuleExplicitNaturalValueBound
compiledBinaryRuleNaturalFieldClassification_package
```


### 2.209 `ConcreteCanonicalLearnerWorkingGrammarBinaryRuleTokenPayloadBounds.lean`

Status: CI passed.

Purpose:

Bounds component-length, terminal-code, and child-variable payloads for every actually stored compiled binary rule.

Main contents:

```lean
compiledBinaryRuleBodyTokenPayloadBound
compiledBinaryRuleFullyExplicitNaturalValueBound
compiledBinaryRuleTokenPayloadBounds_package
```


### 2.210 `ConcreteCanonicalLearnerWorkingGrammarNaturalFieldFullyExplicitBound.lean`

Status: CI passed.

Purpose:

Propagates the fully explicit stored-rule bounds through top-level entries, the complete natural stream, and the logarithmic bit codec.

Main contents:

```lean
compiledWorkingGrammarFullyExplicitNaturalFieldBound
```


### 2.211 `ConcreteCanonicalLearnerWorkingGrammarUniformNaturalFieldBound.lean`

Status: CI passed.

Purpose:

Replaces entry-by-entry maxima by one uniform grammar-wide natural-field bound and corresponding bit width.

Main contents:

```lean
compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
compiledWorkingGrammarUniformNaturalFieldBound
compiledWorkingGrammarUniformNaturalFieldBitWidth
compiledWorkingGrammarUniformNaturalFieldBound_package
```


### 2.212 `ConcreteCanonicalLearnerWorkingGrammarBinaryRuleFamilyBodyBounds.lean`

Status: CI passed.

Purpose:

Bounds body-token counts for constant control, lifted sample, and saturated cut rules by one expression in sample length and fan-out.

Main contents:

```lean
compiledWorkingGrammarBinaryRuleBodyTokenCountSampleFanoutBound
cutWorkingGrammar_binaryRule_bodyTokenCount_le_sampleFanoutBound
```


### 2.213 `ConcreteCanonicalLearnerWorkingGrammarSampleParametricBitBound.lean`

Status: CI passed.

Purpose:

Eliminates all serializer-local maxima and obtains a closed checked logarithmic bit bound using only sampleLengthBudget and fan-out.

Main contents:

```lean
correctedConcreteCompiledGrammarSampleParametricNaturalFieldBound
correctedConcreteCompiledGrammarSampleParametricLogarithmicBitBound
correctedConcreteFiniteHypothesis_logarithmicBitCount_le_sampleParametric
```


### 2.214 `ConcreteCanonicalLearnerWorkingGrammarPaperBitEnvelope.lean`

Status: CI passed.

Purpose:

Compresses the closed structural formula into one paper description scale, one natural-field envelope, and one paper-facing checked bit envelope.

Main contents:

```lean
correctedConcreteCompiledGrammarPaperDescriptionScale
correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope
```


### 2.215 `ConcreteCanonicalLearnerWorkingGrammarPaperPowerBitBound.lean`

Status: CI passed.

Purpose:

Absorbs the paper envelope into a single power of the existing learner-rule-count base, with exponent multiplier 13.

Main contents:

```lean
correctedConcreteCompiledGrammarPaperPowerExponent
correctedConcreteCompiledGrammarPaperPowerBitBound
correctedConcreteFiniteHypothesis_logarithmicBitCount_le_paperPower
```


### 2.216 `ConcreteCanonicalLearnerWorkingGrammarFinalDescriptionPackage.lean`

Status: CI passed.

Purpose:

Attaches the checked logarithmic bit representation and decoder to the actual WorkingMCFG-valued learner and combines it with semantic identification and selected-stage exactness.

Main contents:

```lean
correctedConcreteWorkingGrammarLearner_checkedDescription_package
correctedConcreteWorkingGrammarLearner_checkedDescription_semantic_package
correctedConcreteWorkingGrammarLearner_selectedStage_checkedDescription_package
correctedConcreteWorkingGrammarLearner_finalDescriptionConclusion_package
```


### 2.217 `ConcreteCanonicalLearnerWorkingGrammarCheckedBitRepresentation.lean`

Status: CI passed.

Purpose:

Packages every actual learner output as a checked bit-bounded cut-compiled representation and builds its bounded hierarchy.

Main contents:

```lean
correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentation
correctedConcreteWorkingGrammarLearner_checkedBitBoundedRepresentationHierarchy_package
correctedConcreteWorkingGrammarLearner_identification_checkedBitBoundedRepresentation_package
```


### 2.218 `ConcreteCanonicalLearnerWorkingGrammarFiniteCodeUniverse.lean`

Status: CI passed.

Purpose:

Enumerates every Boolean code up to the paper-power bit budget and proves exact membership, monotonicity, and the 2^(bound+1) universe-size estimate.

Main contents:

```lean
boolListsOfLength
boolListsUpTo
correctedConcreteCompiledGrammarCheckedBitCodeUniverse
correctedConcreteWorkingGrammarLearner_identification_finiteCodeUniverse_package
```


### 2.219 `ConcreteCanonicalLearnerWorkingGrammarFiniteDecodedSearch.lean`

Status: CI passed.

Purpose:

Filters the finite code universe through the checked decoder, yielding an exhaustive finite search containing the actual learner code/presentation pair.

Main contents:

```lean
successfulDecodePairs
checkedBitDecodedCodeSearch
correctedConcreteWorkingGrammarLearnerDecodedPresentationSearch
correctedConcreteWorkingGrammarLearner_identification_finiteDecodedSearch_package
```


### 2.220 `ConcreteCanonicalLearnerWorkingGrammarCanonicalDecodedSearch.lean`

Status: CI passed.

Purpose:

Adds the exact decode/re-encode fixed-point filter, proves code/value uniqueness, and retains the actual learner presentation with the same finite bound.

Main contents:

```lean
canonicalDecodePairs
checkedBitCanonicalDecodedCodeSearch
correctedConcreteWorkingGrammarLearnerCanonicalDecodedPresentationSearch
correctedConcreteWorkingGrammarLearner_identification_canonicalDecodedSearch_package
```


### 2.221 `ConcreteCanonicalLearnerWorkingGrammarCanonicalSearchSelector.lean`

Status: CI passed.

Purpose:

Defines a finite code-indexed selector and proves that lookup by the emitted checked code returns exactly the actual complete presentation.

Main contents:

```lean
selectCanonicalPairByCode
checkedBitCanonicalPairSelectorByCode
correctedConcreteWorkingGrammarLearnerCanonicalPairSelectorResult
correctedConcreteWorkingGrammarLearner_identification_canonicalSelector_package
```


### 2.222 `ConcreteCanonicalLearnerWorkingGrammarCertifiedOutputLearner.lean`

Status: CI passed.

Purpose:

Introduces a certified hypothesis record carrying the actual grammar, presentation, bits, decoder, re-encoder, canonical search, selector, and all correctness/size proofs.

Main contents:

```lean
CorrectedConcreteCertifiedWorkingGrammarHypothesis
correctedConcreteCertifiedWorkingGrammarLearner
correctedConcreteCertifiedWorkingGrammarLearner_outputCertificate
correctedConcreteCertifiedWorkingGrammarLearner_identification_package
```


### 2.223 `ConcreteCanonicalLearnerWorkingGrammarCertifiedOutputMindChanges.lean`

Status: CI passed.

Purpose:

Transfers semantic mind-change counting, characteristic samples, minimum-characteristic stabilization, and minimum-rank bit/search bounds to the certified learner.

Main contents:

```lean
correctedConcreteCertifiedWorkingGrammarMindChangeCount
characteristicSample_certifiedWorkingGrammar_iff_original
startRootedTargetMinimalCharacteristicCertifiedOutput
correctedConcreteCertifiedWorkingGrammarLearner_identification_mindChange_package
```


### 2.224 `ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionComplexity.lean`

Status: CI passed.

Purpose:

Defines attained minimum checked-bit complexity and attained minimum canonical-search complexity for exact certified outputs.

Main contents:

```lean
correctedConcreteCertifiedBitDescriptionComplexity
correctedConcreteCertifiedCanonicalSearchComplexity
startRootedTargetCertifiedBitDescriptionComplexity
startRootedTargetCertifiedCanonicalSearchComplexity
correctedConcreteCertifiedWorkingGrammarLearner_identification_descriptionComplexity_package
```


### 2.225 `ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionProfile.lean`

Status: CI passed.

Purpose:

Introduces a simultaneous two-dimensional bit/search profile requiring one certificate to meet both budgets and builds the increasing rank-profile hierarchy.

Main contents:

```lean
CorrectedConcreteCertifiedDescriptionProfileAtBudgets
CorrectedConcreteCertifiedRankProfileClass
startRootedTarget_certifiedProfileAtCharacteristicRank
correctedConcreteCertifiedWorkingGrammarLearner_identification_descriptionProfile_package
```


### 2.226 `ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionRank.lean`

Status: CI passed.

Purpose:

Defines the first occupied simultaneous profile level by Nat.find, proves the exact threshold theorem, and shows it is bounded by characteristic rank.

Main contents:

```lean
correctedConcreteCertifiedDescriptionRank
startRootedTargetCertifiedDescriptionRank
startRootedTarget_mem_rankProfile_iff_descriptionRank_le
correctedConcreteCertifiedWorkingGrammarLearner_identification_descriptionRank_package
```


### 2.227 `ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionRankObstructions.lean`

Status: CI passed.

Purpose:

Turns profile nonmembership and bit/search lower bounds into strict characteristic-rank lower bounds and partitions the target class into disjoint exact-rank shells.

Main contents:

```lean
startRootedTarget_not_mem_rankProfile_iff_lt_descriptionRank
startRootedTarget_characteristicRank_gt_of_not_mem_certifiedRankProfile
startRootedTarget_descriptionRank_eq_characteristicRank_iff_no_lower_profile
correctedConcreteCertifiedWorkingGrammarLearner_identification_descriptionRankObstruction_package
```


### 2.228 `ConcreteCanonicalLearnerWorkingGrammarObservationRefinementFailure.lean`

Status: CI passed.

Purpose:

Transports semantic target witnesses along observation refinement, proves target-class growth and failure-class shrinkage, and defines strict gain and empty loss classes.

Main contents:

```lean
StartRootedCorrectedConcreteTargetWitness.refineObservation
startRootedCorrectedConcreteTargetClass_subset_of_refines
StartRootedCorrectedConcreteObservationGainClass
correctedConcreteCertifiedWorkingGrammar_observationRefinementFailure_package
```


### 2.229 `ConcreteCanonicalLearnerWorkingGrammarObservationEquivalenceChain.lean`

Status: CI passed.

Purpose:

Adds refinement identity/composition, mutual-refinement equivalence, disjoint gain decomposition along chains, and finest-observation certified learning.

Main contents:

```lean
Refines.identity
Refines.compose
ObservationEquivalent
observationGainClass_compose_eq_union
correctedConcreteCertifiedWorkingGrammar_observationRefinementChain_package
```


### 2.230 `ConcreteCanonicalLearnerWorkingGrammarObservationAblation.lean`

Status: CI passed.

Purpose:

Proves the exact interface-ablation criterion: redundancy is equivalent to empty gain and unchanged target/failure classes; essentiality yields a new certified-learnable fine-observation target.

Main contents:

```lean
CorrectedConcreteObservationRefinementRedundant
CorrectedConcreteObservationRefinementEssential
observationRefinement_ablationCriterion_package
essentialObservationRefinement_exists_newCertifiedTarget
correctedConcreteCertifiedWorkingGrammar_observationAblation_package
```



### 2.231 `ConcreteCanonicalLearnerWorkingGrammarObservationProduct.lean`

Status: CI passed.

Purpose:

Constructs paired finite observations, factor refinements, target/failure
comparisons, semantic synergy, and certified learning for paired-observation
targets.

Main contents:

```lean
pairedObservation
leftTargetClass_subset_pairedTargetClass
rightTargetClass_subset_pairedTargetClass
pairedTargetClass_eq_factorUnion_union_synergy
pairedObservation_semanticDecomposition_package
correctedConcreteCertifiedWorkingGrammar_observationProduct_package
```


### 2.232 `ConcreteCanonicalLearnerWorkingGrammarObservationSelection.lean`

Status: CI passed.

Purpose:

Generalizes paired observations to arbitrary finite selected products and
defines the minimum number of coordinates needed to represent a full-product
target.

Main contents:

```lean
selectedObservationProduct
selectedObservationProductTargetClass_mono
CorrectedConcreteObservationSelectionAtCardinality
correctedConcreteObservationSelectionCardinality
ambientTarget_exists_minimumObservationSelection
correctedConcreteCertifiedWorkingGrammar_observationSelection_package
```


### 2.233 `ConcreteCanonicalLearnerWorkingGrammarObservationSelectionIrredundancy.lean`

Status: CI passed.

Purpose:

Proves that minimum-cardinality observation selections are inclusion-
irredundant and that every retained coordinate is essential.

Main contents:

```lean
CorrectedConcreteObservationSelectionIrredundant
CorrectedConcreteSelectedObservationCoordinateEssential
observationSelection_irredundant_coordinate_package
ambientTarget_exists_minimumIrredundantObservationSelection
correctedConcreteCertifiedWorkingGrammar_observationSelectionIrredundancy_package
```


### 2.234 `ConcreteCanonicalLearnerWorkingGrammarObservationWeightedSelection.lean`

Status: CI passed.

Purpose:

Introduces arbitrary natural-valued selection costs, attained minimum cost,
strictly monotone cost irredundancy, and exact bounded-cost obstruction
theorems.

Main contents:

```lean
CorrectedConcreteObservationSelectionAtCost
HasCorrectedConcreteObservationSelectionCost
correctedConcreteObservationSelectionMinimumCost
observationSelection_not_atCost_iff_lt_minimumCost
ambientTarget_exists_minimumCostCertifiedObservationSelection
correctedConcreteCertifiedWorkingGrammar_observationWeightedSelection_package
```


### 2.235 `ConcreteCanonicalLearnerWorkingGrammarObservationParetoSelection.lean`

Status: CI passed.

Purpose:

Introduces cardinality/cost Pareto profiles, dominance, finite Pareto fronts,
existence, irredundancy, coordinate essentiality, and certified Pareto-selected
learners.

Main contents:

```lean
CorrectedConcreteObservationSelectionParetoOptimal
CorrectedConcreteObservationSelectionParetoFrontier
CorrectedConcreteObservationSelectionParetoProfileSet
observationSelection_exists_paretoOptimal
observationSelection_paretoOptimal_irredundant
ambientTarget_exists_paretoCertifiedObservationSelection
correctedConcreteCertifiedWorkingGrammar_observationParetoSelection_package
```


### 2.236 `ConcreteCanonicalLearnerWorkingGrammarObservationAdditiveWeights.lean`

Status: CI passed.

Purpose:

Specializes weighted selection to additive and positive-additive coordinate
costs and proves the monotonicity/strict-monotonicity needed for irredundancy.

Main contents:

```lean
correctedConcreteObservationSelectionAdditiveCost
correctedConcreteObservationSelectionPositiveAdditiveCost
observationSelectionAtZeroPositiveAdditiveCost_iff
correctedConcreteCertifiedWorkingGrammar_observationAdditiveWeights_package
```


### 2.237 `ConcreteCanonicalLearnerWorkingGrammarObservationFiniteOptimization.lean`

Status: CI passed.

Purpose:

Turns semantic feasibility, minimum cost, Pareto fronts, and Pareto profiles
into explicit finite candidate sets bounded by `2 ^ U.card`.

Main contents:

```lean
correctedConcreteObservationFeasibleSelections
correctedConcreteObservationMinimumCostSelections
correctedConcreteObservationParetoSelections
correctedConcreteObservationParetoProfiles
correctedConcreteObservationMinimumCostSelections_nonempty
correctedConcreteObservationParetoSelections_card_le_two_pow
correctedConcreteCertifiedWorkingGrammar_observationFiniteOptimization_package
```


### 2.238 `ConcreteCanonicalLearnerWorkingGrammarObservationOptimizationSelector.lean`

Status: CI passed.

Purpose:

Selects actual minimum-cost and Pareto candidates from the finite nonempty
search sets and attaches their certified selected-product learners.

Main contents:

```lean
CorrectedConcreteObservationMinimumCostSelectionResult
correctedConcreteObservationMinimumCostSelectionResult
CorrectedConcreteObservationParetoSelectionResult
correctedConcreteObservationParetoSelectionResult
correctedConcreteObservationMinimumCostSelectionResult_certified_package
correctedConcreteObservationParetoSelectionResult_certified_package
correctedConcreteCertifiedWorkingGrammar_observationOptimizationSelector_package
```


### 2.239 `ConcreteCanonicalLearnerWorkingGrammarObservationBudgetFiltration.lean`

Status: CI passed.

Purpose:

Organizes cost-bounded feasible selections into a monotone finite filtration
and identifies the semantic minimum as its first nonempty layer.

Main contents:

```lean
correctedConcreteObservationCostBudgetFiltration
correctedConcreteObservationCostBudgetFiltration_mono
correctedConcreteObservationCostBudgetFiltration_firstNonempty_package
correctedConcreteObservationCostBudgetCandidate_certified_package
correctedConcreteCertifiedWorkingGrammar_observationBudgetFiltration_package
```


### 2.240 `ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRank.lean`

Status: CI passed.

Purpose:

Lifts the budget filtration to cumulative language classes and disjoint exact
selection-rank shells with unique decomposition and certified minimum-rank
selection.

Main contents:

```lean
CorrectedConcreteObservationSelectionCostProfileClass
CorrectedConcreteObservationSelectionExactCostRankClass
observationSelection_mem_costProfileClass_iff_minimum_le
observationSelectionExactCostRankClasses_disjoint
fullProductTarget_existsUnique_exactObservationSelectionCostRank
ambientTarget_observationSelectionCostRank_certified_package
correctedConcreteCertifiedWorkingGrammar_observationSelectionRank_package
```


### 2.241 `ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankComparison.lean`

Status: CI passed.

Purpose:

Compares profiles, filtrations, exact shells, and target ranks under pointwise
cost order and coordinate-weight order.

Main contents:

```lean
CorrectedConcreteObservationSelectionCostPointwiseLe
observationSelectionCostProfileClass_subset_of_pointwiseLe
observationSelectionMinimumCost_le_of_pointwiseLe
ambientTargetObservationSelectionCostRank_le_of_pointwiseLe
ambientTarget_cardinalityCostRank_le_positiveAdditiveCostRank
ambientTarget_twoCostRank_certifiedComparison_package
correctedConcreteCertifiedWorkingGrammar_observationSelectionRankComparison_package
```


### 2.242 `ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankSensitivity.lean`

Status: CI passed.

Purpose:

Proves additive perturbation bounds for selection profiles, filtrations, exact
shells, and ranks, including the coordinate-weight bound `delta * U.card`.

Main contents:

```lean
CorrectedConcreteObservationSelectionCostLeUpToWithin
observationSelectionMinimumCost_le_add_of_leUpToWithin
ambientTargetObservationSelectionCostRank_le_add_of_leUpToWithin
ambientTarget_positiveAdditiveCostRank_le_add_weightPerturbation
ambientTarget_costRankSensitivity_certified_package
correctedConcreteCertifiedWorkingGrammar_observationSelectionRankSensitivity_package
```


### 2.243 `ConcreteCanonicalLearnerWorkingGrammarObservationSelectionCostOverhead.lean`

Status: CI passed.

Purpose:

Analyzes fixed setup overhead: cumulative profiles and filtrations translate,
ranks shift exactly, while minimum subsets and Pareto fronts remain unchanged.

Main contents:

```lean
correctedConcreteObservationSelectionCostWithOverhead
observationSelectionMinimumCost_withOverhead_eq
observationSelection_mem_exactRankWithOverhead_iff
ambientTargetObservationSelectionCostRank_withOverhead_eq
correctedConcreteObservationParetoSelections_withOverhead_eq
ambientTarget_sameMinimumSelection_underCostOverhead_certified_package
correctedConcreteCertifiedWorkingGrammar_observationSelectionCostOverhead_package
```


### 2.244 `ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankZero.lean`

Status: CI passed.

Purpose:

Identifies rank zero with zero-cost representability and, for cardinality and
positive-additive costs, with representability by the empty selected product.

Main contents:

```lean
CorrectedConcreteObservationSelectionZeroCostClass
observationSelectionExactCostRankZeroClass_eq_zeroCostClass
ambientTarget_positiveAdditiveCostRank_eq_zero_iff_emptyProductTarget
ambientTarget_cardinalityCostRank_eq_zero_iff_emptyProductTarget
ambientTarget_positiveAdditiveRankZero_emptyProductCertified_package
correctedConcreteCertifiedWorkingGrammar_observationSelectionRankZero_package
```


### 2.245 `ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankOne.lean`

Status: CI passed.

Purpose:

Identifies cardinality rank one with one-coordinate representability but not
empty-interface representability; positive-additive rank one additionally
requires zero extra weight.

Main contents:

```lean
CorrectedConcreteCardinalityObservationSelectionRankOneClass
CorrectedConcretePositiveAdditiveObservationSelectionRankOneClass
observationSelectionPositiveAdditiveCost_eq_one_iff
ambientTarget_cardinalityCostRank_eq_one_iff_rankOneClass
ambientTarget_positiveAdditiveCostRank_eq_one_iff_rankOneClass
correctedConcreteCertifiedWorkingGrammar_observationSelectionRankOne_package
```


### 2.246 `ConcreteCanonicalLearnerWorkingGrammarObservationSelectionCardinalityRank.lean`

Status: CI passed.

Purpose:

Gives the arbitrary-cardinality-rank witness theorem, bounded exact-shell
decomposition, direct lower-bound obstruction, and irredundant certified
minimum-cardinality selection.

Main contents:

```lean
CorrectedConcreteObservationSelectionExactCardinalityRankWitnessClass
cardinalityObservationSelectionExactRankClass_eq_witnessClass
ambientTarget_cardinalityCostRank_eq_selectionCardinality
fullProductTargetClass_eq_exists_boundedExactCardinalityRank
ambientTarget_cardinalityRank_gt_iff_all_boundedSelections_fail
ambientTarget_exists_cardinalityRankCertifiedSelection
correctedConcreteCertifiedWorkingGrammar_observationSelectionCardinalityRank_package
```


### 2.247 `ConcreteCanonicalLearnerWorkingGrammarObservationSelectionPositiveAdditiveRank.lean`

Status: CI passed.

Purpose:

Gives the arbitrary positive-additive-rank witness theorem, bounded shell
decomposition, cost obstruction, and irredundant certified exact-rank
selection.

Main contents:

```lean
CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
positiveAdditiveObservationSelectionExactRankClass_eq_witnessClass
fullProductTargetClass_eq_exists_boundedExactPositiveAdditiveRank
ambientTarget_positiveAdditiveRank_gt_iff_all_boundedSelections_fail
ambientTarget_exists_positiveAdditiveRankCertifiedSelection
correctedConcreteCertifiedWorkingGrammar_observationSelectionPositiveAdditiveRank_package
```


### 2.248 `ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankEnvelope.lean`

Status: CI passed.

Purpose:

Identifies positive-additive rank with the minimum scalar value on the finite
additive Pareto frontier and derives Pareto-only rank obstructions.

Main contents:

```lean
correctedConcreteObservationPositiveAdditiveParetoRankValues
CorrectedConcreteObservationSelectionPositiveAdditiveParetoEnvelopeRankClass
positiveAdditiveExactCostRankClass_eq_paretoEnvelopeRankClass
ambientTarget_positiveAdditiveRank_isMinimum_paretoRankValue
ambientTarget_positiveAdditiveRank_gt_iff_lt_all_paretoRankValues
ambientTarget_exists_positiveAdditiveRankParetoCertifiedSelection
correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankEnvelope_package
```


### 2.249 `ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankSelector.lean`

Status: CI passed.

Purpose:

Filters the finite Pareto frontier to exact rank-minimizing candidates, selects
one actual subset, proves global optimality/irredundancy/essentiality, and
attaches its certified learner.

Main contents:

```lean
correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections
CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult
correctedConcreteObservationPositiveAdditiveParetoRankSelectionResult
CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult.semantic_package
CorrectedConcreteObservationPositiveAdditiveParetoRankSelectionResult.certified_package
correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankSelector_package
```


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
  ↓
OutputTypePresentationWorkingGrammarEquivalence
  ↓
ConcreteOutputTypeRefinementPresentation
  ↓
StartSeparatedOutputTypeRefinementCompleteness
  ↓
ConcreteTrimmedSuccessfulPresentation
  ↓
ConcreteReducedRepresentativeSelection
  ↓
ConcreteObservationDeterministicClosure
  ↓
ConcreteTypedCharacteristicSample
  ↓
TupleOccurrences
  ↓
BinaryWitnesses
  ↓
ConcreteCanonicalLearner
  ↓
TupleOccurrenceEnumerationCompleteness
  ↓
NamedFillEnumerationBounds
  ↓
BinaryWitnessEnumerationCompleteness
  ↓
ExactConcreteCanonicalLearnerEquivalence
  ↓
ConcreteCanonicalLearnerIdentification
  ↓
ConcreteCanonicalLearnerClassTheorem
  ↓
ConcreteCanonicalLearnerStabilization
  ↓
StartRootedConcreteCanonicalLearnerIdentification
  ↓
StartRootedConcreteCanonicalLearnerClassTheorem
  ↓
ConcreteCanonicalLearnerFiniteEnumerationBounds
  ↓
ConcreteCanonicalLearnerLengthOnlyBounds
  ↓
ConcreteCanonicalLearnerSinglePowerBounds
  ↓
ConcreteCanonicalLearnerPolynomialExponentBounds
  ↓
ConcreteCanonicalLearnerFiniteHypothesis
  ↓
ConcreteCanonicalLearnerFiniteHypothesisSize
  ↓
ConcreteCanonicalLearnerFiniteObjectIdentification
  ↓
ConcreteCanonicalLearnerFiniteObjectMonotone
  ├──→ ConcreteCanonicalLearnerFiniteObjectDirectedSystem
  └──→ ConcreteCanonicalLearnerWorkingGrammarObstruction
          ↓
       ConcreteCanonicalLearnerWorkingGrammarCutSaturation
          ↓
       ConcreteCanonicalLearnerWorkingGrammarConstruction
          ↓
       ConcreteCanonicalLearnerWorkingGrammarEquivalence
          ↓
       ConcreteCanonicalLearnerWorkingGrammarIdentification
          ↓
       ConcreteCanonicalLearnerWorkingGrammarSize
          ↓
       ConcreteCanonicalLearnerWorkingGrammarPresentationSize
          ↓
       ConcreteCanonicalLearnerWorkingGrammarStructuralConditions
          ↓
       ConcreteCanonicalLearnerWorkingGrammarRepresentation
          ↓
       ConcreteCanonicalLearnerWorkingGrammarBoundedRepresentation
          ↓
       ConcreteCanonicalLearnerWorkingGrammarRepresentationRank
          ↓
       ConcreteCanonicalLearnerWorkingGrammarCharacteristicRank
          ↓
       ConcreteCanonicalLearnerWorkingGrammarMindChanges
          ↓
       ConcreteCanonicalLearnerWorkingGrammarDescriptionSize
          ↓
       ConcreteCanonicalLearnerWorkingGrammarNaturalEncoding
          ↓
       ConcreteCanonicalLearnerWorkingGrammarBinaryEncoding
          ↓
       ConcreteCanonicalLearnerWorkingGrammarAutomaticBitWidth
          ↓
       ConcreteCanonicalLearnerWorkingGrammarDenseEncoding
          ↓
       ConcreteCanonicalLearnerWorkingGrammarTaggedDenseEncoding
          ↓
       ConcreteCanonicalLearnerWorkingGrammarTaggedDenseDecoding
          ↓
       ConcreteCanonicalLearnerWorkingGrammarTemplateSerialization
          ↓
       ConcreteCanonicalLearnerWorkingGrammarTemplateTupleFraming
          ↓
       ConcreteCanonicalLearnerWorkingGrammarBinaryRuleSerialization
          ↓
       ConcreteCanonicalLearnerWorkingGrammarTerminalAlphabetEncoding
          ↓
       ConcreteCanonicalLearnerWorkingGrammarBinaryRuleNaturalSerialization
          ↓
       ConcreteCanonicalLearnerWorkingGrammarBinaryRuleTerminalClosure
          ↓
       ConcreteCanonicalLearnerWorkingGrammarPresentationNaturalSerialization
          ↓
       ConcreteCanonicalLearnerWorkingGrammarUnaryBitSerialization
          ↓
       ConcreteCanonicalLearnerWorkingGrammarLogarithmicBitSerialization
          ↓
       ConcreteCanonicalLearnerWorkingGrammarLogarithmicBitBounds
          ↓
       ConcreteCanonicalLearnerWorkingGrammarAutomaticNaturalFieldBitWidth
          ↓
       ConcreteCanonicalLearnerWorkingGrammarNaturalFieldMaximum
          ↓
       ConcreteCanonicalLearnerWorkingGrammarNaturalFieldClassification
          ↓
       ConcreteCanonicalLearnerWorkingGrammarNaturalFieldEntryBounds
          ↓
       ConcreteCanonicalLearnerWorkingGrammarBinaryRuleNaturalFieldClassification
          ↓
       ConcreteCanonicalLearnerWorkingGrammarBinaryRuleTokenPayloadBounds
          ↓
       ConcreteCanonicalLearnerWorkingGrammarNaturalFieldFullyExplicitBound
          ↓
       ConcreteCanonicalLearnerWorkingGrammarUniformNaturalFieldBound
          ↓
       ConcreteCanonicalLearnerWorkingGrammarBinaryRuleFamilyBodyBounds
          ↓
       ConcreteCanonicalLearnerWorkingGrammarSampleParametricBitBound
          ↓
       ConcreteCanonicalLearnerWorkingGrammarPaperBitEnvelope
          ↓
       ConcreteCanonicalLearnerWorkingGrammarPaperPowerBitBound
          ↓
       ConcreteCanonicalLearnerWorkingGrammarFinalDescriptionPackage
          ↓
       ConcreteCanonicalLearnerWorkingGrammarCheckedBitRepresentation
          ↓
       ConcreteCanonicalLearnerWorkingGrammarFiniteCodeUniverse
          ↓
       ConcreteCanonicalLearnerWorkingGrammarFiniteDecodedSearch
          ↓
       ConcreteCanonicalLearnerWorkingGrammarCanonicalDecodedSearch
          ↓
       ConcreteCanonicalLearnerWorkingGrammarCanonicalSearchSelector
          ↓
       ConcreteCanonicalLearnerWorkingGrammarCertifiedOutputLearner
          ↓
       ConcreteCanonicalLearnerWorkingGrammarCertifiedOutputMindChanges
          ↓
       ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionComplexity
          ↓
       ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionProfile
          ↓
       ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionRank
          ↓
       ConcreteCanonicalLearnerWorkingGrammarCertifiedDescriptionRankObstructions
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationRefinementFailure
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationEquivalenceChain
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationAblation
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationProduct
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationSelection
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationSelectionIrredundancy
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationWeightedSelection
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationParetoSelection
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationAdditiveWeights
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationFiniteOptimization
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationOptimizationSelector
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationBudgetFiltration
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRank
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankComparison
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankSensitivity
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationSelectionCostOverhead
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankZero
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationSelectionRankOne
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationSelectionCardinalityRank
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationSelectionPositiveAdditiveRank
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankEnvelope
          ↓
       ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankSelector
```

The main import chain remains deliberately linear.  The directed-system file is
a verified side branch from finite-object monotonicity.  The actual-grammar route
now proceeds through obstruction, cut saturation, construction, equivalence,
identification, quantitative item-count analysis, structural-boundary analysis,
representation hierarchies, minimum ranks, semantic mind-change stabilization,
the complete checked natural/bit serialization chain, closed sample-parametric
and paper-power bounds, finite checked code search and canonical selection,
certificate-carrying outputs, minimum certified description ranks and
obstructions, observation refinement/equivalence/ablation, and finally finite
observation products, semantic optimization, exact selection-rank hierarchies,
cost sensitivity, Pareto envelopes, and an actual certified Pareto-rank
selector.

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



### 4.43 Exact concrete presentation-grammar equivalence

Arbitrary derivations of `P.toWorkingMCFG` are inverted back to typed
presentation derivations.  Therefore:

```lean
P.toWorkingMCFG.StringLanguage = PresentationStringLanguage P.
```

For a complete presentation, this language is exactly the original grammar
language.

### 4.44 Full finite output-type presentation construction

For finite nonterminals and finite observation monoid, the full typed node and
rule sets are explicitly finite and complete.  The formerly external
`CompleteOutputTypePresentation` has been eliminated from the concrete route.

### 4.45 Successful typed trim and automatic occurrences

The successful typed core is built by finite filtering.  Membership supplies an
actual successful occurrence, and the filtered presentation preserves the
string language under start-rooted normality.

### 4.46 Typed-indexed characteristic sample

Anchors are indexed by present successful typed nonterminals rather than by one
representative per base.  This avoids the false general assumption that one
base nonterminal has only one observation type.

### 4.47 Finite sample-rule enumeration

Finite words, tuple codes, well-formed named contexts, tuple occurrences, unit
rules, exact-once templates, and binary witnesses are explicitly enumerated
from the sample.

### 4.48 Enumeration completeness

Every sample unit witness is represented in the finite unit-rule set.  Every
exact-once sample binary witness is represented in the corrected finite binary
set using the bound

```lean
sampleLengthBudget K + dB + dC.
```

### 4.49 Corrected concrete learner equivalence

The corrected finite learner is equivalent, at tuple and string levels, to the
exact-once reachable semantics:

```lean
CorrectedConcreteCanonicalLearnerLanguage K obs f
  = ExactReachableSampleStringLanguage K obs f.
```

### 4.50 Concrete learner exact reconstruction

The fully concrete typed characteristic sample reconstructs the target exactly
under the corrected finite learner.  Exactness is monotone over every positive
finite superset.

### 4.51 Concrete learner Gold identification

Every positive text eventually contains the finite characteristic sample;
thereafter every prefix hypothesis language is exactly the target.

### 4.52 Uniform language-class theorem

One learner, depending only on `obs`, `f`, and the finite input sample,
identifies every language represented by the target class.  The hidden grammar
and its nonterminal type are not learner inputs.

### 4.53 Selected characteristic samples and stages

Classical choice is used only after existence is proved to select one finite
characteristic sample per target and one coverage/stabilization stage per text.
After the selected stage, hypothesis languages are target-equal and pairwise
equal.

### 4.54 Semantic start-rooted weakening

The final route needs only

```lean
G.StringLanguage ⊆ StartRootedStringLanguage G
```

rather than the stronger syntactic `StartSeparated`.  The latter is proved to
be a sufficient condition.

### 4.55 Larger start-rooted target class

The old start-separated class embeds into the larger semantic start-rooted
class, and the same corrected concrete learner identifies this larger class.


### 4.56 Quantitative bounds for the actual brute-force enumerators

The cardinalities of the concrete word, context, tuple-occurrence, unit-rule,
exact-template, and binary-witness finite sets are now Lean-bounded.

### 4.57 Length-only and common-power bounds

The sample-alphabet parameter is eliminated in favor of `sampleLengthBudget`,
and all rule families are absorbed into one common base/exponent expression.

### 4.58 Paper-facing explicit source-rule bound

For the actual canonical finite hypothesis:

```lean
(correctedConcreteFiniteHypothesis K obs f).ruleCount ≤
  (4 * (sampleLengthBudget K + f + 1)) ^
    (64 *
      (sampleLengthBudget K + f + 1) *
      (sampleLengthBudget K + f + 1)).
```

This is a verified finite-size bound, not yet a polynomial-time claim.

### 4.59 Actual dependent finite hypothesis object

The learner output is no longer merely a sample or language facade.  It stores
finite dependent unit and binary rule codes, and listed derivations explicitly
use membership in those stored lists.

### 4.60 Finite-object language equivalence

```lean
finite-object listed language
=
corrected concrete canonical learner language
=
exact-once reachable sample language.
```

### 4.61 Structural sample-extension simulation

Unit and binary rule evidence is transported to larger samples, corresponding
new finite codes are selected, and complete listed derivation trees are
transported rule by rule.

### 4.62 Coherent prefix directed system

Finite hypothesis simulations have identity and composition.  Along a positive
text, prefix hypotheses and their semantic maps form a directed system that is
eventually language constant at the target.

### 4.63 Empty-alphabet obstruction

Every `DerivesTuple` proof in the present lightweight `WorkingMCFG` syntax has a
terminal-rule leaf.  Hence every nonempty generated language implies
`Nonempty α`.  The finite learner on the empty alphabet and sample `{ε}` is a
formal counterexample to unconditional compilation.

### 4.64 Exact compilation domain

A finite learner object is realizable by the present `WorkingMCFG` syntax iff:

```lean
K = ∅ ∨ Nonempty α.
```

The empty-sample case uses a rule-free empty grammar; the nonempty-alphabet case
uses the cut-saturated compiler.

### 4.65 Finite control and cut saturation

Sample singletons and all rule source/target tuples form a finite control set.
Every listed derivation from a control state has a cut-normal form, and all
control-to-control reachable cuts are contained in one finite saturation.

### 4.66 Actual finite WorkingMCFG construction

The compiler creates:

```text
fresh start node
one seed terminal node
one nonterminal for each finite control tuple
constant rules for controls
lifted corrected binary rules
left-identity rules for saturated cuts
start rules for sample words.
```

### 4.67 Reverse derivation translation and exact grammar equivalence

Every compiled grammar derivation is inverted into a seed/control/start view,
and control derivations are converted back to cut-normal listed derivations.
Therefore:

```lean
(H.toCutWorkingMCFG dummy).StringLanguage = H.Language.
```

### 4.68 Actual WorkingMCFG-valued learner

For `Nonempty α`, one target-independent set-driven learner outputs actual
finite `WorkingMCFG` objects and agrees samplewise with the corrected concrete
learner and exact reachable semantics.

### 4.69 WorkingMCFG-valued class identification

Under the established finite/exact/start-rooted/substitutability assumptions,
the actual grammar-valued learner is consistent, language-monotone, has finite
characteristic samples, identifies the whole start-rooted target class, and is
exact after the selected coverage stage.


### 4.70 Actual compiled grammar rule count

The compiler rule lists have exact length formulas, and:

```lean
compiledGrammarRuleCount ≤
  (K.card + 3 * sourceRuleCount + 2) ^ 2.
```

The source finite-rule power bound is substituted into a fully explicit
sample-length-only actual-grammar bound.

### 4.71 Explicit nonterminal enumeration and presentation item count

Every compiled nonterminal is listed explicitly:

```text
fresh start
dummy seed
one control node per finite control code.
```

The list length is `controlCodes.card + 2`, and the complete top-level count
satisfies:

```lean
presentationItemCount ≤
  (K.card + 3 * sourceRuleCount + 3) ^ 2.
```

### 4.72 Exact structural boundary of output hypotheses

Every compiled output satisfies:

```text
start arity one
well-typed start rules
well-typed terminal rules
fan-out at most max 1 f.
```

For nonempty samples, constant control rules ignore both dummy children.
Therefore output hypotheses provably fail `BinaryRulesNondeleting`,
`BasicWorkingConditions`, and `ExactWorkingConditions`.

### 4.73 Exact finite representation theorem

The class `CutCompiledWorkingGrammarLanguageClass` records the structural
conditions the compiler really preserves.  Every language in the semantic
start-rooted target class has an exact representation in this class, obtained
from one finite positive characteristic sample.

### 4.74 Bounded representation hierarchy

Exact representations are stratified by sample-length budgets using
`BoundedCutCompiledWorkingGrammarLanguageClass`.  The hierarchy is monotone,
every learner output lies at its own sample-length level, and every start-rooted
target belongs to some finite level.

### 4.75 Minimum representation and exact-output ranks

The least bounded-representation budget and least exact learner-output budget
are defined by `Nat.find`, are attained, and satisfy:

```text
representation rank ≤ exact-output rank.
```

### 4.76 Minimum characteristic-sample rank

The least total word length of a characteristic sample is defined and attained.
For every start-rooted target:

```text
representation rank
≤ exact-output rank
≤ characteristic rank
≤ selected characteristic-sample total length.
```

### 4.77 Semantic mind changes and stabilization

The prefix-language hypothesis is monotone.  Every semantic language change
forces a strict increase in prefix-sample cardinality, so:

```lean
mindChangeCount T N ≤ (T.prefixSample N).card.
```

A minimum-budget characteristic sample is selected.  After its coverage stage,
all output languages equal the target, no later language change occurs, and the
cumulative mind-change count is constant.


### 4.78 Abstract and dense encoded description size

The top-level presentation count is now connected to abstract entry costs,
natural codes, unary sizes, binary payload lengths, dense list positions, and
one globally tagged dense presentation code.  Stored top-level entries have
collision-free codes and checked decoders.

### 4.79 Dependent template and binary-rule serialization

Dependent template atoms, words, and output tuples are converted to
nondependent structural tokens.  Output-component boundaries are
length-prefixed.  Complete binary rules are reconstructed with checked
nonterminal references, child arities, variable indices, and terminal codes.

### 4.80 Finite terminal closure of actual compiled rules

The augmented terminal alphabet is exactly

```lean
insert dummy (sampleAlphabet K).
```

Every actual constant, lifted, and saturated compiled binary rule is proved to
use only this finite alphabet.  Therefore the complete stored binary-rule
natural codec has an unconditional round trip.

### 4.81 Complete natural grammar codec

Every nonterminal declaration and every start, terminal, and binary rule is
serialized as a tagged natural payload.  The complete presentation is one
length-framed `List Nat` with a checked whole-presentation decoder and exact
natural-field count.

### 4.82 Prefix-free bit codecs

Two complete `List Bool` codecs are verified:

```text
unary natural-field code
logarithmic-structure binary-tree natural-field code.
```

Both decode the complete grammar back to the exact tagged presentation list.

### 4.83 Automatic least fitting field width

The complete natural stream automatically selects its least positive common
binary width.  No externally supplied `CodesFitInBits` or
`NaturalFieldsFitInBits` premise remains.

### 4.84 One-value reduction of grammar bit size

Let `naturalFieldValueBound` be the maximum of:

```text
the complete natural-field count
the largest natural field value in the complete grammar serialization.
```

Then the checked grammar bit stream satisfies:

```text
grammarBitCount
≤
(naturalFieldCount + 1) *
  (2 * binaryNatCodeLength naturalFieldValueBound + 1).
```

All remaining encoded-size work is therefore reduced to bounding two ordinary
natural quantities by sample and grammar parameters.



### 4.31 Closed checked description size

```text
Every natural field in the complete checked serialization is classified.
Every stored binary token payload is bounded.
naturalFieldCount and naturalFieldValueBound are bounded by sample length and fan-out.
The complete checked logarithmic bit stream has a closed sample-parametric bound.
It also has the single-power paper bound
  (4 * (sampleLengthBudget K + f + 1)) ^
    ((64 * (sampleLengthBudget K + f + 1)^2) * 13).
```

### 4.32 Finite exhaustive code search and canonical selection

```text
All Boolean lists within the paper-power budget are finitely enumerated.
Successful checked decodings are finitely enumerated.
Canonical decode/re-encode fixed points are finitely enumerated.
The actual learner code/presentation pair belongs to the canonical search.
Lookup by the emitted learner code returns exactly the actual presentation.
```

### 4.33 Certified learner outputs

```text
Each output itself stores:
  actual WorkingMCFG,
  complete presentation,
  checked bit code,
  decoder and re-encoder,
  finite canonical search,
  exact selector,
  all round-trip, membership, and size proofs.

The certified learner remains consistent, language-monotone, and identifies the
same semantic start-rooted target class.
```

### 4.34 Minimum certified complexity and rank

```text
Minimum checked-bit complexity is defined and attained.
Minimum finite-search complexity is defined and attained.
One-certificate joint bit/search profiles form an increasing hierarchy.
The first occupied profile rank is defined and attained.
Certified description rank ≤ characteristic rank.
Profile nonmembership and bit/search lower bounds imply characteristic-rank lower bounds.
The target class is partitioned into disjoint exact certified-description-rank shells.
```

### 4.35 Observation refinement and ablation

```text
Observation refinement transports semantic target witnesses.
Target classes grow and observation-failure classes shrink.
Strict gain classes record exactly the newly representable languages.
Mutual refinement gives equal target and failure classes.
Incremental gains compose disjointly along a refinement chain.
A refinement is redundant iff its gain class is empty iff target/failure classes are unchanged.
An essential refinement yields a genuinely new fine-observation target with an
exact minimum-rank certified description.
```


### 4.36 Finite observation products and selected interfaces

```text
paired observations refine each factor
arbitrary finite selected products refine every selected factor
target classes grow under selected-product extension
failure classes shrink
paired and multi-factor synergy classes isolate genuinely joint information.
```

### 4.37 Minimum selection, irredundancy, and Pareto structure

```text
minimum-cardinality selections exist and are attained
strictly monotone weighted minima are irredundant
every retained coordinate of a minimum/Pareto selection is essential
cardinality/cost Pareto fronts and Pareto profiles are nonempty
selected products carry their own certified learners.
```

### 4.38 Explicit finite semantic optimization

```text
all feasible selections form a finite subset of U.powerset
minimum-cost selections form a nonempty finite set
Pareto selections and Pareto profiles form finite sets
all candidate families have cardinality at most 2^|U|
actual minimum-cost and Pareto selectors are constructed by finite choice.
```

### 4.39 Budget filtrations and exact selection-rank shells

```text
cost-bounded candidate layers are monotone
the minimum cost is exactly the first nonempty layer
cumulative language profiles have exact threshold theorems
exact rank shells are pairwise disjoint
every full-product target has one unique exact selection rank.
```

### 4.40 Cost comparison, perturbation, and normalization

```text
pointwise cheaper costs give larger profiles and no larger ranks
coordinatewise larger weights cannot decrease positive-additive rank
bounded cost perturbations shift ranks by a proved additive bound
coordinate weight error d gives rank error at most d * |U|
fixed overhead shifts every rank exactly and preserves minimum subsets/Pareto fronts.
```

### 4.41 Rank-zero, rank-one, and arbitrary-rank structure

```text
rank zero = representability by a zero-cost selection
cardinality/positive-additive rank zero = empty-product representability
cardinality rank one = one-coordinate but not zero-coordinate representability
positive-additive rank one additionally has zero extra weight
arbitrary cardinality and positive-additive ranks have direct minimum witnesses
full target classes decompose into bounded unique exact-rank shells.
```

### 4.42 Pareto rank envelope and selector

```text
positive-additive rank is the minimum scalar total on the additive Pareto frontier
the finite Pareto scalar set has at most 2^|U| values
rank lower bounds can be checked only against Pareto scalar values
the finite frontier can be filtered to exact rank minimizers
one actual rank-minimizing Pareto subset is selected
that subset is irredundant, coordinate-essential, globally optimal, and certified-learnable.
```


## 5. What remains as explicit assumptions or unfinished work?

CI #738 completes the qualitative positive-learning theorem, actual finite
grammar compilation, exact semantic reconstruction, closed checked
sample-parametric description-size analysis, finite exhaustive checked-code
search, certified output learner, minimum certified description-rank framework,
the abstract observation refinement/equivalence/ablation theory, and the full
semantic finite observation-selection optimization/rank/Pareto-selector layer.

The remaining limitations are now much more concentrated.

### 5.1 Executable coding versus `noncomputable` finite definitions

The current learner, finite code search, minimum-rank witnesses, and dense-code
choices are mathematically finite but still use classical choice,
function-valued `Finset`s, and noncomputable filters/images.  The codecs and
finite search theorems are checked, but an extracted executable implementation
equivalent to the present learner is still absent.

### 5.2 Polynomial-time construction

The present canonical learner still enumerates all bounded words over the
sample alphabet.  The verified single-power rule and bit bounds honestly
measure that brute-force construction; they are not polynomial-time bounds.

A polynomial implementation should enumerate only actual sample-derived
objects:

```text
substrings and factors of observed words
bounded component splits
well-formed hole placements
tuple occurrences
parent/child context reconstructions
exact-once templates supported by those factorizations.
```

### 5.3 Description size

The checked description-size problem is closed at the current paper-facing
level.

Verified:

```text
complete checked List Nat serialization
complete prefix-free checked List Bool serialization
classification of every natural field
bounds for every stored binary-token payload
sample/fan-out bounds for field count and field maximum
closed sample-parametric logarithmic bit bound
single-power paper bit bound
finite Boolean-code universe
finite exhaustive checked decoder search
canonical decode/re-encode search
exact code-indexed selector.
```

Possible future improvement is sharpness, not closure: reduce constants and
exponents, or tie the minimum certified complexity more tightly to target
grammar parameters.

### 5.4 Paper-side exact-working conditions of output hypotheses

The structural boundary remains formally settled: nonempty-sample compiled
outputs do not satisfy the paper's nondeleting or exact-working conditions,
because constant control rules erase dummy children.

The final paper must either:

```text
allow the broader cut-compiled hypothesis syntax,
or construct a language-preserving strict normal-form compiler.
```

### 5.5 Semantic start-rooted normality

The target class still assumes `G.StartRootedNormal`; `StartSeparated` remains
a verified sufficient condition.  A general language-preserving start
normalization is not formalized.

### 5.6 Terminal-alphabet domain

For nonempty samples, actual compilation into the present `WorkingMCFG` syntax
requires `Nonempty α`, and the obstruction is formally necessary.  The finite
rule-object learner itself does not require this hypothesis.

### 5.7 Sharper target-dependent bounds

Minimum representation, exact-output, characteristic-sample, certified bit,
certified search, and simultaneous description ranks now exist and are attained.

Still open or non-sharp:

```text
characteristic-sample cardinality and total length in target-grammar parameters
text-order-independent coverage-stage bound
target-specific total mind-change bound independent of text repetitions
tight lower bounds showing description rank = characteristic rank for concrete targets
tight minimum checked-bit complexity for explicit target families.
```

### 5.8 Observation design

The semantic mathematical framework is now verified:

```text
refinement target monotonicity and failure contravariance
strict gain, empty loss, mutual equivalence, and chain decomposition
redundancy/essentiality ablation criterion
paired and arbitrary finite selected observation products
minimum-cardinality and arbitrary weighted selection
irredundancy and coordinate essentiality
two-objective Pareto fronts and positive-additive scalarization
explicit finite feasible/minimum/Pareto candidate sets
actual classical minimum/Pareto/rank-minimizing selectors
budget filtrations and exact rank-shell decompositions
rank comparison, perturbation sensitivity, and fixed-overhead normalization
rank-zero/rank-one/arbitrary-rank witness theorems
Pareto-envelope characterization and certified Pareto-rank selection.
```

Still open:

```text
one concrete strict-gain witness for a chosen observation pair
a decidable finite encoding replacing semantic target-membership filters
executable observation-selection algorithms
decision and optimization complexity
NP-hardness or NP-completeness of observation design
concrete quantitative comparisons across explicit observation families.
```

### 5.9 Negative and exclusion results

Still unformalized:

```text
unbounded no-advice non-identifiability
copy-language exclusion
member-kernel exclusion
other observation-independent lower bounds.
```

### 5.10 Paper/API cleanup

The repository now contains a long verified linear history.  A final public
import should expose the CI #738 endpoints and place historical facades and
intermediate decomposition files behind internal/legacy imports.

## 6. Immediate next files

The current CI #738 endpoint is:

```lean
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankSelector.lean
```

The semantic observation-selection problem is now highly developed.  The next
major step should convert it into a decidable encoded optimization problem or
supply the missing concrete separation witness.

### 6.1 `ConcreteCanonicalLearnerWorkingGrammarObservationSelectionDecisionProblem.lean`

Introduce a finite encoded feasibility table/oracle separated from semantic
target-class membership, and define the decision variants

```text
does some selection of cost at most b cover the target requirement?
does some Pareto candidate have scalar value at most b?
is the minimum observation-selection rank at most b?
```

Prove equivalence with the existing finite optimization layer whenever the
encoded table correctly represents semantic feasibility.

### 6.2 `ConcreteCanonicalLearnerWorkingGrammarObservationSelectionComplexity.lean`

Once the decision encoding is stable, formalize certificates, verification,
membership in NP, and the intended NP-hardness/NP-completeness reduction.

### 6.3 `ConcreteCanonicalLearnerWorkingGrammarObservationStrictGainWitness.lean`

Construct one explicit refinement and one explicit finite exact start-rooted
working MCFG language lying in the fine target class but not the coarse target
class.  This remains the main missing concrete observation-separation example.

### 6.4 `ExecutableConcreteCanonicalLearner.lean`

Replace classical/function-valued finite objects by decidable list-based codes
and prove semantic equivalence with the present certified learner and checked
serializer.

### 6.5 `SampleFactorizationEnumeration.lean`

Replace all-bounded-word enumeration by decompositions of actual sample words.

### 6.6 `ConcreteCanonicalLearnerConstructionComplexity.lean`

Prove fixed-parameter or polynomial construction-time bounds for the executable
factorization learner.

### 6.7 Boundary theorem files

```text
StrictWorkingGrammarNormalization.lean
StartRootedNormalization.lean
NoAdviceNonIdentification.lean
CopyLanguageExclusion.lean
MemberKernelExclusion.lean
```

## 7. Updated roadmap toward the full paper theorem

### Stage A: Reachable semantic theorem

Status: complete.

### Stage B: Exact-once splicing and successful-occurrence semantics

Status: complete.

### Stage C: Full finite output-type presentation and presentation grammar

Status: complete.

### Stage D: Successful trim and typed characteristic sample

Status: complete under semantic start-rooted normality.

### Stage E: Corrected concrete canonical learner

Status: complete, including exact finite enumeration, semantic equivalence,
reconstruction, class-level Gold identification, and stabilization.

### Stage F: Actual finite hypothesis and actual WorkingMCFG-valued learner

Status: complete on the exact domain `K = ∅ ∨ Nonempty α`.

### Stage G: Quantitative actual-grammar analysis

Status: complete at the current coarse paper-facing level.

Verified:

```text
rule, nonterminal, and presentation-item bounds
complete checked natural/bit codecs
all natural-field classifications and bounds
closed sample/fan-out logarithmic bit theorem
single-power paper bit theorem.
```

### Stage H: Finite checked search and certified output learner

Status: complete semantically.

Verified:

```text
finite code universe
finite exhaustive decoder search
canonical decode/re-encode search
exact code-indexed selector
certificate-carrying learner output
certified consistency, monotonicity, identification, and mind-change transfer.
```

### Stage I: Certified complexity and rank theory

Status: complete semantically.

Verified:

```text
attained minimum checked-bit complexity
attained minimum search complexity
joint description profiles
minimum simultaneous description rank
exact profile threshold theorem
rank obstruction theorems
exact-rank shell partition.
```

### Stage J: Observation refinement, products, and semantic optimization

Status: semantic framework essentially complete.

Verified:

```text
witness transport under refinement
target/failure monotonicity
strict gain and empty loss
mutual-refinement equivalence
chain composition and disjoint gains
redundancy/essentiality criterion
paired and arbitrary finite selected products
minimum-cardinality and weighted selection
finite minimum/Pareto candidate searches and selectors
budget filtrations and exact selection-rank shells
cost comparison, sensitivity, and normalization
rank-zero/rank-one/arbitrary-rank characterizations
Pareto-envelope theorem and actual certified Pareto-rank selector.
```

Still needed:

```text
concrete strict-gain example
decidable selection-problem encoding
selection/optimization complexity and hardness.
```

### Stage K: Executability and construction time

Status: open/substantial.

### Stage L: Target/start and hypothesis normal forms

Status: optional/open.

### Stage M: Negative and exclusion theorems

Status: open.

## 8. Trust map

### Strongly verified now

```text
fixed finite-observation algebra and output types
exact-once named-context splicing and its necessity
full finite output-type presentation and exact presentation-grammar equivalence
successful typed trim and typed-indexed characteristic samples
finite tuple/context/unit/exact-template/binary-witness enumeration and completeness
corrected finite canonical learner and exact reachable equivalence
actual finite hypothesis and actual cut-compiled WorkingMCFG learner
Gold identification, consistency, language monotonicity, and selected-stage exactness
rule/nonterminal/presentation-item size bounds
representation, exact-output, and characteristic-sample ranks
semantic mind-change counting and minimum-characteristic stabilization
complete checked natural and prefix-free logarithmic bit codecs
classification and sample/fan-out bounds for every natural field
closed sample-parametric and single-power paper bit bounds
checked bit-bounded representations
finite Boolean-code universe
finite exhaustive checked-decoder search
canonical decode/re-encode search and exact selector
certificate-carrying learner outputs
minimum certified bit/search complexities
joint profile hierarchy and minimum certified description rank
profile/complexity obstruction theorems
observation refinement target/failure monotonicity
strict gain, empty loss, mutual equivalence, and chain decomposition
interface ablation redundancy/essentiality criterion
paired and arbitrary finite selected observation products
minimum-cardinality and weighted observation selection
finite feasible/minimum/Pareto candidate sets and actual selectors
budget filtrations and exact selection-rank shells
cost comparison, perturbation sensitivity, and fixed-overhead normalization
rank-zero, rank-one, and arbitrary rank witness/decomposition theorems
positive-additive Pareto-envelope theorem
actual rank-minimizing Pareto selector with certified selected-product learner.
```

### Verified but intentionally non-executable or broader than paper working conditions

```text
classical selection of characteristic samples, minimum-rank witnesses, and coverage stages
noncomputable Finset images/filters over function-valued objects
classical dense-code and finite-search constructions
fixed-observation substitutability as a semantic target promise
semantic StartRootedNormal as a target-class condition
dummy-terminal cut-saturated compiler
compiled language exactness despite failure of nondeleting/exact-working output conditions
minimum complexities and ranks as semantic Nat.find invariants
observation gain/essentiality results conditional on an inhabited strict-gain class.
```

### Not yet verified

```text
fully executable decidable learner equivalent to the certified learner
polynomial sample-factorization learner
verified construction-time complexity
strict compiler preserving exact-working output conditions
general start-rooted normalization
concrete strict observation-gain witness
decidable/executable encoding of semantic observation-selection feasibility
observation-selection decision and optimization complexity
NP-hardness or NP-completeness of observation design
no-advice non-identifiability
copy-language and member-kernel exclusions.
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
lake build LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankSelector
```

Latest confirmed CI point:

```text
Lean CI #738
Commit: 6ef91db
```

Current strongest semantic/certified endpoints:

```lean
correctedConcreteCertifiedWorkingGrammarLearner_identification_descriptionRankObstruction_package
correctedConcreteCertifiedWorkingGrammar_observationRefinementFailure_package
correctedConcreteCertifiedWorkingGrammar_observationRefinementChain_package
correctedConcreteCertifiedWorkingGrammar_observationAblation_package
correctedConcreteCertifiedWorkingGrammar_observationSelectionRank_package
correctedConcreteCertifiedWorkingGrammar_observationSelectionCardinalityRank_package
correctedConcreteCertifiedWorkingGrammar_observationSelectionPositiveAdditiveRank_package
correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankEnvelope_package
correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankSelector_package
```

Current strongest checked-description and finite-search endpoints:

```lean
correctedConcreteFiniteHypothesis_logarithmicBitCount_le_paperPower
correctedConcreteWorkingGrammarLearner_finalDescriptionConclusion_package
correctedConcreteWorkingGrammarLearner_identification_finiteCodeUniverse_package
correctedConcreteWorkingGrammarLearner_identification_finiteDecodedSearch_package
correctedConcreteWorkingGrammarLearner_identification_canonicalDecodedSearch_package
correctedConcreteWorkingGrammarLearner_identification_canonicalSelector_package
```

Confirmed end-to-end implication:

```text
finite N and finite observation monoid M
+
ExactWorkingConditions
+
StartRootedNormal
+
FanoutAtMost f
+
FixedNamedTupleSubstitutable f obs L(G)
+
Nonempty terminal alphabet
⇒ finite typed characteristic sample
⇒ corrected finite canonical learner
⇒ actual finite hypothesis
⇒ actual cut-compiled WorkingMCFG output with exactly the same language
⇒ explicit grammar and presentation bounds
⇒ complete checked natural and logarithmic bit serialization
⇒ closed sample/fan-out single-power bit bound
⇒ finite checked code universe
⇒ finite exhaustive and canonical decoded search
⇒ exact code-indexed recovery of the actual presentation
⇒ certificate-carrying learner output
⇒ attained minimum certified bit/search complexities
⇒ attained minimum simultaneous certified-description rank
⇒ profile obstructions yielding characteristic-rank lower bounds
⇒ Gold identification and semantic mind-change stabilization.
```

Observation design now additionally gives:

```text
paired and finite selected products preserve every selected factor's targets
minimum-cardinality and minimum weighted selections are attained
minimum and Pareto selections are irredundant and coordinate-essential
finite feasible/minimum/Pareto searches have at most 2^|U| candidates
cost budgets form a monotone filtration whose first nonempty layer is the rank
every full-product target lies in one unique exact selection-rank shell
pointwise cost order and bounded perturbations control rank changes
fixed overhead shifts rank exactly without changing minimum/Pareto subsets
cardinality and positive-additive rank-zero/one/arbitrary shells are characterized
positive-additive rank is the minimum scalar value on the additive Pareto frontier
an actual rank-minimizing Pareto subset is selected and certified.
```

Recommended next file:

```text
ConcreteCanonicalLearnerWorkingGrammarObservationSelectionDecisionProblem.lean
```

Reason:

CI #738 completes the semantic finite observation-selection optimization layer,
including explicit finite candidates, minimum/Pareto selectors, exact rank
hierarchies, sensitivity, and a certified Pareto-rank selector.  The largest
remaining gap in that direction is now computational: semantic target-class
membership still appears inside noncomputable finite filters.  The next file
should isolate a decidable finite feasibility encoding and prove its equivalence
to the current semantic selection problem under a correctness interface.  That
creates the right foundation for NP membership and the intended hardness
results.  The concrete strict-gain witness remains the parallel mathematical
example track.
