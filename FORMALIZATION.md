# Formalization Supplement

Lean 4 artifact for the paper:

**Residual Concept Representations for Two-Sided Monoid-Typed CFG Descriptors**

Author: Takayuki Kuriyama  
Repository: `growupkuriyama-hub/lean_cfg_project`  
Supplement path: `lean_cfg_project/FORMALIZATION.MD`  
Current checked artifact snapshot: commit `702dcf5`  
GitHub Actions: Lean CI #207 passed  
Pushed by: `growupkuriyama-hub`

---

## Purpose of this document

This file is intended as a paper-facing formalization supplement rather than a repository README.  It explains what the Lean artifact verifies, how the verified modules correspond to the mathematical development in the paper, how to reproduce the checks, and where the formalization boundary lies.

The accompanying paper studies finite presentation-level descriptors extracted from context-free grammar presentations equipped with a fixed finite monoid homomorphism `h : Sigma* -> M`.  The main semantic bridge is:

```text
E_h(G) -> P(Q) -> Concepts(Q, q[L])
```

Here `E_h(G)` is a two-sided fixed-`h` presentation descriptor, `q : Sigma* -> Q` is a multiplicative word observation, `P(Q)` is powerset-valued state semantics, and `Concepts(Q, q[L])` is the residual concept universe determined by the observed language image.

The formalization does **not** claim that CFG equivalence is solved or that a canonical CFG presentation has been constructed.  The verified claim is more precise: the Lean artifact checks substantial parts of the semantic bridge from two-sided fixed-`h` CFG descriptors to powerset semantics, residual concept semantics, finite saturation, observed syntactic concepts, and checked adequacy criteria.

---

## Current artifact status

The current checked snapshot is:

```text
commit: 702dcf5
CI run: Lean CI #207
pushed by: growupkuriyama-hub
status: passed
latest checked theorem-body extension: finite adequacy examples / item 5
latest checked theorem-body target: LeanCfgProject.EndpointMonoidAdequacy
current theorem-body chain:
  LeanCfgProject.ResidualConceptNucleus
  LeanCfgProject.PointwiseAdequacy
  LeanCfgProject.UniformAdequacy
  LeanCfgProject.ObservedQuotientResidual
  LeanCfgProject.ObservedQuotientClosure
  LeanCfgProject.ObservedQuotientClosureImage
  LeanCfgProject.ObservedSyntacticSaturation
  LeanCfgProject.ObservedFactorMinimality
  LeanCfgProject.DiamondSemilatticeAdequacy
  LeanCfgProject.ZMod3FailureExample
  LeanCfgProject.EndpointMonoidAdequacy
previous theorem-body snapshot: commit b1e651e / Lean CI #195 / LeanCfgProject.ObservedFactorMinimality
previous paper-facing final-index snapshot: commit 0e6dbb5 / Lean CI #184 / LeanCfgProject.ICSubmissionSummary_v14
previous release-index snapshot: commit c6c1705 / Lean CI #180
```

The current theorem-body development target checked by CI #207 is:

```bash
lake build LeanCfgProject.EndpointMonoidAdequacy
```

The current stable paper-facing final-index target from the previous indexed
snapshot remains:

```bash
lake build LeanCfgProject.ICSubmissionSummary_v14
```

The theorem-body item1--item4 chain can be checked explicitly by running:

```bash
lake build LeanCfgProject.ResidualConceptNucleus
lake build LeanCfgProject.PointwiseAdequacy
lake build LeanCfgProject.UniformAdequacy
lake build LeanCfgProject.ObservedQuotientResidual
lake build LeanCfgProject.ObservedQuotientClosure
lake build LeanCfgProject.ObservedQuotientClosureImage
lake build LeanCfgProject.ObservedSyntacticSaturation
lake build LeanCfgProject.ObservedFactorMinimality
lake build LeanCfgProject.DiamondSemilatticeAdequacy
lake build LeanCfgProject.ZMod3FailureExample
lake build LeanCfgProject.EndpointMonoidAdequacy
```



The earlier release-index checkpoint `c6c1705` / Lean CI #180, the final-index checkpoint `0e6dbb5` / Lean CI #184, and the theorem-body item1--item4 checkpoint `b1e651e` / Lean CI #195 remain useful historical base points.  The current theorem-body development state is checked at commit `702dcf5` by Lean CI #207.

The CI also keeps repository-level checks that reject placeholder proof commands and project-level axiom declarations in Lean source files.

At the current checked snapshot, the artifact verifies the following major groups of results:

- finite monoid-typed CFG descriptor architecture;
- observation quotients and pointed-boundary theorems;
- concrete counterexamples showing that naive finite observation is not concatenation-compatible;
- powerset-valued state semantics under multiplicative word observations;
- residual Galois connection, concept closure, concept extents, and concept products;
- multiplicative/nuclear behavior of residual concept closure under subset product;
- pointwise adequacy equivalences between residual equality, common-context equality, and residual coverage;
- uniform adequacy equivalences between nonempty-subset adequacy, singleton adequacy, and single observed-syntactic block conditions;
- quotient/factor-map invariance for residuals, common contexts, concept closure, point concepts, and concept products;
- observed-syntactic saturation and minimality/maximality of exact observed factor maps;
- carrier-level descriptor semantics;
- two-sided frame soundness and frame-to-residual / frame-to-intent preservation;
- finite-stage carrier saturation correctness;
- least closed solution characterization for saturation;
- saturation-computed concept semantics;
- closed-stage stability and algorithmic correctness;
- local stopping correctness for the checkable equality `U_(N+1) = U_N`;
- unconditional finite stopping by an indicator-cardinality measure under finite state and finite observation assumptions;
- bounded carrier-stage computation of state semantics and residual concept semantics;
- bounded preservation of two-sided frame residual/intent information;
- a general frame-adequacy criterion reducing equality of residual concepts to a coverage condition;
- finite K4 adequacy examples witnessing strict raw-image inclusion and nontrivial concept collapse;
- the observed syntactic congruence `SameObservedSyntactic` for an arbitrary monoid pair `(Q,S)`;
- saturation of concept closures and two-sided residuals under the observed syntactic congruence;
- maximality of the observed syntactic congruence among two-sided stable `S`-preserving relations;
- the canonical residual closure system, namely that closed extents are exactly intersections of two-sided residuals;
- carrier-level observed-syntactic-block adequacy for the standard observation `h` and factor-through-`h` observations;
- the finite observed-learning layer: canonical observed frame structures, decidability wrappers, finite observed frame bases, finite-set reconstruction, faithful-representative reconstruction, and observed-concept identification wrappers;
- the canonical point-frame incidence core: singleton concept/frame incidence, equality of point concepts exactly as observed syntactic equivalence, and the paper-facing universal-frame-model core;
- v27.1 reduced-frame and observed-concept release layers: point-frame corollaries, lightweight reduced frame-model core definitions, canonical frame-model corollaries, observed subset stability, point-frame learning transport, observed-membership equivalence, point-frame incidence transport, finite residual-basis transport, observed-learning release theorems, point-frame release theorems, finite-basis release theorems, and the artifact release-index target;
- v27.2 release-regression and release-certificate layers: observed-learning release regression, point-frame release regression, finite-basis release regression, release manifest, CI #180 reproducibility index, artifact metadata capsule, release certificate, observed-learning certificate, point-frame certificate, finite-basis certificate, and paper formalization bridge;
- v27.2 final-index layer: paper-claim index, theorem-table index, frozen artifact index, dependency certificate, FORMALIZATION supplement certificate, paper submission checklist, final smoke test, and the top-level target `ICSubmissionSummary_v14`;
- finite adequacy examples for the diamond meet-semilattice, the three-element cyclic monoid/Z3 failure witness, and the endpoint monoid;
- paper-facing summary, audit, release-index, final-index, and appendix-index targets for reproducibility.

---

## How to reproduce the current check

From the repository root, run:

```bash
lake build LeanCfgProject.ICSubmissionSummary_v14
```

For a broader paper-facing import check around the current final-index layer, run:

```bash
lake build LeanCfgProject.ICSubmissionSummary_v14
lake build LeanCfgProject.ICFinalSmokeTest_v27_2
lake build LeanCfgProject.ICPaperSubmissionChecklist_v27_2
lake build LeanCfgProject.ICFormalizationSupplementCertificate_v27_2
lake build LeanCfgProject.ICFrozenArtifactIndex_v27_2
```

Older broad paper-facing targets such as `ICFullPaperSummary_v2`, `ICArtifactFreezeIndex`, and `ICReproducibilitySummary` are still useful for historical regression checks, but the current final-index path is centered on `ICSubmissionSummary_v14`.

For ordinary development, the repository uses a lightweight CI strategy: instead of explicitly building every historical experimental target one by one, it builds high-level summary modules whose imports force Lean to check the relevant dependency graph.

The current top-level paper-facing summary modules include:

```text
LeanCfgProject/ICSubmissionSummary_v14.lean
LeanCfgProject/ICFinalSmokeTest_v27_2.lean
LeanCfgProject/ICPaperSubmissionChecklist_v27_2.lean
LeanCfgProject/ICFormalizationSupplementCertificate_v27_2.lean
LeanCfgProject/ICDependencyCertificate_v27_2.lean
LeanCfgProject/ICFrozenArtifactIndex_v27_2.lean
LeanCfgProject/ICTheoremTableIndex_v27_2.lean
LeanCfgProject/ICPaperClaimIndex_v27_2.lean
LeanCfgProject/ICSubmissionSummary_v13.lean
LeanCfgProject/ICReleaseSmokeTest_v27_2.lean
LeanCfgProject/ICAppendixReleaseIndex_v27_2.lean
LeanCfgProject/ICPaperFormalizationBridge_v27_2.lean
LeanCfgProject/FiniteBasisCertificate_v27_2.lean
LeanCfgProject/PointFrameCertificate_v27_2.lean
LeanCfgProject/ObservedLearningCertificate_v27_2.lean
LeanCfgProject/ICReleaseCertificate_v27_2.lean
LeanCfgProject/ICArtifactMetadata_ci180.lean
LeanCfgProject/ICSubmissionSummary_v12.lean
LeanCfgProject/ICReproducibilityIndex_ci180.lean
LeanCfgProject/ICReleaseManifest_v27_2.lean
LeanCfgProject/FiniteBasisReleaseRegression_v27_2.lean
LeanCfgProject/PointFrameReleaseRegression_v27_2.lean
LeanCfgProject/ObservedLearningReleaseRegression_v27_2.lean
LeanCfgProject/ICSubmissionSummary_v11.lean
LeanCfgProject/ICFormalizationReleaseIndex_v27.lean
LeanCfgProject/ICArtifactAudit_v27.lean
LeanCfgProject/FiniteBasisReleaseTheorems_v27.lean
LeanCfgProject/PointFrameReleaseTheorems_v27.lean
LeanCfgProject/ObservedLearningReleaseTheorems_v27.lean
LeanCfgProject/ICSubmissionSummary_v10.lean
LeanCfgProject/ObservedConceptSubmissionIndex_v27.lean
LeanCfgProject/ObservedLearningSubmissionAudit_v27.lean
LeanCfgProject/PointFrameTransportSummary_v27.lean
LeanCfgProject/ObservedSubsetTransportPackage_v27.lean
LeanCfgProject/ICSubmissionSummary_v9.lean
LeanCfgProject/ObservedConceptObjectReleaseIndex_v27.lean
LeanCfgProject/FiniteResidualBasisTransport_v27.lean
LeanCfgProject/PointFrameIncidenceTransport_v27.lean
LeanCfgProject/ObservedMembershipEquivalence_v27.lean
LeanCfgProject/ICSubmissionSummary_v8.lean
LeanCfgProject/ICSubmissionSafeExpansion_v27.lean
LeanCfgProject/ObservedFiniteBasisStablePackage_v27.lean
LeanCfgProject/CanonicalPointFrameStablePackage_v27.lean
LeanCfgProject/ObservedLearningStablePackage_v27.lean
LeanCfgProject/ICSubmissionSummary_v7.lean
LeanCfgProject/ICPaperFormalizationSummary_v28.lean
LeanCfgProject/ReducedFrameModelPaperSummary.lean
LeanCfgProject/PointFrameLearningBridge.lean
LeanCfgProject/ObservedSubsetStability.lean
LeanCfgProject/CanonicalFrameModelCorollaries.lean
LeanCfgProject/FrameModelCoreBasic.lean
LeanCfgProject/ICSubmissionSummary_v6.lean
LeanCfgProject/ICPaperFormalizationSummary_v27.lean
LeanCfgProject/FiniteObservedBasisCorollaries.lean
LeanCfgProject/FaithfulRepresentativeCorollaries.lean
LeanCfgProject/ObservedLearningQueryModel.lean
LeanCfgProject/ReducedFrameModelCoreDefs.lean
LeanCfgProject/PointFrameCorollaries.lean
LeanCfgProject/ObservedLearningPaperSummary_v2.lean
LeanCfgProject/ObservedLearningConstructibilitySummary.lean
LeanCfgProject/UniversalFrameModelCore.lean
LeanCfgProject/CanonicalPointFrame.lean
LeanCfgProject/SingletonClosureIncidence.lean
LeanCfgProject/ICSubmissionSummary_v4.lean
LeanCfgProject/ObservedLearningPaperSummary.lean
LeanCfgProject/FiniteObservedConceptIdentification.lean
LeanCfgProject/ICSubmissionSummary_v3.lean
LeanCfgProject/ICFullPaperSummary_v2.lean
LeanCfgProject/ICFastCI_v2.lean
LeanCfgProject/ICReproducibilitySummary.lean
LeanCfgProject/ICArtifactFreezeIndex.lean
LeanCfgProject/ICArtifactAppendixCoverage.lean
LeanCfgProject/ICArtifactReleaseSummary.lean
LeanCfgProject/ObservedSyntacticPaperSummary.lean
LeanCfgProject/ICSemanticBridgeSummary_v3.lean
```

When preparing a release tag or an archived artifact, the individually listed lower-level modules can also be built explicitly as a full regression check.

---

## Formalization map

The Lean development is best read as a layered formalization.

### 1. Descriptor architecture

Files:

```text
LeanCfgProject/Step25_Test.lean
LeanCfgProject/FullArchitecture_Test.lean
```

This layer formalizes the fixed finite monoid typing infrastructure:

- words and fixed finite monoid homomorphisms;
- typed states and full typed states;
- typed terminal and binary rules;
- productivity and reachability;
- trimmed states;
- extracted profiles and extracted typed rules;
- finite context structures;
- witnessed finite context structures;
- morphisms;
- extraction and realization interfaces;
- the inductive families `YieldFamily` and `ContextFamily`.

This is the presentation-level architecture behind finite two-sided monoid-typed CFG descriptors.

---

### 2. Observation quotients and boundary results

Files:

```text
LeanCfgProject/LanguageQuotient.lean
LeanCfgProject/ObservationFinite.lean
LeanCfgProject/ObservationCounterexample.lean
LeanCfgProject/ObservationCounterexample_v2.lean
LeanCfgProject/ObservationSignatureCounterexample.lean
```

This layer defines language-level observation relations and their stabilized variants.  Representative declarations include:

```text
HTypedContextTypes
SameHTypedObservation
SameHTypedSyntacticObservation
SameSyntacticContext
SameHTypedPointedObservation
SameHTypedPointedSyntacticObservation
RelationContained
TwoSidedStable
sameHTypedSyntacticObservation_maximal
pointedSynObs_iff_syntacticContext_and_h_eq
ObservationSignature
sameHTypedObservation_iff_observationSignature_eq
sameHTypedObservation_kernel
```

The counterexample modules verify, for `L = {ab, cd}` and a parity observation, that the naive finite `h`-typed observation is not generally compatible with concatenation.  Representative declarations include:

```text
same_observation_a_c
same_observation_b_b
not_same_observation_ab_cb
naive_observation_not_concat_compatible
observationSignature_a_eq_c
observationSignature_ab_ne_cb
observationSignature_not_concat_compatible
```

This justifies the paper's distinction between raw finite observation, syntactic stabilization, pointed stabilization, and residual concept semantics.

---

### 3. Powerset-valued state semantics

File:

```text
LeanCfgProject/StateSemantics.lean
```

This layer defines abstract powerset-valued semantics for languages and grammar states under a multiplicative word observation `q : Sigma* -> Q`.

Representative declarations:

```text
Language
ImageOfLanguage
LangMul
SetMul
StateSemantics
image_langMul_eq_setMul
terminal_sound
binary_sound
```

The key verified fact is that multiplicative observations turn concatenation into subset multiplication:

```text
q[Y Z] = q[Y] q[Z]
```

Consequently, terminal and binary CFG rules are interpreted soundly by singleton insertion and subset multiplication inclusions.

---

### 4. Residual concept semantics

File:

```text
LeanCfgProject/ResidualConcept.lean
```

This layer formalizes two-sided residuals, common contexts, concept closure, concept extents, and concept products over an abstract monoid carrier `Q`.

Representative declarations:

```text
TwoSidedResidual
CommonContexts
ElementsOfContexts
ConceptClosure
residual_galois_connection
subset_conceptClosure
state_semantics_subset_residual
commonContexts_antitone
elementsOfContexts_antitone
conceptClosure_mono
binary_sound_after_closure
commonContexts_conceptClosure
conceptClosure_idempotent
IsConceptExtent
conceptClosure_isConceptExtent
ConceptProduct
conceptProduct_isConceptExtent
binary_sound_as_conceptProduct
```

For `S = q[L]`, the incidence relation is:

```text
gamma I_S (alpha, beta)  iff  alpha * gamma * beta ∈ S
```

The module verifies that this incidence induces a Galois-style residual concept closure that is extensive, monotone, and idempotent, and that binary rule soundness persists after closure.

---

### 5. Finite saturation framework

Files:

```text
LeanCfgProject/FiniteSaturation.lean
LeanCfgProject/CarrierSaturationCorrectness.lean
LeanCfgProject/CarrierSaturationLeast.lean
LeanCfgProject/CarrierSaturationConceptSoundness.lean
```

The generic saturation module defines an inflationary one-step saturation operator and its iterates:

```text
SaturationStep
IsSaturationClosed
saturationStep_mono
SaturationIter
terminal_mem_saturationIter_one
binary_mul_mem_saturationIter_succ
```

The carrier-level modules instantiate this framework for CFG descriptor semantics.  Representative declarations include:

```text
CarrierTerminalImage
CarrierBinaryRel
CarrierSaturationImage
carrier_saturationIter_subset_stateSemantics
carrier_yield_mem_saturationIter_exists
carrier_saturationImage_eq_stateSemantics
carrierSaturationImage_isSaturationClosed
carrierSaturationImage_least_closed_solution
CarrierSaturationConceptSemantics
carrierSaturationConceptSemantics_eq_carrierConceptSemantics
```

This verifies that carrier saturation computes carrier state semantics and that the saturation image is the least closed simultaneous solution of the terminal and binary inclusions.  After residual closure, saturation-computed concept semantics agrees with direct carrier concept semantics.

---

### 6. Descriptor-level semantic bridge

Files:

```text
LeanCfgProject/DescriptorSemantics.lean
LeanCfgProject/DescriptorResidualSemantics.lean
LeanCfgProject/CarrierConceptSemantics.lean
```

This layer connects descriptor-level terminal and binary rules to powerset-valued and residual concept semantics.

Representative declarations:

```text
CarrierYieldSet
CarrierStateSemantics
carrier_terminal_sound
carrier_binary_rule_hbin
carrier_binary_sound
carrier_binary_sound_after_closure
carrier_binary_sound_as_conceptProduct
CarrierStartLanguage
context_yield_mem_startLanguage
carrier_state_semantics_subset_residual
CarrierStartImage
CarrierConceptSemantics
carrierConceptSemantics_isConceptExtent
carrier_binary_sound_as_conceptSemantics
carrier_context_concept_subset_residual_closure
```

This layer supports the paper's bridge:

```text
E_h(G) -> P(Q) -> Concepts(Q, q[L])
```

---

### 7. Two-sided frame soundness and frame-intent preservation

Files:

```text
LeanCfgProject/FrameSoundness.lean
LeanCfgProject/SaturationFrameBridge.lean
LeanCfgProject/FrameIntentClosureBridge.lean
LeanCfgProject/ClosedStageFrameBridge.lean
LeanCfgProject/ClosedStageFrameIntentStability.lean
LeanCfgProject/LocalStoppingFrameResidual.lean
LeanCfgProject/FiniteStoppingFrameResidual.lean
```

This layer verifies that the two-sided frame carried by typed descriptor states is semantically active rather than decorative.

Representative declarations:

```text
carrier_yield_frame_sound
carrier_context_frame_sound
carrier_state_semantics_subset_frame_residual_h
carrier_frame_mem_commonContexts_h
carrier_concept_semantics_subset_frame_residual_closure_h
carrier_saturationImage_subset_frame_residual_h
carrier_frame_mem_commonContexts_saturation_h
carrier_frame_mem_commonContexts_carrierConcept_h
carrier_frame_mem_commonContexts_saturationConcept_h
carrierClosedStageConceptSemantics_subset_frame_residual_closure_h
carrier_frame_mem_commonContexts_closedStageConcept_h
carrier_frame_mem_commonContexts_laterClosedStageConcept_h
carrier_localStopped_frame_intent_and_residual_h
exists_le_carrierStage_frame_intent_and_residual_h_of_fintype
exists_le_carrierStage_computes_concept_and_frame_h_of_fintype
```

The verified interpretation is that typed two-sided frames persist as residual bounds and as intent-side common contexts, including after saturation, closure, local stopping, and bounded finite stopping.

---

### 8. Closed-stage correctness and local stopping

Files:

```text
LeanCfgProject/SaturationStability.lean
LeanCfgProject/ClosedStageConceptBridge.lean
LeanCfgProject/SaturationMonotoneChain.lean
LeanCfgProject/ClosedStageAlgorithmCorrectness.lean
LeanCfgProject/FiniteCoverageStopping.lean
LeanCfgProject/ClosedStageEquivalences.lean
LeanCfgProject/ClosedStageConceptStability.lean
LeanCfgProject/ClosedStageRuleSemantics.lean
LeanCfgProject/LaterClosedStageClosure.lean
LeanCfgProject/LocalStoppingCorrectness.lean
LeanCfgProject/LocalStoppingRuleSemantics.lean
LeanCfgProject/LocalStoppingFrameResidual.lean
```

This layer proves that a closed saturation stage computes the semantic object intended by the paper.  It also packages the checkable local stopping condition:

```text
U_(N+1) = U_N
```

Representative declarations:

```text
saturationIter_succ_eq_of_closed
carrierSaturationImage_eq_of_closed_stage
carrierStateSemantics_eq_closed_saturationStage
CarrierClosedStageConceptSemantics
carrierClosedStageConceptSemantics_eq_carrierConceptSemantics
closedStage_computes_carrierStateSemantics
closedStage_computes_carrierConceptSemantics
carrierSaturationStage_closed_iff_succ_eq
carrierSaturationStage_closed_iff_eq_stateSemantics
carrierSaturationStage_closed_of_succ_eq
carrierSaturationStage_eq_saturationImage_of_succ_eq
carrierSaturationStage_eq_stateSemantics_of_succ_eq
carrierClosedStageConcept_eq_carrierConcept_of_succ_eq
carrierSaturationIter_eq_stateSemantics_of_succ_eq_later
carrierClosedStageConcept_later_eq_carrierConcept_of_succ_eq
carrier_terminalImage_subset_stoppedStage_of_succ_eq
carrier_binaryRule_mul_mem_laterStoppedStage_of_succ_eq
```

This gives the algorithmic reading: if a saturation stage is closed, or if the local equality test detects closure, then that finite stage computes state semantics and its residual closure computes concept semantics.

---

### 9. Unconditional finite stopping and bounded computation

Files:

```text
LeanCfgProject/FiniteStoppingCore.lean
LeanCfgProject/MeasureStoppingCriterion.lean
LeanCfgProject/FiniteSaturationMeasure.lean
LeanCfgProject/FiniteStoppingFrameResidual.lean
LeanCfgProject/FiniteStoppedFrameAdequacy.lean
```

This layer proves a bounded finite-stopping theorem for saturation over a finite state set and a finite observation carrier.

The proof is organized as follows:

1. a purely numerical stopping theorem for monotone bounded natural-number sequences;
2. a general measure-based stopping criterion for monotone stage families;
3. an indicator-cardinality measure for finite subsets of a finite carrier;
4. carrier-level specialization giving bounded finite stages computing state and concept semantics;
5. frame-residual preservation and finite-stopped frame adequacy consequences.

Representative declarations:

```text
exists_le_eq_succ_of_monotone_bounded
exists_le_pointwise_stable_of_measure
exists_le_saturationStableStage_of_measure
exists_le_isSaturationClosed_of_measure
StageCard
SatMeasureIndicator
satMeasureIndicator_mono
satMeasureIndicator_bound
satMeasureIndicator_strict_of_change
exists_le_stable_stage_of_fintype
exists_le_isSaturationClosed_stage_of_fintype
exists_le_carrierIsSaturationClosed_stage_of_fintype
exists_le_carrierStage_computes_stateSemantics_of_fintype
exists_le_carrierStage_computes_conceptSemantics_of_fintype
exists_le_carrierStage_computes_stateSemantics_h_of_fintype
exists_le_carrierStage_computes_conceptSemantics_h_of_fintype
exists_le_carrierStage_frame_intent_and_residual_h_of_fintype
exists_le_carrierStage_computes_concept_and_frame_h_of_fintype
```

This upgrades the algorithmic story from “if a finite stage is closed, then it is correct” to “under finite state and finite carrier assumptions, a bounded closed stage exists and computes the semantics.”

The finite-state hypothesis is essential and should not be omitted.

---

### 10. Observed syntactic concepts and canonical residual closure

Files:

```text
LeanCfgProject/ObservedSyntacticConcept.lean
LeanCfgProject/ObservedSyntacticCongruence.lean
LeanCfgProject/CanonicalResidualClosureSystem.lean
LeanCfgProject/ObservedSyntacticResidualCorollaries.lean
LeanCfgProject/ObservedSyntacticBlockAdequacyCorollaries.lean
LeanCfgProject/ObservedSyntacticPaperCorollaries.lean
```

This layer formalizes the canonical observed-syntactic object used in the current paper draft.

The central relation is:

```text
SameObservedSyntactic S x y
```

meaning that all two-sided `S`-membership tests agree on `x` and `y`.

Representative declarations:

```text
SameObservedSyntactic
sameObservedSyntactic_refl
sameObservedSyntactic_symm
sameObservedSyntactic_trans
conceptClosure_saturated_under_sameObservedSyntactic
twoSidedResidual_saturated_under_sameObservedSyntactic
conceptClosure_twoSidedResidual_eq
syntacticBlockAdequacy
sameObservedSyntactic_mul_left
sameObservedSyntactic_mul_right
sameObservedSyntactic_mul
sameObservedSyntactic_maximal
observedSyntacticCongruence_summary
ResidualIntersection
residualIntersection_closed
conceptClosure_eq_residualIntersection_commonContexts
isConceptExtent_iff_exists_residualIntersection
canonicalResidualClosureSystem_summary
```

The verified mathematical content is:

- concept closures are saturated under observed syntactic equivalence;
- two-sided residuals are saturated under observed syntactic equivalence;
- every two-sided residual is already concept-closed;
- in a monoid, observed syntactic equivalence is stable under multiplication and is maximal among two-sided stable `S`-preserving relations;
- concept extents are exactly intersections of two-sided residuals;
- if a frame residual lies in one observed syntactic block, then every nonempty sound state image inside that residual generates the whole residual by concept closure.

This is the Lean counterpart of the paper's canonical residual closure system and syntactic-block adequacy theorem.

---

### 11. K4 residual adequacy witness

Files:

```text
LeanCfgProject/FrameAdequacyCriterion.lean
LeanCfgProject/K4ResidualAdequacyExample.lean
LeanCfgProject/K4AdequacyStrictness.lean
LeanCfgProject/K4ConceptCollapse.lean
LeanCfgProject/K4AdequacyPaperSummary.lean
LeanCfgProject/AdequacyBridgeSummary.lean
```

This layer provides a finite worked example showing that residual concept closure is doing genuine work.

Representative declarations:

```text
adequacy_of_residual_coverage
adequacy_iff_residual_coverage
k4_bridge_bidirectional
k4_adequacy_is_nontrivial
k4_nontrivial_collapse_summary
k4_paper_witness_strict_raw_soundness_but_concept_adequacy
k4_paper_witness_distinct_raw_images_same_concept
k4_paper_witness_two_strict_raw_images_with_frame_adequacy
k4_paper_bidirectional_and_nontrivial
k4_paper_nontrivial_collapse_summary
```

The verified phenomenon is that raw singleton images can be strict subsets of their frame residuals, while their residual concept closures coincide with the corresponding frame residual concepts.  The example also verifies that distinct raw powerset images can collapse to the same residual concept.

---

### 13. Carrier-level observed-block adequacy

Files:

```text
LeanCfgProject/CarrierObservedAdequacy.lean
LeanCfgProject/CarrierObservedAdequacyCorollaries.lean
```

This layer lifts abstract observed-syntactic-block adequacy back to CFG descriptor semantics.

Representative declarations:

```text
carrier_frame_adequacy_of_observedSyntacticBlock_h
carrier_frame_residual_eq_conceptSemantics_of_observedSyntacticBlock_h
carrier_frame_residual_subset_conceptSemantics_of_observedSyntacticBlock_h
carrier_frame_adequacy_of_observedSyntacticBlock_factor
carrierObservedAdequacy_summary_h
paper_carrierObservedBlockAdequacy_h
paper_frameResidual_eq_carrierConcept_of_observedBlock_h
paper_frameResidual_subset_carrierConcept_of_observedBlock_h
```

The verified theorem says, in paper terms: for a productive carrier state, if its state image is nonempty and its frame residual lies in a single observed syntactic block, then the carrier concept semantics of that state is exactly the corresponding frame residual.

This is checked both for the standard observation `h` and for observations factoring through `h`.

---


### 14. Finite observed-learning layer

Files:

```text
LeanCfgProject/ObservedFrameStructure.lean
LeanCfgProject/ObservedFrameStructureDecidable.lean
LeanCfgProject/FiniteObservedFrameBasis.lean
LeanCfgProject/FiniteSetQueryReconstruction.lean
LeanCfgProject/FaithfulRepresentatives.lean
LeanCfgProject/ObservedLearningExamples.lean
LeanCfgProject/FiniteObservedConceptIdentification.lean
LeanCfgProject/ObservedLearningCorollaries.lean
LeanCfgProject/ObservedLearningConstructibilitySummary.lean
LeanCfgProject/ObservedLearningPaperSummary.lean
LeanCfgProject/ObservedLearningPaperSummary_v2.lean
```

This layer corresponds to the paper's finite observed-learning section.  The target is not the original language itself, but the observed frame-concept data determined by the finite observed subset `S = q[L]`.

Representative declarations:

```text
FrameResidual
SingleObservedBlock
ObservedFrameStructure
canonicalObservedFrameStructure
canonical_frameResidual_closed
frameResidual_singleBlock_generates_residual
sameObservedSyntactic_has_decision
frameResidual_membership_has_decision
singleObservedBlock_has_decision
conceptClosure_has_common_frame_basis
conceptClosure_has_finite_frame_basis
closedConcept_has_finite_frame_basis
finiteObservedFrameBasis_summary
finiteSet_eq_of_same_membership
finiteSet_counterexample_of_ne
finiteSet_reconstruction_package
FaithfulRepresentatives
observedSubset_eq_representative_membership
observedSubset_eq_of_same_representative_answers
observedFrameStructure_identified_from_membership
observedFrameStructure_identified_from_faithful_representatives
finiteObservedConceptIdentification_summary
identified_frameResidual_from_membership
identified_singleBlock_from_membership
identified_finite_frame_basis_from_membership
faithful_representatives_identify_frameResidual
observedLearningConstructibility_from_membership
observedLearningConstructibility_summary
```

The verified interpretation is:

- the observed frame-concept structure is determined by the observed subset `S`;
- every concept closure has a finite observed frame-basis presentation when `Q` is finite;
- equality of all membership answers for two observed subsets identifies the canonical observed frame structure;
- faithful representatives identify the observed subset and hence the observed frame structure;
- once `S` is identified, frame residuals and single-block predicates are identified as well.

This supports the paper's finite observed analogue of distributional learning: the formalized target is the `q`-observed frame-concept object, not the full language `L`.

---

### 15. Canonical point-frame incidence and universal-core layer

Files:

```text
LeanCfgProject/SingletonClosureIncidence.lean
LeanCfgProject/CanonicalPointFrame.lean
LeanCfgProject/UniversalFrameModelCore.lean
LeanCfgProject/PointFrameCorollaries.lean
LeanCfgProject/ReducedFrameModelCoreDefs.lean
LeanCfgProject/FrameModelCoreBasic.lean
LeanCfgProject/CanonicalFrameModelCorollaries.lean
LeanCfgProject/CanonicalPointFrameStablePackage_v27.lean
LeanCfgProject/PointFrameIncidenceTransport_v27.lean
LeanCfgProject/PointFrameTransportSummary_v27.lean
LeanCfgProject/PointFrameReleaseTheorems_v27.lean
```

This layer corresponds to the paper's canonical reduced frame representation discussion, including the Ganter--Wille/FCA-inspired representation viewpoint specialized to the two-sided monoid incidence induced by `(Q,S)`.

Representative declarations:

```text
SingletonConcept
singletonConcept_subset_residual_iff
singletonConcept_subset_frame_iff
singletonConcept_subset_residual_of_mem
CanonicalPoint
CanonicalFrame
canonicalPoint_subset_frame_iff
canonicalPoint_eq_iff_sameObservedSyntactic
sameObservedSyntactic_iff_canonicalPoint_eq
canonicalObservedFrameStructure_represents_incidence
canonicalObservedFrameStructure_pointCollapse
universalFrameModelCore_summary
canonical_point_frame_incidence_checked
canonical_point_collapse_checked
canonical_point_frame_core_checked
observedMembershipEquivalent_transport_point_frame_incidence
observedMembershipEquivalent_transport_point_collapse
transcript_point_frame_transport_summary
pointFrame_release_core
pointFrame_release_transcript_transport
```

The key checked incidence lemma is:

```text
ConceptClosure S {gamma} ⊆ TwoSidedResidual S a b
  iff
a * gamma * b ∈ S
```

The layer also verifies that equality of canonical point concepts is exactly the observed syntactic equivalence relation.  This provides the Lean-checked core of the paper's canonical reduced frame representation story.  The full abstract complete-lattice isomorphism theorem for arbitrary reduced frame models remains a natural next formalization target, but the point-frame incidence and point-collapse pillars are now checked.

---

### 16. Summary, appendix, and reproducibility targets

Files:

```text
LeanCfgProject/SemanticBridgeSummary.lean
LeanCfgProject/ICSemanticBridgeSummary.lean
LeanCfgProject/ICSemanticBridgeSummary_v2.lean
LeanCfgProject/AttackSemanticBridgeSummary.lean
LeanCfgProject/ObservedSyntacticBridgeSummary.lean
LeanCfgProject/ICSemanticBridgeSummary_v3.lean
LeanCfgProject/ObservedSyntacticPaperSummary.lean
LeanCfgProject/ICPaperArtifactSummary.lean
LeanCfgProject/ICLeanAppendixIndex.lean
LeanCfgProject/ICSubmissionSummary_v1.lean
LeanCfgProject/ICArtifactReleaseSummary.lean
LeanCfgProject/ICArtifactAppendixCoverage.lean
LeanCfgProject/ICFastCI.lean
LeanCfgProject/ICFullPaperSummary_v1.lean
LeanCfgProject/ICSubmissionSummary_v2.lean
LeanCfgProject/ICArtifactFreezeIndex.lean
LeanCfgProject/ICReproducibilitySummary.lean
LeanCfgProject/ICFastCI_v2.lean
LeanCfgProject/ICFullPaperSummary_v2.lean
LeanCfgProject/ICSubmissionSummary_v3.lean
LeanCfgProject/ICSubmissionSummary_v4.lean
LeanCfgProject/ObservedLearningPaperSummary.lean
LeanCfgProject/ObservedLearningPaperSummary_v2.lean
LeanCfgProject/ICSubmissionSummary_v11.lean
LeanCfgProject/PointFrameCorollaries.lean
LeanCfgProject/ReducedFrameModelCoreDefs.lean
LeanCfgProject/ObservedLearningQueryModel.lean
LeanCfgProject/FaithfulRepresentativeCorollaries.lean
LeanCfgProject/FiniteObservedBasisCorollaries.lean
LeanCfgProject/ICPaperFormalizationSummary_v27.lean
LeanCfgProject/ICSubmissionSummary_v6.lean
LeanCfgProject/FrameModelCoreBasic.lean
LeanCfgProject/CanonicalFrameModelCorollaries.lean
LeanCfgProject/ObservedSubsetStability.lean
LeanCfgProject/PointFrameLearningBridge.lean
LeanCfgProject/ReducedFrameModelPaperSummary.lean
LeanCfgProject/ICPaperFormalizationSummary_v28.lean
LeanCfgProject/ICSubmissionSummary_v7.lean
LeanCfgProject/ObservedLearningStablePackage_v27.lean
LeanCfgProject/CanonicalPointFrameStablePackage_v27.lean
LeanCfgProject/ObservedFiniteBasisStablePackage_v27.lean
LeanCfgProject/ICSubmissionSafeExpansion_v27.lean
LeanCfgProject/ICSubmissionSummary_v8.lean
LeanCfgProject/ObservedMembershipEquivalence_v27.lean
LeanCfgProject/PointFrameIncidenceTransport_v27.lean
LeanCfgProject/FiniteResidualBasisTransport_v27.lean
LeanCfgProject/ObservedConceptObjectReleaseIndex_v27.lean
LeanCfgProject/ICSubmissionSummary_v9.lean
LeanCfgProject/ObservedSubsetTransportPackage_v27.lean
LeanCfgProject/PointFrameTransportSummary_v27.lean
LeanCfgProject/ObservedLearningSubmissionAudit_v27.lean
LeanCfgProject/ObservedConceptSubmissionIndex_v27.lean
LeanCfgProject/ICSubmissionSummary_v10.lean
LeanCfgProject/ObservedLearningReleaseTheorems_v27.lean
LeanCfgProject/PointFrameReleaseTheorems_v27.lean
LeanCfgProject/FiniteBasisReleaseTheorems_v27.lean
LeanCfgProject/ICArtifactAudit_v27.lean
LeanCfgProject/ICFormalizationReleaseIndex_v27.lean
```

These modules are intentionally lightweight.  Their role is to give stable paper-facing import targets, appendix-index targets, and fast CI targets.

The current recommended top-level target is:

```text
LeanCfgProject.ICSubmissionSummary_v14
```

If this module builds, Lean has checked the current v27.2 final-index import graph, including the observed-learning layer, canonical point-frame incidence core, finite residual-basis transport layer, release-facing audit targets, release-regression and certificate layers, theorem-table index, frozen artifact index, FORMALIZATION supplement certificate, submission checklist, and final smoke test, through the normal dependency system.

---


## Theorem-body item1--item5 additions checked by CI #207

After the v27.2 final-index snapshot, the development was extended by a new
theorem-body chain focused on the mathematical core of the paper rather than on
release packaging.  Items 1--4 were checked at commit `b1e651e` by Lean CI #195.
The current item 5 finite-example extension is checked at commit `702dcf5` by
Lean CI #207.

The checked theorem-body modules are:

```text
LeanCfgProject/ResidualConceptNucleus.lean
LeanCfgProject/PointwiseAdequacy.lean
LeanCfgProject/UniformAdequacy.lean
LeanCfgProject/ObservedQuotientResidual.lean
LeanCfgProject/ObservedQuotientClosure.lean
LeanCfgProject/ObservedQuotientClosureImage.lean
LeanCfgProject/ObservedSyntacticSaturation.lean
LeanCfgProject/ObservedFactorMinimality.lean
```

The main new checked declarations include:

```text
conceptClosure_setMul_subset
conceptProduct_closure_closure_eq
conceptProduct_unital_on_concept_extents
commonContexts_conceptClosure_eq
pointwiseAdequacy_iff_commonContexts_eq
pointwiseAdequacy_iff_residual_subset_closure
commonContexts_eq_iff_residual_subset_closure
pointwiseAdequacy_equivalences
UniformAdequacyOn
SingletonAdequacyOn
SingleObservedSyntacticBlockOn
uniformAdequacyOn_iff_singletonAdequacyOn_residual
singletonAdequacyOn_iff_singleObservedSyntacticBlockOn_residual
uniformAdequacy_equivalences_for_residual
quotient_residual_preimage_eq
quotient_residual_image_surj
quotient_commonContexts_preimage_eq
quotient_conceptClosure_preimage_eq
quotient_preimage_isConceptExtent
quotient_setMul_image_eq
quotient_residual_image_eq
quotient_conceptClosure_image_eq
quotient_pointConcept_image_eq
quotient_conceptProduct_image_eq
sameObservedSyntactic_mem_iff
image_pullback_eq_of_fibers_sameObservedSyntactic
observedSyntacticFactor_residual_preimage_eq
observedSyntacticFactor_residual_image_eq
observedSyntacticFactor_conceptClosure_preimage_eq
observedSyntacticFactor_conceptClosure_image_eq
observedSyntacticFactor_conceptProduct_image_eq
sameObservedSyntactic_of_factor_eq_of_pullback
factor_kernel_subset_sameObservedSyntactic
image_pullback_iff_fibers_sameObservedSyntactic
imagePullbackFactor_residual_image_eq
imagePullbackFactor_conceptClosure_image_eq
imagePullbackFactor_conceptProduct_image_eq
residual_A_E_eq
closure_singleton_E_eq
closure_singleton_A_ne_residual_A_E
diamond_two_block_pointwise_adequacy_witness
residual_zero_zero_eq
closure_singleton_zero_eq
closure_singleton_zero_ne_residual_zero_zero
not_sameObservedSyntactic_zero_one
zmod3_failure_witness
residual_one_BB_eq
sameObservedSyntactic_AA_AB
S_single_observed_syntactic_block
closure_singleton_AB_eq
endpoint_monoid_aperiodic_adequacy_witness
```

These modules add the following verified mathematical content.

First, residual concept closure is multiplicative/nuclear with respect to subset
product:

```text
cl_S(A) · cl_S(B) ⊆ cl_S(A · B).
```

Consequently the closed extents carry the expected closure-induced product, and
the checked file also verifies the basic unit behavior of `ConceptProduct` on
concept extents.

Second, pointwise adequacy of a sound state image inside a two-sided residual is
equivalent to both equality of common-context intents and residual coverage:

```text
cl_S(U) = Res_S(a,b)
  iff
U^▷ = Res_S(a,b)^▷
  iff
Res_S(a,b) ⊆ cl_S(U),
```

where `U^▷` is represented in Lean by `CommonContexts S U`.

Third, uniform adequacy over nonempty subsets of a residual is equivalent to
singleton adequacy and to the residual lying in one observed-syntactic block:

```text
(∀ nonempty U ⊆ R, cl_S(U)=R)
  iff
(∀ rho∈R, cl_S({rho})=R)
  iff
(∀ rho sigma∈R, rho ≈_S sigma).
```

The Lean statement is slightly stronger than the nonempty-residual presentation:
if the residual is empty, the three predicates are vacuously true.

Fourth, quotient/factor-map invariance is verified for an abstract surjective
multiplicative observed factor map `π : Q -> Qbar`.  If `Sbar` has exactly `S`
as its pullback, namely `π x ∈ Sbar iff x ∈ S`, then Lean checks:

```text
π^{-1}(Res_{Sbar}(πa,πb)) = Res_S(a,b),
π(Res_S(a,b)) = Res_{Sbar}(πa,πb),
CommonContexts_S(π^{-1}Ubar)
  =
π-frame-preimage(CommonContexts_{Sbar}(Ubar)),
cl_S(π^{-1}Ubar) = π^{-1}(cl_{Sbar}(Ubar)),
π(cl_S(W)) = cl_{Sbar}(π(W)),
π(ConceptProduct_S(A,B))
  =
ConceptProduct_{Sbar}(π(A),π(B)).
```

The same image theorem is also checked for singleton point concepts.

Fifth, the abstract factor-map theorem is connected back to observed syntactic
equivalence.  If the fibers of `π` are contained in `SameObservedSyntactic S`,
then `S` is exactly the pullback of its image:

```text
π^{-1}(π(S)) = S.
```

Conversely, if a multiplicative factor map has exact observed pullback, then
each fiber is contained in `SameObservedSyntactic S`:

```text
πx = πy  implies  x ≈_S y.
```

In particular, the checked theorem

```text
image_pullback_iff_fibers_sameObservedSyntactic
```

expresses the equivalence between exact image-pullback preservation and fiber
containment in the observed syntactic congruence.  This gives the Lean-checked
core of the statement that `SameObservedSyntactic` is the maximal kernel relation
compatible with the observed subset `S`, and that exact observed factor maps
factor through the observed-syntactic information.

Sixth, three finite adequacy examples are checked as theorem-body modules rather
than as release wrappers.

The diamond meet-semilattice example verifies a four-element monoid witness in
which a two-sided residual `Res_S(A,E)` is `{E,A}`, the singleton closure
`cl_S({E})` reaches that residual, while `cl_S({A})` remains smaller.  This is a
finite checked example separating raw singleton images from residual-concept
adequacy.

The three-element cyclic monoid example, presented as a `Z/3` failure witness,
verifies that for `S = {0,1}` and `U = {0}`, one has `Res_S(0,0)=S` but
`cl_S(U)=U`, and also verifies `¬ SameObservedSyntactic S 0 1`.  This gives a
small checked obstruction showing that nontrivial residual coverage is not
automatic.

The endpoint-monoid example verifies an aperiodic witness with
`S = {AA,AB}` and `U = {AB}`.  Lean checks `Res_S(1,BB)=S`, that all elements of
`S` lie in one `SameObservedSyntactic` block, and that `cl_S({AB})=S`.  This is
the current checked finite example connecting single-block adequacy with an
aperiodic non-group monoid.

These item 5 examples are theorem-body additions.  They are not release
certificates, submission checklists, audit wrappers, or manifest modules.


## v27.1 release-index additions checked by CI #180

The CI #180 run checked the current release-facing path through:

```text
LeanCfgProject.ICSubmissionSummary_v14
LeanCfgProject.ICFormalizationReleaseIndex_v27
LeanCfgProject.ICArtifactAudit_v27
LeanCfgProject.ObservedLearningReleaseTheorems_v27
LeanCfgProject.PointFrameReleaseTheorems_v27
LeanCfgProject.FiniteBasisReleaseTheorems_v27
```

The release-index layer packages the recent v27.1 additions as paper-facing audit targets.  In particular, it records that:

- observed membership equality identifies the canonical observed frame structure, frame residuals, single-block predicates, and observed relations;
- observed subset equality and observed-membership transcripts transport `SameObservedSyntactic`, `CanonicalPoint`, `CanonicalFrame`, `FrameResidual`, and `SingleObservedBlock`;
- canonical point-frame incidence and point collapse are stable under observed membership equality;
- faithful representatives transport the canonical point-frame incidence and point-collapse data;
- finite frame-residual basis facts are available for finite observed carriers and can be transported along observed-membership equivalence;
- the release-facing summary target `ICSubmissionSummary_v11` imports these packages through Lean's normal dependency graph.

Warnings reported in CI #180 concern linter suggestions such as unused `Fintype` hypotheses in theorem statements; they do not indicate failed proof obligations.

---

## v27.2 release-certificate and final-index additions checked after CI #180

After the CI #180 release-index state, the development was extended through
the v27.2 release-regression, release-certificate, and final-index layers.  This
extension is now checked at commit `0e6dbb5` by Lean CI #184.  The current
checked top-level target is:

```text
LeanCfgProject.ICSubmissionSummary_v14
```

The v27.2 path includes the following paper-facing targets:

```text
LeanCfgProject.ICSubmissionSummary_v14
LeanCfgProject.ICFinalSmokeTest_v27_2
LeanCfgProject.ICPaperSubmissionChecklist_v27_2
LeanCfgProject.ICFormalizationSupplementCertificate_v27_2
LeanCfgProject.ICDependencyCertificate_v27_2
LeanCfgProject.ICFrozenArtifactIndex_v27_2
LeanCfgProject.ICTheoremTableIndex_v27_2
LeanCfgProject.ICPaperClaimIndex_v27_2
LeanCfgProject.ICSubmissionSummary_v13
LeanCfgProject.ICReleaseSmokeTest_v27_2
LeanCfgProject.ICAppendixReleaseIndex_v27_2
LeanCfgProject.ICPaperFormalizationBridge_v27_2
LeanCfgProject.FiniteBasisCertificate_v27_2
LeanCfgProject.PointFrameCertificate_v27_2
LeanCfgProject.ObservedLearningCertificate_v27_2
LeanCfgProject.ICReleaseCertificate_v27_2
LeanCfgProject.ICArtifactMetadata_ci180
LeanCfgProject.ICSubmissionSummary_v12
LeanCfgProject.ICReproducibilityIndex_ci180
LeanCfgProject.ICReleaseManifest_v27_2
LeanCfgProject.FiniteBasisReleaseRegression_v27_2
LeanCfgProject.PointFrameReleaseRegression_v27_2
LeanCfgProject.ObservedLearningReleaseRegression_v27_2
```

The new layer records that:

- the release metadata now records commit `0e6dbb5`, Lean CI #184, and
  `growupkuriyama-hub` as pusher, while preserving `c6c1705` / CI #180 as the earlier release-index checkpoint;
- the release-certificate layer collects the manifest, reproducibility index,
  release index, and v12 submission target;
- observed-learning, point-frame, and finite-basis certificate modules re-expose
  the corresponding release-regression theorems under stable paper-facing names;
- the paper formalization bridge connects the v27.2 paper text to the checked
  CI #180/v12 artifact state;
- the theorem-table index, frozen artifact index, dependency certificate, and
  FORMALIZATION supplement certificate provide stable names for the paper
  appendix and reproducibility supplement;
- the final smoke test and `ICSubmissionSummary_v14` give a compact target for
  the end-of-day artifact state.

These v27.2 modules are deliberately conservative: they do not add new low-level
mathematical assumptions.  Their role is to make the checked theorem/file
correspondence, release metadata, and paper-facing top-level target explicit and
stable inside Lean.

---

## Main theorem/file correspondence

| Paper-level component | Lean files |
|---|---|
| Descriptor architecture | `Step25_Test.lean`, `FullArchitecture_Test.lean` |
| Observation quotients and pointed boundary | `LanguageQuotient.lean`, `ObservationFinite.lean` |
| Observation counterexamples | `ObservationCounterexample.lean`, `ObservationCounterexample_v2.lean`, `ObservationSignatureCounterexample.lean` |
| Powerset-valued semantics | `StateSemantics.lean` |
| Residual concept semantics | `ResidualConcept.lean` |
| Descriptor-level carrier semantics | `DescriptorSemantics.lean`, `DescriptorResidualSemantics.lean`, `CarrierConceptSemantics.lean` |
| Frame soundness and frame-intent preservation | `FrameSoundness.lean`, `SaturationFrameBridge.lean`, `FrameIntentClosureBridge.lean`, `ClosedStageFrameBridge.lean`, `ClosedStageFrameIntentStability.lean`, `LocalStoppingFrameResidual.lean`, `FiniteStoppingFrameResidual.lean` |
| Carrier saturation correctness | `FiniteSaturation.lean`, `CarrierSaturationCorrectness.lean`, `CarrierSaturationLeast.lean` |
| Saturation-computed concept semantics | `CarrierSaturationConceptSoundness.lean` |
| Closed-stage correctness | `SaturationStability.lean`, `ClosedStageConceptBridge.lean`, `SaturationMonotoneChain.lean`, `ClosedStageAlgorithmCorrectness.lean`, `ClosedStageEquivalences.lean`, `ClosedStageConceptStability.lean`, `ClosedStageRuleSemantics.lean`, `LaterClosedStageClosure.lean` |
| Local stopping correctness | `LocalStoppingCorrectness.lean`, `LocalStoppingRuleSemantics.lean`, `LocalStoppingFrameResidual.lean` |
| Bounded finite stopping | `FiniteStoppingCore.lean`, `MeasureStoppingCriterion.lean`, `FiniteSaturationMeasure.lean`, `FiniteStoppingFrameResidual.lean`, `FiniteStoppedFrameAdequacy.lean` |
| Observed syntactic concept object | `ObservedSyntacticConcept.lean`, `ObservedSyntacticCongruence.lean` |
| Residual-concept nucleus, adequacy, and observed factor-map invariance | `ResidualConceptNucleus.lean`, `PointwiseAdequacy.lean`, `UniformAdequacy.lean`, `ObservedQuotientResidual.lean`, `ObservedQuotientClosure.lean`, `ObservedQuotientClosureImage.lean`, `ObservedSyntacticSaturation.lean`, `ObservedFactorMinimality.lean` |
| Canonical residual closure system | `CanonicalResidualClosureSystem.lean`, `ObservedSyntacticResidualCorollaries.lean` |
| Syntactic-block adequacy | `ObservedSyntacticBlockAdequacyCorollaries.lean`, `ObservedSyntacticPaperCorollaries.lean` |
| Finite adequacy examples | `DiamondSemilatticeAdequacy.lean`, `ZMod3FailureExample.lean`, `EndpointMonoidAdequacy.lean` |
| K4 adequacy witness | `K4ResidualAdequacyExample.lean`, `K4AdequacyStrictness.lean`, `K4ConceptCollapse.lean`, `K4AdequacyPaperSummary.lean`, `AdequacyBridgeSummary.lean` |
| Carrier observed-block adequacy | `CarrierObservedAdequacy.lean`, `CarrierObservedAdequacyCorollaries.lean` |
| Finite observed-learning layer | `ObservedFrameStructure.lean`, `ObservedFrameStructureDecidable.lean`, `FiniteObservedFrameBasis.lean`, `FiniteSetQueryReconstruction.lean`, `FaithfulRepresentatives.lean`, `ObservedLearningExamples.lean`, `FiniteObservedConceptIdentification.lean`, `ObservedLearningCorollaries.lean`, `ObservedLearningConstructibilitySummary.lean`, `ObservedLearningPaperSummary.lean`, `ObservedLearningPaperSummary_v2.lean` |
| Canonical point-frame incidence and reduced-frame core | `SingletonClosureIncidence.lean`, `CanonicalPointFrame.lean`, `UniversalFrameModelCore.lean`, `PointFrameCorollaries.lean`, `ReducedFrameModelCoreDefs.lean`, `FrameModelCoreBasic.lean`, `CanonicalFrameModelCorollaries.lean`, `CanonicalPointFrameStablePackage_v27.lean`, `PointFrameIncidenceTransport_v27.lean`, `PointFrameTransportSummary_v27.lean`, `PointFrameReleaseTheorems_v27.lean` |
| Paper-facing summary, release-index, release-certificate, and final-index targets | `ICSubmissionSummary_v14.lean`, `ICFinalSmokeTest_v27_2.lean`, `ICPaperSubmissionChecklist_v27_2.lean`, `ICFormalizationSupplementCertificate_v27_2.lean`, `ICDependencyCertificate_v27_2.lean`, `ICFrozenArtifactIndex_v27_2.lean`, `ICTheoremTableIndex_v27_2.lean`, `ICPaperClaimIndex_v27_2.lean`, `ICSubmissionSummary_v13.lean`, `ICReleaseCertificate_v27_2.lean`, `ICArtifactMetadata_ci180.lean`, `ICSubmissionSummary_v12.lean`, `ICSubmissionSummary_v11.lean`, `ICFormalizationReleaseIndex_v27.lean`, `ICArtifactAudit_v27.lean` |

---

## Current mathematical interpretation

The current Lean artifact supports the following conservative paper-level reading.

The presentation-level architecture, observation relations, concrete observation counterexamples, powerset-valued state semantics, residual concept semantics, carrier semantic bridges, frame soundness, finite saturation correctness, least closed solution characterization, saturation-computed concept semantics, closed-stage correctness, local stopping correctness, bounded finite stopping, observed syntactic congruence, canonical residual closure system, K4 adequacy witnesses, and carrier observed-block adequacy all build successfully in Lean 4 under the repository CI policy.

In paper terms, the verified semantic bridge is:

```text
E_h(G) -> P(Q) -> Concepts(Q, q[L])
```

with the following additional verified facts:

- carrier saturation computes carrier state semantics;
- saturation is the least closed simultaneous solution of terminal and binary inclusions;
- saturation-computed concept semantics agrees with carrier concept semantics;
- closed saturation stages compute state and concept semantics;
- local stopping `U_(N+1) = U_N` implies closedness and semantic correctness;
- under finite state and finite observation assumptions, a bounded closed stage exists;
- a bounded carrier stage computes state semantics and residual concept semantics;
- typed two-sided frames survive as residual bounds and as intent-side common contexts;
- concept closure and two-sided residuals are saturated by the observed syntactic congruence;
- the observed syntactic congruence is maximal among two-sided stable relations preserving the observed subset;
- concept extents are exactly residual intersections;
- finite K4 examples witness strict raw-image inclusion but residual-concept adequacy;
- carrier states are frame-adequate under the checked nonempty single observed-syntactic-block hypothesis;
- the finite `q`-observed frame-concept object is identified once the observed subset `S` is identified;
- finite observed frame bases exist for concept closures when `Q` is finite;
- faithful representatives identify the observed subset and therefore the canonical observed frame structure;
- singleton point concepts represent two-sided incidence against frame residuals;
- equality of canonical point concepts is exactly observed syntactic equivalence;
- observed subset equality and observed membership transcripts transport canonical points, canonical frames, frame residuals, single-block predicates, observed relations, and point-frame incidence;
- observed-membership equivalence is formalized as a reusable transport interface;
- finite residual-basis facts are packaged and transported along observed-membership equivalence;
- the v27.1 release-facing audit target `ICSubmissionSummary_v11` imports the observed-learning, point-frame, finite-basis, and release-index packages;
- residual concept closure is multiplicative/nuclear with respect to subset product;
- pointwise residual adequacy is equivalent to common-context equality and residual coverage;
- uniform residual adequacy is equivalent to singleton adequacy and to the single observed-syntactic-block condition;
- residuals, common contexts, concept closures, point concepts, and concept products are preserved by exact surjective multiplicative observed factor maps;
- exact image-pullback preservation is equivalent to factor-map fibers being contained in the observed syntactic congruence;
- the diamond meet-semilattice, three-element cyclic monoid, and endpoint monoid give checked finite examples of residual-concept adequacy, failure of automatic residual coverage, and aperiodic single-block adequacy.

---

## Formalization boundary

The current Lean artifact does **not** claim that:

- the entire accompanying paper is fully formalized;
- CFG equivalence is solved;
- a canonical CFG presentation has been constructed;
- every fixed-`h` descriptor is a language-level invariant;
- all residual concepts are exactly realized by typed presentation states without additional hypotheses;
- finite residual-concept bases have been constructed for broad classes of fixed-`h` substitutable CFLs;
- the pointed-boundary theorem has been developed into a complete standalone regular-language theory;
- the normal-coset and mod-`k` families have all been formalized;
- the full abstract complete-lattice isomorphism theorem for arbitrary reduced frame models has been formalized;
- polynomial-time complexity bounds such as `O(|Q|^4)` have been formalized inside Lean.

The artifact verifies an unconditional bounded finite-stopping theorem only under both finite state and finite observation carrier assumptions.  It also verifies observed-syntactic-block adequacy only under the stated nonempty single-block hypothesis.

These boundaries are intentional: the paper separates checked formalization results from open problems and future formalization targets.

---

## Suggested citation in the paper

A concise artifact statement for the paper could be:

```text
The accompanying Lean 4 artifact was checked at commit 702dcf5 by GitHub
Actions Lean CI #207, pushed by growupkuriyama-hub.  The current
theorem-body target is LeanCfgProject.EndpointMonoidAdequacy.  The previous
theorem-body item1--item4 target LeanCfgProject.ObservedFactorMinimality was
checked at commit b1e651e / Lean CI #195.  The previous paper-facing final-index
target LeanCfgProject.ICSubmissionSummary_v14 was checked at commit 0e6dbb5 /
Lean CI #184, with the earlier release-index checkpoint at commit c6c1705 /
Lean CI #180.  The development verifies the descriptor architecture, residual
concept semantics, carrier saturation correctness, bounded finite-stopping
results, observed syntactic congruence and maximality, the canonical residual
closure system, K4 adequacy witnesses, carrier-level observed-block adequacy,
the finite observed-learning layer, the canonical point-frame incidence core
for the reduced representation viewpoint, and the v27.1/v27.2 paper-facing
release, certificate, and final-index packages.  The theorem-body extension
additionally verifies the multiplicative nucleus property of residual concept
closure, pointwise and uniform adequacy equivalences, abstract factor-map
invariance for residuals/common contexts/concept closures/point concepts/concept
products, the equivalence between exact observed image-pullback preservation and
fiber containment in the observed syntactic congruence, and three finite
adequacy examples: a diamond meet-semilattice witness, a three-element cyclic
monoid / Z/3 failure witness, and an endpoint-monoid aperiodic adequacy witness.
The artifact intentionally does not claim a full formalization of the paper, the
full abstract universal representation theorem, an actual quotient-monoid
instance for every presentation inside Lean, or an unrestricted adequacy
theorem.
```

---

## Future formalization targets

Natural next targets include:

1. preparing a public release tag corresponding to the commit `0e6dbb5` / Lean CI #184 / `ICSubmissionSummary_v14` artifact snapshot;
2. preparing an archived artifact snapshot with a persistent identifier;
3. adding a lightweight online blueprint linking paper statements to declarations;
4. formalizing the full abstract reduced-frame-model isomorphism theorem;
5. formalizing the normal-coset and mod-`k` adequacy families;
6. formalizing more concrete faithful-representative examples for observed learning;
7. formalizing the actual quotient monoid/congruence instance for `SameObservedSyntactic`, beyond the currently checked abstract factor-map invariance theorem;
8. developing restricted adequacy theorems for additional controlled subclasses;
9. keeping future extensions modular and preserving the current CI discipline.
