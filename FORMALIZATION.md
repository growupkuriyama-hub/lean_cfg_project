# Formalization Supplement

Lean 4 artifact for the paper:

**Residual Concept Semantics for Two-Sided Fixed-`h` CFG Presentations**

Author: Takayuki Kuriyama  
Repository: `growupkuriyama-hub/lean_cfg_project`  
Current checked artifact snapshot: commit `370bdcb`  
GitHub Actions: Lean CI #157 passed

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
commit: 370bdcb
CI run: Lean CI #157
status: passed
```

The current fast paper-facing target is:

```bash
lake build LeanCfgProject.ICSubmissionSummary_v3
```

The CI also keeps repository-level checks that reject placeholder proof commands and project-level axiom declarations in Lean source files.

At the current checked snapshot, the artifact verifies the following major groups of results:

- finite monoid-typed CFG descriptor architecture;
- observation quotients and pointed-boundary theorems;
- concrete counterexamples showing that naive finite observation is not concatenation-compatible;
- powerset-valued state semantics under multiplicative word observations;
- residual Galois connection, concept closure, concept extents, and concept products;
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
- paper-facing summary and appendix-index targets for reproducibility.

---

## How to reproduce the current check

From the repository root, run:

```bash
lake build LeanCfgProject.ICSubmissionSummary_v3
```

For a broader paper-facing import check, run:

```bash
lake build LeanCfgProject.ICFullPaperSummary_v2
lake build LeanCfgProject.ICArtifactFreezeIndex
lake build LeanCfgProject.ICReproducibilitySummary
```

For ordinary development, the repository uses a lightweight CI strategy: instead of explicitly building every historical experimental target one by one, it builds high-level summary modules whose imports force Lean to check the relevant dependency graph.

The current top-level paper-facing summary modules include:

```text
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

### 12. Carrier-level observed-block adequacy

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

### 13. Summary, appendix, and reproducibility targets

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
```

These modules are intentionally lightweight.  Their role is to give stable paper-facing import targets, appendix-index targets, and fast CI targets.

The current recommended top-level target is:

```text
LeanCfgProject.ICSubmissionSummary_v3
```

If this module builds, Lean has checked the current paper-facing import graph through the normal dependency system.

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
| Canonical residual closure system | `CanonicalResidualClosureSystem.lean`, `ObservedSyntacticResidualCorollaries.lean` |
| Syntactic-block adequacy | `ObservedSyntacticBlockAdequacyCorollaries.lean`, `ObservedSyntacticPaperCorollaries.lean` |
| K4 adequacy witness | `K4ResidualAdequacyExample.lean`, `K4AdequacyStrictness.lean`, `K4ConceptCollapse.lean`, `K4AdequacyPaperSummary.lean`, `AdequacyBridgeSummary.lean` |
| Carrier observed-block adequacy | `CarrierObservedAdequacy.lean`, `CarrierObservedAdequacyCorollaries.lean` |
| Paper-facing summary targets | `ICSubmissionSummary_v3.lean`, `ICFullPaperSummary_v2.lean`, `ICFastCI_v2.lean`, `ICReproducibilitySummary.lean`, `ICArtifactFreezeIndex.lean`, `ICArtifactAppendixCoverage.lean` |

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
- carrier states are frame-adequate under the checked nonempty single observed-syntactic-block hypothesis.

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
- the endpoint-monoid non-coset witness and the normal-coset / mod-`k` families have all been formalized.

The artifact verifies an unconditional bounded finite-stopping theorem only under both finite state and finite observation carrier assumptions.  It also verifies observed-syntactic-block adequacy only under the stated nonempty single-block hypothesis.

These boundaries are intentional: the paper separates checked formalization results from open problems and future formalization targets.

---

## Suggested citation in the paper

A concise artifact statement for the paper could be:

```text
The accompanying Lean 4 artifact was checked at commit 370bdcb by GitHub
Actions Lean CI #157.  The top-level paper-facing target is
LeanCfgProject.ICSubmissionSummary_v3.  The development verifies the descriptor
architecture, residual concept semantics, carrier saturation correctness,
bounded finite-stopping results, observed syntactic congruence and maximality,
the canonical residual closure system, K4 adequacy witnesses, and carrier-level
observed-block adequacy.  The artifact intentionally does not claim a full
formalization of the paper or an unrestricted adequacy theorem.
```

---

## Future formalization targets

Natural next targets include:

1. preparing a public release tag corresponding to the paper version;
2. preparing an archived artifact snapshot with a persistent identifier;
3. adding a lightweight online blueprint linking paper statements to declarations;
4. formalizing the endpoint-monoid non-coset witness;
5. formalizing the normal-coset and mod-`k` adequacy families;
6. investigating quotient invariance of the observed syntactic concept object;
7. developing restricted adequacy theorems for additional controlled subclasses;
8. keeping future extensions modular and preserving the current CI discipline.
