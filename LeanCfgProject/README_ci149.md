# lean_cfg_project

Lean 4 artifact for the paper:

**Residual Concept Semantics for Two-Sided Fixed-`h` CFG Presentations**

Author: Takayuki Kuriyama  
Repository: `growupkuriyama-hub/lean_cfg_project`  
Current verified artifact snapshot: commit `04d0d88`  
GitHub Actions: Lean CI #149 passed

---

## Overview

This repository contains an experimental Lean 4 formalization supporting a semantic bridge from two-sided fixed-`h` context-free grammar descriptors to residual concept semantics.

The paper studies finite presentation-level descriptors `E_h(G)` obtained from CFG presentations refined by a fixed finite monoid homomorphism `h : Sigma* -> M`.  The main semantic bridge has the form

```text
E_h(G) -> P(Q) -> Concepts(Q, q[L])
```

where `q : Sigma* -> Q` is a multiplicative word observation.

The goal is **not** to claim a canonical CFG presentation or to solve CFG equivalence.  The verified goal is more modest and more precise: fixed-`h` two-sided CFG presentation descriptors admit sound powerset-valued and residual-concept semantic interpretations inside a language-level residual/concept universe.

The Lean development verifies selected components of this bridge, including:

- finite monoid-typed CFG descriptor architecture;
- `h`-typed observation quotients and boundary theorems;
- concrete counterexamples showing that naive finite observation is not concatenation-compatible;
- powerset-valued state semantics;
- residual Galois connection and concept closure;
- carrier-level descriptor semantics;
- frame soundness and frame-to-residual / frame-to-intent preservation;
- finite-stage carrier saturation correctness;
- least closed solution formulation for saturation;
- saturation-computed concept semantics;
- closed-stage stability and algorithmic correctness;
- local stopping correctness for the checkable condition `U_(N+1) = U_N`;
- local-stopping rule semantics and frame/residual preservation;
- unconditional finite-stopping via an indicator-cardinality measure for finite state sets and finite observations;
- bounded carrier-stage computation of state semantics and residual concept semantics;
- bounded finite-stage preservation of two-sided frame residual/intent information;
- a general frame-adequacy criterion reducing equality of residual concepts to a coverage condition;
- a finite K4 residual-adequacy worked example, including strict raw-image and nontrivial concept-collapse witnesses;
- the observed syntactic congruence `SameObservedSyntactic` for an arbitrary monoid pair `(Q,S)`;
- saturation of concept closures and two-sided residuals under the observed syntactic congruence;
- maximality of the observed syntactic congruence among two-sided stable `S`-preserving relations;
- the canonical residual closure system: closed extents are exactly intersections of two-sided residuals;
- carrier-level observed-syntactic-block adequacy for standard `h` and factor-through-`h` observations;
- summary CI targets for the paper appendix.

---

## Current CI status

The artifact is checked by GitHub Actions using `leanprover/lean-action@v1` with mathlib cache enabled.

Current checked snapshot:

```text
commit: 04d0d88
CI run: Lean CI #149
status: passed
```

The CI policy rejects Lean source files containing:

- `sorry`
- project-level `axiom` declarations

Current status under the repository CI policy:

```text
sorry: 0
project-level axiom declarations: 0
GitHub Actions: green
```

---

## How to build

From the repository root, build individual modules with `lake build`.  The CI currently checks the following targets:

```bash
lake build LeanCfgProject.Step25_Test
lake build LeanCfgProject.FullArchitecture_Test
lake build LeanCfgProject.StateSemantics
lake build LeanCfgProject.ResidualConcept
lake build LeanCfgProject.LanguageQuotient
lake build LeanCfgProject.DescriptorSemantics
lake build LeanCfgProject.DescriptorResidualSemantics
lake build LeanCfgProject.ObservationCounterexample
lake build LeanCfgProject.ObservationCounterexample_v2
lake build LeanCfgProject.ObservationFinite
lake build LeanCfgProject.CarrierConceptSemantics
lake build LeanCfgProject.FiniteSaturation
lake build LeanCfgProject.ObservationSignatureCounterexample
lake build LeanCfgProject.SemanticBridgeSummary
lake build LeanCfgProject.FrameSoundness
lake build LeanCfgProject.CarrierSaturationCorrectness
lake build LeanCfgProject.SaturationFrameBridge
lake build LeanCfgProject.CarrierSaturationLeast
lake build LeanCfgProject.CarrierSaturationConceptSoundness
lake build LeanCfgProject.FrameIntentClosureBridge
lake build LeanCfgProject.ICSemanticBridgeSummary
lake build LeanCfgProject.SaturationStability
lake build LeanCfgProject.ClosedStageConceptBridge
lake build LeanCfgProject.ClosedStageFrameBridge
lake build LeanCfgProject.SaturationMonotoneChain
lake build LeanCfgProject.ClosedStageAlgorithmCorrectness
lake build LeanCfgProject.ICSemanticBridgeSummary_v2
lake build LeanCfgProject.FiniteCoverageStopping
lake build LeanCfgProject.ClosedStageEquivalences
lake build LeanCfgProject.ClosedStageConceptStability
lake build LeanCfgProject.ClosedStageFrameIntentStability
lake build LeanCfgProject.ClosedStageRuleSemantics
lake build LeanCfgProject.LaterClosedStageClosure
lake build LeanCfgProject.LocalStoppingCorrectness
lake build LeanCfgProject.LocalStoppingRuleSemantics
lake build LeanCfgProject.LocalStoppingFrameResidual
lake build LeanCfgProject.AttackSemanticBridgeSummary
lake build LeanCfgProject.FiniteStoppingCore
lake build LeanCfgProject.MeasureStoppingCriterion
lake build LeanCfgProject.FiniteSaturationMeasure
lake build LeanCfgProject.FiniteStoppingFrameResidual
lake build LeanCfgProject.FrameAdequacyCriterion
lake build LeanCfgProject.K4ResidualAdequacyExample
lake build LeanCfgProject.K4AdequacyStrictness
lake build LeanCfgProject.K4ConceptCollapse
lake build LeanCfgProject.FiniteStoppedFrameAdequacy
lake build LeanCfgProject.AdequacyBridgeSummary
lake build LeanCfgProject.ObservedSyntacticConcept
lake build LeanCfgProject.ObservedSyntacticCongruence
lake build LeanCfgProject.CanonicalResidualClosureSystem
lake build LeanCfgProject.CarrierObservedAdequacy
```

---

## Main verified layers

The project is best read as a sequence of connected layers.

### 1. Descriptor architecture

Files:

```text
LeanCfgProject/Step25_Test.lean
LeanCfgProject/FullArchitecture_Test.lean
```

This layer formalizes the basic fixed-finite-monoid typing infrastructure:

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
- a retraction-style interface;
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

This layer defines language-level observation relations and their stabilized variants.

Main declarations include:

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

It formalizes the distinction between finite but non-composition-compatible observation quotients, unpointed syntactic observation as a two-sided stable refinement, and pointed observation, which collapses to ordinary syntactic context equivalence together with the kernel of `h`.

The concrete counterexample modules verify, for the language `L = {ab, cd}` and the parity observation, that the naive finite `h`-typed observation is not generally compatible with concatenation.

Main counterexample declarations include:

```text
parityHom
counterexampleLanguage
same_observation_a_c
same_observation_b_b
not_same_observation_ab_cb
naive_observation_not_concat_compatible
observationSignature_a_eq_c
observationSignature_ab_ne_cb
observationSignature_not_concat_compatible
```

---

### 3. Powerset-valued state semantics

File:

```text
LeanCfgProject/StateSemantics.lean
```

This layer defines abstract powerset-valued semantics for languages and grammar states under a multiplicative word observation `q : Sigma* -> Q`.

Main declarations include:

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

The key mathematical idea is that if `q` is multiplicative, then image semantics turns concatenation into subset multiplication:

```text
q[Y Z] = q[Y] q[Z]
```

Consequently, terminal and binary CFG rules are interpreted soundly as singleton insertion and subset multiplication inclusions.

---

### 4. Residual concept semantics

File:

```text
LeanCfgProject/ResidualConcept.lean
```

This layer formalizes two-sided residuals, Galois maps, concept closure, concept extents, and concept products over an abstract monoid carrier `Q`.

Main declarations include:

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

For `S = q[L]`, the relation

```text
gamma I_S (alpha, beta)  iff  alpha * gamma * beta ∈ S
```

induces a Galois connection between subsets of `Q` and subsets of `Q × Q`.  The module verifies that the induced concept closure is extensive, monotone, and idempotent, and that binary rule soundness persists after residual concept closure.

---

### 5. Finite saturation components

File:

```text
LeanCfgProject/FiniteSaturation.lean
```

This module provides the generic finite powerset-saturation framework used later by carrier-level semantics.

Main declarations include:

```text
SaturationStep
IsSaturationClosed
saturationStep_mono
SaturationIter
terminal_mem_saturationIter_one
binary_mul_mem_saturationIter_succ
```

The original module verifies the inflationary one-step saturation operator, monotonicity, finite iteration, and terminal/binary insertion lemmas.

---

### 6. Descriptor-level semantic bridge

Files:

```text
LeanCfgProject/DescriptorSemantics.lean
LeanCfgProject/DescriptorResidualSemantics.lean
LeanCfgProject/CarrierConceptSemantics.lean
```

This layer connects carrier terminal/binary rule semantics to powerset-valued and residual concept semantics.

Main declarations include:

```text
CarrierYieldSet
CarrierStateSemantics
carrier_terminal_sound
carrier_binary_rule_hbin
carrier_binary_sound
carrier_binary_sound_after_closure
carrier_binary_sound_as_conceptProduct
CarrierStartLanguage
context_yield_mem_startLanguage_aux
context_yield_mem_startLanguage
carrier_state_semantics_subset_residual
CarrierStartImage
CarrierConceptSemantics
carrierConceptSemantics_isConceptExtent
carrier_binary_sound_as_conceptSemantics
carrier_context_concept_subset_residual_closure
```

This layer verifies that carrier terminal and binary rules from the descriptor architecture are interpreted soundly by the abstract semantic layer, that carrier states map into closed residual concept extents, and that verified carrier contexts induce residual soundness.

---

### 7. Frame soundness and frame-intent preservation

Files:

```text
LeanCfgProject/FrameSoundness.lean
LeanCfgProject/SaturationFrameBridge.lean
LeanCfgProject/FrameIntentClosureBridge.lean
LeanCfgProject/ClosedStageFrameBridge.lean
LeanCfgProject/ClosedStageFrameIntentStability.lean
LeanCfgProject/LocalStoppingFrameResidual.lean
```

This layer verifies that the two-sided typed frame is not merely decorative.

It proves:

- yield-frame soundness;
- context-frame soundness under start-frame hypotheses;
- frame-to-residual soundness for the standard observation `h`;
- frame membership in the intent side of the residual concept incidence;
- preservation of frame information after saturation;
- preservation of frame information after residual concept closure;
- closed-stage versions of frame residual and frame-intent preservation;
- local-stopping versions of frame residual and frame-intent preservation.

Representative declarations include:

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
```

Mathematically, these modules support the statement that typed two-sided frames persist as residual bounds and as intent-side common contexts in the residual concept semantics, including after closed-stage stabilization and after local stopping is detected.

---

### 8. Carrier saturation correctness and least closed solution

Files:

```text
LeanCfgProject/CarrierSaturationCorrectness.lean
LeanCfgProject/CarrierSaturationLeast.lean
```

This layer lifts the generic saturation framework to carrier grammar semantics.

Main declarations include:

```text
CarrierTerminalImage
CarrierBinaryRel
CarrierSaturationImage
saturationIter_subset_of_closed
saturationIter_mono_of_le
carrier_saturationIter_subset_stateSemantics
carrier_yield_mem_saturationIter_exists
carrier_saturationImage_eq_stateSemantics
carrier_terminal_mem_saturationImage
carrier_binary_mul_mem_saturationImage
carrierSaturationImage_isSaturationClosed
carrierSaturationImage_subset_of_closed
carrierStateSemantics_isSaturationClosed
carrierSaturationImage_least_closed_solution
```

This is the main Lean-checked strengthening of the finite-saturation part of the paper.  It verifies that carrier finite-stage saturation images agree with carrier state semantics and that the carrier saturation image is the least closed simultaneous solution of the terminal and binary inclusions.

---

### 9. Saturation-computed concept semantics

File:

```text
LeanCfgProject/CarrierSaturationConceptSoundness.lean
```

This layer defines concept semantics computed from carrier saturation images and proves that it agrees with the previously defined carrier concept semantics.

Main declarations include:

```text
CarrierSaturationConceptSemantics
carrierSaturationConceptSemantics_isConceptExtent
carrier_binaryRel_sound_as_saturationConceptSemantics
carrier_binaryRule_sound_as_saturationConceptSemantics
carrierSaturationConceptSemantics_eq_carrierConceptSemantics
```

This verifies that finite saturation is not merely an auxiliary construction: after residual closure, it gives the same carrier concept semantics as the direct definition from yield semantics.

---

### 10. Closed-stage stability and algorithmic correctness

Files:

```text
LeanCfgProject/SaturationStability.lean
LeanCfgProject/ClosedStageConceptBridge.lean
LeanCfgProject/ClosedStageFrameBridge.lean
LeanCfgProject/SaturationMonotoneChain.lean
LeanCfgProject/ClosedStageAlgorithmCorrectness.lean
LeanCfgProject/FiniteCoverageStopping.lean
LeanCfgProject/ClosedStageEquivalences.lean
LeanCfgProject/ClosedStageConceptStability.lean
LeanCfgProject/ClosedStageFrameIntentStability.lean
LeanCfgProject/ClosedStageRuleSemantics.lean
LeanCfgProject/LaterClosedStageClosure.lean
```

This layer formalizes the closed-stage criterion for effective semantic computation.

If a finite saturation stage is closed under the one-step saturation operator, then:

- the next stage is equal to it;
- all later stages are equal to it;
- all later stages are also closed;
- that closed stage computes the carrier saturation image;
- that closed stage computes the carrier state semantics;
- its residual closure computes the carrier concept semantics;
- binary rules remain sound at the closed-stage concept level;
- terminal and binary rule inclusions remain true at the stopped stage and later stages;
- typed two-sided frames remain visible on the intent side and remain bounded by frame residual closure.

Representative declarations include:

```text
saturationIter_succ_eq_of_closed
saturationIter_subset_closed_stage
carrierSaturationImage_eq_of_closed_stage
carrierStateSemantics_eq_closed_saturationStage
CarrierClosedStageConceptSemantics
carrierClosedStageConceptSemantics_eq_carrierConceptSemantics
carrier_binaryRule_sound_as_closedStageConceptSemantics
saturationIter_eq_of_le_closed_stage
carrierSaturationIter_eq_closed_stage_add
closedStage_computes_carrierStateSemantics
closedStage_computes_carrierConceptSemantics
carrierSaturationStage_closed_of_covers_saturationImage
carrierSaturationStage_closed_iff_succ_eq
carrierSaturationStage_closed_iff_eq_stateSemantics
carrierClosedStageConceptSemantics_later_eq_carrierConceptSemantics
carrier_binaryRule_sound_as_laterClosedStageConceptSemantics
carrier_terminalImage_subset_laterClosedStageConcept
carrierSaturationIter_closed_of_closed_add
```

This supports the algorithmic reading of the paper: once a saturation stage is verified to be closed, that finite stage computes the state semantics and its residual closure computes the concept semantics; after that point, all later stages are stable and closed.

---

### 11. Local stopping correctness

Files:

```text
LeanCfgProject/LocalStoppingCorrectness.lean
LeanCfgProject/LocalStoppingRuleSemantics.lean
LeanCfgProject/LocalStoppingFrameResidual.lean
```

This layer packages the checkable local stopping condition

```text
U_(N+1) = U_N
```

as an algorithmic correctness principle.

If the local stopping equality is detected, then:

- stage `N` is closed;
- stage `N` equals the full carrier saturation image;
- stage `N` computes carrier state semantics;
- its residual closure computes carrier concept semantics;
- all later stages compute the same state semantics;
- all later closed-stage concept semantics compute the same carrier concept semantics;
- terminal and binary rule inclusions hold at the stopped stage and all later stages;
- for the standard observation `h`, typed frames persist as intent-side common contexts and residual-closure bounds.

Representative declarations include:

```text
carrierSaturationStage_closed_of_succ_eq
carrierSaturationStage_eq_saturationImage_of_succ_eq
carrierSaturationStage_eq_stateSemantics_of_succ_eq
carrierClosedStageConcept_eq_carrierConcept_of_succ_eq
carrierSaturationIter_eq_stateSemantics_of_succ_eq_later
carrierClosedStageConcept_later_eq_carrierConcept_of_succ_eq
carrier_terminalImage_subset_stoppedStage_of_succ_eq
carrier_binaryRule_mul_mem_laterStoppedStage_of_succ_eq
carrierSaturationIter_closed_of_succ_eq_add
carrier_stoppedStageConcept_subset_frame_residual_closure_h
carrier_laterStoppedStageConcept_subset_frame_residual_closure_h
carrier_localStopped_frame_intent_and_residual_h
```

This layer gives the checkable stopping-equality correctness theorem.  It is now complemented by the unconditional finite-stopping layer below, which proves that such a closed stage exists for finite state sets and finite observation carriers.

---


### 12. Unconditional finite stopping and bounded computation

Files:

```text
LeanCfgProject/FiniteStoppingCore.lean
LeanCfgProject/MeasureStoppingCriterion.lean
LeanCfgProject/FiniteSaturationMeasure.lean
LeanCfgProject/FiniteStoppingFrameResidual.lean
```

This layer proves the unconditional finite-stopping theorem for saturation over a finite state set and a finite observation carrier.

The proof is organized in four stages.

First, `FiniteStoppingCore.lean` proves the purely numerical core: a monotone natural-number sequence bounded by `B` has a local stopping point `f (N+1) = f N` for some `N ≤ B`.

Second, `MeasureStoppingCriterion.lean` abstracts the stopping argument to any stage family equipped with a bounded monotone measure that strictly increases whenever some component changes.  It then specializes this criterion to generic saturation and carrier saturation.

Third, `FiniteSaturationMeasure.lean` instantiates the abstract measure.  Instead of relying on fragile `Set.ncard` API details, it defines an indicator-cardinality measure on finite `Q` by summing `if q ∈ U then 1 else 0` over `Finset.univ`.  The resulting saturation measure is bounded by `|State| * |Q|`, is monotone, and strictly increases whenever a saturation component changes.  Consequently, if `State` and `Q` are finite, there exists `N ≤ |State| * |Q|` such that `SaturationIter (N+1) = SaturationIter N` componentwise, and hence stage `N` is closed.

Fourth, `FiniteStoppingFrameResidual.lean` combines this bounded finite-stopping theorem with the two-sided frame residual/intent bridge.  For the standard observation `h`, there exists a bounded finite stage whose residual concept closure computes carrier concept semantics and simultaneously retains the typed two-sided frame as intent-side and residual-bound data.

Representative declarations include:

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

Mathematically, this upgrades the algorithmic story from "if a local stopping equality is detected, then it is correct" to "for finite state sets and finite observation carriers, such a bounded closed stage exists, computes the state and concept semantics, and preserves two-sided frame information."

---

### 13. Observed syntactic concepts and adequacy layer

Files:

```text
LeanCfgProject/FrameAdequacyCriterion.lean
LeanCfgProject/K4ResidualAdequacyExample.lean
LeanCfgProject/K4AdequacyStrictness.lean
LeanCfgProject/K4ConceptCollapse.lean
LeanCfgProject/FiniteStoppedFrameAdequacy.lean
LeanCfgProject/AdequacyBridgeSummary.lean
LeanCfgProject/ObservedSyntacticConcept.lean
LeanCfgProject/ObservedSyntacticCongruence.lean
LeanCfgProject/CanonicalResidualClosureSystem.lean
LeanCfgProject/CarrierObservedAdequacy.lean
```

This layer is the main new verified content at commit `04d0d88` / Lean CI #149. It formalizes the canonical observed-syntactic concept layer used by the v25.2 paper draft.

The general adequacy criterion reduces equality of residual concepts to a concrete coverage condition:

```text
U ⊆ R, R ⊆ ConceptClosure S U  ==>  ConceptClosure S R = ConceptClosure S U
```

The K4 worked example verifies a finite nontrivial residual-concept phenomenon: raw singleton images can be proper subsets of their frame residuals, while their residual concept closures still coincide with the frame residual concepts. It also verifies that distinct raw powerset images can collapse to the same residual concept.

The observed syntactic modules define the two-sided observed syntactic congruence `SameObservedSyntactic S x y`, prove it is an equivalence relation, prove saturation of concept closures and residuals under this equivalence, prove residuals are already concept-closed, and prove the syntactic-block adequacy theorem: if a frame residual is contained in one observed syntactic block, then every nonempty sound state image inside it generates that residual by concept closure.

The congruence module proves the maximality package: in a monoid, `SameObservedSyntactic S` is two-sided stable, preserves membership in `S`, and contains every two-sided stable relation preserving `S`.

The canonical closure module proves that concept extents are exactly intersections of two-sided residuals. This is the Lean counterpart of the paper's statement that the residual concept universe is a canonical closure system determined by `(Q,S)`.

The carrier adequacy module lifts the abstract syntactic-block theorem back to CFG descriptor semantics. For standard observation `h`, and also for observations factoring through `h`, a productive carrier state whose frame residual is a single observed syntactic block is frame-adequate at the residual-concept level.

Representative declarations include:

```text
adequacy_of_residual_coverage
adequacy_iff_residual_coverage
carrier_frame_adequacy_of_coverage_h
k4_bridge_bidirectional
k4_adequacy_is_nontrivial
k4_nontrivial_collapse_summary
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
carrier_frame_adequacy_of_observedSyntacticBlock_h
carrier_frame_adequacy_of_observedSyntacticBlock_factor
carrierObservedAdequacy_summary_h
```

Mathematically, this upgrades the artifact from a soundness/effectiveness bridge to a checked adequacy route: the presentation-dependent descriptor image lands inside a presentation-independent observed residual-concept universe, and exact frame representation follows under the single observed-syntactic-block hypothesis.

---

### 14. Summary targets

Files:

```text
LeanCfgProject/SemanticBridgeSummary.lean
LeanCfgProject/ICSemanticBridgeSummary.lean
LeanCfgProject/ICSemanticBridgeSummary_v2.lean
LeanCfgProject/AttackSemanticBridgeSummary.lean
```

These files are compact CI targets collecting the semantic-bridge modules relevant to the paper appendix and reproducibility statement.

They intentionally prove only lightweight availability theorems.  Their role is to ensure that the observation, saturation, counterexample, residual-concept, carrier-concept, frame-soundness, closed-stage algorithmic, and local-stopping modules build simultaneously.

Representative declarations include:

```text
semanticBridgeSummary_observationSignatureKernel_available
semanticBridgeSummary_counterexample_available
semanticBridgeSummary_finiteSaturation_available
semanticBridgeSummary_carrierConceptSemantics_available
icSemanticBridgeSummary_saturationCorrectness_available
icSemanticBridgeSummaryV2_algorithmicCorrectness_available
attackSemanticBridgeSummary_finiteCoverageStopping_available
attackSemanticBridgeSummary_closedStageEquivalences_available
attackSemanticBridgeSummary_closedStageConceptStability_available
attackSemanticBridgeSummary_localStoppingCorrectness_available
attackSemanticBridgeSummary_localStoppingRuleSemantics_available
attackSemanticBridgeSummary_localStoppingFrameResidual_available
```

---

## Main files

```text
LeanCfgProject/
  Step25_Test.lean
  FullArchitecture_Test.lean

  StateSemantics.lean
  ResidualConcept.lean
  FiniteSaturation.lean

  LanguageQuotient.lean
  ObservationFinite.lean
  ObservationCounterexample.lean
  ObservationCounterexample_v2.lean
  ObservationSignatureCounterexample.lean

  DescriptorSemantics.lean
  DescriptorResidualSemantics.lean
  CarrierConceptSemantics.lean

  FrameSoundness.lean
  CarrierSaturationCorrectness.lean
  SaturationFrameBridge.lean
  CarrierSaturationLeast.lean
  CarrierSaturationConceptSoundness.lean
  FrameIntentClosureBridge.lean

  ICSemanticBridgeSummary.lean
  SaturationStability.lean
  ClosedStageConceptBridge.lean
  ClosedStageFrameBridge.lean
  SaturationMonotoneChain.lean
  ClosedStageAlgorithmCorrectness.lean
  ICSemanticBridgeSummary_v2.lean

  FiniteCoverageStopping.lean
  ClosedStageEquivalences.lean
  ClosedStageConceptStability.lean
  ClosedStageFrameIntentStability.lean
  ClosedStageRuleSemantics.lean
  LaterClosedStageClosure.lean
  LocalStoppingCorrectness.lean
  LocalStoppingRuleSemantics.lean
  LocalStoppingFrameResidual.lean
  AttackSemanticBridgeSummary.lean
  FiniteStoppingCore.lean
  MeasureStoppingCriterion.lean
  FiniteSaturationMeasure.lean
  FiniteStoppingFrameResidual.lean

  FrameAdequacyCriterion.lean
  K4ResidualAdequacyExample.lean
  K4AdequacyStrictness.lean
  K4ConceptCollapse.lean
  FiniteStoppedFrameAdequacy.lean
  AdequacyBridgeSummary.lean
  ObservedSyntacticConcept.lean
  ObservedSyntacticCongruence.lean
  CanonicalResidualClosureSystem.lean
  CarrierObservedAdequacy.lean

  SemanticBridgeSummary.lean
```

---

## Current mathematical interpretation

The repository should be read as a machine-checked Lean model of the core architecture and its semantic extension.

At commit `04d0d88`, the currently verified development supports the following conservative claim:

```text
The presentation-level architecture, observation relations, observation-signature
kernel, concrete observation counterexamples, abstract powerset-valued state
semantics, residual concept semantic layer, descriptor-level carrier semantic
bridges, frame soundness, carrier saturation correctness, least closed solution
formulation, saturation-computed concept semantics, closed-stage stability,
closed-stage algorithmic correctness, local stopping correctness, local stopping
rule semantics, local stopping frame/residual preservation, unconditional finite stopping,
bounded carrier state/concept computation, finite-stopping frame/residual preservation,
frame adequacy criteria, finite K4 residual-adequacy witnesses, observed syntactic congruence and maximality,
canonical residual closure systems, carrier observed-syntactic-block adequacy, and semantic-bridge summary targets
build successfully in Lean 4 with no sorry and no project-level axioms under the repository CI policy.
```

In paper terms, the verified semantic bridge is:

```text
E_h(G) -> P(Q) -> Concepts(Q, q[L])
```

with the additional verified facts that:

- carrier saturation computes carrier state semantics;
- saturation is the least closed simultaneous solution of terminal and binary inclusions;
- saturation-computed concept semantics agrees with carrier concept semantics;
- closed saturation stages compute state and concept semantics;
- local stopping `U_(N+1) = U_N` implies closedness and semantic correctness;
- for finite state sets and finite observation carriers, a bounded closed stage exists;
- a bounded carrier stage computes state semantics and residual concept semantics;
- stopped stages and all later stages are rule-closed semantic models;
- typed two-sided frames survive as residual bounds and as intent-side common contexts, including after local stopping and at a bounded finite stopping stage;
- concept closure and two-sided residuals are saturated by the observed syntactic congruence;
- the observed syntactic congruence is maximal among two-sided stable `S`-preserving relations;
- concept extents are exactly residual intersections;
- finite K4 examples witness strict raw-image inclusion but residual-concept adequacy;
- carrier states are frame-adequate under the checked nonempty single observed-syntactic-block hypothesis.

---

## Current formalization boundary

The current Lean artifact does **not** claim that:

- the entire accompanying paper is fully formalized;
- CFG equivalence is solved;
- a canonical CFG presentation has been constructed;
- every fixed-`h` descriptor is a language-level invariant;
- an unrestricted adequacy theorem has been proved saying that all residual concepts are exactly realized by typed presentation states without the checked nonempty single observed-syntactic-block hypothesis;
- finite residual-concept bases have been constructed for broad classes of fixed-`h` substitutable CFLs;
- the regularity corollary from the pointed-boundary theorem has been fully developed in a separate regular-language module.

These points are intentionally separated from the verified bridge results and are treated in the paper as future formalization targets or open problems.
The current artifact **does** verify an unconditional bounded finite-stopping theorem for saturation when both the state set and the observation carrier are finite, and it now also verifies the observed-syntactic-block adequacy criterion and its carrier-level instantiation.  This should not be misstated as a theorem from `Fintype Q` alone: the finite-state hypothesis is essential.


---

## Paper correspondence

The intended paper version corresponding to this artifact snapshot is:

```text
Residual Concept Semantics for Two-Sided Fixed-h CFG Presentations
Version v25.2 or later
Lean CI #149
commit b1e9b4d
```

The paper appendix contains a theorem/file correspondence table mapping selected paper statements to Lean declarations and CI-checked modules.

A concise correspondence is:

| Paper-level component | Lean files |
|---|---|
| Descriptor architecture | `Step25_Test.lean`, `FullArchitecture_Test.lean` |
| Observation quotients and pointed boundary | `LanguageQuotient.lean`, `ObservationFinite.lean` |
| Observation counterexample | `ObservationCounterexample.lean`, `ObservationCounterexample_v2.lean`, `ObservationSignatureCounterexample.lean` |
| Powerset-valued semantics | `StateSemantics.lean` |
| Residual concept semantics | `ResidualConcept.lean` |
| Carrier descriptor semantics | `DescriptorSemantics.lean`, `DescriptorResidualSemantics.lean`, `CarrierConceptSemantics.lean` |
| Frame soundness and frame-intent preservation | `FrameSoundness.lean`, `SaturationFrameBridge.lean`, `FrameIntentClosureBridge.lean`, `ClosedStageFrameBridge.lean`, `ClosedStageFrameIntentStability.lean`, `LocalStoppingFrameResidual.lean` |
| Carrier saturation correctness | `FiniteSaturation.lean`, `CarrierSaturationCorrectness.lean`, `CarrierSaturationLeast.lean` |
| Saturation-computed concept semantics | `CarrierSaturationConceptSoundness.lean` |
| Closed-stage correctness | `SaturationStability.lean`, `ClosedStageConceptBridge.lean`, `SaturationMonotoneChain.lean`, `ClosedStageAlgorithmCorrectness.lean`, `ClosedStageEquivalences.lean`, `ClosedStageConceptStability.lean`, `ClosedStageRuleSemantics.lean`, `LaterClosedStageClosure.lean` |
| Local stopping correctness | `LocalStoppingCorrectness.lean`, `LocalStoppingRuleSemantics.lean`, `LocalStoppingFrameResidual.lean` |
| Observed syntactic concept object and adequacy criterion | `ObservedSyntacticConcept.lean`, `ObservedSyntacticCongruence.lean`, `CanonicalResidualClosureSystem.lean`, `CarrierObservedAdequacy.lean` |
| K4 residual adequacy worked example | `K4ResidualAdequacyExample.lean`, `K4AdequacyStrictness.lean`, `K4ConceptCollapse.lean`, `AdequacyBridgeSummary.lean` |
| Summary targets | `SemanticBridgeSummary.lean`, `ICSemanticBridgeSummary.lean`, `ICSemanticBridgeSummary_v2.lean`, `AttackSemanticBridgeSummary.lean`, `AdequacyBridgeSummary.lean` |

---

## Continuous integration

The repository uses GitHub Actions to run Lean verification automatically on push, pull request, and manual workflow dispatch.

Workflow file:

```text
.github/workflows/lean.yml
```

The CI checks the core files, rejects `sorry`, rejects project-level `axiom` declarations, and builds the semantic bridge modules listed above.

---

## Research direction

The current formalization supports a research program around the semantic bridge:

```text
E_h(G) -> P(Q) -> Concepts(Q, q[L])
```

Here:

- `E_h(G)` is a presentation-level fixed-`h` two-sided descriptor;
- `Q` is a language-level observation carrier or quotient candidate;
- `P(Q)` is powerset-valued state semantics;
- `q[L]` is the start image of the language;
- `Concepts(Q, q[L])` is the residual Galois / Clark-style concept universe.

The refined open problem is to identify useful finite generated residual concept bases for fixed-`h` substitutable context-free languages, without collapsing the problem to regular-language recognition.

---

## Next Lean targets

Near-term proof targets include:

1. preparing an online companion blueprint with links to declarations and CI logs;
2. preparing an artifact snapshot or release tag corresponding to the paper;
3. investigating finite generated residual concept bases for fixed-`h` substitutable context-free languages;
4. formalizing the endpoint-monoid non-coset witness and the normal-coset / mod-k families;
5. investigating quotient invariance of the observed syntactic concept object;
6. developing restricted adequacy results for controlled examples or subclasses beyond the checked single-block criterion;
7. keeping future extensions small and modular.

The guiding principle is to keep each Lean extension compatible with the no-`sorry` / no-project-level-`axiom` CI discipline, and to distinguish clearly between checked formalization results and open mathematical problems.

---

## Citation / artifact note

This repository is an evolving research artifact.  A public release tag, archived artifact snapshot, and paper-specific DOI may be added once the corresponding paper version and repository state are frozen.
