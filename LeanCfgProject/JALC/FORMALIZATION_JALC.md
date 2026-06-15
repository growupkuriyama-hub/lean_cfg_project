# Lean Formalization Record for the JALC Paper

This document records the Lean 4 formalization status for the JALC-oriented paper:

```text
A Finite Representation Theorem for Two-Sided Monoid-Typed CFG Presentations
```

This file is specific to the JALC paper. It is separate from the repository-level `FORMALIZATION.md`, which records formalization results for a different paper or a broader repository-level development.

This version updates the record through the full-refinement, full-kept,
finite-main theorem, certified fixed-point extraction, algorithmic bridge,
full algorithmic agreement kernels, the executable-interface experiments,
and the bounded-search/no-strict-growth/freshness/collision obstruction
sequence through Lean CI #360.

The main previously recorded algorithmic agreement reference run remains:

```text
Lean CI #304
Commit: a434bb3
Pushed by: growupkuriyama-hub
Target: LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement
```

The later executable-interface chain includes the following confirmed runs:

```text
Lean CI #307
Commit: 2cde4a4
Pushed by: growupkuriyama-hub
Target: LeanCfgProject.JALC.PaperFacingExperimentClosure
```

```text
Lean CI #314
Target chain including:
  LeanCfgProject.JALC.PaperFacingProductiveReachableIteratorCertificate
Status: succeeded
```

The latest user-reported successful target before the later executable-limit extension was:

```text
Target: LeanCfgProject.JALC.PaperFacingStepDecidability
Status: succeeded
```

The latest user-reported successful target after the bounded-search and concrete bounded-witness bridge extension is:

```text
Target: LeanCfgProject.JALC.PaperFacingConcreteBoundedWitnessBridge
Status: succeeded
```

It also retains the earlier full finite-main reference run:

```text
Lean CI #292
Commit: d02ac8d
Pushed by: growupkuriyama-hub
Target: LeanCfgProject.JALC.PaperFacingFullFiniteMain
```

---

## Latest update: bounded-search success, no-strict-growth, strict-growth freshness, and finite obstruction bridge

This update records the newest Lean formalization milestones through the
bounded-search/no-strict-growth and finite-obstruction bridge sequence.

The latest user-reported successful CI run is:

```text
Lean CI #360
Commit: fc41370
Pushed by: growupkuriyama-hub
Latest target:
  LeanCfgProject.JALC.PaperFacingFiniteObstructionViaCollision
Status: succeeded
```

This run confirms the newest target:

```text
LeanCfgProject.JALC.PaperFacingFiniteObstructionViaCollision
```

and, through the import chain and the user's full workflow, confirms the
following bounded-search and finite-obstruction targets developed after the
previous `ConcreteBoundedWitnessBridge` milestone:

```text
LeanCfgProject.JALC.PaperFacingConcreteTwoStageBoundedSearch
LeanCfgProject.JALC.PaperFacingConcreteTwoStageSearchCertificate
LeanCfgProject.JALC.PaperFacingBoundedSearchCompleteness
LeanCfgProject.JALC.PaperFacingConcreteTwoStageSearchConsistency
LeanCfgProject.JALC.PaperFacingConcreteTwoStageSearchSuccess
LeanCfgProject.JALC.PaperFacingBoundedSearchOffsetCompleteness
LeanCfgProject.JALC.PaperFacingBoundedSearchWithinBound
LeanCfgProject.JALC.PaperFacingListGrowthStabilization
LeanCfgProject.JALC.PaperFacingConcreteNoStrictGrowthSearchSuccess
LeanCfgProject.JALC.PaperFacingStrictGrowthWitnessFreshness
LeanCfgProject.JALC.PaperFacingStrictGrowthCountingInterface
LeanCfgProject.JALC.PaperFacingFreshFamilyFinEmbedding
LeanCfgProject.JALC.PaperFacingSmallSupportObstruction
LeanCfgProject.JALC.PaperFacingDoubletonSupportObstruction
LeanCfgProject.JALC.PaperFacingCollisionObstructionBridge
LeanCfgProject.JALC.PaperFacingFiniteObstructionViaCollision
```

The newly added modules in this phase are:

```text
ConcreteTwoStageBoundedSearchKernel.lean
PaperFacingConcreteTwoStageBoundedSearch.lean

ConcreteTwoStageSearchCertificateKernel.lean
PaperFacingConcreteTwoStageSearchCertificate.lean

BoundedSearchCompletenessKernel.lean
PaperFacingBoundedSearchCompleteness.lean

ConcreteTwoStageSearchConsistencyKernel.lean
PaperFacingConcreteTwoStageSearchConsistency.lean

ConcreteTwoStageSearchSuccessKernel.lean
PaperFacingConcreteTwoStageSearchSuccess.lean

BoundedSearchOffsetCompletenessKernel.lean
PaperFacingBoundedSearchOffsetCompleteness.lean

BoundedSearchWithinBoundKernel.lean
PaperFacingBoundedSearchWithinBound.lean

ListGrowthStabilizationKernel.lean
PaperFacingListGrowthStabilization.lean

ConcreteNoStrictGrowthSearchSuccessKernel.lean
PaperFacingConcreteNoStrictGrowthSearchSuccess.lean

StrictGrowthWitnessFreshnessKernel.lean
PaperFacingStrictGrowthWitnessFreshness.lean

StrictGrowthCountingInterfaceKernel.lean
PaperFacingStrictGrowthCountingInterface.lean

FreshFamilyFinEmbeddingKernel.lean
PaperFacingFreshFamilyFinEmbedding.lean

SmallSupportObstructionKernel.lean
PaperFacingSmallSupportObstruction.lean

DoubletonSupportObstructionKernel.lean
PaperFacingDoubletonSupportObstruction.lean

CollisionObstructionBridgeKernel.lean
PaperFacingCollisionObstructionBridge.lean

FiniteObstructionViaCollisionKernel.lean
PaperFacingFiniteObstructionViaCollision.lean
```

### New verified chain

The current checked chain is now substantially stronger than the earlier
bounded-witness bridge.  The development verifies:

```text
list-stability witness
=> StableAt
=> ClosureCertificate
=> CertifiedExtraction
=> FullKept decidability
```

and also:

```text
bounded list-stability search succeeds
=> ListStabilityWitness
=> StableAt
```

The later finite-growth layer verifies the following bridge:

```text
NoStrictGrowthWithinBound
=> list-stability at some height within fuel
=> bounded search at that fuel succeeds
=> StableAt at the returned witness height
```

The concrete two-stage layer verifies:

```text
productive bounded search succeeds
+ reachable bounded search succeeds at the returned productive witness height
=> ConcreteBoundedWitnessData
=> ConcreteTwoStageSearchCertificate
=> CertifiedExtraction
=> FullKept decidability
```

The no-strict-growth concrete bridge verifies:

```text
productive step is monotone
+ reachable steps are monotone
+ productive no-strict-growth certificate within productive fuel
+ reachable no-strict-growth certificate within reachable fuel
  for the productive witness returned by the first search
=> productive bounded search succeeds
=> reachable bounded search succeeds
=> concrete two-stage bounded search succeeds
=> FullKept decidability
```

The strict-growth freshness layer verifies:

```text
F is monotone
+ strict growth occurs at heights i and j
+ i < j
=> the selected strict-growth witnesses at i and j are distinct
```

The counting-interface layer verifies:

```text
strict growth at every height up to fuel
=> FreshStrictGrowthFamily indexed by heights up to fuel
```

and conversely packages the obstruction route:

```text
FreshFamilyImpossible
=> strict growth cannot occur at every height up to fuel
=> some no-strict-growth height exists within fuel
=> bounded search succeeds
=> closure certificate
```

The finite-index embedding layer verifies:

```text
FreshStrictGrowthFamily xs F fuel
=> injective map Fin (fuel + 1) -> α
   whose values all lie in xs
```

and:

```text
FinEmbeddingImpossible
=> FreshFamilyImpossible
=> bounded search succeeds
```

The small finite-obstruction layer verifies the first concrete finite-list
pigeonhole cases:

```text
support = []
=> FinEmbeddingImpossible
=> bounded search succeeds
```

```text
support = [a]
+ fuel >= 1
=> FinEmbeddingImpossible
=> bounded search succeeds
```

```text
support = [a, b]
+ fuel >= 2
=> FinEmbeddingImpossible
=> bounded search succeeds
```

The collision-obstruction layer verifies the uniform collision interface:

```text
every candidate finite-index embedding has a collision
=> no injective finite-index embedding exists
=> no fresh strict-growth family exists
=> no full strict-growth run exists
=> no-strict-growth within fuel
=> bounded search succeeds
=> closure certificate
```

Finally, the newest target `PaperFacingFiniteObstructionViaCollision` verifies
that the earlier finite embedding obstructions route through the collision
interface:

```text
FinEmbeddingImpossible
=> CollisionObstruction
=> bounded search succeeds
=> closure certificate
```

and packages the empty, singleton, and doubleton support cases in the common
collision-obstruction form.

### Current best formalized statement

The strongest honest statement supported by the newest Lean development is:

```text
The Lean 4 development verifies a certificate-producing bounded-search
architecture for the concrete full all-copy refinement.  It checks that
no-strict-growth certificates imply bounded-search success; that productive and
reachable no-strict-growth certificates imply concrete two-stage bounded-search
success and FullKept decidability; that persistent strict growth produces fresh
support witnesses; that fresh witness families yield finite-index injections
into the support list; and that finite embedding/collision obstructions route
back to bounded-search success and closure certificates.  The empty, singleton,
and doubleton support obstruction cases are checked, and the general
finite-support pigeonhole theorem is reduced to a finite collision/counting
argument.
```

### Remaining gap after CI #360

The remaining main formalization gap is now sharply localized.  The artifact
does not yet prove the fully general finite-list pigeonhole theorem:

```text
fuel >= support.length
=> FinEmbeddingImpossible support fuel
```

or equivalently a general collision property:

```text
support list xs is shorter than Fin (fuel + 1)
=> every map Fin (fuel + 1) -> α with values in xs has a collision
```

Once this finite-list collision theorem is supplied, the already checked bridge
routes it to:

```text
NoStrictGrowthWithinBound
=> bounded search succeeds
=> concrete two-stage search succeeds
=> CertifiedExtraction
=> FullKept decidability
```

Thus, after CI #360, the remaining hard point is no longer the extraction
architecture itself, but the general finite pigeonhole/counting theorem for
support lists.

### Recommended newest CI command

For the latest target and its import dependencies:

```text
lake build LeanCfgProject.JALC.PaperFacingFiniteObstructionViaCollision
```

For a fuller regression suite, include:

```text
lake build LeanCfgProject.JALC.PaperFacingConcreteTwoStageBoundedSearch
lake build LeanCfgProject.JALC.PaperFacingConcreteTwoStageSearchCertificate
lake build LeanCfgProject.JALC.PaperFacingBoundedSearchCompleteness
lake build LeanCfgProject.JALC.PaperFacingConcreteTwoStageSearchConsistency
lake build LeanCfgProject.JALC.PaperFacingConcreteTwoStageSearchSuccess
lake build LeanCfgProject.JALC.PaperFacingBoundedSearchOffsetCompleteness
lake build LeanCfgProject.JALC.PaperFacingBoundedSearchWithinBound
lake build LeanCfgProject.JALC.PaperFacingListGrowthStabilization
lake build LeanCfgProject.JALC.PaperFacingConcreteNoStrictGrowthSearchSuccess
lake build LeanCfgProject.JALC.PaperFacingStrictGrowthWitnessFreshness
lake build LeanCfgProject.JALC.PaperFacingStrictGrowthCountingInterface
lake build LeanCfgProject.JALC.PaperFacingFreshFamilyFinEmbedding
lake build LeanCfgProject.JALC.PaperFacingSmallSupportObstruction
lake build LeanCfgProject.JALC.PaperFacingDoubletonSupportObstruction
lake build LeanCfgProject.JALC.PaperFacingCollisionObstructionBridge
lake build LeanCfgProject.JALC.PaperFacingFiniteObstructionViaCollision
```

Recommended newest paper-level claim:

```text
The formalization now checks not only the theorem-facing finite representation
and full-kept correctness kernels, but also a substantial bounded-search
certificate architecture.  In particular, the Lean development verifies that
no-strict-growth and finite collision certificates are sufficient to force
bounded-search success, closure certificates, concrete two-stage extraction,
and FullKept decidability.  The remaining unverified endpoint is the fully
general finite-list pigeonhole theorem guaranteeing such collision certificates
for arbitrary finite support lists of the required length.
```

---

---

## Latest update: executable-limit, list-stability, bounded-search, and concrete bounded-witness bridge

This update records the later successful Lean targets added after the previously
recorded `PaperFacingStepDecidability` milestone.

The following additional paper-facing targets were reported as successfully
passing in the conversation:

```text
LeanCfgProject.JALC.PaperFacingExecutableLimit
LeanCfgProject.JALC.PaperFacingListStabilityExtraction
LeanCfgProject.JALC.PaperFacingBoundedStabilitySearch
LeanCfgProject.JALC.PaperFacingConcreteBoundedWitnessBridge
```

A temporary target

```text
LeanCfgProject.JALC.PaperFacingListStabilityDecision
```

was also checked during the development of the list-stability decision layer.
The later bounded-search target was deliberately simplified so that the generic
bounded-search kernel does not depend on this temporary paper-facing target.

The currently most advanced user-reported successful target is therefore:

```text
LeanCfgProject.JALC.PaperFacingConcreteBoundedWitnessBridge
```

This target verifies a thin bridge from generic bounded list-stability witnesses
back to the concrete full all-copy extraction interface.  In particular, it
checks that, if productive and reachable list-stability witnesses are supplied
for the concrete full all-copy rule data, then they can be converted into
`ConcreteListStabilityData`, and hence into the already checked
`CertifiedExtraction` and `FullKept` decidability chain.

The newly added executable-interface modules are:

```text
StepPreservationKernel.lean
ConcreteStepPreservationKernel.lean
PaperFacingFullIteratorCertificate.lean
ActualListIteratorKernel.lean
FiniteStabilizationBoundaryKernel.lean
DescriptorReconstructionBoundaryKernel.lean
PaperFacingExecutableLimit.lean

ListStabilityKernel.lean
ConcreteListStabilityKernel.lean
PaperFacingListStabilityExtraction.lean

BoundedListStabilitySearchKernel.lean
PaperFacingBoundedStabilitySearch.lean

ConcreteBoundedWitnessBridgeKernel.lean
PaperFacingConcreteBoundedWitnessBridge.lean
```

The main new verified chain is:

```text
finite universe support
+ finite list-stability witness
=> StableAt
=> ClosureCertificate
=> CertifiedExtraction

generic bounded search
=> Option ListStabilityWitness

productive ListStabilityWitness
+ reachable ListStabilityWitness
+ concrete full-rule universes and rule decisions
=> ConcreteListStabilityData
=> CertifiedExtraction
=> FullKept decidability
```

The current artifact is still not claimed to be a complete executable extraction
algorithm.  The remaining executable gap is the automatic proof that the bounded
search succeeds within a specific finite bound, together with an end-to-end
construction of the concrete rule decisions and descriptor reconstruction from
arbitrary finite CFG presentation data.

Recommended newest CI commands:

```text
lake build LeanCfgProject.JALC.PaperFacingExecutableLimit
lake build LeanCfgProject.JALC.PaperFacingListStabilityExtraction
lake build LeanCfgProject.JALC.PaperFacingBoundedStabilitySearch
lake build LeanCfgProject.JALC.PaperFacingConcreteBoundedWitnessBridge
```

Recommended current high-level CI suite:

```text
lake build LeanCfgProject.JALC.Summary
lake build LeanCfgProject.JALC.PaperFacingFullFiniteMain
lake build LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement
lake build LeanCfgProject.JALC.PaperFacingExperimentClosure
lake build LeanCfgProject.JALC.PaperFacingProductiveReachableIteratorCertificate
lake build LeanCfgProject.JALC.PaperFacingIteratorFromDecidableIterates
lake build LeanCfgProject.JALC.PaperFacingStepDecidability
lake build LeanCfgProject.JALC.PaperFacingExecutableLimit
lake build LeanCfgProject.JALC.PaperFacingListStabilityExtraction
lake build LeanCfgProject.JALC.PaperFacingBoundedStabilitySearch
lake build LeanCfgProject.JALC.PaperFacingConcreteBoundedWitnessBridge
lake build LeanCfgProject.JALC.PaperFacingExecutableLimit
lake build LeanCfgProject.JALC.PaperFacingListStabilityExtraction
lake build LeanCfgProject.JALC.PaperFacingBoundedStabilitySearch
lake build LeanCfgProject.JALC.PaperFacingConcreteBoundedWitnessBridge
```

Recommended current paper-level claim:

```text
The Lean 4 development verifies the theorem-facing finite representation
kernels, the full all-copy/full-kept correctness interface, and the direct
agreement between the certified Algorithm 1 kept predicate and the abstract
FullKept predicate.  It also checks a substantial executable-interface chain:
finite rule/list certificates, step decidability, concrete step preservation,
finite list-stability certificates, generic bounded search for list-stability
witnesses, and the bridge from productive/reachable bounded witnesses to
concrete certified extraction and FullKept decidability.  The artifact is not
yet a full extracted implementation that automatically finds the finite
fixed-point heights and reconstructs descriptors from arbitrary CFG
presentation data.
```

---

---

## 1. Repository and paper-facing targets

Repository:

```text
growupkuriyama-hub/lean_cfg_project
```

Formalization directory for this paper:

```text
LeanCfgProject/JALC/
```

Original paper-facing Lean target:

```text
LeanCfgProject.JALC.Summary
```

Earlier finite-representation target:

```text
LeanCfgProject.JALC.FiniteRepresentationBundle
```

Current high-level full finite-main target:

```text
LeanCfgProject.JALC.PaperFacingFullFiniteMain
```

Current high-level algorithmic agreement target:

```text
LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement
```

Current high-level executable-interface and bounded-search targets:

```text
LeanCfgProject.JALC.PaperFacingStepDecidability
LeanCfgProject.JALC.PaperFacingExecutableLimit
LeanCfgProject.JALC.PaperFacingListStabilityExtraction
LeanCfgProject.JALC.PaperFacingBoundedStabilitySearch
LeanCfgProject.JALC.PaperFacingConcreteBoundedWitnessBridge
LeanCfgProject.JALC.PaperFacingConcreteTwoStageBoundedSearch
LeanCfgProject.JALC.PaperFacingConcreteTwoStageSearchCertificate
LeanCfgProject.JALC.PaperFacingBoundedSearchCompleteness
LeanCfgProject.JALC.PaperFacingConcreteTwoStageSearchConsistency
LeanCfgProject.JALC.PaperFacingConcreteTwoStageSearchSuccess
LeanCfgProject.JALC.PaperFacingBoundedSearchOffsetCompleteness
LeanCfgProject.JALC.PaperFacingBoundedSearchWithinBound
LeanCfgProject.JALC.PaperFacingListGrowthStabilization
LeanCfgProject.JALC.PaperFacingConcreteNoStrictGrowthSearchSuccess
LeanCfgProject.JALC.PaperFacingStrictGrowthWitnessFreshness
LeanCfgProject.JALC.PaperFacingStrictGrowthCountingInterface
LeanCfgProject.JALC.PaperFacingFreshFamilyFinEmbedding
LeanCfgProject.JALC.PaperFacingSmallSupportObstruction
LeanCfgProject.JALC.PaperFacingDoubletonSupportObstruction
LeanCfgProject.JALC.PaperFacingCollisionObstructionBridge
LeanCfgProject.JALC.PaperFacingFiniteObstructionViaCollision
```

Recommended current CI commands:

```text
lake build LeanCfgProject.JALC.Summary
lake build LeanCfgProject.JALC.PaperFacingFullFiniteMain
lake build LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement
lake build LeanCfgProject.JALC.PaperFacingExperimentClosure
lake build LeanCfgProject.JALC.PaperFacingProductiveReachableIteratorCertificate
lake build LeanCfgProject.JALC.PaperFacingIteratorFromDecidableIterates
lake build LeanCfgProject.JALC.PaperFacingStepDecidability
LeanCfgProject.JALC.PaperFacingExecutableLimit
LeanCfgProject.JALC.PaperFacingListStabilityExtraction
LeanCfgProject.JALC.PaperFacingBoundedStabilitySearch
LeanCfgProject.JALC.PaperFacingConcreteBoundedWitnessBridge
```

The current minimal GitHub Actions workflow may build only:

```text
LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement
```

when testing the newest theorem-facing algorithmic agreement package. For archival continuity, it is still reasonable to keep both `LeanCfgProject.JALC.Summary` and `LeanCfgProject.JALC.PaperFacingFullFiniteMain` in CI as earlier high-level targets.

---

## 2. Reference CI runs

### Baseline CI run

Earlier baseline run:

```text
Lean CI #236
Commit: a4e2d6a
Pushed by: growupkuriyama-hub
Target: LeanCfgProject.JALC.Summary
Command: lake build LeanCfgProject.JALC.Summary
```

This run checked the original finite typed infrastructure:

```text
LeanCfgProject.JALC.Basic
LeanCfgProject.JALC.TwoSidedContext
LeanCfgProject.JALC.Descriptor
LeanCfgProject.JALC.ResidualConcept
LeanCfgProject.JALC.Summary
```

### Extended finite-representation target

The following high-level target was added and checked during the finite-universe/cardinality extension:

```text
LeanCfgProject.JALC.FiniteRepresentationBundle
```

It bundles the finite-universe and finite-cardinality results for typed and kept-state constructions.

### Latest full finite-main CI run

Latest successful extended CI run recorded in the chat:

```text
Lean CI #292
Commit: d02ac8d
Pushed by: growupkuriyama-hub
Target:
  lake build LeanCfgProject.JALC.PaperFacingFullFiniteMain
```

This run includes the theorem-facing full-refinement chain through:

```text
LeanCfgProject.JALC.FullFiniteMainKernel
LeanCfgProject.JALC.PaperFacingFullFiniteMain
```

and their dependencies.

### Latest algorithmic agreement CI run

Latest successful algorithmic agreement CI run recorded in the chat:

```text
Lean CI #304
Commit: a434bb3
Pushed by: growupkuriyama-hub
Target:
  lake build LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement
```

This run includes the certified fixed-point extraction and algorithmic agreement chain through:

```text
LeanCfgProject.JALC.FiniteClosureKernel
LeanCfgProject.JALC.ProductiveReachableClosureKernel
LeanCfgProject.JALC.PaperFacingFixedPoint

LeanCfgProject.JALC.AlgorithmicExtractionKernel
LeanCfgProject.JALC.PaperFacingAlgorithmicExtraction

LeanCfgProject.JALC.AlgorithmicFullBridgeKernel
LeanCfgProject.JALC.PaperFacingAlgorithmicFullBridge

LeanCfgProject.JALC.FullAlgorithmicAgreementKernel
LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement
```

and their dependencies.  In particular, the previous conditional bridge from a
computed kept predicate to the full-kept theorem package is closed for the
concrete full all-copy rule data: a certified run of Algorithm 1 over
`fullExtractionRuleData tau G` computes exactly the abstract `FullKept tau G`
predicate.

### Post-#304 executable-interface CI runs

After the direct algorithmic agreement target, the development was extended
toward an executable fixed-point extraction boundary.  The following later
targets were introduced and checked in the conversation.

```text
LeanCfgProject.JALC.PaperFacingExperimentClosure
LeanCfgProject.JALC.PaperFacingStageDecidability
LeanCfgProject.JALC.PaperFacingRuleStageBoundary
LeanCfgProject.JALC.PaperFacingListCertificate
LeanCfgProject.JALC.PaperFacingClosureTraceList
LeanCfgProject.JALC.PaperFacingIteratorTraceBoundary
LeanCfgProject.JALC.PaperFacingProductiveReachableIteratorCertificate
LeanCfgProject.JALC.PaperFacingIteratorFromDecidableIterates
LeanCfgProject.JALC.PaperFacingStepDecidability
```

The currently most advanced checked target is:

```text
LeanCfgProject.JALC.PaperFacingConcreteBoundedWitnessBridge
```

This target checks the generic recursion principle that if a predicate
transformer preserves decidability, then all of its finite iterates are
decidable, and specializes this boundary to the productive and reachable
closure steps used by the certified Algorithm 1 package.

---

## 3. Purpose of the formalization

The purpose of this Lean development is to provide a machine-checked companion artifact for the finite two-sided monoid-typed representation theorem developed in the JALC paper.

The current development has five layers.

First, it checks the finite typed infrastructure used by the paper:

* finite monoid observers;
* two-sided h-types;
* typed nonterminals;
* observed two-sided contexts;
* finite descriptor-level rule universes;
* finite descriptors;
* finite extent/intent operators;
* a lightweight residual/concept layer.

Second, it checks theorem-facing kernels for intended-copy representation:

* yield-type and context-type invariants for frame transport;
* orientation-sensitive transport over arbitrary monoids;
* finite arithmetic kernel of the bracketing non-rigidity witness;
* finite kernel of the productive-first trimming witness;
* intended-copy injectivity and equivalence;
* preservation and reflection of terminal, binary, and start rules;
* derivation preservation and reflection;
* start-language preservation and reflection;
* kept-state representation kernels;
* finite-universe and finite-cardinality kernels.

Third, it now checks full-refinement and full-kept correctness kernels:

* an abstract full all-copy typed refinement;
* inclusion of the intended-copy lift into the full refinement;
* language inclusion from the original grammar into the full refinement;
* full-refinement yield invariants;
* exclusion of wrong-yield productive copies under yield soundness;
* productive-subgrammar reachability for the full refinement;
* exclusion of wrong-frame copies by productive-part reachability;
* full-kept correctness, i.e. `FullKept` copies are exactly intended copies under the stated assumptions.

Fourth, it packages these results into a finite main theorem layer:

* full-kept trimmed language equivalence;
* full main theorem package;
* full finite-main theorem package;
* finite kept-state representation for the full-kept construction, assuming finite input data and decidable keptness.

Fifth, it now checks the certified algorithmic-extraction layer corresponding to
Algorithm 1 in the paper:

* abstract finite-closure certificates for monotone predicate iteration;
* productivity closure and productive-part reachability closure;
* a certified Algorithm 1 package computing `computedProductive`, `computedReachable`, and `computedKept`;
* a bridge from the computed kept predicate to the full-kept theorem package;
* a direct agreement theorem showing that, for the concrete full all-copy rule data `fullExtractionRuleData tau G`, a certified run of Algorithm 1 computes exactly `FullKept tau G`.

Sixth, it now checks an executable-interface chain for the fixed-point
extraction boundary:

* transfer from computed keptness decidability to `FullKept` decidability;
* reduction of computed keptness decidability to decidability of the productive
  and reachable stages;
* finite list certificates for predicates and their use in producing
  `DecidablePred` instances;
* closure trace-list certificates at the certified productivity and reachability
  heights;
* iterator trace payloads bundling terminal, start, binary, productive-trace,
  and reachable-trace finite list certificates;
* productive/reachable iterator certificate payloads;
* construction of iterator outputs by filtering complete finite universe lists
  when the target iterate predicates are decidable;
* generic finite-iterate decidability from a step preserving decidability.

The development is still not claimed to be a complete executable extraction algorithm.  In particular, it does not yet provide an extracted implementation that automatically enumerates the full rule universe and constructs the fixed-point certificates from finite input data.  However, the previous assumption-level gap between the Algorithm 1 predicate and the abstract `FullKept` predicate has now been closed at the theorem-facing certified-kernel level, and the executable-interface boundary has been substantially refined.

---

## 4. Overall status summary

### Strongly checked

The Lean development currently checks:

* the finite carrier architecture;
* the orientation of the two-sided frame-transport equation over arbitrary monoids;
* finite witnesses for non-rigidity and productive-first trimming;
* the intended-copy state map;
* state-level injectivity and equivalence for intended copies;
* rule preservation and reflection;
* derivation preservation and reflection;
* start-language preservation and reflection;
* kept-state structure and language kernels;
* finite-universe and cardinality kernels;
* full all-copy typed refinement;
* inclusion of the intended-copy lift into the full refinement;
* original-to-full language inclusion;
* yield invariants for full typed derivations;
* reflection of full typed derivations to untyped derivations;
* elimination of wrong-yield productive full copies;
* productive-subgrammar reachability in the full refinement;
* elimination of wrong-frame copies under productive-part reachability;
* full-kept correctness;
* full-kept trimmed language equivalence;
* finite full-main theorem package;
* finite fixed-point closure certificates;
* certified productivity and productive-part reachability closures;
* certified Algorithm 1 extraction package;
* bridge from computed keptness to full-kept correctness/language/representation kernels;
* direct agreement theorem: Algorithm 1 over the concrete full all-copy rule data computes exactly `FullKept`;
* decidability transfer from `computedKept` to `FullKept`;
* reduction of `computedKept` decidability to `computedProductive` and `computedReachable` decidability;
* finite list certificate interface for predicate decidability;
* closure trace-list certificate interface for the certified productivity and reachability heights;
* iterator trace boundary bundling rule-list and closure-trace data;
* productive/reachable iterator certificate boundary;
* finite-universe filtering interface for building iterator outputs from decidable iterates;
* generic finite-iterate decidability from a decidability-preserving step;
* concrete preservation of decidability for the productive and reachable steps;
* executable-limit bridge from concrete step-preservation data to FullKept decidability;
* finite list-stability data to certified extraction;
* generic bounded search producing finite list-stability witnesses;
* conversion of bounded productive/reachable witnesses into concrete list-stability data;
* bridge from concrete bounded witnesses to certified extraction and FullKept decidability.

### Still prose-level or assumption-level

The following parts are not yet fully formalized as executable or end-to-end Lean theorems:

* the complete extraction theorem from arbitrary CFG presentations;
* an extracted implementation that automatically enumerates the full all-copy rule universe and constructs the fixed-point certificates;
* decidability of `FullKept` membership as an extracted algorithm from finite data;
* shortlex witness preservation;
* context-closure coincidence lemmas for the full two-sided construction;
* complete descriptor reconstruction from arbitrary presentation data.

### Current honest claim

The current artifact supports the following claim:

```text
The Lean 4 development checks the finite typed infrastructure, the intended-copy
state/rule/derivation/language kernels, full-refinement yield and frame kernels,
full-kept correctness, full-kept trimmed language equivalence, a finite
full-main theorem package, and certified Algorithm 1 kernels.  In particular,
for the concrete full all-copy rule data, the artifact checks that a certified
Algorithm 1 run computes exactly the abstract `FullKept` predicate used in the
main theorem.  It is still not an extracted executable implementation that
constructs the fixed-point certificates and descriptors automatically from
arbitrary CFG presentation data.
```

This is the recommended level of claim for the JALC paper.

---

## 5. Checked files: current directory overview

The current JALC formalization consists of the following modules.

```text
LeanCfgProject/JALC/
  Basic.lean
  TwoSidedContext.lean
  Descriptor.lean
  ResidualConcept.lean
  Summary.lean

  Transport.lean
  Bracketing.lean
  ProductiveFirst.lean
  PaperFacing.lean

  InverseKernel.lean
  RoundTripKernel.lean
  IntendedCopyEquiv.lean
  RuleLiftSummary.lean
  StateRuleIsoKernel.lean

  DerivationLiftKernel.lean
  StartLanguageKernel.lean

  KeptStateKernel.lean
  RepresentationKernel.lean
  PaperFacingAdvanced.lean

  KeptStructureKernel.lean
  KeptDerivationKernel.lean
  KeptStartLanguageKernel.lean
  KeptRepresentationKernel.lean

  FiniteUniverseKernel.lean
  FiniteRepresentationKernel.lean
  PaperFacingFinite.lean

  FiniteCardinalityKernel.lean
  PaperFacingCardinality.lean
  FiniteRepresentationBundle.lean

  ReachableProductiveKernel.lean
  LiftedKeptCorrectnessKernel.lean
  PaperFacingKeptCorrectness.lean

  FullRefinementKernel.lean
  FullRefinementLanguageKernel.lean
  PaperFacingFullRefinement.lean

  FullYieldKernel.lean
  FullYieldPruningKernel.lean
  PaperFacingFullYield.lean

  FullFrameReachabilityKernel.lean
  FullKeptCorrectnessKernel.lean
  PaperFacingFullKept.lean

  FullTrimmedLanguageKernel.lean
  FullMainTheoremKernel.lean
  PaperFacingFullMain.lean

  FullFiniteMainKernel.lean
  PaperFacingFullFiniteMain.lean

  FiniteClosureKernel.lean
  ProductiveReachableClosureKernel.lean
  PaperFacingFixedPoint.lean

  AlgorithmicExtractionKernel.lean
  PaperFacingAlgorithmicExtraction.lean

  AlgorithmicFullBridgeKernel.lean
  PaperFacingAlgorithmicFullBridge.lean

  FullAlgorithmicAgreementKernel.lean
  PaperFacingFullAlgorithmicAgreement.lean

  FullKeptDecidabilityKernel.lean
  AlgorithmicFiniteMainKernel.lean
  ExecutableFullKeptExtraction.lean
  DescriptorReconstructionKernel.lean
  ContextClosureCoincidenceKernel.lean
  ShortlexWitnessKernel.lean
  PaperFacingExperimentClosure.lean

  StageDecidabilityKernel.lean
  PaperFacingStageDecidability.lean

  StagePayloadBridgeKernel.lean
  RuleStageBoundaryKernel.lean
  PaperFacingRuleStageBoundary.lean

  ListCertificateKernel.lean
  PaperFacingListCertificate.lean

  ClosureTraceListKernel.lean
  PaperFacingClosureTraceList.lean

  IteratorTraceBoundaryKernel.lean
  PaperFacingIteratorTraceBoundary.lean

  ListIterateCertificateKernel.lean
  MonotoneListIteratorKernel.lean
  FiniteUniverseListEnumerationKernel.lean
  RulePredicateListCertificateKernel.lean
  ProductiveReachableIteratorCertificateKernel.lean
  PaperFacingProductiveReachableIteratorCertificate.lean

  IteratorFromDecidableIteratesKernel.lean
  PaperFacingIteratorFromDecidableIterates.lean

  IterDecidabilityKernel.lean
  ProductiveReachableStepDecidabilityKernel.lean
  PaperFacingStepDecidability.lean

  StepPreservationKernel.lean
  ConcreteStepPreservationKernel.lean
  PaperFacingFullIteratorCertificate.lean
  ActualListIteratorKernel.lean
  FiniteStabilizationBoundaryKernel.lean
  DescriptorReconstructionBoundaryKernel.lean
  PaperFacingExecutableLimit.lean

  ListStabilityKernel.lean
  ConcreteListStabilityKernel.lean
  PaperFacingListStabilityExtraction.lean

  BoundedListStabilitySearchKernel.lean
  PaperFacingBoundedStabilitySearch.lean

  ConcreteBoundedWitnessBridgeKernel.lean
  PaperFacingConcreteBoundedWitnessBridge.lean

  ConcreteTwoStageBoundedSearchKernel.lean
  PaperFacingConcreteTwoStageBoundedSearch.lean
  ConcreteTwoStageSearchCertificateKernel.lean
  PaperFacingConcreteTwoStageSearchCertificate.lean
  BoundedSearchCompletenessKernel.lean
  PaperFacingBoundedSearchCompleteness.lean
  ConcreteTwoStageSearchConsistencyKernel.lean
  PaperFacingConcreteTwoStageSearchConsistency.lean
  ConcreteTwoStageSearchSuccessKernel.lean
  PaperFacingConcreteTwoStageSearchSuccess.lean
  BoundedSearchOffsetCompletenessKernel.lean
  PaperFacingBoundedSearchOffsetCompleteness.lean
  BoundedSearchWithinBoundKernel.lean
  PaperFacingBoundedSearchWithinBound.lean
  ListGrowthStabilizationKernel.lean
  PaperFacingListGrowthStabilization.lean
  ConcreteNoStrictGrowthSearchSuccessKernel.lean
  PaperFacingConcreteNoStrictGrowthSearchSuccess.lean
  StrictGrowthWitnessFreshnessKernel.lean
  PaperFacingStrictGrowthWitnessFreshness.lean
  StrictGrowthCountingInterfaceKernel.lean
  PaperFacingStrictGrowthCountingInterface.lean
  FreshFamilyFinEmbeddingKernel.lean
  PaperFacingFreshFamilyFinEmbedding.lean
  SmallSupportObstructionKernel.lean
  PaperFacingSmallSupportObstruction.lean
  DoubletonSupportObstructionKernel.lean
  PaperFacingDoubletonSupportObstruction.lean
  CollisionObstructionBridgeKernel.lean
  PaperFacingCollisionObstructionBridge.lean
  FiniteObstructionViaCollisionKernel.lean
  PaperFacingFiniteObstructionViaCollision.lean
```

The recommended current high-level algorithmic target is:

```text
LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement
```

The recommended full finite-main target remains:

```text
LeanCfgProject.JALC.PaperFacingFullFiniteMain
```

The earlier high-level finite target remains:

```text
LeanCfgProject.JALC.FiniteRepresentationBundle
```

The original summary target remains:

```text
LeanCfgProject.JALC.Summary
```

---

## 6. Module-by-module status

### `Basic.lean`

This file defines the original finite observer infrastructure.

Checked components include:

* explicit finite monoid observer interface on words;
* observer carrier `M`;
* multiplication, unit, and monoid-law data;
* observer map on words;
* two-sided h-types with left, middle, and right monoid components;
* typed nonterminals;
* boundary pairs;
* finite carrier constructions for two-sided types and typed nonterminals;
* middle-transport operation;
* unit-transport sanity lemma.

This file establishes the initial typed finite universe used by the descriptor and residual/concept layers.

---

### `TwoSidedContext.lean`

This file defines finite h-observed two-sided contexts.

Checked components include:

* observed contexts as pairs of left and right monoid values;
* empty observed context;
* application of an observed context to a middle h-value;
* conversion from observed context plus middle value to a two-sided type;
* total observed value of a two-sided type;
* composition of observed contexts;
* identity laws for the empty observed context;
* finite universe of observed contexts.

This corresponds to the paper’s use of finite observed context data instead of raw unbounded string contexts.

---

### `Descriptor.lean`

This file defines the finite descriptor-level rule universe.

Checked components include:

* terminal rules over typed nonterminals and observed contexts;
* nullary rules;
* binary rules;
* finite universes of terminal, nullary, and binary rules;
* full descriptor universe;
* finite descriptors with start typed nonterminal and finite rule supports;
* rule-count function for finite descriptors;
* empty descriptor and its zero rule-count lemma.

This file is the formal counterpart of the paper’s descriptor-level finite representation layer.

---

### `ResidualConcept.lean`

This file defines a lightweight finite residual/concept layer over typed states and observed contexts.

Checked components include:

* typed-state carrier;
* observed-context carrier;
* incidence relation between typed states and observed contexts;
* finite extents;
* finite intents;
* state-side and context-side closure operators;
* residual concepts as finite extent/intent pairs satisfying closure equations;
* boundary-incidence sanity-check model;
* membership characterizations for finite extent and intent;
* antitonicity of extent and intent.

This file is useful infrastructure, but it is now best described as supplementary rather than the central theorem-facing part of the artifact.

---

### `Summary.lean`

This file imports the original JALC formalization modules and exposes the original paper-facing checked target.

It summarizes the checked availability of:

* finite monoid observers;
* two-sided h-types;
* observed contexts;
* typed nonterminals;
* finite descriptors;
* residual concepts;
* finite typed-state universes;
* finite observed-context universes;
* full descriptor universes.

Original CI target:

```text
LeanCfgProject.JALC.Summary
```

This target should remain in CI for continuity.

---

### `Transport.lean`

This is one of the most important theorem-facing modules.

It defines:

* `WordObserver`, an observer from words to a monoid;
* `TypedDeriv`, a typed derivation tree with yield annotation;
* `TypedCtx`, a one-hole typed context derivation;
* yield-type invariant for typed derivations;
* context-type invariant for two-sided frame transport.

The most important point is that the transport invariant is checked over an arbitrary monoid, not a commutative monoid. This matters because the two-sided frame-transport equation is orientation-sensitive:

```text
A_p^{m,n} -> B_q^{m,r*n} C_r^{m*q,n}
```

If the order of multiplication were reversed, the proof would generally fail without commutativity. Thus, this module checks the orientation-sensitive part of the paper’s typed refinement mechanism.

Checked theorem-facing content:

```text
TypedDeriv.yield_type_invariant
TypedCtx.context_type_invariant
```

Paper-level meaning:

```text
yield-type and context-type invariants for the two-sided frame-transport law,
checked over arbitrary monoids.
```

---

### `Bracketing.lean`

This module checks the finite arithmetic kernel of the bracketing non-rigidity witness.

The paper compares two presentations of the one-word language `{abc}`:

```text
G1: a(bc)
G2: (ab)c
```

over `ZMod 2`, written additively, with `h(a)=h(b)=h(c)=1`.

Checked content includes:

* definition of type triples `(yield, left frame, right frame)`;
* left-child and right-child type triple computations;
* the extracted type-triple lists for `G1` and `G2`;
* membership separation by `(0,1,0)` and `(0,0,1)`;
* confirmation that the two presentations have the same number of extracted states;
* finite arithmetic kernel of the non-rigidity argument.

Important checked statement:

```text
bracketing_nonrigidity_arithmetic_kernel
```

Paper-level meaning:

```text
The type-triple calculation used in the bracketing non-rigidity witness is
machine-checked.
```

This module does not claim to formalize the whole extraction theorem. It checks the finite calculation at the core of the example.

---

### `ProductiveFirst.lean`

This module checks the finite witness explaining why productive-first trimming is needed.

It defines a toy finite model with:

* nonterminals `X`, `Y`, `Z`;
* typed copies over `ZMod 2`;
* intended copies;
* a wrong-yield parent copy;
* a wrong-frame `Y` copy;
* binary transport in the toy example;
* full-start copies;
* full-productive copies;
* displayed full reachability;
* productive-first reachability.

Checked content includes:

* the intended binary transport;
* the spurious binary transport;
* the wrong-yield parent is a full start copy;
* the spurious `Y` copy is productive in the full refinement;
* the wrong-yield parent is not productive;
* the spurious `Y` copy is reachable in the displayed full path;
* the spurious `Y` copy is not kept after productive-first trimming;
* the intended `Y` copy is kept while the spurious `Y` copy is not.

Important checked statements:

```text
productive_first_counterexample_kernel
productive_first_keeps_intended_not_spurious
```

Paper-level meaning:

```text
A finite witness for the necessity of productive-first trimming is
machine-checked.
```

This is not a general fixed-point theorem for productive/reachable trimming. It is a finite witness corresponding to the paper’s example.

---

### `PaperFacing.lean`

This module gathers the first theorem-facing checks under stable names suitable for the paper and formalization report.

It exposes:

* checked yield-type invariant;
* checked context-type invariant;
* checked bracketing non-rigidity arithmetic kernel;
* checked productive-first counterexample kernel;
* checked finite example kernels.

Representative names:

```text
checked_yield_type_invariant
checked_context_type_invariant
checked_bracketing_nonrigidity_kernel
checked_productive_first_counterexample_kernel
checked_finite_example_kernels
```

Paper-level meaning:

```text
This module provides stable paper-facing names for the initial theorem-facing
Lean checks.
```

---

### `InverseKernel.lean`

This module defines the intended typed copy of an original state and proves basic injectivity and rule-lift injectivity.

Checked components include:

* `TypedState`;
* `StateTyping`;
* `intendedCopy`;
* intended-copy label recovery;
* injectivity of `intendedCopy`;
* predicate `IsIntended`;
* terminal, binary, and start rules over original states;
* terminal, binary, and start rules over intended typed copies;
* lifting of terminal, binary, and start rules;
* injectivity of these lifts.

Important checked statements:

```text
intendedCopy_injective
liftTerminal_injective
liftBinary_injective
liftStart_injective
```

Paper-level meaning:

```text
The state-copy map X ↦ (X, yt X, lt X, rt X) is injective, and rule lifting
along this map is injective.
```

---

### `RoundTripKernel.lean`

This module defines untyped and typed rule structures and proves preservation and reflection of rules under intended-copy lifting.

Checked components include:

* `UntypedStructure`;
* `TypedStructure`;
* `liftStructure`;
* terminal-rule preservation and reflection;
* binary-rule preservation and reflection;
* start-rule preservation and reflection;
* bundled rule-lift kernel.

Important checked statements:

```text
terminal_lift_iff
binary_lift_iff
start_lift_iff
rule_lift_kernel
```

Paper-level meaning:

```text
Terminal, binary, and start rules are preserved and reflected by the
intended-copy lift.
```

---

### `IntendedCopyEquiv.lean`

This module proves that original states are equivalent to the subtype of intended typed copies.

Checked components include:

* intended-copy subtype;
* map from original states to intended typed copies;
* inverse map by reading labels;
* left and right inverse laws;
* equivalence between original states and intended copies.

Important checked statement:

```text
intended_copy_bijection_kernel
```

Paper-level meaning:

```text
The original state type is equivalent to the subtype of intended typed copies.
```

---

### `RuleLiftSummary.lean`

This module packages the rule-preservation and rule-reflection results.

Checked components include:

* `RuleLiftSummary`;
* terminal-rule equivalence;
* binary-rule equivalence;
* start-rule equivalence;
* bundled rule-lift summary theorem.

Important checked statement:

```text
rule_lift_summary_kernel
```

Paper-level meaning:

```text
The intended-copy lift preserves and reflects terminal, binary, and start
rules.
```

---

### `StateRuleIsoKernel.lean`

This module combines state-level equivalence data with rule preservation/reflection.

Checked components include:

* `StateRuleKernel`;
* left and right inverse properties for intended-copy state equivalence;
* rule-lift summary as part of the same kernel.

Important checked statement:

```text
state_rule_kernel_for_intended_lift
```

Paper-level meaning:

```text
The intended-copy construction gives the core state-and-rule isomorphism data.
```

---

### `DerivationLiftKernel.lean`

This module defines derivations in untyped and typed rule structures and proves derivation preservation/reflection.

Checked components include:

* `UntypedDeriv`;
* `TypedRuleDeriv`;
* preservation of derivations under intended-copy lifting;
* reflection of typed derivations by reading the original label;
* derivation equivalence for intended copies.

Important checked statements:

```text
derivation_preserved
derivation_reflected
intended_derivation_lift_iff
derivation_lift_kernel
```

Paper-level meaning:

```text
Derivation trees are preserved and reflected by the intended-copy lift.
```

This is one of the key steps connecting rule-level structure to language-level preservation.

---

### `StartLanguageKernel.lean`

This module lifts the derivation result to start languages.

Checked components include:

* untyped start language;
* typed start language;
* start-language preservation under intended-copy lifting;
* start-language reflection;
* language equivalence between original and lifted intended-copy structures.

Important checked statement:

```text
start_language_kernel
```

Paper-level meaning:

```text
The lifted intended-copy structure generates the same start language as the
original structure.
```

---

### `KeptStateKernel.lean`

This module introduces a general predicate `Kept` on typed states and proves that, if kept states are exactly intended copies, then original states are equivalent to kept typed states.

Checked components include:

* `KeptSubtype`;
* map from original states to kept intended copies;
* inverse map by reading labels;
* left inverse;
* right inverse under the hypothesis that every kept typed state is intended;
* equivalence between original states and kept typed states.

Important checked statement:

```text
kept_state_equivalence_kernel
```

Paper-level meaning:

```text
If kept typed states coincide with intended copies, then original states are
equivalent to the kept typed-state subtype.
```

This isolates the kept-state correctness statement later discharged for the abstract `FullKept` predicate.

---

### `RepresentationKernel.lean`

This module packages the consequences of the kept-state/intended-copy equality.

Checked components include:

* `RepresentationKernel`;
* state equivalence;
* terminal-rule preservation/reflection;
* binary-rule preservation/reflection;
* start-rule preservation/reflection;
* start-language preservation/reflection.

Important checked statements:

```text
representationKernel_from_kept_intended
representationKernel_state_equiv
representationKernel_language
```

Paper-level meaning:

```text
Once kept typed states are known to be exactly intended copies, the
state/rule/language representation kernel follows.
```

This module is close to the main representation theorem and is now used downstream by the full-kept correctness package.

---

### `PaperFacingAdvanced.lean`

This module exposes the representation-kernel consequences under stable paper-facing names.

Checked components include:

* checked representation kernel from kept/intended equality;
* checked state equivalence consequence;
* checked language equivalence consequence.

Representative names:

```text
checked_representation_kernel_from_kept_intended
checked_state_equiv_from_kept_intended
checked_language_equivalence_from_kept_intended
```

Paper-level meaning:

```text
The main representation consequences are available from the kept-state
correctness hypothesis.
```

---

### `KeptStructureKernel.lean`

This module restricts rule structures to kept typed states.

Checked components include:

* terminal rules over kept typed states;
* binary rules over kept typed states;
* start declarations over kept typed states;
* kept-state rule structures;
* lifting terminal, binary, and start rules to kept intended copies;
* injectivity of kept rule lifts;
* preservation and reflection of kept terminal, binary, and start rules.

Important checked statements:

```text
kept_terminal_lift_iff
kept_binary_lift_iff
kept_start_lift_iff
```

Paper-level meaning:

```text
The original rule structure and the kept intended-copy structure have matching
terminal, binary, and start rules.
```

---

### `KeptDerivationKernel.lean`

This module defines derivations over kept-state structures and proves derivation preservation/reflection.

Checked components include:

* `KeptDeriv`;
* preservation of untyped derivations under kept intended-copy lifting;
* reflection of kept derivations by reading labels;
* derivation equivalence for kept intended copies.

Important checked statements:

```text
kept_derivation_lift_iff
kept_derivation_kernel
```

Paper-level meaning:

```text
Derivations are preserved and reflected between the original structure and the
kept intended-copy structure.
```

---

### `KeptStartLanguageKernel.lean`

This module lifts kept-state derivation equivalence to start-language equivalence.

Checked components include:

* kept-state start language;
* preservation of start-language membership;
* reflection of start-language membership;
* start-language equivalence for kept intended-copy lifting.

Important checked statement:

```text
kept_start_language_kernel
```

Paper-level meaning:

```text
The kept intended-copy structure generates exactly the same start language as
the original structure.
```

---

### `KeptRepresentationKernel.lean`

This module packages kept-state rule and language equivalence.

Checked components include:

* `KeptRepresentationKernel`;
* terminal-rule equivalence;
* binary-rule equivalence;
* start-rule equivalence;
* start-language equivalence.

Important checked statement:

```text
keptRepresentationKernel_holds
```

Paper-level meaning:

```text
The kept intended-copy structure preserves and reflects rules and preserves the
generated start language.
```

This module is particularly relevant to the paper’s representation theorem because it works over the kept-state structure rather than only the full lifted structure.

---

### `FiniteUniverseKernel.lean`

This module proves finite-universe kernels for the typed representation.

Checked components include equivalences between:

* typed states and a fourfold product;
* terminal rules and state-terminal pairs;
* binary rules and triples of states;
* start declarations and states;
* typed terminal rules and typed-state/terminal pairs;
* typed binary rules and triples of typed states;
* typed start declarations and typed states;
* kept terminal rules and kept-state/terminal pairs;
* kept binary rules and triples of kept states;
* kept start declarations and kept states.

It also provides finite-instance witnesses for typed states and typed rule universes.

Important checked statements:

```text
typedStateEquivProduct
typedRuleUniverses_fintype_exist
```

Paper-level meaning:

```text
The typed state and rule universes are finite when the input state set,
monoid, and alphabet are finite.
```

---

### `FiniteRepresentationKernel.lean`

This module packages finite-universe witnesses.

Checked components include:

* `FiniteTypedUniverses`;
* finite typed-state/rule universes under finite input data;
* finite kept-state subtype under decidable keptness;
* finite kept terminal/binary/start rule universes;
* `FiniteKeptUniverses`.

Important checked statements:

```text
finiteTypedUniverses_of_finite
finiteKeptUniverses_of_finite
```

Paper-level meaning:

```text
Both the full typed construction and the kept-state construction have finite
state/rule universes under finite input data.
```

---

### `PaperFacingFinite.lean`

This module exposes finite-universe results under paper-facing names.

Representative names:

```text
checked_finite_typed_universes
checked_finite_kept_universes
```

Paper-level meaning:

```text
The finite-universe part of the representation theorem is available as
paper-facing checked statements.
```

---

### `FiniteCardinalityKernel.lean`

This module records cardinality kernels for finite typed universes.

Checked components include cardinality equivalences for:

* typed states;
* terminal rules;
* binary rules;
* start rules;
* typed terminal rules;
* typed binary rules;
* typed start rules;
* kept terminal rules;
* kept binary rules;
* kept start rules.

Important checked statements:

```text
typed_cardinality_kernel
kept_cardinality_kernel
```

Paper-level meaning:

```text
The finite universes are not only finite; they are equivalent to explicit
finite product universes, with checked cardinality identities.
```

This supports the “finite representation” claim more directly than a mere existence-of-finiteness statement.

---

### `PaperFacingCardinality.lean`

This module exposes the cardinality kernels under paper-facing names.

Representative names:

```text
checked_typed_cardinality_kernel
checked_kept_cardinality_kernel
```

Paper-level meaning:

```text
The cardinality/product-universe kernels are available as paper-facing checked
statements.
```

---

### `FiniteRepresentationBundle.lean`

This module bundles the finite-universe and finite-cardinality results.

Checked components include:

* `TypedFiniteBundle`;
* `KeptFiniteBundle`;
* typed finite bundle under finite input data;
* kept finite bundle under finite input data and decidable keptness.

Important checked statements:

```text
typedFiniteBundle_of_finite
keptFiniteBundle_of_finite
```

Paper-level meaning:

```text
The finite representation side of the construction is bundled into a compact
checked target.
```

Earlier high-level target:

```text
LeanCfgProject.JALC.FiniteRepresentationBundle
```

---

### `ReachableProductiveKernel.lean`

This module introduces reachability and productivity predicates for untyped and typed rule structures.

Checked components include:

* untyped reachability;
* typed reachability;
* untyped productivity;
* typed productivity;
* preservation and reflection of reachability for intended-copy lifting;
* preservation and reflection of productivity for intended-copy lifting;
* proof that reachable typed states in the intended-copy lift are intended;
* proof that productive typed states in the intended-copy lift are intended;
* reduced untyped structures.

Important checked statements:

```text
reachable_preserved
reachable_reflected
typed_reachable_lifted_is_intended
productive_preserved
productive_reflected
typed_productive_lifted_is_intended
```

Paper-level meaning:

```text
The intended-copy lift has the expected reachability and productivity behavior.
```

---

### `LiftedKeptCorrectnessKernel.lean`

This module defines the kept predicate obtained by productivity and reachability in the intended-copy lift.

Checked components include:

* `LiftedKept`;
* intended copies are kept under reducedness;
* kept states in the intended-copy lift are intended;
* lifted kept-correctness kernel;
* representation kernel from lifted kept-correctness.

Important checked statements:

```text
liftedKept_correctness_kernel
representation_from_liftedKept_correctness
```

Paper-level meaning:

```text
For the intended-copy lift, productive and reachable typed states are exactly
the intended copies, under reducedness.
```

---

### `PaperFacingKeptCorrectness.lean`

This module exposes the intended-copy kept-correctness checks under paper-facing names.

Representative names:

```text
checked_lifted_reachable_is_intended
checked_lifted_productive_is_intended
checked_lifted_kept_correctness_kernel
checked_representation_from_lifted_kept_correctness
```

Paper-level meaning:

```text
The intended-copy lift satisfies the kept-correctness property used by the
representation kernels.
```

---

### `FullRefinementKernel.lean`

This module defines the abstract full all-copy typed refinement.

Checked components include:

* binary transport compatibility for intended state typings;
* rule-typing compatibility for original structures;
* full terminal rules;
* full binary rules;
* full start declarations;
* full typed structure;
* inclusion of intended terminal rules into the full refinement;
* inclusion of intended binary rules into the full refinement;
* inclusion of intended start declarations into the full refinement;
* inclusion of the intended-copy lift into the full all-copy typed refinement.

Important checked statements:

```text
full_terminal_contains_intended
full_binary_contains_intended
full_start_contains_intended
liftStructure_included_in_full
```

Paper-level meaning:

```text
The intended-copy lift is a substructure of the full all-copy typed refinement
under the rule-typing compatibility assumptions.
```

---

### `FullRefinementLanguageKernel.lean`

This module lifts full-refinement inclusion to derivations and start languages.

Checked components include:

* monotonicity of typed derivations under typed-structure inclusion;
* monotonicity of typed start languages under typed-structure inclusion;
* preservation of original derivations into the full refinement at intended copies;
* language inclusion from the original structure into the full all-copy refinement.

Important checked statements:

```text
typed_derivation_mono
typed_start_language_mono
full_refinement_derivation_preserved
full_refinement_language_preserved
full_refinement_language_inclusion_kernel
```

Paper-level meaning:

```text
Every original derivation and every original start-language word appears in the
full all-copy typed refinement.
```

---

### `PaperFacingFullRefinement.lean`

This module exposes the full-refinement inclusion kernels under paper-facing names.

Representative names:

```text
checked_liftStructure_included_in_full
checked_full_refinement_derivation_preserved
checked_full_refinement_language_preserved
checked_full_refinement_language_inclusion_kernel
```

Paper-level meaning:

```text
The original-to-full-refinement inclusion direction is machine-checked.
```

---

### `FullYieldKernel.lean`

This module proves yield-type invariants for full all-copy typed derivations.

Checked components include:

* word type induced by a terminal type map;
* multiplicativity of word type over append;
* yield type of every full-refinement typed derivation;
* reflection of full typed derivations to untyped derivations;
* untyped yield soundness;
* yield-correct typed copies;
* proof that every productive full-refinement copy has the correct yield;
* proof that wrong-yield copies are not productive.

Important checked statements:

```text
full_derivation_yield_type
full_derivation_reflected
full_productive_copy_correct_yield
wrong_yield_copy_not_productive
```

Paper-level meaning:

```text
Productivity in the full refinement eliminates wrong-yield copies, under
yield soundness of the original structure.
```

---

### `FullYieldPruningKernel.lean`

This module packages the yield-pruning step.

Checked components include:

* `YieldProductiveKept`;
* productive full copies imply yield-correct productive keptness;
* equivalence between yield-productive keptness and productivity under yield soundness;
* intended copies of productive untyped states are productive in the full refinement;
* intended copies survive the yield-correct productivity filter.

Important checked statements:

```text
full_productive_implies_yieldProductiveKept
yieldProductiveKept_iff_productive
intendedCopy_full_productive
intendedCopy_yieldProductiveKept
```

Paper-level meaning:

```text
The first trimming stage removes wrong-yield copies while retaining intended
productive copies.
```

---

### `PaperFacingFullYield.lean`

This module exposes the full-yield and yield-pruning kernels under paper-facing names.

Representative names:

```text
checked_full_derivation_yield_type
checked_full_derivation_reflected
checked_full_productive_copy_correct_yield
checked_wrong_yield_copy_not_productive
checked_yieldProductiveKept_iff_productive
```

Paper-level meaning:

```text
The yield side of the full-refinement pruning argument is machine-checked.
```

---

### `FullFrameReachabilityKernel.lean`

This module formalizes productive-subgrammar reachability in the full refinement and proves frame correctness.

Checked components include:

* frame-correct typed copies;
* `ProductiveReachableFull`, an inductive reachability predicate in which a binary step may be followed only when the sibling side is productive;
* preservation of untyped reachability as productive-part reachability of intended copies in the full refinement, under reducedness;
* start-frame correctness;
* left-child frame correctness using productivity of the right sibling;
* right-child frame correctness using productivity of the left sibling;
* proof that productive-part reachability forces the intended left and right frames.

Important checked statements:

```text
productiveReachableFull_preserved_of_reduced
start_frame_correct
left_frame_correct
right_frame_correct
productiveReachableFull_frame_correct
```

Paper-level meaning:

```text
In the full all-copy typed refinement, once productivity has removed wrong-yield
copies, reachability inside the productive part eliminates wrong-frame copies.
```

This is the main Lean-checked kernel corresponding to the prose claim that productive-first trimming followed by reachability leaves only intended-frame copies.

---

### `FullKeptCorrectnessKernel.lean`

This module combines full productivity and productive-part reachability.

Checked components include:

* `FullCorrectCopy`, i.e. correct yield and correct frame;
* `FullKept`, i.e. productive and productive-part reachable full-refinement copies;
* proof that a fully correct copy is intended;
* proof that every full kept copy is fully correct;
* proof that every full kept copy is intended;
* proof that every intended copy is full kept under reducedness;
* full kept-correctness kernel;
* representation kernel from full kept-correctness.

Important checked statements:

```text
fullCorrectCopy_isIntended
fullKept_correctCopy
fullKept_isIntended
intendedCopy_fullKept_of_reduced
fullKept_correctness_kernel
representation_from_fullKept_correctness
```

Paper-level meaning:

```text
Under typing compatibility, yield soundness, and reducedness, the full-kept
copies are exactly the intended copies, and the representation kernel follows.
```

---

### `PaperFacingFullKept.lean`

This module exposes the full-kept correctness kernels under paper-facing names.

Representative names:

```text
checked_productiveReachableFull_frame_correct
checked_fullKept_correctCopy
checked_fullKept_isIntended
checked_fullKept_correctness_kernel
checked_representation_from_fullKept_correctness
```

Paper-level meaning:

```text
The main kept-correctness result for the full all-copy typed refinement is
available under stable paper-facing names.
```

---

### `FullTrimmedLanguageKernel.lean`

This module uses full kept-correctness to package the language of the full-kept trimmed structure.

Checked components include:

* intended-copy proof for the `FullKept` predicate;
* full-kept kept-state structure;
* start-language equivalence between the full-kept trimmed structure and the original untyped grammar;
* quantified full-kept trimmed language kernel;
* kept representation package for the full-kept trimmed structure.

Important checked statements:

```text
fullKept_trimmed_language_iff
fullKept_trimmed_language_kernel
fullKept_trimmed_representation_kernel
```

Paper-level meaning:

```text
The structure obtained by trimming the full refinement by the full-kept predicate
generates exactly the original start language.
```

---

### `FullMainTheoremKernel.lean`

This module packages the main full-refinement theorem-level consequences.

Checked components include:

* `FullRefinementMainKernel`;
* full kept-correctness;
* full-kept trimmed language equivalence;
* representation kernel;
* language component of the main package;
* representation component of the main package.

Important checked statements:

```text
full_refinement_main_kernel
full_refinement_main_language
full_refinement_main_representation
```

Paper-level meaning:

```text
The main full-refinement representation package is machine-checked, conditional
on the stated compatibility, yield-soundness, and reducedness assumptions.
```

---

### `PaperFacingFullMain.lean`

This module exposes the main full-refinement theorem package under paper-facing names.

Representative names:

```text
checked_fullKept_trimmed_language_kernel
checked_full_refinement_main_kernel
checked_full_refinement_main_representation
```

Paper-level meaning:

```text
The full-kept trimming theorem and its representation consequence are available
as stable paper-facing Lean targets.
```

---

### `FullFiniteMainKernel.lean`

This module connects the full main theorem package to the finite-representation kernels.

Checked components include:

* `FullFiniteMainKernel`;
* full main theorem package;
* finite typed-state and typed-rule universe bundle;
* finite kept-state and kept-rule universe bundle for `FullKept`;
* full-kept trimmed language equivalence;
* full-kept representation kernel;
* finite typed-universe component;
* finite kept-universe component.

Important checked statements:

```text
full_finite_main_kernel
full_finite_main_language
full_finite_main_kept_finite
full_finite_main_typed_finite
```

Paper-level meaning:

```text
Under finite input data and decidable FullKept membership, the full-kept
construction gives a finite kept-state representation with the same start
language as the original grammar.
```

The decidability assumption is explicit and should be read as the boundary
between the mathematical kept predicate and an executable extraction procedure.

---

### `PaperFacingFullFiniteMain.lean`

This module exposes the finite full-main theorem package under paper-facing names.

Representative names:

```text
checked_full_finite_main_kernel
checked_full_finite_main_language
checked_full_finite_main_kept_finite
```

Paper-level meaning:

```text
The current top-level paper-facing target checks the finite full-main
representation package.
```

Earlier full finite-main top-level target:

```text
LeanCfgProject.JALC.PaperFacingFullFiniteMain
```

Recorded full finite-main CI:

```text
Lean CI #292
Commit: d02ac8d
```

The newer algorithmic agreement target is recorded below in
`PaperFacingFullAlgorithmicAgreement.lean`.

---

### `FiniteClosureKernel.lean`

This module introduces a small general-purpose finite-closure certificate layer
for monotone predicate iteration.

Checked components include:

* predicate inclusion;
* monotonicity;
* pre-fixed and fixed predicates;
* finite iteration certificates;
* certified closure;
* fixedness of the certified closure;
* least-pre-fixedness of the certified closure.

Important checked statements:

```text
certifiedClosure_fixed
certifiedClosure_least_prefixed
```

Paper-level meaning:

```text
The fixed-point part of Algorithm 1 is represented by a reusable certified
closure kernel.
```

This is not yet an extracted iterator that constructs certificates
automatically; it is a theorem-facing certificate interface for finite
fixed-point computations.

---

### `ProductiveReachableClosureKernel.lean`

This module instantiates the finite-closure certificate layer for the two stages
of Algorithm 1.

Checked components include:

* productivity step from terminal and binary rule predicates;
* monotonicity of the productivity step;
* certified productivity closure;
* reachability step inside a fixed productive predicate;
* monotonicity of productive-part reachability;
* certified reachable closure;
* computed keptness as the intersection of computed productivity and computed reachability.

Important checked statements:

```text
productiveClosure_fixed
productiveClosure_least_prefixed
reachableClosure_fixed
reachableClosure_least_prefixed
computedKept_productive
computedKept_reachable
```

Paper-level meaning:

```text
The productive-first and productive-part reachability structure of Algorithm 1
is machine-checked at the certified fixed-point level.
```

---

### `PaperFacingFixedPoint.lean`

This module exposes the finite fixed-point and productive/reachable closure
kernels under stable paper-facing names.

Representative names:

```text
checked_productiveClosure_fixed
checked_reachableClosure_fixed
checked_computedKept_productive
checked_computedKept_reachable
```

Paper-level meaning:

```text
The fixed-point skeleton used by Algorithm 1 is available as a paper-facing
Lean target.
```

---

### `AlgorithmicExtractionKernel.lean`

This module packages the fixed-point closure kernels in the shape of Algorithm 1.

Checked components include:

* `ExtractionRuleData`, consisting of terminal, binary, and start predicates;
* `CertifiedExtraction`, consisting of a productivity certificate followed by a productive-part reachability certificate;
* `computedProductive`;
* `computedReachable`;
* `computedKept`;
* fixedness and least-pre-fixedness of both computed stages;
* keptness as the intersection of the two computed stages;
* bundled certified extraction kernel.

Important checked statements:

```text
computedProductive_fixed
computedProductive_least_prefixed
computedReachable_fixed
computedReachable_least_prefixed
computedKept_iff
certifiedExtractionKernel_holds
algorithmic_extraction_kernel
```

Paper-level meaning:

```text
Algorithm 1 is represented as a certified two-stage fixed-point extraction
package.
```

---

### `PaperFacingAlgorithmicExtraction.lean`

This module exposes the certified Algorithm 1 extraction package under stable
paper-facing names.

Representative names:

```text
checked_algorithmic_productive_fixed
checked_algorithmic_reachable_fixed
checked_algorithmic_kept_iff
checked_algorithmic_extraction_kernel
checked_certifiedExtractionKernel_holds
```

Paper-level meaning:

```text
The paper-facing artifact includes a certified Algorithm 1 kernel.
```

---

### `AlgorithmicFullBridgeKernel.lean`

This module bridges the certified Algorithm 1 package to the full-kept theorem
package.

Checked components include:

* `ComputedAgreesWithFullKept`;
* transfer of intended-copy keptness from `FullKept` to computed keptness under agreement;
* transfer of intendedness of computed kept states under agreement;
* representation kernel for the computed kept predicate under agreement;
* computed kept-state structure;
* computed trimmed language equivalence under agreement;
* bundled algorithmic/full bridge.

Important checked statements:

```text
computed_kept_correctness_kernel
representation_from_computed_agreement
computed_trimmed_language_kernel
algorithmic_full_bridge_kernel
```

Paper-level meaning:

```text
Once a computed kept predicate is identified with the abstract FullKept
predicate, the existing full-kept correctness, language, and representation
kernels transfer to the computed predicate.
```

---

### `PaperFacingAlgorithmicFullBridge.lean`

This module exposes the algorithmic/full bridge under stable paper-facing names.

Representative names:

```text
checked_computed_kept_correctness_kernel
checked_computed_trimmed_language_kernel
checked_representation_from_computed_agreement
checked_algorithmic_full_bridge_kernel
```

Paper-level meaning:

```text
The conditional bridge from Algorithm 1 output to the full-kept theorem package
is available as a paper-facing target.
```

---

### `FullAlgorithmicAgreementKernel.lean`

This module closes the previous bridge for the concrete full all-copy typed rule
data.

Checked components include:

* `fullExtractionRuleData`, the Algorithm 1 rule data induced by `fullTypedStructure tau G`;
* pre-fixedness of typed productivity for the full rule data;
* agreement between computed productivity and `TypedProductive (fullTypedStructure tau G)`;
* pre-fixedness of productive-part reachability for the computed productive predicate;
* inclusion from computed reachability to `ProductiveReachableFull`;
* helper lemmas for terminal, binary, start, left-child, and right-child steps;
* inclusion from `ProductiveReachableFull` back to computed reachability for productive states;
* direct agreement theorem between computed keptness and `FullKept`;
* closed algorithmic/full bridge theorem for the concrete full rule data.

Important checked statements:

```text
fullExtractionRuleData
full_computedProductive_agrees
full_computedReachable_to_productiveReachable
full_productiveReachable_to_computedReachable_of_productive
fullAlgorithmicComputedKept_agrees
closed_algorithmic_full_bridge_kernel
```

Paper-level meaning:

```text
For the concrete terminal, binary, and start predicates of the full all-copy
typed refinement, a certified run of Algorithm 1 computes exactly the abstract
FullKept predicate used in the main theorem.
```

This removes the previous assumption-level bridge condition
`ComputedAgreesWithFullKept` for the concrete full rule data.  The remaining
algorithmic boundary is not this agreement theorem, but the extraction of an
actual executable fixed-point implementation and automatic construction of the
certificates from finite data.

---

### `PaperFacingFullAlgorithmicAgreement.lean`

This module exposes the direct full algorithmic agreement result under stable
paper-facing names.

Representative names:

```text
checked_fullExtractionRuleData
checked_full_computedProductive_agrees
checked_full_computedReachable_to_productiveReachable
checked_fullAlgorithmicComputedKept_agrees
checked_closed_algorithmic_full_bridge_kernel
```

Paper-level meaning:

```text
This is the current high-level algorithmic target.  It checks that Algorithm 1,
when instantiated with the concrete full all-copy rule data, computes exactly
the FullKept predicate and therefore closes the algorithmic/full bridge.
```

Current high-level algorithmic target:

```text
LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement
```

Latest recorded CI:

```text
Lean CI #304
Commit: a434bb3
Pushed by: growupkuriyama-hub
```


---


### `FullKeptDecidabilityKernel.lean`

This module records the decidability-transfer boundary from the computed kept
predicate to the abstract `FullKept` predicate.

Checked components include:

* a decidability package for `computedKept`;
* transfer of decidability along the checked agreement theorem;
* production of `Nonempty (DecidablePred (FullKept tau G))` from a certified
  run whose computed-kept predicate is decidable.

Paper-level meaning:

```text
If the certified Algorithm 1 run supplies a decidable computed-kept predicate,
then the abstract FullKept predicate used in the main theorem is decidable.
```

---

### `AlgorithmicFiniteMainKernel.lean`

This module connects certified algorithmic decidability to the finite-main
theorem layer.

Checked components include:

* a boundary package connecting Algorithm 1 output to the finite-main theorem;
* transfer from executable/certified keptness data to the full finite-main
  theorem package.

Paper-level meaning:

```text
The finite-main representation package can be reached from the certified
Algorithm 1 boundary once the required keptness decidability is supplied.
```

---

### `ExecutableFullKeptExtraction.lean`

This module introduces the executable-payload boundary for `FullKept`
extraction.

Checked components include:

* an executable-style payload consisting of a certified extraction and a
  decidable computed-kept predicate;
* transfer from this payload to the algorithmic finite-main boundary.

Paper-level meaning:

```text
This is the first executable-facing interface: a certified extraction plus a
decidable computed-kept predicate is enough to reach the finite representation
package.
```

It is not yet a construction of the payload from arbitrary finite input data.

---

### `DescriptorReconstructionKernel.lean`

This module records descriptor-reconstruction as a future boundary.

Checked components include:

* theorem-facing markers separating descriptor reconstruction from the current
  certified extraction chain.

Paper-level meaning:

```text
Descriptor reconstruction from the computed kept universe remains a later
implementation/formalization phase.
```

---

### `ContextClosureCoincidenceKernel.lean`

This module records context-closure coincidence as a future boundary.

Checked components include:

* theorem-facing markers for the context-closure coincidence phase.

Paper-level meaning:

```text
Full context-closure coincidence for arbitrary one-hole contexts remains outside
the present artifact.
```

---

### `ShortlexWitnessKernel.lean`

This module records shortlex witness normalization as a future boundary.

Checked components include:

* theorem-facing markers for shortlex witness preservation/normalization.

Paper-level meaning:

```text
Shortlex witness normalization is recognized as a future phase and is not
claimed as part of the current checked theorem package.
```

---

### `PaperFacingExperimentClosure.lean`

This module exposes the final-artifact and experiment-closure boundary under a
paper-facing target.

Representative checked target:

```text
LeanCfgProject.JALC.PaperFacingExperimentClosure
```

Recorded CI:

```text
Lean CI #307
Commit: 2cde4a4
Target: LeanCfgProject.JALC.PaperFacingExperimentClosure
```

Paper-level meaning:

```text
The theorem-facing certified Algorithm 1 agreement is connected to a finite
decidability/extraction boundary, while descriptor reconstruction,
context-closure coincidence, and shortlex normalization are explicitly separated
as future phases.
```

---

### `StageDecidabilityKernel.lean`

This module reduces computed-kept decidability to the two stage decisions of
Algorithm 1.

Checked components include:

* construction of `DecidablePred (computedKept E)` from
  `DecidablePred (computedProductive E)` and
  `DecidablePred (computedReachable E)`;
* a `StageDecidableCertifiedRun` payload;
* transfer from a stage-decidable certified run to `FullKept` decidability.

Paper-level meaning:

```text
The kept-state decision problem splits into the productive and reachable stage
decisions of Algorithm 1.
```

---

### `PaperFacingStageDecidability.lean`

This module exposes the stage-decidability boundary under stable paper-facing
names.

Representative target:

```text
LeanCfgProject.JALC.PaperFacingStageDecidability
```

Paper-level meaning:

```text
A certified Algorithm 1 run with decidable productive and reachable stages
supplies decidable FullKept membership.
```

---

### `StagePayloadBridgeKernel.lean`

This module connects a stage-decidable certified run to the executable payload
boundary.

Checked components include:

* construction of `ExecutableFullKeptExtractionData tau G` from a
  `StageDecidableCertifiedRun tau G`;
* transfer to the algorithmic finite-main boundary.

Paper-level meaning:

```text
The two stage decisions provide the executable-facing computed-kept decision
payload.
```

---

### `RuleStageBoundaryKernel.lean`

This module records a richer rule-stage payload.

Checked components include:

* decidable terminal, start, and binary predicates for the concrete full rule
  data;
* decidable computed productive and reachable stages;
* transfer from this richer payload to `FullKept` decidability.

Paper-level meaning:

```text
This records the rule-predicate decisions that a later finite enumerator should
supply, while still using the stage-decidability boundary for the closure
stages.
```

---

### `PaperFacingRuleStageBoundary.lean`

This module exposes the rule-stage boundary under stable paper-facing names.

Representative target:

```text
LeanCfgProject.JALC.PaperFacingRuleStageBoundary
```

Paper-level meaning:

```text
Decidable rule predicates and decidable productive/reachable stages are a
sufficient certified boundary for FullKept decidability.
```

---

### `ListCertificateKernel.lean`

This module introduces finite list certificates for predicates.

Checked components include:

* `ListPredicateCertificate P`, consisting of a finite support list, soundness,
  and completeness;
* construction of `DecidablePred P` from a list certificate;
* binary-triple predicates for curried binary rule predicates;
* construction of stage-list and rule-list boundary payloads from list
  certificates.

Paper-level meaning:

```text
A finite list exactly representing a predicate gives a machine-checked
decidability package for that predicate.
```

---

### `PaperFacingListCertificate.lean`

This module exposes the list-certificate boundary under a paper-facing target.

Representative target:

```text
LeanCfgProject.JALC.PaperFacingListCertificate
```

Paper-level meaning:

```text
Finite list certificates for computedProductive and computedReachable are enough
to obtain FullKept decidability.
```

---

### `ClosureTraceListKernel.lean`

This module connects list certificates to the certified closure heights inside a
`CertifiedExtraction`.

Checked components include:

* productive trace-list certificates at `E.productiveCert.height`;
* reachable trace-list certificates at `E.reachableCert.height`;
* conversion of these trace-list certificates into list certificates for
  `computedProductive E` and `computedReachable E`;
* transfer from trace-list data to `FullKept` decidability.

Paper-level meaning:

```text
Finite lists representing the certified closure iterates at the two Algorithm 1
heights are enough to recover decidable productive/reachable stage predicates.
```

---

### `PaperFacingClosureTraceList.lean`

This module exposes the closure trace-list boundary.

Representative target:

```text
LeanCfgProject.JALC.PaperFacingClosureTraceList
```

Paper-level meaning:

```text
The certified productivity and reachability closure heights are connected to
finite list certificates.
```

---

### `IteratorTraceBoundaryKernel.lean`

This module bundles rule-list data and closure-trace data into one iterator
trace payload.

Checked components include:

* `IteratorTraceBoundaryData`, containing terminal, start, binary, productive
  trace, and reachable trace list certificates;
* transfer to `StageTraceListBoundaryData`;
* transfer to `RuleListBoundaryData`;
* two independent routes to `FullKept` decidability.

Paper-level meaning:

```text
The finite output that a later iterator should return is organized as a single
payload that reaches FullKept decidability.
```

---

### `PaperFacingIteratorTraceBoundary.lean`

This module exposes the iterator trace boundary.

Representative target:

```text
LeanCfgProject.JALC.PaperFacingIteratorTraceBoundary
```

Paper-level meaning:

```text
Rule-list certificates and closure-trace list certificates combine into a
single finite iterator-output boundary.
```

---

### `ListIterateCertificateKernel.lean`

This module introduces list certificates for finite iterates.

Checked components include:

* `ListIterateCertificate F n`;
* productive iterate certificates at the certified productivity height;
* reachable iterate certificates at the certified reachability height;
* conversion to the previous closure trace-list boundary;
* transfer from iterate-list data to `FullKept` decidability.

Paper-level meaning:

```text
Finite list certificates for specific finite iterates are the immediate output
format expected from a later list-based iterator.
```

---

### `MonotoneListIteratorKernel.lean`

This module records the output interface for a list iterator.

Checked components include:

* `ListIteratorOutput F n`;
* productive and reachable iterator output abbreviations;
* conversion from iterator outputs to iterate-list boundary data;
* transfer from stage iterator outputs to `FullKept` decidability.

Paper-level meaning:

```text
A list iterator that outputs certificates for the two certified closure heights
is enough to feed the existing FullKept decidability chain.
```

---

### `FiniteUniverseListEnumerationKernel.lean`

This module records complete finite universe lists and filtering.

Checked components include:

* `UniverseList α`, a finite list containing all elements of `α`;
* conversion of a decidable predicate and a complete universe list into a
  `ListPredicateCertificate`;
* typed-state and binary-triple universe-list aliases;
* bundled state/triple universe lists for rule predicates.

Recorded CI:

```text
Lean CI #314
Status: succeeded
```

Paper-level meaning:

```text
Once a finite universe is listed and a predicate is decidable, filtering the
universe gives a finite list certificate for the predicate.
```

---

### `RulePredicateListCertificateKernel.lean`

This module constructs rule-predicate list certificates from finite universe
lists and rule-predicate decisions.

Checked components include:

* decidability payload for terminal, start, and binary rule predicates;
* terminal-list certificate by filtering the state universe;
* start-list certificate by filtering the state universe;
* binary-list certificate by filtering the binary-triple universe;
* bundled `FullRuleListCertificates`.

Paper-level meaning:

```text
The terminal, start, and binary rule predicates of the concrete full rule data
can be represented by finite list certificates when supplied with finite
universe lists and predicate decisions.
```

---

### `ProductiveReachableIteratorCertificateKernel.lean`

This module combines rule-list certificates and iterator outputs into the final
pre-implementation payload.

Checked components include:

* `ProductiveReachableIteratorCertificateData`;
* conversion to `IteratorTraceBoundaryData`;
* transfer to `FullKept` decidability through both trace-list and rule-list
  routes;
* exposure of productive/reachable list certificates.

Representative target:

```text
LeanCfgProject.JALC.PaperFacingProductiveReachableIteratorCertificate
```

Paper-level meaning:

```text
Rule-list certificates plus productive/reachable iterator outputs form the
pre-implementation payload that reaches FullKept decidability.
```

---

### `PaperFacingProductiveReachableIteratorCertificate.lean`

This module exposes the productive/reachable iterator certificate boundary.

Representative target:

```text
LeanCfgProject.JALC.PaperFacingProductiveReachableIteratorCertificate
```

Paper-level meaning:

```text
This target checks the final finite-output interface immediately before
implementing the fixed-point iterator itself.
```

---

### `IteratorFromDecidableIteratesKernel.lean`

This module builds iterator outputs from decidable iterates by filtering a
complete finite state universe.

Checked components include:

* construction of `ListIteratorOutput F n` from a complete universe list and
  `DecidablePred (Iter F n)`;
* `ProductiveReachableIterateDecisionData`;
* construction of productive and reachable iterator outputs from iterate
  decisions;
* transfer to `ProductiveReachableIteratorCertificateData`;
* transfer to `FullKept` decidability.

Paper-level meaning:

```text
If the productive and reachable iterate predicates at the certified heights are
decidable, then complete finite state-universe lists can be filtered to produce
the required iterator outputs.
```

---

### `PaperFacingIteratorFromDecidableIterates.lean`

This module exposes the iterator-from-decidable-iterates boundary.

Representative target:

```text
LeanCfgProject.JALC.PaperFacingIteratorFromDecidableIterates
```

Paper-level meaning:

```text
Decidable productive/reachable iterates can be converted into finite iterator
outputs by finite-universe filtering.
```

---

### `IterDecidabilityKernel.lean`

This module proves the generic finite-iterate decidability recursion.

Checked components include:

* `PreservesDecidablePred F`;
* recursive construction of `DecidablePred (Iter F n)` for every finite `n`
  when `F` preserves decidability;
* construction of list-iterator output from a decidability-preserving step and
  a complete finite universe list;
* a generic decidable iterator data package.

Important checked statements:

```text
decidablePred_iter
decidablePred_iter_nonempty
listIteratorOutput_of_preservesDecidable
```

Paper-level meaning:

```text
A finite iterate does not need decidability as a separate assumption if the step
itself preserves decidability.
```

---

### `ProductiveReachableStepDecidabilityKernel.lean`

This module specializes finite-iterate decidability to the productive and
reachable closure steps.

Checked components include:

* `ProductiveReachableStepDecidabilityData`;
* productive iterate decidability from productive-step decidability
  preservation;
* reachable iterate decidability from reachable-step decidability preservation;
* conversion to the previous iterate-decision data;
* transfer to `FullKept` decidability.

Paper-level meaning:

```text
If the productive and reachable closure steps preserve decidability, then the
certified productive/reachable iterates are decidable and the FullKept
decidability chain follows.
```

---

### `PaperFacingStepDecidability.lean`

This module exposes the most recent executable-interface theorem.

Representative target:

```text
LeanCfgProject.JALC.PaperFacingStepDecidability
```

Latest status:

```text
Status: succeeded
Reported by user after fixing IterDecidabilityKernel.lean
```

Paper-level meaning:

```text
The current artifact has reached the point where finite-iterate decidability is
reduced to decidability preservation of the productive and reachable steps.
```

This is still not a full executable fixed-point implementation.  The next
natural target is to prove that the concrete `ProductiveStep` and
`ReachableStep` preserve decidability from decidable terminal, start, binary,
and previous-stage predicates.

---

## 7. Current CI guard

The intended policy for the JALC Lean directory remains:

```text
no proof-bypassing placeholder commands
no extra primitive declarations
```

The GitHub Actions workflow checks the JALC Lean directory for the corresponding terms.

Recommended CI workflow:

```text
lake build LeanCfgProject.JALC.Summary
lake build LeanCfgProject.JALC.PaperFacingFullFiniteMain
lake build LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement
lake build LeanCfgProject.JALC.PaperFacingExperimentClosure
lake build LeanCfgProject.JALC.PaperFacingProductiveReachableIteratorCertificate
lake build LeanCfgProject.JALC.PaperFacingIteratorFromDecidableIterates
lake build LeanCfgProject.JALC.PaperFacingStepDecidability
```

followed by the placeholder guard.

A minimal workflow for checking only the newest theorem-facing package may build:

```text
lake build LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement
```

Because `PaperFacingFullAlgorithmicAgreement.lean` imports the full algorithmic agreement kernel, which imports the certified extraction, full bridge, full-kept, and full finite-main dependencies, building this target checks the newest extended artifact without listing every intermediate module.  `PaperFacingFullFiniteMain.lean` should still be kept as a stable full finite-main theorem target.

---

## 8. What is claimed

The current Lean development checks the finite typed infrastructure and a broad set of theorem-facing kernels for the paper.

In particular, it checks:

* finite observer and descriptor infrastructure;
* two-sided context infrastructure;
* a residual/concept support layer;
* orientation-sensitive frame transport over arbitrary monoids;
* yield-type and context-type invariants;
* finite non-rigidity witness calculations;
* finite productive-first trimming witness calculations;
* intended-copy injectivity and equivalence;
* preservation and reflection of terminal, binary, and start rules;
* preservation and reflection of derivations;
* preservation and reflection of start-language membership;
* kept-state rule, derivation, and language kernels;
* finite universe and finite cardinality kernels;
* intended-copy reachability/productivity kernels;
* full all-copy typed refinement;
* original-to-full inclusion;
* full derivation yield invariants;
* elimination of wrong-yield productive copies;
* elimination of wrong-frame copies by productive-part reachability;
* full-kept correctness;
* full-kept trimmed language equivalence;
* finite full-main theorem package;
* finite fixed-point closure certificates;
* certified productivity and productive-part reachability closures;
* certified Algorithm 1 extraction package;
* bridge from computed keptness to full-kept correctness/language/representation kernels;
* direct agreement theorem: Algorithm 1 over the concrete full all-copy rule data computes exactly `FullKept`;
* decidability transfer from `computedKept` to `FullKept`;
* reduction of `computedKept` decidability to `computedProductive` and `computedReachable` decidability;
* finite list certificate interface for predicate decidability;
* closure trace-list certificate interface for the certified productivity and reachability heights;
* iterator trace boundary bundling rule-list and closure-trace data;
* productive/reachable iterator certificate boundary;
* finite-universe filtering interface for building iterator outputs from decidable iterates;
* generic finite-iterate decidability from a decidability-preserving step.

Thus, the artifact now supports a much stronger claim than the original baseline. It is no longer only a finite-carrier consistency check; it verifies the main mathematical kernels surrounding the finite representation theorem, including the full-kept correctness statement for the abstract full-refinement construction.

---

## 9. What is not claimed

The current Lean development is not a complete executable end-to-end formalization of the full paper.

The most important remaining components are:

```text
extracted implementation of the fixed-point algorithm
automatic construction of fixed-point certificates from finite input data
decidability and computation of FullKept membership as executable code
end-to-end descriptor reconstruction from arbitrary CFG presentation data
```

More explicitly, the current development does not yet fully formalize:

* the concrete extraction algorithm from arbitrary CFG presentations;
* an extracted executable productive-first and reachable trimming procedure;
* automatic construction of the fixed-point certificates used by `CertifiedExtraction`;
* proof that a concrete bounded search necessarily succeeds within a specified
  finite support bound;
* an extracted terminating list-based fixed-point iterator;
* decidability of `FullKept` membership as an extracted procedure;
* shortlex witness preservation;
* full context-closure coincidence for all one-hole contexts;
* complete descriptor reconstruction from arbitrary presentation data.

The current artifact proves the mathematical kept-correctness, finite-representation, and certified algorithmic agreement packages for the abstract full-refinement construction under explicit assumptions:

```text
TypingCompatible tau T G
UntypedYieldSound tau T G
UntypedReduced G
DecidablePred (FullKept tau G)
Fintype V, Fintype M, Fintype Sigma
CertifiedExtraction (fullExtractionRuleData tau G)
```

The last assumption is a certificate-level formulation of the two fixed-point computations in Algorithm 1.  It is weaker than an extracted executable implementation, but stronger than a prose-level algorithmic claim: the artifact proves that any certified run over the concrete full all-copy rule data computes exactly `FullKept`.

This boundary should be stated explicitly in the paper.

---

## 10. Suggested paper wording

The following wording is recommended for the paper or appendix.

```text
An accompanying Lean 4 development checks theorem-facing kernels of the finite
representation theorem.  The checked modules include the original finite typed
infrastructure for observers, two-sided h-types, observed contexts and finite
descriptors, and additional kernels for the two-sided frame-transport
invariants, non-rigidity and productive-first examples, intended-copy state
equivalence, rule preservation and reflection, derivation and start-language
preservation, kept-state representation kernels, finite-universe/cardinality
kernels, full all-copy refinement, full-refinement yield and frame kernels,
full-kept correctness, full-kept trimmed language equivalence, a finite
full-main theorem package, certified fixed-point extraction kernels, and a
direct agreement theorem showing that Algorithm 1 over the concrete full
all-copy rule data computes exactly the abstract FullKept predicate.  In
particular, the frame-transport invariants are checked over arbitrary monoids,
so the checked proof does not rely on commutativity.
```

The boundary should be stated as follows.

```text
The development is not claimed to be a complete executable formalization of the
full extraction algorithm.  The current top-level theorem package assumes the
typing-compatibility, yield-soundness and reducedness conditions for the
abstract full refinement, assumes decidability of the FullKept predicate when
deriving the finite-main package, and represents Algorithm 1 by certified
fixed-point closures rather than by extracted executable code.  The automatic
construction of these certificates and the end-to-end descriptor reconstruction
from arbitrary CFG presentation data remain outside the present Lean artifact.
```

A shorter version:

```text
The Lean 4 artifact checks the finite typed infrastructure and several
theorem-facing kernels of the representation theorem, including
orientation-sensitive frame transport over arbitrary monoids, finite
non-rigidity and productive-first witnesses, intended-copy state equivalence,
rule/derivation/language preservation, full-refinement yield and frame
invariants, full-kept correctness, full-kept trimmed language equivalence, and a
finite full-main theorem package, and certified Algorithm 1 kernels proving
that the concrete full all-copy rule data computes the abstract FullKept
predicate.  We do not claim an extracted executable implementation of the full
extraction algorithm; automatic certificate construction and complete descriptor
reconstruction remain outside the present artifact.
```

---

## 11. Reproduction instructions

At the root of the repository, run:

```text
lake build LeanCfgProject.JALC.Summary
lake build LeanCfgProject.JALC.PaperFacingFullFiniteMain
lake build LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement
lake build LeanCfgProject.JALC.PaperFacingExperimentClosure
lake build LeanCfgProject.JALC.PaperFacingProductiveReachableIteratorCertificate
lake build LeanCfgProject.JALC.PaperFacingIteratorFromDecidableIterates
lake build LeanCfgProject.JALC.PaperFacingStepDecidability
```

Expected checked targets:

```text
LeanCfgProject.JALC.Summary
LeanCfgProject.JALC.PaperFacingFullFiniteMain
LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement
```

Reference baseline CI run:

```text
Lean CI #236
Commit: a4e2d6a
```

Latest successful full finite-main CI run:

```text
Lean CI #292
Commit: d02ac8d
Pushed by: growupkuriyama-hub
```

Latest successful algorithmic agreement CI run:

```text
Lean CI #304
Commit: a434bb3
Pushed by: growupkuriyama-hub
```

Latest recorded experiment-closure CI run:

```text
Lean CI #307
Commit: 2cde4a4
Pushed by: growupkuriyama-hub
Target: LeanCfgProject.JALC.PaperFacingExperimentClosure
```

Latest recorded finite-universe filtering / iterator-boundary CI run:

```text
Lean CI #314
Status: succeeded
```

Latest user-reported executable-interface target:

```text
LeanCfgProject.JALC.PaperFacingStepDecidability
Status: succeeded
```

---

## 12. Recommended citation in the paper

A concise citation in the paper can be written as:

```text
The accompanying Lean 4 artifact checks the modules
LeanCfgProject.JALC.Summary, LeanCfgProject.JALC.PaperFacingFullFiniteMain, and
LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement.  The baseline
reference run was Lean CI #236 at commit a4e2d6a; the full finite-main run was
Lean CI #292 at commit d02ac8d; and the latest algorithmic agreement run
reported here is Lean CI #304 at commit a434bb3.
```

A more descriptive version is:

```text
The finite typed architecture and theorem-facing kernels were checked in Lean 4.
The checked development includes finite observers, two-sided h-types, observed
contexts, finite descriptors, transport invariants over arbitrary monoids,
finite example kernels, intended-copy state/rule/derivation/language kernels,
kept-state representation kernels, full-refinement yield and frame kernels,
full-kept correctness, full-kept trimmed language equivalence, and
finite-universe/cardinality kernels, certified fixed-point extraction kernels,
and a direct agreement kernel proving that Algorithm 1 over the concrete
full all-copy rule data computes FullKept.  The current high-level algorithmic
target is LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement, together with
the full finite-main target LeanCfgProject.JALC.PaperFacingFullFiniteMain and
the original summary target LeanCfgProject.JALC.Summary.
```

---

## 13. Practical assessment

As a JALC companion artifact, the current development is very strong.

A fair assessment is:

```text
JALC submission support: very high
Complete executable main-theorem formalization: still partial
Mathematical full-refinement main kernel: substantially checked
Finite representation side: substantially checked
Extraction/trimming algorithm: certified-kernel level, not executable-code level
```

Approximate internal assessment:

```text
JALC-facing Lean value: 98--99 / 100
Full mathematical main-kernel formalization: 88--91 / 100
Finite-representation side: 90--93 / 100
Certified Algorithm 1 / FullKept agreement: 91--94 / 100
Executable extraction/fixed-point implementation: 58--65 / 100
Executable-interface boundary toward fixed-point extraction: 78--84 / 100
```

These numbers should not be written in the paper, but they are useful for internal planning.

---

## 14. Next possible Lean targets

The next serious formalization target would be:

```text
ExecutableFullKeptExtraction.lean
```

Goal:

```text
construct the fixed-point certificates used by CertifiedExtraction from finite
input data, yielding an executable productive-first and reachable trimming
procedure over the full all-copy typed universe
```

The agreement theorem itself is now checked by:

```text
FullAlgorithmicAgreementKernel.lean
PaperFacingFullAlgorithmicAgreement.lean
```

The remaining executable target would require formalizing:

* finite enumeration of the full all-copy typed rule universe;
* decidable terminal, binary, and start predicates for `fullExtractionRuleData`;
* construction of productivity fixed-point certificates;
* construction of productive-part reachability fixed-point certificates;
* extraction of a decidable `FullKept` predicate from these certificates;
* optional extraction of a finite descriptor from the computed kept universe.

A second possible target is:

```text
DescriptorReconstructionKernel.lean
```

Goal:

```text
construct an explicit finite descriptor from the full-kept finite universe and
prove that it presents the same start language
```

This would connect the current theorem-facing representation package even more directly to the paper’s descriptor-level output.

These targets are harder than the current packaging kernels. They are the right next steps only after the current artifact is recorded in the paper and formalization report.


---

## 15. Update after CI #304: executable-interface chain through step decidability

This section records the Lean work added after the `PaperFacingFullAlgorithmicAgreement`
target.

### 15.1 Confirmed targets

The post-#304 executable-interface chain introduced and checked the following
paper-facing targets:

```text
LeanCfgProject.JALC.PaperFacingExperimentClosure
LeanCfgProject.JALC.PaperFacingStageDecidability
LeanCfgProject.JALC.PaperFacingRuleStageBoundary
LeanCfgProject.JALC.PaperFacingListCertificate
LeanCfgProject.JALC.PaperFacingClosureTraceList
LeanCfgProject.JALC.PaperFacingIteratorTraceBoundary
LeanCfgProject.JALC.PaperFacingProductiveReachableIteratorCertificate
LeanCfgProject.JALC.PaperFacingIteratorFromDecidableIterates
LeanCfgProject.JALC.PaperFacingStepDecidability
```

The most recent target reported successful by the user is:

```text
LeanCfgProject.JALC.PaperFacingStepDecidability
```

### 15.2 Conceptual chain now checked

The checked executable-interface chain can be summarized as:

```text
CertifiedExtraction (fullExtractionRuleData tau G)
+ computedProductive / computedReachable stage decisions
  => computedKept decision
  => FullKept decision
```

Then:

```text
finite list certificates for computedProductive/computedReachable
  => stage decisions
  => computedKept decision
  => FullKept decision
```

Then:

```text
trace-list certificates at E.productiveCert.height and E.reachableCert.height
  => finite list certificates for computedProductive/computedReachable
```

Then:

```text
iterator outputs for productive/reachable finite iterates
  => trace-list certificates
  => FullKept decision
```

Then:

```text
complete finite state-universe list
+ decidability of the productive/reachable iterate predicates
  => iterator outputs by filtering
```

Finally:

```text
PreservesDecidablePred F
  => DecidablePred (Iter F n) for every finite n
```

Specialized to the two Algorithm 1 stages, this gives:

```text
productive step preserves decidability
+ reachable step preserves decidability
  => decidability of the certified productive/reachable iterates
  => iterator outputs
  => FullKept decidability
```

### 15.3 What this improves

Before this chain, the artifact had a theorem-facing certified Algorithm 1
agreement result, but the executable side still had a large gap between a
certified fixed-point closure and a finite-data implementation.

After this chain, the remaining executable gap is much narrower:

```text
prove ProductiveStep and ReachableStep preserve decidability
from concrete rule-predicate decisions
```

and then:

```text
construct the finite iterator/certificates automatically
from finite input data
```

Thus the artifact has moved from:

```text
certified Algorithm 1 as an assumption-level fixed-point package
```

toward:

```text
a staged finite-data interface for an executable fixed-point extraction
```

### 15.4 Current honest boundary

The current artifact still does not claim:

```text
a complete extracted implementation of Algorithm 1
automatic construction of closure certificates
automatic descriptor reconstruction
```

The current artifact can honestly claim:

```text
The Lean development checks the theorem-facing full-refinement and
FullKept correctness kernels, the certified Algorithm 1 agreement theorem for
the concrete full all-copy rule data, and a staged executable-interface chain.
This chain proves that finite rule/list/trace certificates and finite iterate
decidability feed into FullKept decidability, and that finite iterate
decidability follows from a generic decidability-preservation principle for the
closure step.
```

### 15.5 Best next Lean target

The next mathematically natural target is:

```text
StepPreservationKernel.lean
```

Goal:

```text
ProductiveStep preserves decidability
ReachableStep preserves decidability
```

from the relevant decidable rule predicates and previous-stage predicates.

A likely next target after that is:

```text
ConcreteProductiveReachableStepKernel.lean
```

Goal:

```text
instantiate the step-preservation lemmas for fullExtractionRuleData tau G
using terminal/start/binary rule-predicate decisions
```

These targets would reduce the remaining executable-interface assumptions even
further, without yet requiring a complete terminating extracted implementation.


---

## 10. Later executable-interface modules after `PaperFacingStepDecidability`

### `StepPreservationKernel.lean`

This module proves the generic finite-search deciders needed to show that the
productive and reachable closure steps preserve predicate decidability over a
complete finite universe list.

Checked components include:

* finite existential search over a complete universe list;
* decidability of productive witnesses for binary rules;
* decidability preservation for `ProductiveStep`;
* decidability preservation for `ReachableStep`.

Paper-level meaning:

```text
The concrete fixed-point steps used by Algorithm 1 preserve decidability when
terminal/start/binary predicates and the current productive predicate are
decidable over a finite universe.
```

---

### `ConcreteStepPreservationKernel.lean`

This module specializes the generic step-preservation lemmas to the concrete
full all-copy rule data.

Checked components include:

* construction of concrete productive-step decidability preservation;
* construction of concrete reachable-step decidability preservation;
* conversion from concrete rule-universe/rule-decision data to the previous
  step-decidability interface;
* transfer to `FullKept` decidability.

Paper-level meaning:

```text
Concrete finite rule data and rule-predicate decisions are sufficient to supply
the step-preservation assumptions required by the finite-iterate decidability
chain.
```

---

### `PaperFacingFullIteratorCertificate.lean`

This module exposes the concrete step-preservation boundary under paper-facing
names.

Representative target:

```text
LeanCfgProject.JALC.PaperFacingFullIteratorCertificate
```

Paper-level meaning:

```text
The concrete full all-copy rule data can feed the finite iterator certificate
chain through checked step-preservation data.
```

---

### `ActualListIteratorKernel.lean`

This module packages the actual list-iterator interface from concrete
step-preservation data.

Checked components include:

* construction of productive/reachable iterator certificate data from concrete
  step-preservation data;
* transfer from this iterator certificate data to `FullKept` decidability.

Paper-level meaning:

```text
Concrete rule-universe and rule-decision data can be routed through the iterator
certificate interface to obtain FullKept decidability.
```

---

### `FiniteStabilizationBoundaryKernel.lean`

This module keeps the stable-height boundary explicit.

Checked components include:

* `StableHeightData`;
* conversion from stable productive/reachable heights into a
  `CertifiedExtraction`;
* certified extraction kernel for those stable heights.

Paper-level meaning:

```text
If stable heights for the productive and reachable closures are supplied, they
produce the certified extraction object used by the Algorithm 1 chain.
```

This module does not yet prove that a particular finite bound always supplies
such stable heights.

---

### `DescriptorReconstructionBoundaryKernel.lean`

This module records a finite descriptor-output boundary connected to the current
executable chain.

Checked components include:

* minimal finite descriptor-output interface;
* boundary data combining concrete step-preservation data with descriptor output;
* transfer from descriptor-boundary data to `FullKept` decidability.

Paper-level meaning:

```text
Descriptor reconstruction remains a separated output phase, but the current
executable chain can already be connected to a finite descriptor-output
interface.
```

---

### `PaperFacingExecutableLimit.lean`

This module exposes the executable-limit package under a paper-facing target.

Representative target:

```text
LeanCfgProject.JALC.PaperFacingExecutableLimit
```

Paper-level meaning:

```text
The artifact has reached the boundary at which concrete rule decisions and
finite universes can feed the certified iterator/FullKept decidability chain,
while automatic stable-height discovery and descriptor reconstruction remain
outside the current end-to-end implementation.
```

---

### `ListStabilityKernel.lean`

This module introduces list-stability over a complete finite universe list.

Checked components include:

* `AgreeOnList`;
* conversion from list agreement over a complete universe list to global
  predicate agreement;
* conversion from list stability of `F (Iter F n)` and `Iter F n` to
  `StableAt F n`;
* construction of closure certificates from list-stability data;
* two-stage productive/reachable list-stability data;
* conversion from list-stability data to `CertifiedExtraction`.

Paper-level meaning:

```text
A finite support equality check at a proposed fixed-point height is enough to
produce the stable-height certificate required by Algorithm 1.
```

---

### `ConcreteListStabilityKernel.lean`

This module specializes the generic list-stability interface to the concrete
full all-copy rule data.

Checked components include:

* concrete productive list-stability data;
* concrete reachable list-stability data;
* conversion from concrete list-stability data to `CertifiedExtraction`;
* transfer from concrete list-stability data to `FullKept` decidability.

Paper-level meaning:

```text
Finite support-stability proofs for the concrete productive and reachable stages
are sufficient to build the certified extraction object and recover FullKept
decidability.
```

---

### `PaperFacingListStabilityExtraction.lean`

This module exposes the concrete list-stability extraction package.

Representative target:

```text
LeanCfgProject.JALC.PaperFacingListStabilityExtraction
```

Paper-level meaning:

```text
The finite support-stability interface is connected to certified extraction and
FullKept decidability under stable paper-facing names.
```

---

### `BoundedListStabilitySearchKernel.lean`

This module introduces a generic bounded search for list-stability witnesses.

Checked components include:

* decidability of finite list agreement from decidable predicates;
* fixed-height decidability of list stability;
* `ListStabilityWitness`;
* bounded search over candidate heights up to a supplied fuel;
* conversion from a successful bounded-search witness to `ClosureCertificate`
  and `StableAt`.

Representative target:

```text
LeanCfgProject.JALC.PaperFacingBoundedStabilitySearch
```

Paper-level meaning:

```text
Given a finite list-stability decision procedure and a fuel bound, the artifact
can search for a finite witness of stability and convert any successful result
into the closure certificate required by the fixed-point interface.
```

This is a bounded-search interface.  It does not yet prove that a particular
fuel always succeeds.

---

### `PaperFacingBoundedStabilitySearch.lean`

This module exposes the generic bounded-search interface under paper-facing
names.

Representative target:

```text
LeanCfgProject.JALC.PaperFacingBoundedStabilitySearch
```

Paper-level meaning:

```text
The generic finite bounded-search layer is checked independently of the concrete
full-rule extraction layer.
```

---

### `ConcreteBoundedWitnessBridgeKernel.lean`

This module reconnects the generic bounded-search witnesses to the concrete
full all-copy extraction interface.

Checked components include:

* concrete productive stage operator;
* concrete reachable stage operator after fixing the productive height;
* `ConcreteBoundedWitnessData`;
* conversion from productive/reachable bounded witnesses to
  `ConcreteListStabilityData`;
* construction of `CertifiedExtraction` from bounded-witness data;
* transfer from bounded-witness data to `FullKept` decidability.

Representative target:

```text
LeanCfgProject.JALC.PaperFacingConcreteBoundedWitnessBridge
```

Paper-level meaning:

```text
If bounded search supplies productive and reachable list-stability witnesses for
the concrete full all-copy rule data, then these witnesses are accepted by the
existing concrete list-stability/certified-extraction/FullKept decidability
chain.
```

---

### `PaperFacingConcreteBoundedWitnessBridge.lean`

This module exposes the concrete bounded-witness bridge under paper-facing names.

Representative target:

```text
LeanCfgProject.JALC.PaperFacingConcreteBoundedWitnessBridge
```

Latest status:

```text
Status: succeeded
Reported by user after fixing the universe level of
ConcreteBoundedWitnessData.
```

Paper-level meaning:

```text
The current most advanced executable-interface target checks the bridge from
generic bounded fixed-point witnesses back to the concrete full all-copy
Algorithm 1 extraction package.
```

---

## 11. Updated honest status after the bounded-witness bridge

### Newly checked after `PaperFacingStepDecidability`

The later development additionally checks:

* concrete productive-step and reachable-step preservation of decidability;
* conversion from concrete step-preservation data to the iterator certificate
  chain;
* executable-limit bridge from concrete step data to `FullKept` decidability;
* finite list-stability checks as sufficient data for `StableAt`;
* conversion from finite list-stability data to `CertifiedExtraction`;
* generic bounded search for list-stability witnesses;
* conversion from bounded-search witnesses to closure certificates;
* concrete bridge from bounded productive/reachable witnesses to
  `ConcreteListStabilityData`;
* transfer from concrete bounded witnesses to `CertifiedExtraction` and
  `FullKept` decidability.

### Still not yet checked

The following remain outside the current checked artifact:

* proof that bounded search succeeds within a specific finite bound, such as the
  length of the finite support;
* automatic construction of productive and reachable bounded witnesses from
  arbitrary finite CFG presentation data;
* end-to-end extracted fixed-point iterator returning successful witnesses;
* automatic enumeration of all concrete full-rule universes from arbitrary
  input data;
* final descriptor reconstruction from computed kept states and rules;
* full context-closure coincidence and shortlex witness normalization.

### Updated honest claim

The current artifact supports the following stronger but still honest claim:

```text
The Lean 4 development checks the theorem-facing finite representation kernels,
the full-kept correctness theorem, the certified Algorithm 1 agreement theorem,
and a substantial executable-interface chain.  In addition to finite
rule/list-certificate and step-decidability interfaces, it now verifies
concrete step-preservation, finite list-stability certificates, generic bounded
search for list-stability witnesses, and a bridge from bounded
productive/reachable witnesses to concrete certified extraction and FullKept
decidability.  The remaining gap is not the agreement between Algorithm 1 and
FullKept, but the fully automatic construction of successful bounded witnesses,
fixed-point certificates, and final finite descriptors from arbitrary finite CFG
presentation data.
```
---

## 7. Additional module-by-module status after CI #360

### `ConcreteTwoStageBoundedSearchKernel.lean`

This module defines the concrete two-stage bounded-search input and combines
productive and reachable bounded list-stability witnesses into
`ConcreteBoundedWitnessData`.

Checked components include:

* concrete bounded-search input data;
* productive bounded-witness search;
* reachable bounded-witness search at the returned productive height;
* construction of concrete bounded witness data from component witnesses;
* success theorem for the combined two-stage search.

Paper-level meaning:

```text
If productive and reachable bounded list-stability searches both succeed, then
the concrete full all-copy extraction interface receives the witness data it
needs.
```

---

### `PaperFacingConcreteTwoStageBoundedSearch.lean`

This paper-facing target exposes the concrete two-stage bounded-search bridge.

Target:

```text
LeanCfgProject.JALC.PaperFacingConcreteTwoStageBoundedSearch
```

---

### `ConcreteTwoStageSearchCertificateKernel.lean`

This module wraps a successful concrete two-stage bounded search as a certificate.

Checked components include:

* `ConcreteTwoStageSearchCertificate`;
* conversion from a successful search result to certified extraction;
* conversion from a successful search result to `FullKept` decidability.

Paper-level meaning:

```text
A successful concrete two-stage bounded search is a certified extraction
payload.
```

---

### `PaperFacingConcreteTwoStageSearchCertificate.lean`

This paper-facing target exposes the concrete two-stage search certificate.

Target:

```text
LeanCfgProject.JALC.PaperFacingConcreteTwoStageSearchCertificate
```

---

### `BoundedSearchCompletenessKernel.lean`

This module proves that if a list-stability witness exists at a bounded height,
the bounded search can return such a witness.

Checked components include:

* bounded-search success from an exact list-stability witness;
* extraction of a `ListStabilityWitness`;
* routing of bounded-search success to `StableAt`.

Paper-level meaning:

```text
The generic bounded list-stability search is complete relative to a supplied
bounded stability witness.
```

---

### `PaperFacingBoundedSearchCompleteness.lean`

This paper-facing target exposes bounded-search completeness.

Target:

```text
LeanCfgProject.JALC.PaperFacingBoundedSearchCompleteness
```

---

### `ConcreteTwoStageSearchConsistencyKernel.lean`

This module checks consistency between the option-valued two-stage search and
the explicit certificate form.

Checked components include:

* construction of a `ConcreteTwoStageSearchCertificate` from a successful
  option-valued search;
* routing to `CertifiedExtraction`;
* routing to `FullKept` decidability.

Paper-level meaning:

```text
The executable-looking option-valued search and the theorem-facing certificate
interface agree on successful runs.
```

---

### `PaperFacingConcreteTwoStageSearchConsistency.lean`

This paper-facing target exposes the concrete two-stage search consistency
bridge.

Target:

```text
LeanCfgProject.JALC.PaperFacingConcreteTwoStageSearchConsistency
```

---

### `ConcreteTwoStageSearchSuccessKernel.lean`

This module proves that component-level productive and reachable bounded-search
success implies combined concrete two-stage bounded-search success.

Checked components include:

* productive component search success;
* reachable component search success at the productive witness height;
* combined construction of `ConcreteBoundedWitnessData`;
* routing to `FullKept` decidability.

Paper-level meaning:

```text
Successful productive and reachable component searches are enough to certify
the concrete full all-copy extraction.
```

---

### `PaperFacingConcreteTwoStageSearchSuccess.lean`

This paper-facing target exposes the concrete two-stage search success theorem.

Target:

```text
LeanCfgProject.JALC.PaperFacingConcreteTwoStageSearchSuccess
```

---

### `BoundedSearchOffsetCompletenessKernel.lean`

This module proves that a bounded-search success or stability witness remains
usable when the fuel is increased.

Checked components include:

* offset extension of bounded-search completeness;
* preservation of search success under larger fuel.

Paper-level meaning:

```text
Once stability is witnessed within a bound, increasing the bounded-search fuel
does not invalidate the certificate.
```

---

### `PaperFacingBoundedSearchOffsetCompleteness.lean`

This paper-facing target exposes offset completeness for bounded search.

Target:

```text
LeanCfgProject.JALC.PaperFacingBoundedSearchOffsetCompleteness
```

---

### `BoundedSearchWithinBoundKernel.lean`

This module packages stability appearing at some height within a given fuel.

Checked components include:

* `StableWithinBound`;
* conversion of within-bound stability to bounded-search success;
* extraction of a `ListStabilityWitness`.

Paper-level meaning:

```text
The search does not require stability exactly at the fuel; it is enough that
stability occurs at some height not exceeding the fuel.
```

---

### `PaperFacingBoundedSearchWithinBound.lean`

This paper-facing target exposes within-bound bounded-search success.

Target:

```text
LeanCfgProject.JALC.PaperFacingBoundedSearchWithinBound
```

---

### `ListGrowthStabilizationKernel.lean`

This module connects no-strict-growth on a finite support list to list-stability.

Checked components include:

* `ListStrictGrowth`;
* `NoStrictGrowthWithinBound`;
* proof that no strict growth at a height gives list-stability at that height;
* routing from no-strict-growth within fuel to bounded-search success.

Paper-level meaning:

```text
The bounded-search problem is reduced to finding a height at which no new
support element enters the next iterate.
```

---

### `PaperFacingListGrowthStabilization.lean`

This paper-facing target exposes the no-strict-growth to bounded-search bridge.

Target:

```text
LeanCfgProject.JALC.PaperFacingListGrowthStabilization
```

---

### `ConcreteNoStrictGrowthSearchSuccessKernel.lean`

This module plugs the generic no-strict-growth bridge into the concrete
two-stage extraction pipeline.

Checked components include:

* productive no-strict-growth to productive bounded-search success;
* reachable no-strict-growth to reachable bounded-search success;
* component no-strict-growth certificates to concrete two-stage search success;
* bundled `ConcreteNoStrictGrowthSuccessData`;
* routing to `FullKept` decidability.

Paper-level meaning:

```text
If no-strict-growth certificates are supplied for the productive and reachable
steps, the concrete full all-copy extraction is certified.
```

---

### `PaperFacingConcreteNoStrictGrowthSearchSuccess.lean`

This paper-facing target exposes the concrete no-strict-growth search-success
bridge.

Target:

```text
LeanCfgProject.JALC.PaperFacingConcreteNoStrictGrowthSearchSuccess
```

---

### `StrictGrowthWitnessFreshnessKernel.lean`

This module proves that strict-growth witnesses at ordered heights are fresh.

Checked components include:

* monotone inclusion of finite iterates along `≤`;
* `StrictGrowthAt`;
* `StrictGrowthWitnessAt`;
* extraction of witnesses from strict growth;
* proof that witnesses at heights `i < j` are distinct.

Paper-level meaning:

```text
Persistent strict growth forces a sequence of pairwise fresh support witnesses.
```

---

### `PaperFacingStrictGrowthWitnessFreshness.lean`

This paper-facing target exposes strict-growth witness freshness.

Target:

```text
LeanCfgProject.JALC.PaperFacingStrictGrowthWitnessFreshness
```

---

### `StrictGrowthCountingInterfaceKernel.lean`

This module packages the counting interface following witness freshness.

Checked components include:

* `StrictGrowthRun`;
* `FreshStrictGrowthFamily`;
* construction of a fresh family from a full strict-growth run;
* `FreshFamilyImpossible`;
* obstruction route from impossibility of fresh families to bounded-search
  success and closure certificates.

Paper-level meaning:

```text
If strict growth continues up to a fuel, it yields a fresh witness family; if
such a family is impossible, bounded search succeeds.
```

---

### `PaperFacingStrictGrowthCountingInterface.lean`

This paper-facing target exposes the strict-growth counting interface.

Target:

```text
LeanCfgProject.JALC.PaperFacingStrictGrowthCountingInterface
```

---

### `FreshFamilyFinEmbeddingKernel.lean`

This module repackages fresh strict-growth witness families as finite-indexed
embeddings into the support list.

Checked components include:

* `freshFamilyFinElem`;
* support membership of selected elements;
* injectivity of the finite-indexed element map;
* `FreshFamilyFinEmbedding`;
* `FinEmbeddingImpossible`;
* routing from finite embedding impossibility to bounded-search success.

Paper-level meaning:

```text
A fresh strict-growth family gives an injective map from `Fin (fuel + 1)` into
the support list.  Therefore, finite pigeonhole obstructions can force
bounded-search success.
```

---

### `PaperFacingFreshFamilyFinEmbedding.lean`

This paper-facing target exposes the fresh-family finite-index embedding bridge.

Target:

```text
LeanCfgProject.JALC.PaperFacingFreshFamilyFinEmbedding
```

---

### `SmallSupportObstructionKernel.lean`

This module proves the first concrete finite-list obstructions.

Checked components include:

* empty support obstruction;
* singleton support obstruction for fuel at least one;
* routing from these obstructions to bounded-search success.

Paper-level meaning:

```text
For support lists of length zero or one, the required finite-index embedding is
impossible once the domain is too large, and bounded search succeeds.
```

---

### `PaperFacingSmallSupportObstruction.lean`

This paper-facing target exposes empty and singleton support obstructions.

Target:

```text
LeanCfgProject.JALC.PaperFacingSmallSupportObstruction
```

---

### `DoubletonSupportObstructionKernel.lean`

This module proves the doubleton finite-list obstruction.

Checked components include:

* impossibility of an injective map from at least three finite indices into a
  two-element support list;
* routing from doubleton obstruction to bounded-search success.

Paper-level meaning:

```text
For support lists of length two, fuel at least two is enough to force a
finite-index embedding obstruction and hence bounded-search success.
```

---

### `PaperFacingDoubletonSupportObstruction.lean`

This paper-facing target exposes the doubleton support obstruction.

Target:

```text
LeanCfgProject.JALC.PaperFacingDoubletonSupportObstruction
```

---

### `CollisionObstructionBridgeKernel.lean`

This module isolates a general collision interface.

Checked components include:

* `FinEmbeddingCollisionProperty`;
* proof that collision property implies `FinEmbeddingImpossible`;
* proof that collision property implies `FreshFamilyImpossible`;
* proof that collision property implies no full strict-growth run;
* routing from collision property to no-strict-growth within fuel;
* routing to bounded-search success and closure certificates;
* packaged `CollisionObstruction`.

Paper-level meaning:

```text
It is enough to prove that every candidate finite-index map into the support
has a collision; the rest of the bounded-search and extraction pipeline is
already checked.
```

---

### `PaperFacingCollisionObstructionBridge.lean`

This paper-facing target exposes the collision obstruction bridge.

Target:

```text
LeanCfgProject.JALC.PaperFacingCollisionObstructionBridge
```

---

### `FiniteObstructionViaCollisionKernel.lean`

This module connects direct finite embedding impossibilities to the collision
interface.

Checked components include:

* conversion from `FinEmbeddingImpossible` to `FinEmbeddingCollisionProperty`;
* conversion to packaged `CollisionObstruction`;
* routing from embedding impossibility through the collision bridge to
  bounded-search success and closure certificates;
* transport of collision obstructions along equalities of support lists;
* empty, singleton, and doubleton cases routed through the collision interface.

Paper-level meaning:

```text
The finite obstruction and collision obstruction interfaces agree, and the
checked small-support cases now use the common collision-obstruction route.
```

Latest recorded CI:

```text
Lean CI #360
Commit: fc41370
Target: LeanCfgProject.JALC.PaperFacingFiniteObstructionViaCollision
Status: succeeded
```

---

### `PaperFacingFiniteObstructionViaCollision.lean`

This is the latest paper-facing target.

Target:

```text
LeanCfgProject.JALC.PaperFacingFiniteObstructionViaCollision
```

Paper-level meaning:

```text
This target confirms that finite embedding impossibility, collision
obstructions, bounded-search success, and closure certificates are connected in
one checked route, with the empty, singleton, and doubleton support cases
packaged through the same interface.
```
