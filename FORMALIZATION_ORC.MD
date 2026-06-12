# Formalization Supplement

Lean 4 artifact for the paper:

**Observed Residual Concept Quantales for Context-Free Presentations: Canonicity, Adequacy, and Two Regular Boundaries**

Author: Takayuki Kuriyama  
Repository: `growupkuriyama-hub/lean_cfg_project`  
Supplement path: `lean_cfg_project/FORMALIZATION_ORC.MD`  
Latest historical theorem-body CI check before relocation: Lean CI #219 passed / `LeanCfgProject.ObservedResidualConcept.ObservedSyntacticQuotientPaperSummary`
Latest post-relocation ORC theorem-batch CI check: ObservedResidualConcept Lean CI #246 succeeded / `LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptMainTheorems`
Latest post-relocation ORC boundary-extension checks: Clark-collapse core, Dedekind lower-bound core, and pointed-boundary core succeeded after subsequent focused CI runs; exact final run number not recorded in this supplement
Post-relocation namespace target: `LeanCfgProject.ObservedResidualConcept.*` / checked by ObservedResidualConcept Lean CI #246 and subsequent focused boundary-extension checks  
Previous pinned theorem-body snapshot: commit `794dc20` / Lean CI #216  
Successful-log audit: through Lean CI #217  
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

## 2026-06-12 namespace and file-layout relocation

The artifact has now been separated from the JALC-specific namespace and placed
under the venue-neutral directory:

```text
lean_cfg_project/LeanCfgProject/ObservedResidualConcept/
```

In Lean module notation, the relocated namespace is:

```text
LeanCfgProject.ObservedResidualConcept
```

The uploaded relocation package contains `178` Lean files under
`ObservedResidualConcept/`.  Representative paths are:

```text
  ObservedResidualConcept/AdequacyBridgeSummary.lean
  ObservedResidualConcept/AttackSemanticBridgeSummary.lean
  ObservedResidualConcept/Basic.lean
  ObservedResidualConcept/CanonicalFrameModelCorollaries.lean
  ObservedResidualConcept/CanonicalPointFrame.lean
  ObservedResidualConcept/CanonicalPointFrameStablePackage_v27.lean
  ObservedResidualConcept/CanonicalResidualClosureSystem.lean
  ObservedResidualConcept/CarrierConceptSemantics.lean
  ObservedResidualConcept/CarrierObservedAdequacy.lean
  ObservedResidualConcept/CarrierObservedAdequacyCorollaries.lean
  ObservedResidualConcept/CarrierSaturationConceptSoundness.lean
  ObservedResidualConcept/CarrierSaturationCorrectness.lean
  ObservedResidualConcept/CarrierSaturationLeast.lean
  ObservedResidualConcept/ClosedStageAlgorithmCorrectness.lean
  ObservedResidualConcept/ClosedStageConceptBridge.lean
  ObservedResidualConcept/ClosedStageConceptStability.lean
  ObservedResidualConcept/ClosedStageEquivalences.lean
  ObservedResidualConcept/ClosedStageFrameBridge.lean
  ObservedResidualConcept/ClosedStageFrameIntentStability.lean
  ObservedResidualConcept/ClosedStageRuleSemantics.lean
  ...
```

The main post-relocation experiment target introduced for the residual concept
quantale core is:

```bash
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCore
```

The historical item7 theorem-body target should now be addressed, after import
migration, as:

```bash
lake build LeanCfgProject.ObservedResidualConcept.ObservedSyntacticQuotientPaperSummary
```

The previous paper-facing final-index target should now be addressed, after
import migration, as:

```bash
lake build LeanCfgProject.ObservedResidualConcept.ICSubmissionSummary_v14
```

Important status note: the CI numbers recorded below remain valid historical
checks for the pre-relocation development.  After moving the files into
`LeanCfgProject/ObservedResidualConcept/`, the import namespace migration was
performed and the new residual-concept theorem-package batch was checked in the
relocated namespace by ObservedResidualConcept Lean CI #246.  Earlier historical
run numbers are therefore retained as provenance, while CI #246 is the current
post-relocation check for the ORC theorem-package files introduced in this
supplement.

### Recommended CI command after relocation

For the current ORC theorem-package experiment, the recommended GitHub Actions
steps are the explicit module checks:

```bash
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCore
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCyclic
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptClassificationCore
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptReduced
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptReducedClassification
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptMainTheorems
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptClarkCollapseCore
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptDedekindLowerBoundCore
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptPointedBoundaryCore
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptClarkCollapseCore
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptDedekindLowerBoundCore
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptPointedBoundaryCore
```

The final target imports the preceding theorem-package layers and is the
paper-facing capstone for the current batch.  A broad `find | xargs lake build`
check is useful as a separate repository regression test, but it is no longer
the recommended paper-facing CI step for this focused ORC batch.

---

## Current post-relocation artifact status

The current post-relocation ORC theorem-package batch was checked by GitHub
Actions as:

```text
workflow: ObservedResidualConcept Lean CI
run: #246
status: succeeded
elapsed time shown in log: 1m 37s
capstone target: LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptMainTheorems
```

The checked post-relocation ORC theorem-package files are:

```text
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptCore.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptCyclic.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptClassificationCore.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptReduced.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptReducedClassification.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptMainTheorems.lean
```

This batch verifies the paper-facing packages for point multiplication and the
kernel of the point map, residual adjunctions and closed-form residuals, cyclic
phase / Girard-style collapse, forward transport under observed-pair
isomorphism, reduced reconstruction from point concepts, and the reduced reverse
classification core.

The subsequent boundary-extension experiments add three focused theorem-body
modules:

```text
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptClarkCollapseCore.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptDedekindLowerBoundCore.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptPointedBoundaryCore.lean
```

These focused checks were run after the CI #246 theorem-package batch and were
reported as passing after the corresponding repair commits.  The exact final run
number is not recorded in this supplement.  Their checked content is:

- Clark-collapse core: a surjective recognizing monoid observation transports
  the marked membership set, residuals, closures, point concepts, concept
  products, and observed syntactic equivalence;
- Dedekind lower-bound core: lower sets are exactly the closed extents of the
  lower-set context, and Boolean-cube lower sets inject into the corresponding
  closed-extents object;
- pointed-boundary core: pointed syntactic observation is exactly ordinary
  two-sided syntactic equivalence intersected with the kernel of the monoid
  observation.

The latest historical theorem-body check before the namespace relocation was:

```text
latest CI check: Lean CI #219
status: passed
latest checked theorem-body extension: exact observed syntactic quotient invariance and universal property / item 7
latest checked theorem-body target: LeanCfgProject.ObservedResidualConcept.ObservedSyntacticQuotientPaperSummary
modules built in Lean CI #219:
  LeanCfgProject.ObservedResidualConcept.ObservedSyntacticExactQuotient
  LeanCfgProject.ObservedResidualConcept.ObservedSyntacticExactQuotientUniversal
  LeanCfgProject.ObservedResidualConcept.ObservedSyntacticQuotientPaperSummary
commit for Lean CI #219: not recorded in the supplied log excerpt
previous pinned theorem-body snapshot: commit 794dc20 / Lean CI #216 / LeanCfgProject.ObservedResidualConcept.ZeroAdjoinedNormalCosetConsequences
previous theorem-body snapshot: commit 702dcf5 / Lean CI #207 / LeanCfgProject.ObservedResidualConcept.EndpointMonoidAdequacy
previous theorem-body item1--item4 snapshot: commit b1e651e / Lean CI #195 / LeanCfgProject.ObservedResidualConcept.ObservedFactorMinimality
previous paper-facing final-index snapshot: commit 0e6dbb5 / Lean CI #184 / LeanCfgProject.ObservedResidualConcept.ICSubmissionSummary_v14
previous release-index snapshot: commit c6c1705 / Lean CI #180
CI log audit:
  archive: LeanLog1-217.zip
  run-number range present in archive: #9--#217
  successful run logs inspected: 103
  core theorem-body targets found in successful logs: 20 / 20
  missing core theorem-body targets: 0
  unique LeanCfgProject.* targets detected from actual Run lake build lines: 158
  latest successful run in archive: Lean CI #217 / commit 06ad84d
current theorem-body chain:
  LeanCfgProject.ObservedResidualConcept.ResidualConceptNucleus
  LeanCfgProject.ObservedResidualConcept.PointwiseAdequacy
  LeanCfgProject.ObservedResidualConcept.UniformAdequacy
  LeanCfgProject.ObservedResidualConcept.ObservedQuotientResidual
  LeanCfgProject.ObservedResidualConcept.ObservedQuotientClosure
  LeanCfgProject.ObservedResidualConcept.ObservedQuotientClosureImage
  LeanCfgProject.ObservedResidualConcept.ObservedSyntacticSaturation
  LeanCfgProject.ObservedResidualConcept.ObservedFactorMinimality
  LeanCfgProject.ObservedResidualConcept.DiamondSemilatticeAdequacy
  LeanCfgProject.ObservedResidualConcept.ZMod3FailureExample
  LeanCfgProject.ObservedResidualConcept.EndpointMonoidAdequacy
  LeanCfgProject.ObservedResidualConcept.NormalCosetAdequacy
  LeanCfgProject.ObservedResidualConcept.NormalCosetAdequacyCorollaries
  LeanCfgProject.ObservedResidualConcept.ZeroAdjoinedNormalCosetAdequacy
  LeanCfgProject.ObservedResidualConcept.NormalCosetSyntacticCharacterization
  LeanCfgProject.ObservedResidualConcept.ZeroAdjoinedNormalCosetCharacterization
  LeanCfgProject.ObservedResidualConcept.NormalCosetResidualFormula
  LeanCfgProject.ObservedResidualConcept.ZeroAdjoinedNormalCosetResidualFormula
  LeanCfgProject.ObservedResidualConcept.NormalCosetConsequences
  LeanCfgProject.ObservedResidualConcept.ZeroAdjoinedNormalCosetConsequences
  LeanCfgProject.ObservedResidualConcept.ObservedSyntacticExactQuotient
  LeanCfgProject.ObservedResidualConcept.ObservedSyntacticExactQuotientUniversal
  LeanCfgProject.ObservedResidualConcept.ObservedSyntacticQuotientPaperSummary
```

The latest theorem-body development target checked by CI #219 is:

```bash
lake build LeanCfgProject.ObservedResidualConcept.ObservedSyntacticQuotientPaperSummary
```

The current stable paper-facing final-index target from the previous indexed
snapshot remains:

```bash
lake build LeanCfgProject.ObservedResidualConcept.ICSubmissionSummary_v14
```

The theorem-body item1--item7 chain can be checked explicitly by running:

```bash
lake build LeanCfgProject.ObservedResidualConcept.ResidualConceptNucleus
lake build LeanCfgProject.ObservedResidualConcept.PointwiseAdequacy
lake build LeanCfgProject.ObservedResidualConcept.UniformAdequacy
lake build LeanCfgProject.ObservedResidualConcept.ObservedQuotientResidual
lake build LeanCfgProject.ObservedResidualConcept.ObservedQuotientClosure
lake build LeanCfgProject.ObservedResidualConcept.ObservedQuotientClosureImage
lake build LeanCfgProject.ObservedResidualConcept.ObservedSyntacticSaturation
lake build LeanCfgProject.ObservedResidualConcept.ObservedFactorMinimality
lake build LeanCfgProject.ObservedResidualConcept.DiamondSemilatticeAdequacy
lake build LeanCfgProject.ObservedResidualConcept.ZMod3FailureExample
lake build LeanCfgProject.ObservedResidualConcept.EndpointMonoidAdequacy
lake build LeanCfgProject.ObservedResidualConcept.NormalCosetAdequacy
lake build LeanCfgProject.ObservedResidualConcept.NormalCosetAdequacyCorollaries
lake build LeanCfgProject.ObservedResidualConcept.ZeroAdjoinedNormalCosetAdequacy
lake build LeanCfgProject.ObservedResidualConcept.NormalCosetSyntacticCharacterization
lake build LeanCfgProject.ObservedResidualConcept.ZeroAdjoinedNormalCosetCharacterization
lake build LeanCfgProject.ObservedResidualConcept.NormalCosetResidualFormula
lake build LeanCfgProject.ObservedResidualConcept.ZeroAdjoinedNormalCosetResidualFormula
lake build LeanCfgProject.ObservedResidualConcept.NormalCosetConsequences
lake build LeanCfgProject.ObservedResidualConcept.ZeroAdjoinedNormalCosetConsequences
lake build LeanCfgProject.ObservedResidualConcept.ObservedSyntacticExactQuotient
lake build LeanCfgProject.ObservedResidualConcept.ObservedSyntacticExactQuotientUniversal
lake build LeanCfgProject.ObservedResidualConcept.ObservedSyntacticQuotientPaperSummary
```



The earlier release-index checkpoint `c6c1705` / Lean CI #180, the final-index checkpoint `0e6dbb5` / Lean CI #184, the theorem-body item1--item4 checkpoint `b1e651e` / Lean CI #195, and the finite-example checkpoint `702dcf5` / Lean CI #207 remain useful historical base points.  The item6 theorem-body development state is pinned at commit `794dc20` by Lean CI #216.  The subsequent exact observed quotient layer is checked by Lean CI #219.

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
- normal-coset and zero-adjoined normal-coset adequacy, syntactic-block characterization, residual formulas, and consequence layers;
- exact observed syntactic quotient invariance, residual/concept/product preservation, and universal-property lifting for maps constant on observed-syntactic blocks;
- the post-relocation ORC theorem-package batch: point-map homomorphism and kernel, residual adjunctions, closed-form residuals, cyclic phase collapse, forward classification transport, reduced reconstruction, and reduced reverse classification;
- the post-relocation boundary-extension batch: Clark-collapse transport for surjective recognizing observations, Dedekind lower-bound combinatorial core, and pointed-boundary collapse to syntactic equivalence intersected with observation kernel;
- paper-facing summary, audit, release-index, final-index, and appendix-index targets for reproducibility.

---


## New residual-concept core experiment checked by ObservedResidualConcept Lean CI #246

A new core module has been added for the residual concept quantale experiment:

```text
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptCore.lean
```

Expected module name:

```text
LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCore
```

The module is intended to cover the paper-level planned core around closed-form
residuals and the point homomorphism.  Its representative declarations include:

```text
Res
Intent
Extent
cl
Closed
point
mulSet
odot
Approx
ldiv
rdiv
subset_cl
cl_mono
intent_cl_eq_intent
cl_idem
Res_closed
S_closed
mul_cl_subset_cl_mul
point_mul
point_eq_iff_Approx
point_homomorphism_kernel
mem_ldiv_closed_iff
mem_rdiv_closed_iff
odot_subset_iff_rdiv
odot_subset_iff_ldiv
Res_eq_singleton_division
Res_eq_point_division
Approx_refl
Approx_symm
Approx_trans
Approx_mul_left
Approx_mul_right
Approx_mul
```

This target is deliberately thinner than the full classification or Clark
collapse theorem.  Its role is to provide a compact theorem-body layer for:

- concept closure as the Galois closure of two-sided frames;
- multiplicative/nuclear behavior of closure under subset multiplication;
- exact multiplicativity of singleton point concepts;
- the kernel of the point map as observed syntactic equivalence;
- closed-form left and right residual tests against closed extents;
- the basic residuation adjunctions for the closed product;
- residuals as divisions of the membership object `S`, both by singletons and by point concepts.

This module has passed in the relocated namespace as part of ObservedResidualConcept Lean CI #246.  The adjacent theorem-package modules added in the same batch are:

```text
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptCyclic.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptClassificationCore.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptReduced.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptReducedClassification.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptMainTheorems.lean
```

These are now claimed as checked for the current batch by ObservedResidualConcept Lean CI #246.  The subsequent focused boundary-extension checks add theorem-body cores for Clark collapse, Dedekind lower bounds, and the pointed boundary.  A full internal quotient-monoid construction remains a future target.


## ORC theorem-package batch checked by ObservedResidualConcept Lean CI #246

The post-relocation ORC theorem-package batch was checked after the namespace
migration by ObservedResidualConcept Lean CI #246.  The capstone module is:

```text
LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptMainTheorems
```

The batch consists of six new theorem-package modules:

```text
LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCore
LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCyclic
LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptClassificationCore
LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptReduced
LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptReducedClassification
LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptMainTheorems
```

The main checked declarations include:

```text
point_mul
point_eq_iff_Approx
point_homomorphism_kernel
odot_subset_iff_rdiv
odot_subset_iff_ldiv
Res_eq_singleton_division
Res_eq_point_division
Approx_mul
CyclicSet
Perp
Perp_eq_LeftPerp_of_cyclic
cl_eq_doublePerp_of_cyclic
closed_eq_doublePerp_of_cyclic
ldiv_S_eq_rdiv_S_of_cyclic
Perp_involutive_on_closed_of_cyclic
cyclic_phase_collapse_package
ObservedPairIso
image_Res
preimage_Res
image_cl
image_point
image_mulSet
image_odot
approx_iff
transport_package
Reduced
point_eq_iff_eq_of_reduced
point_injective_of_reduced
point_subset_closed_iff_mem
point_subset_S_iff_mem
point_subset_Res_iff_mem
point_eq_odot_iff_eq_mul_of_reduced
exists_context_separates_of_ne_of_reduced
ReducedPointObjectEquiv
map_one_of_reduced
map_mul_of_reduced
inv_map_one_of_reduced
inv_map_mul_of_reduced
mem_iff_of_point_mem
toObservedPairIso
induced_image_Res
induced_image_cl
induced_image_point
induced_image_odot
induced_approx_iff
reduced_classification_package
main_point_kernel_package
main_residuation_package
main_residual_closed_form_package
main_membership_object_package
main_cyclic_phase_package
main_forward_classification_package
main_reduced_reconstruction_package
main_reduced_reverse_classification_package
main_single_pair_batch_package
```

The checked mathematical content of this batch is:

- the point-concept map is multiplicative for the concept product;
- the kernel of the point-concept map is exactly the observed syntactic congruence `Approx S`;
- closed-form residual formulas are expressed by left and right divisions of the membership object `S`;
- the concept product satisfies the expected residuation adjunctions against closed extents;
- in cyclic observed sets, the two-sided closure collapses to a double-perp phase closure and satisfies Girard-style involutive equations on closed extents;
- observed-pair isomorphisms transport residuals, closures, point concepts, concept products, and `Approx`;
- reduced observed pairs recover equality, membership, and multiplication from point concepts, containment in `S`, and concept product;
- point-level unit/product/membership preservation between reduced observed pairs induces an observed monoid-pair isomorphism;
- the above results are bundled into paper-facing theorem packages in `ObservedResidualConceptMainTheorems.lean`.

This batch deliberately avoids claiming the full quotient construction
`Q / Approx S` and a bundled complete quantale isomorphism theorem.  Clark
collapse, Dedekind-style lower bounds, and the pointed boundary are handled by
subsequent focused theorem-body modules listed below.  The full quotient type
and bundled complete quantale isomorphism remain future formalization targets.


## CI log audit through Lean CI #217

After the theorem-body item1--item6 development was checked at commit `794dc20`
by Lean CI #216, the downloaded GitHub Actions logs were audited through Lean CI
#217.  The audit was based on the archive `LeanLog1-217.zip`.

The audit result was:

```text
run-number range present in uploaded archive: #9--#217
successful run logs inspected: 103
downloaded successful log zip files inspected: 103
core theorem-body targets checked: 20 / 20
missing core theorem-body targets: 0
unique LeanCfgProject.* targets detected from actual Run lake build lines: 158
actual Run lake build lines detected after per-run de-duplication: 1260
latest successful run in archive: Lean CI #217 / commit 06ad84d
```

The audit confirms that the core theorem-body chain listed in this supplement
was not skipped in the successful CI history.  In particular, the following
milestones were found in successful logs:

```text
Lean CI #195 / commit b1e651e:
  item1--item4 theorem-body chain through
  LeanCfgProject.ObservedResidualConcept.ObservedFactorMinimality

Lean CI #207 / commit 702dcf5:
  finite examples through
  LeanCfgProject.ObservedResidualConcept.EndpointMonoidAdequacy

Lean CI #216 / commit 794dc20:
  normal-coset and zero-adjoined normal-coset consequence targets through
  LeanCfgProject.ObservedResidualConcept.ZeroAdjoinedNormalCosetConsequences

Lean CI #217 / commit 06ad84d:
  subsequent successful re-check of
  LeanCfgProject.ObservedResidualConcept.NormalCosetConsequences
  LeanCfgProject.ObservedResidualConcept.ZeroAdjoinedNormalCosetConsequences
```

Important limitation: the uploaded audit archive contains successful run logs
only.  It is therefore evidence that each claimed core theorem-body target was
successfully checked at least once, not a complete archive of every failed
intermediate attempt.  This is the intended use of the audit: it supports the
paper-facing claim that the listed theorem-body experiments are present in the
successful GitHub Actions history.



## Exact observed quotient layer checked by Lean CI #219

After the successful-log audit through Lean CI #217, the development was
extended by an exact observed quotient layer.  The supplied Lean CI #219 log
shows that the active target

```bash
lake build LeanCfgProject.ObservedResidualConcept.ObservedSyntacticQuotientPaperSummary
```

completed successfully.  In that run, Lean built the following three new modules:

```text
LeanCfgProject.ObservedResidualConcept.ObservedSyntacticExactQuotient
LeanCfgProject.ObservedResidualConcept.ObservedSyntacticExactQuotientUniversal
LeanCfgProject.ObservedResidualConcept.ObservedSyntacticQuotientPaperSummary
```

The #219 log excerpt does not display the corresponding commit hash, so this
supplement records the run number and target name, while preserving `794dc20` /
Lean CI #216 as the last pinned commit-level theorem-body snapshot.

The checked mathematical content of this layer is:

- exact observed quotient maps have exact observed pullback;
- two-sided residuals are preserved by preimage and image along such maps;
- common contexts and concept closures are preserved by pullback;
- concept closures, singleton point concepts, and concept products are preserved by image;
- closed extents pull back to closed extents;
- every map constant on `SameObservedSyntactic S` classes descends uniquely through an exact observed quotient map;
- if the original map is multiplicative, then the descended map is multiplicative.

This is not yet an internal construction of the quotient monoid `Q / SameObservedSyntactic S`.
Rather, it is the theorem-body layer immediately below that construction: once
a concrete quotient projection is provided, these theorems give the residual,
concept, product, and universal-property consequences.


## How to reproduce the current check

There are now three useful reproduction modes.

To reproduce the current post-relocation ORC theorem-package batch checked by ObservedResidualConcept Lean CI #246, run:

```bash
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCore
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptCyclic
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptClassificationCore
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptReduced
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptReducedClassification
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptMainTheorems
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptClarkCollapseCore
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptDedekindLowerBoundCore
lake build LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptPointedBoundaryCore
```

First, to reproduce the current theorem-body item1--item6 endpoint checked by
Lean CI #216, run from the repository root:

```bash
lake build LeanCfgProject.ObservedResidualConcept.ZeroAdjoinedNormalCosetConsequences
```

For a direct explicit check of the whole current theorem-body chain, run the
twenty-three `lake build` commands listed in the current artifact status block above.

Second, to reproduce the stable paper-facing final-index checkpoint checked at
commit `0e6dbb5` by Lean CI #184, run:

```bash
lake build LeanCfgProject.ObservedResidualConcept.ICSubmissionSummary_v14
```

For a broader paper-facing import check around the final-index layer, run:

```bash
lake build LeanCfgProject.ObservedResidualConcept.ICSubmissionSummary_v14
lake build LeanCfgProject.ObservedResidualConcept.ICFinalSmokeTest_v27_2
lake build LeanCfgProject.ObservedResidualConcept.ICPaperSubmissionChecklist_v27_2
lake build LeanCfgProject.ObservedResidualConcept.ICFormalizationSupplementCertificate_v27_2
lake build LeanCfgProject.ObservedResidualConcept.ICFrozenArtifactIndex_v27_2
```

Older broad paper-facing targets such as `ICFullPaperSummary_v2`, `ICArtifactFreezeIndex`, and `ICReproducibilitySummary` are still useful for historical regression checks, but the current final-index path is centered on `ICSubmissionSummary_v14`.

For ordinary development, the repository uses a lightweight CI strategy: instead of explicitly building every historical experimental target one by one, it builds high-level summary modules whose imports force Lean to check the relevant dependency graph.

The current top-level paper-facing summary modules include:

```text
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v14.lean
LeanCfgProject/ObservedResidualConcept/ICFinalSmokeTest_v27_2.lean
LeanCfgProject/ObservedResidualConcept/ICPaperSubmissionChecklist_v27_2.lean
LeanCfgProject/ObservedResidualConcept/ICFormalizationSupplementCertificate_v27_2.lean
LeanCfgProject/ObservedResidualConcept/ICDependencyCertificate_v27_2.lean
LeanCfgProject/ObservedResidualConcept/ICFrozenArtifactIndex_v27_2.lean
LeanCfgProject/ObservedResidualConcept/ICTheoremTableIndex_v27_2.lean
LeanCfgProject/ObservedResidualConcept/ICPaperClaimIndex_v27_2.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v13.lean
LeanCfgProject/ObservedResidualConcept/ICReleaseSmokeTest_v27_2.lean
LeanCfgProject/ObservedResidualConcept/ICAppendixReleaseIndex_v27_2.lean
LeanCfgProject/ObservedResidualConcept/ICPaperFormalizationBridge_v27_2.lean
LeanCfgProject/ObservedResidualConcept/FiniteBasisCertificate_v27_2.lean
LeanCfgProject/ObservedResidualConcept/PointFrameCertificate_v27_2.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningCertificate_v27_2.lean
LeanCfgProject/ObservedResidualConcept/ICReleaseCertificate_v27_2.lean
LeanCfgProject/ObservedResidualConcept/ICArtifactMetadata_ci180.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v12.lean
LeanCfgProject/ObservedResidualConcept/ICReproducibilityIndex_ci180.lean
LeanCfgProject/ObservedResidualConcept/ICReleaseManifest_v27_2.lean
LeanCfgProject/ObservedResidualConcept/FiniteBasisReleaseRegression_v27_2.lean
LeanCfgProject/ObservedResidualConcept/PointFrameReleaseRegression_v27_2.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningReleaseRegression_v27_2.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v11.lean
LeanCfgProject/ObservedResidualConcept/ICFormalizationReleaseIndex_v27.lean
LeanCfgProject/ObservedResidualConcept/ICArtifactAudit_v27.lean
LeanCfgProject/ObservedResidualConcept/FiniteBasisReleaseTheorems_v27.lean
LeanCfgProject/ObservedResidualConcept/PointFrameReleaseTheorems_v27.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningReleaseTheorems_v27.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v10.lean
LeanCfgProject/ObservedResidualConcept/ObservedConceptSubmissionIndex_v27.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningSubmissionAudit_v27.lean
LeanCfgProject/ObservedResidualConcept/PointFrameTransportSummary_v27.lean
LeanCfgProject/ObservedResidualConcept/ObservedSubsetTransportPackage_v27.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v9.lean
LeanCfgProject/ObservedResidualConcept/ObservedConceptObjectReleaseIndex_v27.lean
LeanCfgProject/ObservedResidualConcept/FiniteResidualBasisTransport_v27.lean
LeanCfgProject/ObservedResidualConcept/PointFrameIncidenceTransport_v27.lean
LeanCfgProject/ObservedResidualConcept/ObservedMembershipEquivalence_v27.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v8.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSafeExpansion_v27.lean
LeanCfgProject/ObservedResidualConcept/ObservedFiniteBasisStablePackage_v27.lean
LeanCfgProject/ObservedResidualConcept/CanonicalPointFrameStablePackage_v27.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningStablePackage_v27.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v7.lean
LeanCfgProject/ObservedResidualConcept/ICPaperFormalizationSummary_v28.lean
LeanCfgProject/ObservedResidualConcept/ReducedFrameModelPaperSummary.lean
LeanCfgProject/ObservedResidualConcept/PointFrameLearningBridge.lean
LeanCfgProject/ObservedResidualConcept/ObservedSubsetStability.lean
LeanCfgProject/ObservedResidualConcept/CanonicalFrameModelCorollaries.lean
LeanCfgProject/ObservedResidualConcept/FrameModelCoreBasic.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v6.lean
LeanCfgProject/ObservedResidualConcept/ICPaperFormalizationSummary_v27.lean
LeanCfgProject/ObservedResidualConcept/FiniteObservedBasisCorollaries.lean
LeanCfgProject/ObservedResidualConcept/FaithfulRepresentativeCorollaries.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningQueryModel.lean
LeanCfgProject/ObservedResidualConcept/ReducedFrameModelCoreDefs.lean
LeanCfgProject/ObservedResidualConcept/PointFrameCorollaries.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningPaperSummary_v2.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningConstructibilitySummary.lean
LeanCfgProject/ObservedResidualConcept/UniversalFrameModelCore.lean
LeanCfgProject/ObservedResidualConcept/CanonicalPointFrame.lean
LeanCfgProject/ObservedResidualConcept/SingletonClosureIncidence.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v4.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningPaperSummary.lean
LeanCfgProject/ObservedResidualConcept/FiniteObservedConceptIdentification.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v3.lean
LeanCfgProject/ObservedResidualConcept/ICFullPaperSummary_v2.lean
LeanCfgProject/ObservedResidualConcept/ICFastCI_v2.lean
LeanCfgProject/ObservedResidualConcept/ICReproducibilitySummary.lean
LeanCfgProject/ObservedResidualConcept/ICArtifactFreezeIndex.lean
LeanCfgProject/ObservedResidualConcept/ICArtifactAppendixCoverage.lean
LeanCfgProject/ObservedResidualConcept/ICArtifactReleaseSummary.lean
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticPaperSummary.lean
LeanCfgProject/ObservedResidualConcept/NormalCosetAdequacy.lean
LeanCfgProject/ObservedResidualConcept/NormalCosetAdequacyCorollaries.lean
LeanCfgProject/ObservedResidualConcept/ZeroAdjoinedNormalCosetAdequacy.lean
LeanCfgProject/ObservedResidualConcept/NormalCosetSyntacticCharacterization.lean
LeanCfgProject/ObservedResidualConcept/ZeroAdjoinedNormalCosetCharacterization.lean
LeanCfgProject/ObservedResidualConcept/NormalCosetResidualFormula.lean
LeanCfgProject/ObservedResidualConcept/ZeroAdjoinedNormalCosetResidualFormula.lean
LeanCfgProject/ObservedResidualConcept/NormalCosetConsequences.lean
LeanCfgProject/ObservedResidualConcept/ZeroAdjoinedNormalCosetConsequences.lean
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticExactQuotient.lean
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticExactQuotientUniversal.lean
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticQuotientPaperSummary.lean
LeanCfgProject/ObservedResidualConcept/ICSemanticBridgeSummary_v3.lean
```

When preparing a release tag or an archived artifact, the individually listed lower-level modules can also be built explicitly as a full regression check.

---

## Formalization map

The Lean development is best read as a layered formalization.

### 1. Descriptor architecture

Files:

```text
LeanCfgProject/ObservedResidualConcept/Step25_Test.lean
LeanCfgProject/ObservedResidualConcept/FullArchitecture_Test.lean
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
LeanCfgProject/ObservedResidualConcept/LanguageQuotient.lean
LeanCfgProject/ObservedResidualConcept/ObservationFinite.lean
LeanCfgProject/ObservedResidualConcept/ObservationCounterexample.lean
LeanCfgProject/ObservedResidualConcept/ObservationCounterexample_v2.lean
LeanCfgProject/ObservedResidualConcept/ObservationSignatureCounterexample.lean
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
LeanCfgProject/ObservedResidualConcept/StateSemantics.lean
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
LeanCfgProject/ObservedResidualConcept/ResidualConcept.lean
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
LeanCfgProject/ObservedResidualConcept/FiniteSaturation.lean
LeanCfgProject/ObservedResidualConcept/CarrierSaturationCorrectness.lean
LeanCfgProject/ObservedResidualConcept/CarrierSaturationLeast.lean
LeanCfgProject/ObservedResidualConcept/CarrierSaturationConceptSoundness.lean
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
LeanCfgProject/ObservedResidualConcept/DescriptorSemantics.lean
LeanCfgProject/ObservedResidualConcept/DescriptorResidualSemantics.lean
LeanCfgProject/ObservedResidualConcept/CarrierConceptSemantics.lean
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
LeanCfgProject/ObservedResidualConcept/FrameSoundness.lean
LeanCfgProject/ObservedResidualConcept/SaturationFrameBridge.lean
LeanCfgProject/ObservedResidualConcept/FrameIntentClosureBridge.lean
LeanCfgProject/ObservedResidualConcept/ClosedStageFrameBridge.lean
LeanCfgProject/ObservedResidualConcept/ClosedStageFrameIntentStability.lean
LeanCfgProject/ObservedResidualConcept/LocalStoppingFrameResidual.lean
LeanCfgProject/ObservedResidualConcept/FiniteStoppingFrameResidual.lean
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
LeanCfgProject/ObservedResidualConcept/SaturationStability.lean
LeanCfgProject/ObservedResidualConcept/ClosedStageConceptBridge.lean
LeanCfgProject/ObservedResidualConcept/SaturationMonotoneChain.lean
LeanCfgProject/ObservedResidualConcept/ClosedStageAlgorithmCorrectness.lean
LeanCfgProject/ObservedResidualConcept/FiniteCoverageStopping.lean
LeanCfgProject/ObservedResidualConcept/ClosedStageEquivalences.lean
LeanCfgProject/ObservedResidualConcept/ClosedStageConceptStability.lean
LeanCfgProject/ObservedResidualConcept/ClosedStageRuleSemantics.lean
LeanCfgProject/ObservedResidualConcept/LaterClosedStageClosure.lean
LeanCfgProject/ObservedResidualConcept/LocalStoppingCorrectness.lean
LeanCfgProject/ObservedResidualConcept/LocalStoppingRuleSemantics.lean
LeanCfgProject/ObservedResidualConcept/LocalStoppingFrameResidual.lean
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
LeanCfgProject/ObservedResidualConcept/FiniteStoppingCore.lean
LeanCfgProject/ObservedResidualConcept/MeasureStoppingCriterion.lean
LeanCfgProject/ObservedResidualConcept/FiniteSaturationMeasure.lean
LeanCfgProject/ObservedResidualConcept/FiniteStoppingFrameResidual.lean
LeanCfgProject/ObservedResidualConcept/FiniteStoppedFrameAdequacy.lean
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
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticConcept.lean
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticCongruence.lean
LeanCfgProject/ObservedResidualConcept/CanonicalResidualClosureSystem.lean
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticResidualCorollaries.lean
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticBlockAdequacyCorollaries.lean
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticPaperCorollaries.lean
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

### 10a. Exact observed syntactic quotient invariance and universal property

Files:

```text
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticExactQuotient.lean
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticExactQuotientUniversal.lean
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticQuotientPaperSummary.lean
```

This layer formalizes the exact quotient-map form of the observed syntactic
quotient story.  It assumes a surjective multiplicative map `pi : Q -> Qbar`
whose kernel is exactly `SameObservedSyntactic S` and verifies the consequences
needed by the paper.

Representative declarations:

```text
exactObservedQuotient_pullback_eq
exactObservedQuotient_residual_preimage_eq
exactObservedQuotient_residual_image_eq
exactObservedQuotient_commonContexts_preimage_eq
exactObservedQuotient_conceptClosure_preimage_eq
exactObservedQuotient_conceptClosure_image_eq
exactObservedQuotient_pointConcept_image_eq
exactObservedQuotient_conceptProduct_image_eq
exactObservedQuotient_preimage_isConceptExtent
exactObservedQuotient_invariance_package
RespectsSameObservedSyntactic
exactObservedQuotientLift
exactObservedQuotientLift_commutes
exactObservedQuotientLift_unique
exactObservedQuotient_universal_property
exactObservedQuotientLift_mul
exactObservedQuotient_multiplicative_universal_property
observedSyntacticExactQuotient_paper_package
observedSyntacticExactQuotient_universal_paper_package
observedSyntacticExactQuotient_multiplicative_paper_package
```

The verified interpretation is that an exact observed quotient map preserves the
residual/concept/product structure and satisfies the expected universal property
for maps constant on observed-syntactic blocks.  The actual quotient type and
monoid instance for `SameObservedSyntactic S` remain a future formalization
target, but this layer checks the mathematical consequences expected from such a
quotient projection.

---

### 10b. ORC theorem-package core: point kernels, cyclic phase collapse, and reduced classification

Files:

```text
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptCore.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptCyclic.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptClassificationCore.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptReduced.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptReducedClassification.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptMainTheorems.lean
```

This layer is the post-relocation ORC theorem-package batch checked by
ObservedResidualConcept Lean CI #246.  It is deliberately paper-facing: the
files collect theorem-body packages that support the observed residual concept
quantale presentation without introducing a full quotient construction.

Representative declarations:

```text
point_homomorphism_kernel
Res_eq_singleton_division
Res_eq_point_division
odot_subset_iff_rdiv
odot_subset_iff_ldiv
cyclic_phase_collapse_package
ObservedPairIso.transport_package
reduced_reconstruction_package
ReducedPointObjectEquiv.toObservedPairIso
ReducedPointObjectEquiv.reduced_classification_package
main_single_pair_batch_package
```

The verified interpretation is that point concepts multiply correctly, their
kernel is the observed syntactic congruence, residuals have division-based
closed forms, closed concept products satisfy residuation, cyclic observed sets
admit a double-perp/Girard-style collapse, observed-pair isomorphisms transport
the concept structure, and reduced observed pairs admit reconstruction and a
reduced reverse-classification core.

### 10c. Boundary-extension theorem-body cores: Clark collapse, Dedekind lower bound, and pointed boundary

Files:

```text
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptClarkCollapseCore.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptDedekindLowerBoundCore.lean
LeanCfgProject/ObservedResidualConcept/ObservedResidualConceptPointedBoundaryCore.lean
```

This layer records the focused boundary-extension experiments run after the
CI #246 theorem-package batch.  These files are intentionally theorem-body
cores rather than full formalizations of all surrounding language-theoretic
corollaries.

Representative declarations:

```text
SurjectiveRecognizingObservation
preimage_observed_set
image_observed_set
preimage_Res
image_Res
image_cl
image_point
image_odot
approx_iff
clark_collapse_core_package
IsORCLowerSet
ORCLowerSet
lowerSetClosure
LowerContextClosedExtent
lowerSetClosed_iff_isLowerSet
lowerSet_closedExtent_equiv
boolean_dedekind_lower_bound_core
boolean_card_lowerSets_le_card_closedExtents
MonoidObservation
SyntacticEquiv
ObservationKernel
HTypedContextObservation
RawObsEquiv
PointedObs
SynObs
PointedSynObs
pointedSynObs_iff_syntacticEquiv_and_kernel
pointed_boundary_core_package
```

The checked Clark-collapse core states that a surjective recognizing monoid
observation transports the observed membership set, two-sided residuals,
closures, point concepts, concept products, and observed syntactic equivalence.
This is the Lean-checked theorem-body core below the paper's second regular
boundary.

The checked Dedekind lower-bound core states that the closed extents of the
lower-set context are equivalent to lower sets, and specializes this to Boolean
cubes.  It supplies the combinatorial core of the paper's Dedekind-number
lower-bound discussion without formalizing the full ORC-specific realization
and asymptotic cardinal arithmetic.

The checked pointed-boundary core states that the pointed syntactic
stabilization of a monoid observation is exactly ordinary two-sided syntactic
equivalence intersected with the observation kernel.  The finite-index /
regular-language corollary remains in the paper text, since it invokes the
usual Myhill--Nerode theorem for languages over finite alphabets.


### 11. K4 residual adequacy witness

Files:

```text
LeanCfgProject/ObservedResidualConcept/FrameAdequacyCriterion.lean
LeanCfgProject/ObservedResidualConcept/K4ResidualAdequacyExample.lean
LeanCfgProject/ObservedResidualConcept/K4AdequacyStrictness.lean
LeanCfgProject/ObservedResidualConcept/K4ConceptCollapse.lean
LeanCfgProject/ObservedResidualConcept/K4AdequacyPaperSummary.lean
LeanCfgProject/ObservedResidualConcept/AdequacyBridgeSummary.lean
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
LeanCfgProject/ObservedResidualConcept/CarrierObservedAdequacy.lean
LeanCfgProject/ObservedResidualConcept/CarrierObservedAdequacyCorollaries.lean
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
LeanCfgProject/ObservedResidualConcept/ObservedFrameStructure.lean
LeanCfgProject/ObservedResidualConcept/ObservedFrameStructureDecidable.lean
LeanCfgProject/ObservedResidualConcept/FiniteObservedFrameBasis.lean
LeanCfgProject/ObservedResidualConcept/FiniteSetQueryReconstruction.lean
LeanCfgProject/ObservedResidualConcept/FaithfulRepresentatives.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningExamples.lean
LeanCfgProject/ObservedResidualConcept/FiniteObservedConceptIdentification.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningCorollaries.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningConstructibilitySummary.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningPaperSummary.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningPaperSummary_v2.lean
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
LeanCfgProject/ObservedResidualConcept/SingletonClosureIncidence.lean
LeanCfgProject/ObservedResidualConcept/CanonicalPointFrame.lean
LeanCfgProject/ObservedResidualConcept/UniversalFrameModelCore.lean
LeanCfgProject/ObservedResidualConcept/PointFrameCorollaries.lean
LeanCfgProject/ObservedResidualConcept/ReducedFrameModelCoreDefs.lean
LeanCfgProject/ObservedResidualConcept/FrameModelCoreBasic.lean
LeanCfgProject/ObservedResidualConcept/CanonicalFrameModelCorollaries.lean
LeanCfgProject/ObservedResidualConcept/CanonicalPointFrameStablePackage_v27.lean
LeanCfgProject/ObservedResidualConcept/PointFrameIncidenceTransport_v27.lean
LeanCfgProject/ObservedResidualConcept/PointFrameTransportSummary_v27.lean
LeanCfgProject/ObservedResidualConcept/PointFrameReleaseTheorems_v27.lean
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
LeanCfgProject/ObservedResidualConcept/SemanticBridgeSummary.lean
LeanCfgProject/ObservedResidualConcept/ICSemanticBridgeSummary.lean
LeanCfgProject/ObservedResidualConcept/ICSemanticBridgeSummary_v2.lean
LeanCfgProject/ObservedResidualConcept/AttackSemanticBridgeSummary.lean
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticBridgeSummary.lean
LeanCfgProject/ObservedResidualConcept/ICSemanticBridgeSummary_v3.lean
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticPaperSummary.lean
LeanCfgProject/ObservedResidualConcept/ICPaperArtifactSummary.lean
LeanCfgProject/ObservedResidualConcept/ICLeanAppendixIndex.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v1.lean
LeanCfgProject/ObservedResidualConcept/ICArtifactReleaseSummary.lean
LeanCfgProject/ObservedResidualConcept/ICArtifactAppendixCoverage.lean
LeanCfgProject/ObservedResidualConcept/ICFastCI.lean
LeanCfgProject/ObservedResidualConcept/ICFullPaperSummary_v1.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v2.lean
LeanCfgProject/ObservedResidualConcept/ICArtifactFreezeIndex.lean
LeanCfgProject/ObservedResidualConcept/ICReproducibilitySummary.lean
LeanCfgProject/ObservedResidualConcept/ICFastCI_v2.lean
LeanCfgProject/ObservedResidualConcept/ICFullPaperSummary_v2.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v3.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v4.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningPaperSummary.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningPaperSummary_v2.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v11.lean
LeanCfgProject/ObservedResidualConcept/PointFrameCorollaries.lean
LeanCfgProject/ObservedResidualConcept/ReducedFrameModelCoreDefs.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningQueryModel.lean
LeanCfgProject/ObservedResidualConcept/FaithfulRepresentativeCorollaries.lean
LeanCfgProject/ObservedResidualConcept/FiniteObservedBasisCorollaries.lean
LeanCfgProject/ObservedResidualConcept/ICPaperFormalizationSummary_v27.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v6.lean
LeanCfgProject/ObservedResidualConcept/FrameModelCoreBasic.lean
LeanCfgProject/ObservedResidualConcept/CanonicalFrameModelCorollaries.lean
LeanCfgProject/ObservedResidualConcept/ObservedSubsetStability.lean
LeanCfgProject/ObservedResidualConcept/PointFrameLearningBridge.lean
LeanCfgProject/ObservedResidualConcept/ReducedFrameModelPaperSummary.lean
LeanCfgProject/ObservedResidualConcept/ICPaperFormalizationSummary_v28.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v7.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningStablePackage_v27.lean
LeanCfgProject/ObservedResidualConcept/CanonicalPointFrameStablePackage_v27.lean
LeanCfgProject/ObservedResidualConcept/ObservedFiniteBasisStablePackage_v27.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSafeExpansion_v27.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v8.lean
LeanCfgProject/ObservedResidualConcept/ObservedMembershipEquivalence_v27.lean
LeanCfgProject/ObservedResidualConcept/PointFrameIncidenceTransport_v27.lean
LeanCfgProject/ObservedResidualConcept/FiniteResidualBasisTransport_v27.lean
LeanCfgProject/ObservedResidualConcept/ObservedConceptObjectReleaseIndex_v27.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v9.lean
LeanCfgProject/ObservedResidualConcept/ObservedSubsetTransportPackage_v27.lean
LeanCfgProject/ObservedResidualConcept/PointFrameTransportSummary_v27.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningSubmissionAudit_v27.lean
LeanCfgProject/ObservedResidualConcept/ObservedConceptSubmissionIndex_v27.lean
LeanCfgProject/ObservedResidualConcept/ICSubmissionSummary_v10.lean
LeanCfgProject/ObservedResidualConcept/ObservedLearningReleaseTheorems_v27.lean
LeanCfgProject/ObservedResidualConcept/PointFrameReleaseTheorems_v27.lean
LeanCfgProject/ObservedResidualConcept/FiniteBasisReleaseTheorems_v27.lean
LeanCfgProject/ObservedResidualConcept/ICArtifactAudit_v27.lean
LeanCfgProject/ObservedResidualConcept/ICFormalizationReleaseIndex_v27.lean
```

These modules are intentionally lightweight.  Their role is to give stable paper-facing import targets, appendix-index targets, and fast CI targets.

The current recommended top-level target after relocation is:

```text
LeanCfgProject.ObservedResidualConcept.ICSubmissionSummary_v14
```

If this module builds, Lean has checked the current v27.2 final-index import graph, including the observed-learning layer, canonical point-frame incidence core, finite residual-basis transport layer, release-facing audit targets, release-regression and certificate layers, theorem-table index, frozen artifact index, FORMALIZATION supplement certificate, submission checklist, and final smoke test, through the normal dependency system.

---


## Theorem-body item1--item6 additions checked by CI #216

After the v27.2 final-index snapshot, the development was extended by a new
theorem-body chain focused on the mathematical core of the paper rather than on
release packaging.  Items 1--4 were checked at commit `b1e651e` by Lean CI #195.  The item 5
finite-example extension was checked at commit `702dcf5` by Lean CI #207.  The
current item 6 normal-coset and zero-adjoined normal-coset extension is checked
at commit `794dc20` by Lean CI #216.

The checked theorem-body modules are:

```text
LeanCfgProject/ObservedResidualConcept/ResidualConceptNucleus.lean
LeanCfgProject/ObservedResidualConcept/PointwiseAdequacy.lean
LeanCfgProject/ObservedResidualConcept/UniformAdequacy.lean
LeanCfgProject/ObservedResidualConcept/ObservedQuotientResidual.lean
LeanCfgProject/ObservedResidualConcept/ObservedQuotientClosure.lean
LeanCfgProject/ObservedResidualConcept/ObservedQuotientClosureImage.lean
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticSaturation.lean
LeanCfgProject/ObservedResidualConcept/ObservedFactorMinimality.lean
LeanCfgProject/ObservedResidualConcept/DiamondSemilatticeAdequacy.lean
LeanCfgProject/ObservedResidualConcept/ZMod3FailureExample.lean
LeanCfgProject/ObservedResidualConcept/EndpointMonoidAdequacy.lean
LeanCfgProject/ObservedResidualConcept/NormalCosetAdequacy.lean
LeanCfgProject/ObservedResidualConcept/NormalCosetAdequacyCorollaries.lean
LeanCfgProject/ObservedResidualConcept/ZeroAdjoinedNormalCosetAdequacy.lean
LeanCfgProject/ObservedResidualConcept/NormalCosetSyntacticCharacterization.lean
LeanCfgProject/ObservedResidualConcept/ZeroAdjoinedNormalCosetCharacterization.lean
LeanCfgProject/ObservedResidualConcept/NormalCosetResidualFormula.lean
LeanCfgProject/ObservedResidualConcept/ZeroAdjoinedNormalCosetResidualFormula.lean
LeanCfgProject/ObservedResidualConcept/NormalCosetConsequences.lean
LeanCfgProject/ObservedResidualConcept/ZeroAdjoinedNormalCosetConsequences.lean
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
normalCoset_residual_single_observed_block
normalCoset_residual_singleBlockOn
normalCoset_uniformAdequacyOn_residual
normalCoset_nonempty_subset_generates_residual
normalCoset_singleton_generates_residual
lifted_normalCoset_residual_singleBlockOn
lifted_normalCoset_uniformAdequacyOn_residual
lifted_normalCoset_nonempty_subset_generates_residual
sameObservedSyntactic_normalCoset_iff_pair_difference_mem
normalCoset_syntactic_characterization_package
sameObservedSyntactic_lifted_normalCoset_iff_pair_difference_mem
lifted_normalCoset_syntactic_characterization_package
normalCoset_residual_mem_iff_leftCoset
normalCoset_residual_eq_leftCoset
normalCoset_residual_base_mem
normalCoset_base_singleton_generates_residual
lifted_normalCoset_residual_mem_iff_shifted_liftedCoset
lifted_normalCoset_residual_eq_shifted_liftedCoset
lifted_normalCoset_base_singleton_generates_residual
normalCoset_nonempty_subset_of_shifted_leftCoset_generates_shifted_leftCoset
normalCoset_shifted_leftCoset_self_closure
normalCoset_singleton_in_shifted_leftCoset_generates_shifted_leftCoset
lifted_normalCoset_nonempty_subset_of_shifted_liftedCoset_generates_shifted_liftedCoset
lifted_normalCoset_shifted_liftedCoset_self_closure
lifted_normalCoset_singleton_in_shifted_liftedCoset_generates_shifted_liftedCoset
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

Seventh, the normal-coset family is now checked as a theorem-body layer.  For a
group `G`, a set-level normal subgroup `N`, and the observed set `S=sN`, Lean
checks that every normal-coset residual lies in a single observed-syntactic
block and therefore satisfies uniform adequacy.  The exact observed-syntactic
block is also characterized:

```text
SameObservedSyntactic(sN) x y  iff  x*y^{-1} ∈ N.
```

Lean also checks the residual formula

```text
Res_{sN}(a,b) = (a^{-1} s b^{-1})N,
```

the canonical base-point witness `a^{-1} s b^{-1}`, and the consequence that
every nonempty subset of the shifted coset generates the shifted coset by
residual concept closure.

Eighth, the same normal-coset story is lifted to the zero-adjoined monoid.  For
the monoid obtained by adjoining an absorbing zero to `G`, the lifted observed
set omits zero and keeps the same coset on the nonzero component.  Lean checks
the nonzero syntactic characterization, the lifted residual formula

```text
Res_{lift(sN)}(nz a,nz b) = lift((a^{-1} s b^{-1})N),
```

and the corresponding nonempty-subset, singleton, and self-closure consequences.
This verifies that the normal-coset adequacy mechanism survives in a simple
non-group monoid obtained by adjoining zero.

These item 6 modules are theorem-body additions.  They are not release
certificates, submission checklists, audit wrappers, or manifest modules.



## Theorem-body item7 exact observed quotient extension checked by CI #219

After item1--item6, the development was extended by the exact observed
syntactic quotient layer.  This layer was checked by Lean CI #219 through the
target:

```text
LeanCfgProject.ObservedResidualConcept.ObservedSyntacticQuotientPaperSummary
```

The checked theorem-body modules are:

```text
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticExactQuotient.lean
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticExactQuotientUniversal.lean
LeanCfgProject/ObservedResidualConcept/ObservedSyntacticQuotientPaperSummary.lean
```

The main checked declarations include:

```text
exactObservedQuotient_pullback_eq
exactObservedQuotient_residual_preimage_eq
exactObservedQuotient_residual_image_eq
exactObservedQuotient_commonContexts_preimage_eq
exactObservedQuotient_conceptClosure_preimage_eq
exactObservedQuotient_conceptClosure_image_eq
exactObservedQuotient_pointConcept_image_eq
exactObservedQuotient_conceptProduct_image_eq
exactObservedQuotient_preimage_isConceptExtent
exactObservedQuotient_invariance_package
RespectsSameObservedSyntactic
exactObservedQuotientLift
exactObservedQuotientLift_commutes
exactObservedQuotientLift_unique
exactObservedQuotient_universal_property
exactObservedQuotientLift_mul
exactObservedQuotient_multiplicative_universal_property
observedSyntacticExactQuotient_paper_package
observedSyntacticExactQuotient_universal_paper_package
observedSyntacticExactQuotient_multiplicative_paper_package
```

This item7 layer strengthens the quotient/factor-map part of the formalization.
For any surjective multiplicative map `pi : Q -> Qbar` whose kernel is exactly
`SameObservedSyntactic S`, Lean checks exact pullback of the observed subset,
preimage and image preservation for residuals, pullback preservation for common
contexts and concept closures, image preservation for concept closures, point
concepts and concept products, and pullback preservation of closed extents.

It also verifies the universal-property direction: every map that is constant
on observed-syntactic blocks descends uniquely through the exact quotient map,
and multiplicative maps descend multiplicatively.

These item7 modules are theorem-body additions.  They are not release
certificates, submission checklists, audit wrappers, or manifest modules.


## v27.1 release-index additions checked by CI #180

The CI #180 run checked the current release-facing path through:

```text
LeanCfgProject.ObservedResidualConcept.ICSubmissionSummary_v14
LeanCfgProject.ObservedResidualConcept.ICFormalizationReleaseIndex_v27
LeanCfgProject.ObservedResidualConcept.ICArtifactAudit_v27
LeanCfgProject.ObservedResidualConcept.ObservedLearningReleaseTheorems_v27
LeanCfgProject.ObservedResidualConcept.PointFrameReleaseTheorems_v27
LeanCfgProject.ObservedResidualConcept.FiniteBasisReleaseTheorems_v27
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
LeanCfgProject.ObservedResidualConcept.ICSubmissionSummary_v14
```

The v27.2 path includes the following paper-facing targets:

```text
LeanCfgProject.ObservedResidualConcept.ICSubmissionSummary_v14
LeanCfgProject.ObservedResidualConcept.ICFinalSmokeTest_v27_2
LeanCfgProject.ObservedResidualConcept.ICPaperSubmissionChecklist_v27_2
LeanCfgProject.ObservedResidualConcept.ICFormalizationSupplementCertificate_v27_2
LeanCfgProject.ObservedResidualConcept.ICDependencyCertificate_v27_2
LeanCfgProject.ObservedResidualConcept.ICFrozenArtifactIndex_v27_2
LeanCfgProject.ObservedResidualConcept.ICTheoremTableIndex_v27_2
LeanCfgProject.ObservedResidualConcept.ICPaperClaimIndex_v27_2
LeanCfgProject.ObservedResidualConcept.ICSubmissionSummary_v13
LeanCfgProject.ObservedResidualConcept.ICReleaseSmokeTest_v27_2
LeanCfgProject.ObservedResidualConcept.ICAppendixReleaseIndex_v27_2
LeanCfgProject.ObservedResidualConcept.ICPaperFormalizationBridge_v27_2
LeanCfgProject.ObservedResidualConcept.FiniteBasisCertificate_v27_2
LeanCfgProject.ObservedResidualConcept.PointFrameCertificate_v27_2
LeanCfgProject.ObservedResidualConcept.ObservedLearningCertificate_v27_2
LeanCfgProject.ObservedResidualConcept.ICReleaseCertificate_v27_2
LeanCfgProject.ObservedResidualConcept.ICArtifactMetadata_ci180
LeanCfgProject.ObservedResidualConcept.ICSubmissionSummary_v12
LeanCfgProject.ObservedResidualConcept.ICReproducibilityIndex_ci180
LeanCfgProject.ObservedResidualConcept.ICReleaseManifest_v27_2
LeanCfgProject.ObservedResidualConcept.FiniteBasisReleaseRegression_v27_2
LeanCfgProject.ObservedResidualConcept.PointFrameReleaseRegression_v27_2
LeanCfgProject.ObservedResidualConcept.ObservedLearningReleaseRegression_v27_2
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

### 12. Normal-coset and zero-adjoined normal-coset adequacy checked by CI #216

Files:

```text
LeanCfgProject/ObservedResidualConcept/NormalCosetAdequacy.lean
LeanCfgProject/ObservedResidualConcept/NormalCosetAdequacyCorollaries.lean
LeanCfgProject/ObservedResidualConcept/ZeroAdjoinedNormalCosetAdequacy.lean
LeanCfgProject/ObservedResidualConcept/NormalCosetSyntacticCharacterization.lean
LeanCfgProject/ObservedResidualConcept/ZeroAdjoinedNormalCosetCharacterization.lean
LeanCfgProject/ObservedResidualConcept/NormalCosetResidualFormula.lean
LeanCfgProject/ObservedResidualConcept/ZeroAdjoinedNormalCosetResidualFormula.lean
LeanCfgProject/ObservedResidualConcept/NormalCosetConsequences.lean
LeanCfgProject/ObservedResidualConcept/ZeroAdjoinedNormalCosetConsequences.lean
```

This layer formalizes the normal-coset adequacy family and its zero-adjoined
monoid variant.

Representative declarations:

```text
NormalSubgroupSet
LeftCosetSet
normalCoset_residual_single_observed_block
normalCoset_uniformAdequacyOn_residual
normalCoset_nonempty_subset_generates_residual
normalCoset_singleton_generates_residual
sameObservedSyntactic_normalCoset_iff_pair_difference_mem
normalCoset_syntactic_characterization_package
normalCoset_residual_eq_leftCoset
normalCoset_residual_base_mem
normalCoset_base_singleton_generates_residual
normalCoset_shifted_leftCoset_self_closure
normalCoset_singleton_in_shifted_leftCoset_generates_shifted_leftCoset
ZeroAdjoin
LiftedCosetSet
lifted_normalCoset_uniformAdequacyOn_residual
sameObservedSyntactic_lifted_normalCoset_iff_pair_difference_mem
lifted_normalCoset_residual_eq_shifted_liftedCoset
lifted_normalCoset_shifted_liftedCoset_self_closure
lifted_normalCoset_singleton_in_shifted_liftedCoset_generates_shifted_liftedCoset
```

The verified mathematical content is:

- if `S=sN` for a normal subgroup `N`, then every residual `Res_S(a,b)` lies in a
  single observed-syntactic block;
- equivalently, every nonempty subset of such a residual generates the residual
  by concept closure;
- observed syntactic equivalence for `sN` is exactly equality modulo `N`, namely
  `x ≈_S y` iff `x*y^{-1} ∈ N`;
- every residual has the explicit shifted-coset form
  `Res_{sN}(a,b) = (a^{-1} s b^{-1})N`;
- the shifted coset is closed and every singleton inside it generates it;
- adjoining an absorbing zero preserves these results on the nonzero component,
  with residuals over nonzero frames equal to the lifted shifted cosets.

This checks the paper's normal-coset adequacy mechanism as theorem-body Lean
code, including a non-group zero-adjoined monoid variant.


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
| Exact observed syntactic quotient invariance and universal property | `ObservedSyntacticExactQuotient.lean`, `ObservedSyntacticExactQuotientUniversal.lean`, `ObservedSyntacticQuotientPaperSummary.lean` |
| ORC theorem-package core: point kernel, residual adjunctions, cyclic phase, forward/reduced classification | `ObservedResidualConceptCore.lean`, `ObservedResidualConceptCyclic.lean`, `ObservedResidualConceptClassificationCore.lean`, `ObservedResidualConceptReduced.lean`, `ObservedResidualConceptReducedClassification.lean`, `ObservedResidualConceptMainTheorems.lean` |
| Canonical residual closure system | `CanonicalResidualClosureSystem.lean`, `ObservedSyntacticResidualCorollaries.lean` |
| Syntactic-block adequacy | `ObservedSyntacticBlockAdequacyCorollaries.lean`, `ObservedSyntacticPaperCorollaries.lean` |
| Finite adequacy examples | `DiamondSemilatticeAdequacy.lean`, `ZMod3FailureExample.lean`, `EndpointMonoidAdequacy.lean` |
| Normal-coset and zero-adjoined normal-coset adequacy | `NormalCosetAdequacy.lean`, `NormalCosetAdequacyCorollaries.lean`, `ZeroAdjoinedNormalCosetAdequacy.lean`, `NormalCosetSyntacticCharacterization.lean`, `ZeroAdjoinedNormalCosetCharacterization.lean`, `NormalCosetResidualFormula.lean`, `ZeroAdjoinedNormalCosetResidualFormula.lean`, `NormalCosetConsequences.lean`, `ZeroAdjoinedNormalCosetConsequences.lean` |
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
- exact observed quotient maps preserve residuals, common contexts, concept closures, point concepts, concept products, and closed extents;
- maps constant on observed-syntactic blocks descend uniquely through exact observed quotient maps, and multiplicative maps descend multiplicatively;
- exact image-pullback preservation is equivalent to factor-map fibers being contained in the observed syntactic congruence;
- the diamond meet-semilattice, three-element cyclic monoid, and endpoint monoid give checked finite examples of residual-concept adequacy, failure of automatic residual coverage, and aperiodic single-block adequacy;
- the normal-coset family is checked through uniform adequacy, exact observed-syntactic block characterization, residual shifted-coset formulas, singleton/self-closure consequences, and a zero-adjoined non-group monoid variant;
- the ORC theorem-package batch checks point-concept multiplication, the point-map kernel, residual adjunctions, closed-form residuals, cyclic phase collapse, forward transport under observed-pair isomorphism, reduced reconstruction, and reduced reverse classification.

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
- the mod-`k` language family and its grammar-level saturation instantiation have all been formalized;
- the full abstract complete-lattice isomorphism theorem for arbitrary reduced frame models has been formalized;
- the actual quotient type and monoid instance for `SameObservedSyntactic S` or `Approx S` have been constructed inside Lean;
- the Clark collapse theorem has been fully formalized;
- Dedekind-style lower-bound examples have been fully formalized;
- polynomial-time complexity bounds such as `O(|Q|^4)` have been formalized inside Lean.

The artifact verifies an unconditional bounded finite-stopping theorem only under both finite state and finite observation carrier assumptions.  It also verifies observed-syntactic-block adequacy only under the stated nonempty single-block hypothesis.

These boundaries are intentional: the paper separates checked formalization results from open problems and future formalization targets.

---

## Suggested citation in the paper

A concise artifact statement for the paper could be:

```text
The accompanying Lean 4 artifact is organized under the namespace
LeanCfgProject.ObservedResidualConcept.  The historical theorem-body chain is
pinned through commit 794dc20 / Lean CI #216, pushed by growupkuriyama-hub, with
endpoint LeanCfgProject.ObservedResidualConcept.ZeroAdjoinedNormalCosetConsequences.  A subsequent
audit of downloaded successful GitHub Actions logs through Lean CI #217
confirmed that all 20 expected core theorem-body targets appeared in successful
workflow logs, with missing core targets equal to 0.  The exact observed quotient
layer was then checked by Lean CI #219 through the target
LeanCfgProject.ObservedResidualConcept.ObservedSyntacticQuotientPaperSummary.

After the namespace relocation to LeanCfgProject/ObservedResidualConcept/, the
post-relocation ORC theorem-package batch was checked by ObservedResidualConcept
Lean CI #246.  The capstone target was
LeanCfgProject.ObservedResidualConcept.ObservedResidualConceptMainTheorems, importing the checked
modules ObservedResidualConceptCore, ObservedResidualConceptCyclic,
ObservedResidualConceptClassificationCore, ObservedResidualConceptReduced, and
ObservedResidualConceptReducedClassification.  This batch verifies the
paper-facing packages for point multiplication and the kernel of the point map,
residual adjunctions and closed-form residuals, cyclic phase / Girard-style
collapse, forward transport under observed-pair isomorphism, reduced
reconstruction from point concepts, and the reduced reverse-classification core.

The previous finite-example target LeanCfgProject.ObservedResidualConcept.EndpointMonoidAdequacy was
checked at commit 702dcf5 / Lean CI #207, and the earlier theorem-body
item1--item4 target LeanCfgProject.ObservedResidualConcept.ObservedFactorMinimality was checked at
commit b1e651e / Lean CI #195.  The previous paper-facing final-index target
LeanCfgProject.ObservedResidualConcept.ICSubmissionSummary_v14 was checked at commit 0e6dbb5 / Lean CI
#184, with the earlier release-index checkpoint at commit c6c1705 / Lean CI
#180.

The development verifies the descriptor architecture, residual concept
semantics, carrier saturation correctness, bounded finite-stopping results,
observed syntactic congruence and maximality, the canonical residual closure
system, K4 adequacy witnesses, carrier-level observed-block adequacy, the finite
observed-learning layer, the canonical point-frame incidence core for the
reduced representation viewpoint, the v27.1/v27.2 paper-facing release,
certificate, and final-index packages, the exact observed quotient-map layer,
and the post-relocation ORC theorem packages.  The artifact intentionally does
not claim a full formalization of the paper, a complete abstract universal
representation theorem for arbitrary reduced frame models, an internal quotient
monoid construction for SameObservedSyntactic S or Approx S, the Clark collapse
theorem, Dedekind-style lower bounds, or unrestricted adequacy.
```

## Audit files associated with this supplement

The local audit generated the following auxiliary files:

```text
LEAN_CI_AUDIT_REPORT.md
core_expected_targets_audit.csv
all_checked_targets.csv
successful_runs_summary.csv
missing_core_targets.txt
```

These files are not needed to build the Lean repository.  They are paper-facing
reproducibility evidence for the claim that the listed theorem-body targets were
found in successful GitHub Actions logs through Lean CI #217.  The later exact
observed quotient extension is recorded separately by Lean CI #219.


## Future formalization targets

Natural next targets include:

1. preparing a public release tag corresponding to the pinned theorem-body snapshot `794dc20` / Lean CI #216, together with the successful-log audit through Lean CI #217, the exact observed quotient check by Lean CI #219, and the post-relocation ORC theorem-package check by ObservedResidualConcept Lean CI #246;
2. archiving the paper artifact, FORMALIZATION supplement, and CI log-audit report under a persistent identifier;
3. adding a lightweight online blueprint linking paper statements to Lean declarations;
4. formalizing the full abstract reduced-frame-model isomorphism theorem;
5. formalizing the mod-`k` language family and its grammar-level saturation instance;
6. formalizing more concrete faithful-representative examples for observed learning;
7. formalizing the actual quotient monoid/congruence instance for `SameObservedSyntactic` / `Approx S`, beyond the currently checked abstract factor-map invariance, exact quotient-map universal-property theorems, and reduced reverse-classification core;
8. formalizing the Clark collapse theorem and Dedekind-style lower-bound examples;
9. developing restricted adequacy theorems for additional controlled subclasses;
10. keeping future extensions modular and preserving the current CI discipline.
