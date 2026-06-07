# lean_cfg_project

This repository contains an experimental Lean 4 formalization for the fixed-`h`
CFG / residual concept semantics project.

The project studies finite two-sided monoid-typed structures associated with
context-free grammar presentations, together with a Lean-checked semantic layer
connecting presentation-level descriptors to powerset-valued and residual
concept semantics.

The intended mathematical direction is:

```text
presentation-level descriptor E_h(G)
        -> powerset-valued state semantics P(Q)
        -> residual concept universe Concepts(Q, q[L])
```

The goal is **not** to claim a canonical CFG presentation or to solve CFG
equivalence. The current goal is to formalize a sound architecture in which
fixed-`h` two-sided CFG presentation descriptors admit semantic interpretations
inside a language-level residual/concept universe.

## Verification status

The current verified commit is:

```text
b7705b7
```

GitHub Actions status:

```text
Lean CI #92: passed
```

The current CI checks the following modules:

```bash
lake build LeanCfgProject.Step25_Test
lake build LeanCfgProject.FullArchitecture_Test
lake build LeanCfgProject.StateSemantics
lake build LeanCfgProject.ResidualConcept
lake build LeanCfgProject.LanguageQuotient
lake build LeanCfgProject.ObservationFinite
lake build LeanCfgProject.DescriptorSemantics
lake build LeanCfgProject.DescriptorResidualSemantics
lake build LeanCfgProject.CarrierConceptSemantics
lake build LeanCfgProject.ObservationCounterexample
lake build LeanCfgProject.ObservationCounterexample_v2
```

The CI also rejects Lean source files containing:

- `sorry`
- project-level `axiom` declarations

Current status:

- `Step25_Test.lean`: verified
- `FullArchitecture_Test.lean`: verified
- `StateSemantics.lean`: verified
- `ResidualConcept.lean`: verified
- `LanguageQuotient.lean`: verified
- `ObservationFinite.lean`: verified
- `DescriptorSemantics.lean`: verified
- `DescriptorResidualSemantics.lean`: verified
- `CarrierConceptSemantics.lean`: verified
- `ObservationCounterexample.lean`: verified
- `ObservationCounterexample_v2.lean`: verified
- `sorry`: 0 under the CI policy
- `axiom`: 0 project-level declarations under the CI policy
- GitHub Actions: green

## What is formalized

The project currently has four connected layers.

### 1. Presentation-level architecture

The original verified core formalizes an abstract architecture for finite
two-sided typed context structures associated with CFG presentations.

This layer includes:

- finite monoid-typed refinements of CFG-style rules;
- full typed states carrying yield, left-context, and right-context information;
- extraction of finite context structures from refined grammars;
- realization of witnessed finite context structures as state-separated grammars;
- functorial extraction and realization constructions;
- a retraction-style normalization interface for the extracted/realized architecture.

This part is mainly contained in:

```text
LeanCfgProject/Step25_Test.lean
LeanCfgProject/FullArchitecture_Test.lean
```

### 2. Observation and quotient layer

This layer defines the finite `h`-typed observation relation and its stabilized
variants.

It includes:

- `HTypedContextTypes`;
- `SameHTypedObservation`;
- `SameHTypedSyntacticObservation`;
- `SameHTypedPointedObservation`;
- `SameHTypedPointedSyntacticObservation`;
- SynObs maximality for two-sided stable relations;
- the pointed boundary theorem connecting pointed SynObs with ordinary syntactic context equivalence together with the kernel of `h`;
- an observation-signature/kernel formulation of the naive observation relation.

This part is mainly contained in:

```text
LeanCfgProject/LanguageQuotient.lean
LeanCfgProject/ObservationFinite.lean
```

### 3. Abstract powerset and residual concept semantics

This layer formalizes abstract semantic tools used to connect presentation-level
descriptors with language-level residual/concept semantics.

It includes:

- image semantics of languages under a multiplicative word observation;
- concatenation of languages and subset multiplication;
- powerset-valued state semantics;
- terminal and binary rule soundness over an abstract monoid carrier;
- two-sided residuals of a start image `S = q[L]`;
- quotient-level Galois maps between subsets of `Q` and subsets of `Q × Q`;
- the residual Galois connection;
- residual concept closure as an extensive, monotone, idempotent closure operation;
- concept extents and concept products;
- soundness of binary rules after residual concept closure.

This part is mainly contained in:

```text
LeanCfgProject/StateSemantics.lean
LeanCfgProject/ResidualConcept.lean
```

### 4. Descriptor-level semantic bridge

The newest verified layer connects the existing carrier rule and context-family
architecture to the abstract semantic layer and packages the final carrier-level
concept semantics.

This layer includes:

- carrier yield sets defined from `YieldFamily`;
- carrier state semantics as an instance of abstract `StateSemantics`;
- terminal soundness for carrier terminal rules;
- binary soundness for carrier binary rules;
- binary soundness after residual concept closure;
- carrier concept-product soundness;
- carrier start languages defined from a start set;
- context-family yield-to-start soundness;
- residual soundness for carrier state semantics in a carrier context;
- carrier start images;
- named carrier-level concept semantics;
- proof that carrier concept semantics is a concept extent;
- binary rule soundness at the concept-semantics level;
- context residual closure for carrier concepts.

This part is mainly contained in:

```text
LeanCfgProject/DescriptorSemantics.lean
LeanCfgProject/DescriptorResidualSemantics.lean
LeanCfgProject/CarrierConceptSemantics.lean
```

## Main files

```text
LeanCfgProject/
  Step25_Test.lean
  FullArchitecture_Test.lean
  StateSemantics.lean
  ResidualConcept.lean
  LanguageQuotient.lean
  ObservationFinite.lean
  DescriptorSemantics.lean
  DescriptorResidualSemantics.lean
  CarrierConceptSemantics.lean
  ObservationCounterexample.lean
  ObservationCounterexample_v2.lean
```

### `Step25_Test.lean`

Contains the underlying typed CFG refinement layer, including words,
fixed finite monoid homomorphisms, typed states, full typed states, typed rules,
productivity/reachability, trimmed states, extracted profiles, and extracted
typed rule structures.

### `FullArchitecture_Test.lean`

Builds the architectural layer on top of `Step25_Test.lean`, including finite
context structures, witnessed finite context structures, morphisms,
extraction/realization interfaces, a retraction-style interface, and the
`YieldFamily` / `ContextFamily` inductive structures used in the semantic bridge.

### `LanguageQuotient.lean`

Defines initial language-level observation relations.

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
```

It formalizes the distinction between:

- finite but non-composition-compatible observation quotients;
- unpointed syntactic observation congruences;
- pointed observation relations, which connect to ordinary syntactic congruence
  together with the kernel of `h`.

### `ObservationFinite.lean`

Defines the observation signature and verifies that the naive `h`-typed
observation relation is the kernel of this signature.

Main declarations include:

```text
ObservationSignature
observationSignature_eq_of_sameHTypedObservation
sameHTypedObservation_of_observationSignature_eq
sameHTypedObservation_iff_observationSignature_eq
sameHTypedObservation_kernel
```

This supports the paper-level finite-index argument by identifying the relevant
finite observation data without introducing quotient types.

### `StateSemantics.lean`

Defines abstract powerset-valued semantics for languages and grammar states
under a multiplicative word observation `q : Sigma* -> Q`.

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

The key mathematical idea is that if `q` is multiplicative, then image semantics
turns concatenation into subset multiplication:

```text
q[Y Z] = q[Y] q[Z]
```

Consequently, binary CFG rules are interpreted soundly as subset multiplication
inclusions.

### `ResidualConcept.lean`

Defines residual, Galois, closure, and concept-product structures over an
abstract monoid carrier `Q`.

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

The key mathematical idea is that, for `S = q[L]`, the relation

```text
gamma I_S (alpha, beta)  iff  alpha * gamma * beta ∈ S
```

induces a Galois connection between subsets of `Q` and subsets of `Q × Q`.
The module verifies that the induced concept closure is extensive, monotone, and
idempotent, and that binary rule soundness persists after residual concept
closure.

### `DescriptorSemantics.lean`

Connects carrier terminal and binary rules to powerset-valued and concept-product
semantics.

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
```

This module verifies that carrier terminal and binary rules from the descriptor
layer are soundly interpreted by the abstract semantic layer.

### `DescriptorResidualSemantics.lean`

Connects carrier context families to residual soundness.

Main declarations include:

```text
context_yield_mem_startLanguage_aux
context_yield_mem_startLanguage
carrier_state_semantics_subset_residual
```

This module verifies that if a carrier state occurs in a carrier context, then
its powerset-valued semantics is contained in the corresponding two-sided
residual of the carrier start language image.

### `CarrierConceptSemantics.lean`

Packages the carrier-level map into residual concept semantics.

Main declarations include:

```text
CarrierStartImage
CarrierConceptSemantics
carrierConceptSemantics_isConceptExtent
carrier_binary_sound_as_conceptSemantics
carrier_context_concept_subset_residual_closure
```

This module verifies that carrier states are mapped to closed residual concept
extents, that binary rules remain sound at the concept-semantics level, and that
carrier concepts satisfy the expected residual-closure inclusion for verified
context families.

### `ObservationCounterexample.lean`

Formalizes a concrete obstruction to using the naive finite `h`-typed
observation quotient as a concatenation-compatible quotient.

Main declarations include:

```text
parityHom
counterexampleLanguage
not_same_observation_ab_cb
observation_concat_obstruction_from_a_c
```

For the language `L = {ab, cd}` and the parity observation, this module verifies
that `ab` and `cb` are not equivalent under the naive observation relation, and
records the resulting obstruction to concatenation compatibility.

### `ObservationCounterexample_v2.lean`

Completes the concrete obstruction by verifying that `a` and `c` have the same
naive finite observation while concatenation with `b` separates them.

Main declarations include:

```text
same_observation_a_c
naive_observation_not_concat_compatible
```

Together with `same_observation_b_b` and `not_same_observation_ab_cb`, this
module checks the full concrete fact that the naive finite `h`-typed observation
relation is not generally compatible with concatenation.

## Continuous integration

The repository uses GitHub Actions to run Lean verification automatically on
push, pull request, and manual workflow dispatch.

The workflow file is:

```text
.github/workflows/lean.yml
```

The CI currently performs these checks:

1. build `LeanCfgProject.Step25_Test`;
2. build `LeanCfgProject.FullArchitecture_Test`;
3. reject any remaining `sorry`;
4. reject project-level `axiom` declarations;
5. build `LeanCfgProject.StateSemantics`;
6. build `LeanCfgProject.ResidualConcept`;
7. build `LeanCfgProject.LanguageQuotient`;
8. build `LeanCfgProject.ObservationFinite`;
9. build `LeanCfgProject.DescriptorSemantics`;
10. build `LeanCfgProject.DescriptorResidualSemantics`;
11. build `LeanCfgProject.CarrierConceptSemantics`;
12. build `LeanCfgProject.ObservationCounterexample`;
13. build `LeanCfgProject.ObservationCounterexample_v2`.

## Current mathematical interpretation

The repository should be read as a machine-checked Lean model of the core
architecture and its semantic extension.

The currently verified development supports the following conservative claim:

```text
At commit b7705b7, the presentation-level architecture, the observation
relations and observation-signature kernel, the abstract powerset-valued state
semantics, the residual-concept semantic layer, the descriptor-level carrier
rule/context semantic bridges, the named carrier concept semantics, and the
concrete observation-counterexample modules build successfully in Lean 4 with
no sorry and no project-level axioms under the repository CI policy.
```

It does **not** claim that:

- the entire accompanying paper is fully formalized;
- CFG equivalence is solved;
- a canonical CFG presentation has been constructed;
- every fixed-`h` descriptor is already a language-level invariant.

The intended claim is more modest and more precise:

```text
Fixed-h two-sided CFG presentation descriptors admit sound powerset-valued
and residual-concept semantic interpretations inside a language-level universe.
```

## Research direction

The current formalization supports a research program around the semantic bridge:

```text
E_h(G) -> P(Q) -> Concepts(Q, q[L])
```

Here:

- `E_h(G)` is a presentation-level fixed-`h` two-sided descriptor;
- `Q` is a language-level observation carrier or quotient candidate;
- `P(Q)` is the powerset-valued state semantics;
- `q[L]` is the start image of the language;
- `Concepts(Q, q[L])` is the residual Galois / Clark-style concept universe.

The refined open problem is to identify useful finite generated residual concept
bases for fixed-`h` substitutable context-free languages, without collapsing the
problem to regular-language recognition.

## Next Lean targets

Near-term proof targets include:

1. preparing an online companion blueprint with links to declarations and CI logs;
2. preparing an artifact snapshot or release tag corresponding to the paper;
3. investigating finite generated residual concept bases for fixed-`h`
   substitutable context-free languages;
4. keeping future extensions small and modular.

The guiding principle is to keep each Lean extension compatible with the
no-`sorry` / no-project-level-`axiom` CI discipline, and to distinguish clearly
between checked formalization results and open mathematical problems.
