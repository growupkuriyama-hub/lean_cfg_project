# lean_cfg_project

This repository contains the Lean 4 artifact accompanying the paper
**Residual Concept Semantics for Two-Sided Fixed-h CFG Presentations**.

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
equivalence.  The current goal is to formalize a sound architecture in which
fixed-`h` two-sided CFG presentation descriptors admit semantic interpretations
inside a language-level residual/concept universe.

## Verified commit

Paper version: v11

Verified commit:

```text
b1dbc47
```

GitHub Actions:

```text
Lean CI #84: passed
```

## Main checked modules

```bash
lake build LeanCfgProject.Step25_Test
lake build LeanCfgProject.FullArchitecture_Test
lake build LeanCfgProject.StateSemantics
lake build LeanCfgProject.ResidualConcept
lake build LeanCfgProject.LanguageQuotient
lake build LeanCfgProject.DescriptorSemantics
lake build LeanCfgProject.DescriptorResidualSemantics
lake build LeanCfgProject.ObservationCounterexample
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
- `DescriptorSemantics.lean`: verified
- `DescriptorResidualSemantics.lean`: verified
- `ObservationCounterexample.lean`: verified
- `sorry`: 0 under the CI policy
- `axiom`: 0 project-level declarations under the CI policy
- GitHub Actions: green

## Paper-to-Lean correspondence

See Appendix A of the paper for the correspondence table between paper
statements and Lean declarations.

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

### 2. Abstract powerset and residual concept semantics

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
- soundness of binary rules after residual concept closure;
- initial syntactic-observation definitions for fixed-`h` language quotients.

This part is mainly contained in:

```text
LeanCfgProject/StateSemantics.lean
LeanCfgProject/ResidualConcept.lean
LeanCfgProject/LanguageQuotient.lean
```

### 3. Descriptor-level semantic bridge

This layer connects the existing carrier rule and context-family architecture
to the abstract semantic layer.

It includes:

- carrier yield sets defined from `YieldFamily`;
- carrier state semantics as an instance of abstract `StateSemantics`;
- terminal soundness for carrier terminal rules;
- binary soundness for carrier binary rules;
- binary soundness after residual concept closure;
- carrier concept-product soundness;
- carrier start languages defined from a start set;
- context-family yield-to-start soundness;
- residual soundness for carrier state semantics in a carrier context.

This part is mainly contained in:

```text
LeanCfgProject/DescriptorSemantics.lean
LeanCfgProject/DescriptorResidualSemantics.lean
```

### 4. Observation counterexample

This layer contains a concrete finite example showing that the naive finite
`h`-typed observation quotient is not generally compatible with concatenation.

It uses:

```text
L = {ab, cd}
h(w) = |w| mod 2
```

Main declarations include:

```text
CExSym
Parity
parityHom
counterexampleLanguage
not_same_observation_ab_cb
same_observation_b_b
observation_concat_obstruction_from_a_c
```

This part is contained in:

```text
LeanCfgProject/ObservationCounterexample.lean
```

## Online blueprint

An interactive blueprint will be hosted via GitHub Pages.  The PDF is meant to
be readable as a conventional paper; the online blueprint provides links to
Lean declarations, source files, dependency-oriented blueprint pages, and CI
logs.

The public repository URL and archived artifact DOI will be inserted in the
camera-ready or arXiv release once the repository is made public and the
artifact snapshot is archived.

## No sorry / no user-declared axioms policy

The CI rejects occurrences of `sorry` and project-level `axiom` declarations in
the checked project files.  This policy is meant to keep the artifact honest
about what has actually been checked.

## Current mathematical interpretation

The repository should be read as a machine-checked Lean model of the core
architecture and its semantic extension.

The currently verified development supports the following conservative claim:

```text
At commit b1dbc47, the presentation-level architecture, the abstract
powerset-valued state semantics, the residual-concept semantic layer,
the descriptor-level semantic bridge, and the observation-counterexample
module build successfully in Lean 4 with no sorry and no project-level axiom
declarations under the CI policy.
```

It does **not** claim that:

- the entire accompanying paper is fully formalized;
- CFG equivalence is solved;
- a canonical CFG presentation has been constructed;
- every fixed-`h` descriptor is already a language-level invariant;
- a new full identification theorem for CFLs has been proved.

The intended claim is more modest and more precise:

```text
Fixed-h two-sided CFG presentation descriptors admit sound powerset-valued
and residual-concept semantic interpretations inside a language-level universe.
```
