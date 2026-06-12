# Lean Formalization Record for the JALC Paper

This document records the Lean 4 formalization status for the JALC-oriented paper on finite two-sided context structures and descriptor-level representations for context-free grammar presentations under fixed finite-monoid typing.

This file is specific to the JALC paper.  It is separate from the repository-level `FORMALIZATION.md`, which records formalization results for another paper.

## Repository

Repository:

```text
growupkuriyama-hub/lean_cfg_project
```

Formalization directory for this paper:

```text
LeanCfgProject/JALC/
```

Paper-facing Lean target:

```text
LeanCfgProject.JALC.Summary
```

Reference CI run:

```text
Lean CI #236
Commit: a4e2d6a
Pushed by: growupkuriyama-hub
Target: LeanCfgProject.JALC.Summary
```

The successful CI command was:

```text
lake build LeanCfgProject.JALC.Summary
```

## Purpose of the formalization

The purpose of this Lean development is to check the finite typed architecture used in the JALC paper.

The development is not intended to be a complete formalization of every theorem in the paper.  Instead, it serves as a machine-checked consistency test for the core finite representation infrastructure:

* finite monoid observers;
* two-sided h-types;
* typed nonterminals;
* observed two-sided contexts;
* finite descriptor-level rule universes;
* finite descriptors;
* finite extent/intent operators;
* a lightweight residual/concept layer.

This is the part of the paper where silent type mistakes are most likely to occur, so checking the architecture in Lean gives useful independent evidence that the finite representation framework is internally coherent.

## Checked files

The current JALC formalization consists of the following Lean files:

```text
LeanCfgProject/JALC/
  Basic.lean
  TwoSidedContext.lean
  Descriptor.lean
  ResidualConcept.lean
  Summary.lean
```

The paper-facing aggregation module is:

```text
LeanCfgProject/JALC/Summary.lean
```

The CI target is:

```text
LeanCfgProject.JALC.Summary
```

## Module-by-module status

### `Basic.lean`

This file defines the basic finite observer infrastructure.

Checked components include:

* an explicit finite monoid observer on words;
* the observer carrier `M`;
* explicit multiplication, unit, and monoid laws;
* the observer map on words;
* two-sided h-types with left, middle, and right monoid components;
* typed nonterminals;
* boundary pairs;
* finite carrier constructions for two-sided types and typed nonterminals;
* the basic middle-transport operation;
* the unit-transport sanity lemma.

This file establishes the typed finite universe on which the later descriptor and residual/concept layers are built.

### `TwoSidedContext.lean`

This file defines finite h-observed two-sided contexts.

Checked components include:

* observed contexts as pairs of left and right monoid values;
* the empty observed context;
* application of an observed context to a middle h-value;
* conversion from an observed context and a middle value to a two-sided type;
* total observed value of a two-sided type;
* composition of observed contexts;
* identity laws for the empty observed context;
* the finite universe of observed contexts.

This file corresponds to the paper’s use of finite observed context information rather than raw unbounded string contexts.

### `Descriptor.lean`

This file defines the finite descriptor-level rule universe.

Checked components include:

* terminal rules over typed nonterminals and observed contexts;
* nullary rules;
* binary rules;
* finite universes of terminal, nullary, and binary rules;
* the full descriptor universe;
* finite descriptors with a start typed nonterminal and finite rule supports;
* the rule-count function for finite descriptors;
* the empty descriptor and its zero rule-count lemma.

This file is the formal counterpart of the paper’s descriptor-level finite representation layer.

### `ResidualConcept.lean`

This file defines a lightweight finite residual/concept layer over typed states and observed contexts.

Checked components include:

* typed-state carrier;
* observed-context carrier;
* incidence relations between typed states and observed contexts;
* finite extents;
* finite intents;
* state-side and context-side closure operators;
* residual concepts as finite extent/intent pairs satisfying closure equations;
* a boundary-incidence sanity-check model;
* membership characterizations for finite extent and intent;
* antitonicity of extent and intent.

This file checks that the residual/concept layer can be expressed over finite carriers derived from the typed descriptor architecture.

### `Summary.lean`

This file imports all JALC formalization modules and exposes the paper-facing checked target.

It summarizes the Lean-checked availability of:

* finite monoid observers;
* two-sided h-types;
* observed contexts;
* typed nonterminals;
* finite descriptors;
* residual concepts;
* finite typed-state universes;
* finite observed-context universes;
* full descriptor universes.

The successful CI target is:

```text
LeanCfgProject.JALC.Summary
```

## CI result

The JALC formalization was successfully checked by GitHub Actions.

Reference point:

```text
Lean CI #236
Commit: a4e2d6a
Pushed by: growupkuriyama-hub
Target: LeanCfgProject.JALC.Summary
```

The checked command was:

```text
lake build LeanCfgProject.JALC.Summary
```

At this commit, the following modules were built successfully:

```text
LeanCfgProject.JALC.Basic
LeanCfgProject.JALC.TwoSidedContext
LeanCfgProject.JALC.Descriptor
LeanCfgProject.JALC.ResidualConcept
LeanCfgProject.JALC.Summary
```

## CI guard

The GitHub Actions workflow builds the paper-facing target and checks the JALC Lean directory for proof-bypassing placeholders and extra primitive declarations.

The intended policy for `LeanCfgProject/JALC/` is:

```text
no sorry
no admit
no axiom
```

The successful CI run confirms that the JALC formalization builds under this policy at commit `a4e2d6a`.

## What is claimed

The current Lean development checks the finite typed infrastructure used by the paper.

In particular, it checks that the following paper-level objects can be represented as well-typed finite Lean objects:

* finite observer interface;
* two-sided typed state space;
* finite observed two-sided context space;
* descriptor-level terminal, nullary, and binary rule universes;
* finite descriptors;
* finite extents and intents;
* residual/concept structures over typed states and observed contexts.

Thus, the Lean artifact supports the paper’s claim that the proposed descriptor-level architecture is finite and type-consistent.

## What is not claimed

The current Lean development is not a complete end-to-end formalization of every theorem in the paper.

In particular, it does not claim to formalize the entire mathematical development, every proof in the article, or every semantic equivalence statement.  Its role is more focused: it verifies the finite typed architecture and selected structural properties that underlie the descriptor construction.

This limited claim is intentional.  The formalization is meant to be a reproducible machine-checked companion to the paper, not a replacement for the paper’s mathematical exposition.

## Suggested wording for the paper

The following wording may be used in the paper or appendix.

```text
An accompanying Lean 4 development checks the finite typed architecture used in this paper.  The paper-facing module is LeanCfgProject.JALC.Summary, which was checked by GitHub Actions in Lean CI #236 at commit a4e2d6a.  The checked components include the finite observer interface, two-sided h-types, observed two-sided contexts, descriptor-level finite rule universes, finite descriptors, and a lightweight residual/concept layer over typed states and observed contexts.  We do not claim a complete formalization of every theorem in the paper; rather, the Lean development serves as a machine-checked consistency test for the finite representation architecture.
```

## Reproduction instructions

At the root of the repository, run:

```text
lake build LeanCfgProject.JALC.Summary
```

Expected checked target:

```text
LeanCfgProject.JALC.Summary
```

Reference successful CI run:

```text
Lean CI #236
Commit: a4e2d6a
```

## Recommended citation in the paper

A concise citation in the paper can be written as:

```text
The accompanying Lean 4 artifact checks the module LeanCfgProject.JALC.Summary; the reference CI run is Lean CI #236 at commit a4e2d6a.
```

A more descriptive version is:

```text
The finite typed architecture was checked in Lean 4.  The paper-facing module LeanCfgProject.JALC.Summary imports the checked components for finite observers, two-sided h-types, observed contexts, descriptor-level rule universes, finite descriptors, and the residual/concept layer.  The reference GitHub Actions run is Lean CI #236 at commit a4e2d6a.
```
