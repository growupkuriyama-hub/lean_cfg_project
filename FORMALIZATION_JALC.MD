# Lean Formalization Record for the JALC Paper

This document records the Lean 4 formalization status for the JALC-oriented paper:

```text
A Finite Representation Theorem for Two-Sided Monoid-Typed CFG Presentations
```

This file is specific to the JALC paper. It is separate from the repository-level `FORMALIZATION.md`, which records formalization results for a different paper or a broader repository-level development.

This version updates the earlier record after the recent sequence of JALC Lean experiments that added theorem-facing kernels for transport, non-rigidity, productive-first trimming, intended-copy representation, derivation/language preservation, kept-state representation, and finite-universe/cardinality checks.

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

Current high-level finite-representation target:

```text
LeanCfgProject.JALC.FiniteRepresentationBundle
```

Recommended current CI command:

```text
lake build LeanCfgProject.JALC.Summary
lake build LeanCfgProject.JALC.FiniteRepresentationBundle
```

The current minimal GitHub Actions workflow should build:

```text
LeanCfgProject.JALC.Summary
LeanCfgProject.JALC.FiniteRepresentationBundle
```

and then run the JALC-directory placeholder guard.

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

### Recent extended CI status

After CI #236, the JALC artifact was substantially extended. The following families of modules have been added and reported as passing in GitHub Actions during the recent development sequence:

```text
LeanCfgProject.JALC.Transport
LeanCfgProject.JALC.Bracketing
LeanCfgProject.JALC.ProductiveFirst
LeanCfgProject.JALC.PaperFacing
LeanCfgProject.JALC.InverseKernel
LeanCfgProject.JALC.RoundTripKernel
LeanCfgProject.JALC.IntendedCopyEquiv
LeanCfgProject.JALC.RuleLiftSummary
LeanCfgProject.JALC.StateRuleIsoKernel
LeanCfgProject.JALC.DerivationLiftKernel
LeanCfgProject.JALC.StartLanguageKernel
LeanCfgProject.JALC.KeptStateKernel
LeanCfgProject.JALC.RepresentationKernel
LeanCfgProject.JALC.PaperFacingAdvanced
LeanCfgProject.JALC.KeptStructureKernel
LeanCfgProject.JALC.KeptDerivationKernel
LeanCfgProject.JALC.KeptStartLanguageKernel
LeanCfgProject.JALC.KeptRepresentationKernel
LeanCfgProject.JALC.FiniteUniverseKernel
LeanCfgProject.JALC.FiniteRepresentationKernel
LeanCfgProject.JALC.PaperFacingFinite
LeanCfgProject.JALC.FiniteCardinalityKernel
LeanCfgProject.JALC.PaperFacingCardinality
LeanCfgProject.JALC.FiniteRepresentationBundle
```

Latest successful CI run after the final `FiniteRepresentationBundle` fix:

```text
Lean CI #: TODO
Commit: TODO
Pushed by: growupkuriyama-hub
Targets:
  lake build LeanCfgProject.JALC.Summary
  lake build LeanCfgProject.JALC.FiniteRepresentationBundle
```

The exact latest CI number and commit hash should be copied from GitHub after the final successful run. They were not available in the chat transcript at the time this record was updated.

---

## 3. Purpose of the formalization

The purpose of this Lean development is to provide a machine-checked companion artifact for the finite two-sided monoid-typed representation theorem developed in the JALC paper.

The current development has two layers.

First, it checks the finite typed infrastructure used by the paper:

* finite monoid observers;
* two-sided h-types;
* typed nonterminals;
* observed two-sided contexts;
* finite descriptor-level rule universes;
* finite descriptors;
* finite extent/intent operators;
* a lightweight residual/concept layer.

Second, it now checks theorem-facing kernels that are much closer to the main representation theorem:

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

The development is still not claimed to be a complete formalization of every theorem in the paper. In particular, the full extraction/trimming theorem, especially the equality between reachable productive typed states and intended copies, remains proved in the prose paper. However, most of the structural consequences of that equality have now been formalized.

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
* finite-universe and cardinality kernels.

### Still prose-level

The following parts are not yet fully formalized as general Lean theorems:

* the full extraction theorem from arbitrary CFG presentations;
* the general productive/reachable trimming fixed-point theorem;
* the theorem that reachable productive typed copies are exactly intended copies;
* the complete end-to-end characterization theorem;
* shortlex witness preservation;
* context-closure coincidence lemmas for the full two-sided construction.

### Current honest claim

The current artifact supports the following claim:

```text
The Lean 4 development checks the finite typed infrastructure and a broad set
of theorem-facing kernels for the finite representation theorem. It is not a
complete end-to-end formalization of the full extraction and trimming theorem.
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
```

The recommended current high-level target is:

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

This isolates the remaining major prose burden:

```text
reachable productive typed states = intended copies
```

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

This module is close to the main representation theorem, except that it assumes the kept-state correctness statement rather than proving the full trimming theorem.

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

Current high-level target:

```text
LeanCfgProject.JALC.FiniteRepresentationBundle
```

---

## 7. Current CI guard

The intended policy for the JALC Lean directory remains:

```text
no proof-bypassing placeholder commands
no extra primitive declarations
```

The GitHub Actions workflow checks the JALC Lean directory for the corresponding terms.

Recommended minimal CI workflow:

```text
lake build LeanCfgProject.JALC.Summary
lake build LeanCfgProject.JALC.FiniteRepresentationBundle
```

followed by the placeholder guard.

Because `FiniteRepresentationBundle.lean` imports the newer theorem-facing and finite-representation modules through its dependency chain, building this target checks the extended artifact without needing to list every intermediate module in the CI workflow.

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
* finite universe and finite cardinality kernels.

Thus, the artifact now supports a much stronger claim than the original baseline. It is no longer only a finite-carrier consistency check; it now verifies several structural kernels immediately surrounding the finite representation theorem.

---

## 9. What is not claimed

The current Lean development is not a complete end-to-end formalization of the full paper.

The most important remaining unformalized component is:

```text
reachable productive typed states = intended copies
```

More explicitly, the current development does not yet fully formalize:

* the general extraction theorem from arbitrary CFG presentations;
* the full productive/reachable trimming fixed-point construction;
* the proof that trimming leaves exactly the intended typed copies;
* the full characterization theorem combining extraction, trimming, and descriptor reconstruction;
* shortlex witness preservation;
* full context-closure coincidence for all one-hole contexts.

The current artifact proves many consequences that would follow once kept-state correctness is established, but the kept-state correctness theorem itself remains a prose proof.

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
preservation, kept-state representation kernels, and finite-universe/cardinality
kernels.  In particular, the frame-transport invariants are checked over
arbitrary monoids, so the checked proof does not rely on commutativity.

The development is not claimed to be a complete formalization of the full
extraction and trimming theorem.  The main remaining prose-level component is
the proof that the reachable productive typed states are exactly the intended
copies.  Conditional on that statement, the Lean development checks the
state/rule/language representation kernels and the finite-universe/cardinality
kernels used by the paper.
```

A shorter version:

```text
The Lean 4 artifact checks the finite typed infrastructure and several
theorem-facing kernels of the representation theorem, including
orientation-sensitive frame transport over arbitrary monoids, finite
non-rigidity and productive-first witnesses, intended-copy state equivalence,
rule/derivation/language preservation, kept-state representation kernels, and
finite-universe/cardinality kernels.  We do not claim a complete formalization
of the full extraction and trimming theorem; the equality between reachable
productive typed states and intended copies remains proved in prose.
```

---

## 11. Reproduction instructions

At the root of the repository, run:

```text
lake build LeanCfgProject.JALC.Summary
lake build LeanCfgProject.JALC.FiniteRepresentationBundle
```

Expected checked targets:

```text
LeanCfgProject.JALC.Summary
LeanCfgProject.JALC.FiniteRepresentationBundle
```

Reference baseline CI run:

```text
Lean CI #236
Commit: a4e2d6a
```

Latest successful extended CI run:

```text
Lean CI #: TODO
Commit: TODO
```

Fill in the latest CI number and commit hash after copying them from GitHub Actions.

---

## 12. Recommended citation in the paper

A concise citation in the paper can be written as:

```text
The accompanying Lean 4 artifact checks the modules
LeanCfgProject.JALC.Summary and LeanCfgProject.JALC.FiniteRepresentationBundle.
The baseline reference run was Lean CI #236 at commit a4e2d6a; the latest
extended CI run is Lean CI #TODO at commit TODO.
```

A more descriptive version is:

```text
The finite typed architecture and several theorem-facing kernels were checked
in Lean 4.  The checked development includes finite observers, two-sided
h-types, observed contexts, finite descriptors, transport invariants over
arbitrary monoids, finite example kernels, intended-copy state/rule/derivation
and language kernels, kept-state representation kernels, and
finite-universe/cardinality kernels.  The current high-level target is
LeanCfgProject.JALC.FiniteRepresentationBundle, together with the original
summary target LeanCfgProject.JALC.Summary.
```

---

## 13. Practical assessment

As a JALC companion artifact, the current development is strong.

A fair assessment is:

```text
JALC submission support: high
Complete main-theorem formalization: partial
Finite representation side: substantially checked
Extraction/trimming general theorem: still prose-level
```

Approximate internal assessment:

```text
JALC-facing Lean value: 85--90 / 100
Full main-theorem formalization: 55--60 / 100
Finite-representation side: around 75 / 100
Extraction/trimming theorem: around 30 / 100
```

These numbers should not be written in the paper, but they are useful for internal planning.

---

## 14. Next possible Lean targets

The next serious formalization target would be:

```text
KeptCorrectness.lean
```

Goal:

```text
reachable productive typed copies = intended copies
```

This is the main remaining theorem-level gap. It would require formalizing:

* the actual typed refinement rules;
* productivity;
* reachability;
* productive-first trimming;
* correctness of intended copies;
* exclusion of spurious productive/reachable copies.

This is substantially harder than the current kernel files. It should be attempted only after the current artifact has been recorded in the paper and the formalization report.

