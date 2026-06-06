# \# lean\_cfg\_project

# 

# This repository contains an experimental Lean 4 formalization of an abstract architecture for finite two-sided typed context structures associated with CFG presentations.

# 

# The current formalization is organized around two core Lean modules:

# 

# \* `LeanCfgProject.Step25\_Test`

# \* `LeanCfgProject.FullArchitecture\_Test`

# 

# \## Verification status

# 

# The current verified commit is:

# 

# ```text

# d8d8d4e

# ```

# 

# GitHub Actions status:

# 

# ```text

# Lean CI #61: passed

# ```

# 

# The CI checks the following modules:

# 

# ```bash

# lake build LeanCfgProject.Step25\_Test

# lake build LeanCfgProject.FullArchitecture\_Test

# ```

# 

# The CI also rejects Lean source files containing:

# 

# \* `sorry`

# \* `axiom`

# 

# Current status:

# 

# \* `Step25\_Test.lean`: verified

# \* `FullArchitecture\_Test.lean`: verified

# \* `sorry`: 0

# \* `axiom`: 0

# 

# \## What is formalized

# 

# The project formalizes a finite typed architecture inspired by two-sided context structures for context-free grammar presentations.  The development includes:

# 

# \* finite monoid-typed refinements of CFG-style rules;

# \* full typed states carrying yield, left-context, and right-context information;

# \* extraction of finite context structures from refined grammars;

# \* realization of witnessed finite context structures as state-separated grammars;

# \* functorial extraction and realization constructions;

# \* a retraction-style normalization interface for the extracted/realized architecture.

# 

# The code is intended as a formally checked architectural skeleton, rather than a complete formalization of every theorem in the accompanying mathematical manuscript.

# 

# \## Main files

# 

# ```text

# LeanCfgProject/

# &#x20; Step25\_Test.lean

# &#x20; FullArchitecture\_Test.lean

# ```

# 

# `Step25\_Test.lean` contains the underlying typed CFG refinement layer.

# 

# `FullArchitecture\_Test.lean` builds the categorical and architectural layer on top of `Step25\_Test.lean`.

# 

# \## Continuous integration

# 

# The repository uses GitHub Actions to run Lean verification automatically on push and pull request.

# 

# The workflow file is:

# 

# ```text

# .github/workflows/lean.yml

# ```

# 

# The CI performs three checks:

# 

# 1\. build `LeanCfgProject.Step25\_Test`;

# 2\. build `LeanCfgProject.FullArchitecture\_Test`;

# 3\. reject any remaining `sorry` or `axiom` declarations.

# 

# \## Notes

# 

# This repository is experimental research code.  The formalization should be read as a machine-checked Lean model of the core architecture, not as a claim that the entire associated paper has been fully formalized.

# 

# The important verified fact is that the present Lean development builds successfully with no `sorry` and no `axiom` at commit `d8d8d4e`.

# 

