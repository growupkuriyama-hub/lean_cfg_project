# Formalization record: MCFG arXiv v4 (2026-09-07 baseline)

This file is the authoritative verification ledger for the new Lean 4 formalization of the manuscript

> Positive-Data Learning of Multiple Context-Free Languages under Finite-Monoid Observation

The development is intentionally isolated from both the fixed-h CFG verification and the older MCFG2 experiment.

## 1. Frozen manuscript baseline

The only manuscript source of truth for this verification is:

```text
MCFG_arXiv_v4_20260907_final_v3.tex
Date/version marker: 2026-09-07 final v3 / arXiv-v4 candidate
File size: 128200 bytes
SHA-256: 9999952ce78624a92053ab0d28fc861a23d9ca30bb58c548df11add354c2d9dd
```

All theorem statements, assumptions, numbering/labels, and proof-gap reports in this ledger must be checked against that exact source.

Files in `LeanCfgProject/MCFG2_latex/` whose names also contain `v4` are older working copies and are not the manuscript baseline for this verification.

## 2. Isolation policy

New development:

```text
branch: mcfg-v4-verification
Lean directory: LeanCfgProject/MCFGv4/
CI prefix: verify-mcfg-v4-...
```

Other work is out of scope for writes from this branch:

```text
LeanCfgProject/FixedHCFG/   # #1 TCS fixed-h CFG verification
LeanCfgProject/MCFG2/       # legacy/pre-2026-09-07 MCFG proof and experiment archive
```

`LeanCfgProject/MCFG2/` may be read for proof ideas and reusable lemmas, but no old MCFG2 theorem counts as verification of the frozen v4 manuscript until its statement and hypotheses have been compared with the v4 source and it has been re-established in the `MCFGv4` chain.

## 3. Provenance of the legacy MCFG2 assets

The existing MCFG2 clean-restart ledger predates the frozen manuscript: its confirmed 239-root checkpoint is from 2026-08-04 and the ledger itself describes the restart as rebuilding material from an earlier paper version. The old modules therefore originate in the v2/v3-era development (with later experimental working copies added to the repository) rather than constituting a verification of the 2026-09-07 v4 manuscript.

In particular, the old development used, at several stages, specialized terminal/binary rule interfaces. The frozen v4 manuscript is written for standard finite MCFG presentations of arbitrary finite rule rank. Reuse must therefore be theorem-by-theorem, not by bulk import.

## 4. Verification policy

A manuscript item may be marked `VERIFIED` only if all of the following hold:

1. its Lean statement matches the frozen v4 manuscript at the intended abstraction level;
2. all additional assumptions introduced by Lean are recorded;
3. the proof contains no `sorry` or `admit`;
4. the relevant `LeanCfgProject.MCFGv4.*` target is rebuilt by CI;
5. the theorem-to-manuscript correspondence is entered in `LeanCfgProject/MCFGv4/THEOREM_INVENTORY.md`.

Legacy MCFG2 results are classified only as `legacy candidate` until this process is complete.

## 5. Planned milestones

### V4-A: semantic foundation

Finite observations, standard arbitrary-rank MCFG syntax, oriented tuple contexts, permutation-decoration normalization, orientation-sector canonicalization, fan-out-one specialization, observation-refinement monotonicity, and shared-context substitutability.

### V4-B: refined proof grammar

Output-type refinement, output invariants, preservation of nonpermuting rules, identity exposing contexts, typed-state uniformity, identity-orientation propagation, silent-child compression, and positivity/finiteness of the characteristic sample.

### V4-C: exact reconstruction core

Sample-bounded witness rank, arbitrary-rank witness enumeration, rule-enumeration completeness, effective standard hypotheses, filling identity, witnessed composition, learner soundness, completeness, exact reconstruction, finite tell-tales, TxtBc identification, and TxtEx identification.

### V4-D: fixed-rank complexity

Slicewise-polynomial construction and polynomial-time identification on each fixed rule-rank slice.

### V4-E: comparison/boundary theory

Boundary congruence, fan-out-one comparison with `(k,l)`-substitutability, Yoshinaka inclusion, strictness at fixed rank, strict polynomial extension, and common-context finite-kernel implication.

### V4-F: advice boundary

Universal bounded observation, learner-uniform locking lower bound, and the Gold-superfinite obstruction for unbounded latent observation.

## 6. Current status

```text
Branch created: YES
Frozen source recorded: YES
Theorem inventory extracted from frozen TeX: YES
Independent MCFGv4 namespace started: YES
Legacy theorem migration: NOT STARTED
Main exact-reconstruction chain: NOT STARTED
```

The first CI target is `LeanCfgProject.MCFGv4.Summary`. This initial target checks only the independent finite-observation foundation; it must not be interpreted as verification of any later manuscript theorem yet.
