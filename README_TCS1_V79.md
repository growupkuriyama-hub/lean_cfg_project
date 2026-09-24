# TCS #1 v79 Lean formalization

This release candidate contains the Lean formalization accompanying:

**Takayuki Kuriyama, _Distributional Learning of Context-Free Languages under Fixed Finite-Monoid Typing_.**

## Manuscript baseline

- Manuscript version: **v79**
- Manuscript SHA-256: `3d54aaea1c945e4b9bbdabe92a88f229096d94c93fa3045a3bfda5dfd22426d2`
- Theorem-facing verification head: `c6fe72e31a305b159d93afd82c731c603125d907`
- Final pre-merge CI-guard head: `49556ddca69b6fb056d3d12880066d1d56315db8`
- PR #5 merge commit: `356bf51d3cded68a1a29d2957b656b25a693f7c6`

The v79 manuscript is a non-mathematical micro-revision of v78, so the verified theorem/proof/example surface is inherited unchanged.

## Main entry point

`LeanCfgProject/TCS1/All.lean`

Build with:

```bash
lake build LeanCfgProject.TCS1.All
```

The repository pins the Lean toolchain and dependencies through `lean-toolchain` and `lake-manifest.json`.

## Coverage

The formalization includes the fixed finite-monoid substitutability semantics, exact reconstruction, finite witnesses, conservative Gold learning, executable and materialized membership testing, polynomial combinatorial update bounds, fixed-window and linear-subclass results, expressiveness examples, and the manuscript-order audits for Sections 2--9 and Appendices A--C.

See:

- `FORMALIZATION_TCS1_V79.md`
- `FORMALIZATION_TCS1_V79_BOUNDARY_AUDIT.md`
- `LeanCfgProject/TCS1/V79FullManuscriptAudit.lean`

The remaining external boundary consists of cited literature/background, representation conventions, explicit open problems, and low-level runtime cost semantics outside the manuscript's abstraction level.

## CI checkpoint

Immediately before PR #5 was merged:

- full `TCS1.All` workflow run **#696**: success
- fast Delta workflow run **#365**: success
- CI guards rejecting `sorry` and project-level `axiom` declarations: success

## Archival release

The intended archival tag is:

`tcs1-v79-formalization-1.0.0`

The release is intended to be archived on Zenodo as software associated with the v79 manuscript.
