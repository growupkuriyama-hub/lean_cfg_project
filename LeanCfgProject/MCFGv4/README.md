# MCFGv4 Lean verification

This directory is a fresh paper-facing Lean 4 development for the frozen 2026-09-07 manuscript baseline recorded in `FORMALIZATION_MCFG_V4.md`.

## Non-interference rule

- Do not import `LeanCfgProject.FixedHCFG.*`.
- Do not modify `LeanCfgProject/FixedHCFG/` from this branch.
- Do not modify `LeanCfgProject/MCFG2/` from this branch.
- Do not treat an old `MCFG2` proof as current-v4 verification merely because it compiles.
- Legacy modules may be consulted and selectively re-proved only after their statements and assumptions have been compared with the frozen v4 manuscript.

The new code uses namespace `MCFGv4` so that old experimental declarations in namespace `MCFG` cannot silently determine the new paper-facing interface.

## Manuscript baseline

```text
MCFG_arXiv_v4_20260907_final_v3.tex
SHA-256: 9999952ce78624a92053ab0d28fc861a23d9ca30bb58c548df11add354c2d9dd
```

## Development order

1. `Basic.lean`: words, tuples, and explicit finite-monoid observation.
2. Standard arbitrary-rank MCFG presentation and rule-template evaluation.
3. Oriented tuple contexts and semantic slices.
4. Normalization/orientation results from Section 2.
5. Output-type refinement and silent-child compression.
6. Sample-bounded arbitrary-rank witness enumeration.
7. Soundness, completeness, exact reconstruction, and identification.
8. Fixed-rank complexity.
9. Comparison/boundary results.
10. Bounded/unbounded observation advice results.

`THEOREM_INVENTORY.md` is the source-to-Lean correspondence table. A theorem becomes `VERIFIED` there only after its paper-facing target passes CI without placeholders.
