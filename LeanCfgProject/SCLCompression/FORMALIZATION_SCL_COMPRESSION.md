# #3 SCL-Compression — independent Lean verification plan

Baseline manuscript: `SCL-Compression_arXiv_v1.tex`.

Verification branch: `scl-compression-verification`.

## Isolation policy

This branch was created directly from `master`, not from either active verification branch.

The active branches are:

- `tcs-fixed-h-verification` — #1 fixed-h CFG
- `mcfg-v4-verification` — #2 MCFG v4
- `scl-compression-verification` — #3 SCL-Compression

The #3 development lives only under `LeanCfgProject/SCLCompression/` plus its branch-scoped CI workflow.  It must not modify or import files added only on the #1 or #2 verification branches.  No merge into `master` is required while the three checks are running.

## Verification target

The goal is not line-by-line formalization of the whole paper.  The primary target is the proof kernel supporting the global compression-height theorem.

Manuscript dependency spine:

1. Safety Interface Theorem (`alg:thm:safety-interface`)
2. Finite-index congruence characterization (`alg:thm:free-congruence`)
3. Free-monoid selector (`alg:lem:selector`)
4. Relational-morphism characterization (`alg:thm:relational-characterization`)
5. Compatible-tolerance arity-two saturation (`cr:thm:tolerance-saturation`)
6. Completely-regular arity-two saturation (`cr:thm:cr-saturation`)
7. `V_ab` structural dichotomy (`height:thm:vab-dichotomy`)
8. Global SCL compression-height trichotomy (`height:thm:global-trichotomy`)

Graph realization / NP-completeness is secondary and should be formalized only after the structural spine is stable.

## Phase 1 — abstract safety and relational kernel

Status: started.

Files:

- `SafetyInterface.lean`
  - abstract tuple carrier `Fin d -> alpha`
  - shared-context / equal-distribution unsafe clauses
  - guarded safety iff unsafe-coordinate separation
  - kernel-relation formulation
- `RelationalMorphisms.lean`
  - multiplicative relational morphism fibres
  - fibre disjointness
  - separation monotonicity under fibre shrinking
  - used codomain forms a submonoid

These verify logical/algebraic steps that are used verbatim later, while postponing SCL-specific infrastructure.

## Phase 2 — concrete word and tuple-context semantics

Build independent definitions for:

- words as lists over a finite alphabet
- arity-`d` tuple contexts and tuple distributions `D_L^(d)`
- shared accepting tuple context
- semantic unsafe relation `U_d(L)`
- componentwise observation by a monoid homomorphism

Then instantiate Phase 1 to obtain manuscript conditions (ii) <-> (iii) <-> (iv) of the Safety Interface Theorem.

The SCL principal-concept formulation (i) will be added only after the word-level semantics compiles cleanly; this keeps concept-lattice machinery from contaminating the basic safety proof.

## Phase 3 — syntactic profiles and relational characterization

Formalize:

- finite pointed syntactic monoid interface `(T,P)` as the minimal finite object needed by the proofs
- finite profile transport
- canonical relation induced by a compression map
- unsafe profile separation
- free-monoid selector for an arbitrary relational morphism
- containment of canonical fibres in the chosen relational fibres
- least-codomain relational characterization of `cmp_f`

Checkpoint: manuscript Theorem `alg:thm:relational-characterization` has a no-placeholder Lean proof.

## Phase 4 — completely regular arity-two saturation

This is the highest-value and highest-risk part.

Formalization order:

1. lower-component action and sandwich ideals
2. syntactic-value lifting from safe overlap
3. equalizing-context principle
4. local kernel / centrality / row-column rigidity
5. central translations and defect map
6. local faithfulness of trivial defect
7. multiplicativity of defects
8. support bookkeeping for tuple contexts
9. product compression
10. compatible-tolerance arity-two saturation
11. completely-regular arity-two saturation

No attempt should be made to hide missing semigroup structure behind axioms.  If a standard completely-regular-semigroup result is not present in Mathlib, isolate it as an explicit lemma with a provenance note and then decide whether to prove it locally.

## Phase 5 — global trichotomy

Formalize the finite-side divisor bridge and combine it with the arity-amplification side:

- every finite non-completely-regular monoid has the required obstruction divisor
- nilpotence plus noncommutativity produces the `M_ab` obstruction
- `V_ab` structural dichotomy
- global compression-height trichotomy

Target statement: finite uniform compression heights `3,4,5,...` do not occur.

## Phase 6 — optional computational tail

After the proof kernel is green:

- unsafe-pair graph classification
- compression map -> proper coloring
- proper coloring -> compression map
- exact graph realization
- NP-completeness statements

This phase is useful but is not needed to certify the central algebraic theorem.

## CI policy

The branch-specific workflow builds only `LeanCfgProject.SCLCompression.*` modules and rejects `sorry` / `admit` in this directory.  This prevents #3 failures from blocking or modifying #1/#2 verification work.

## Completion criteria

We will distinguish three levels:

- **Kernel verified**: Safety Interface + relational characterization compile without placeholders.
- **Structural core verified**: completely-regular arity-two saturation also compiles.
- **Main theorem verified**: structural dichotomy + global trichotomy compile from the formalized dependencies.

The recommended publication-grade stopping point is **Main theorem verified**; full graph/complexity formalization is optional.
