# Theorem inventory for the frozen MCFG v4 manuscript

Source: `MCFG_arXiv_v4_20260907_final_v3.tex`  
SHA-256: `9999952ce78624a92053ab0d28fc861a23d9ca30bb58c548df11add354c2d9dd`

This inventory was extracted from the frozen 2026-09-07 TeX. `PENDING` means that no current-v4 verification claim is made yet. Old `MCFG2` modules are only legacy candidates until statement/hypothesis comparison and a fresh `MCFGv4` CI proof are complete.

| TeX line | Section | Kind | Label | Manuscript title | Status | Legacy candidate / note |
|---:|---|---|---|---|---|---|
| 512 | Oriented tuple contexts | lemma | `lem:permutation-decoration` | Permutation-decoration normalization | PENDING | New v4-facing proof expected; arbitrary-rank presentation |
| 541 | Oriented tuple contexts | corollary | `cor:rank-preserving-normalization` | Rank-preserving normalization | PENDING | Depends on nondeleting normalization + previous lemma |
| 669 | Oriented tuple contexts | lemma | `lem:sector-canonicalization` | Canonicalization of orientation sectors | PENDING | Likely small fresh semantic lemma |
| 705 | Oriented tuple contexts | corollary | `cor:identity-sector-equivalence` | Identity-sector formulation | PENDING | Depends on sector canonicalization |
| 725 | Oriented tuple contexts | proposition | `prop:fanout-one-specialization` | Fan-out-one specialization | PENDING | Fresh paper-facing bridge |
| 774 | Oriented tuple contexts | proposition | `prop:h-recognizable-in-slice` | h-recognizable languages lie in the fixed-observation slice | PENDING | Semantic result; inspect legacy only for ideas |
| 803 | Oriented tuple contexts | proposition | `prop:abelian-coset-filter` | Abelian-coset filtering preserves substitutability | PENDING | Fresh semantic result |
| 863 | Oriented tuple contexts | proposition | `prop:h-refinement-monotonicity` | Monotonicity under refinement of the observation morphism | PENDING | `MCFG2/Basic.lean` has a related refinement theorem; statement must be rechecked |
| 883 | Oriented tuple contexts | lemma | `lem:shared-context` | Shared-context substitutability | PENDING | Related abstract machinery exists in `MCFG2/Basic.lean` |
| 910 | Oriented tuple contexts | proposition | `prop:copy-infinite-observation` | The copy language has no finite witnessing observation | PENDING | Fresh boundary example |
| 1089 | Output-type refinement | proposition | `prop:output-invariants` | Output-type invariants | PENDING | `MCFG2/OutputTypeRefinement.lean`, `OutputTypeLift.lean`; old early interface was terminal/binary |
| 1129 | Output-type refinement | lemma | `lem:refinement-nonpermuting` | Output typing preserves nonpermuting rules | PENDING | New arbitrary-rank paper-facing statement |
| 1154 | Output-type refinement | lemma | `lem:identity-exposing-contexts` | Identity exposures exist in the normalized proof grammar | PENDING | Legacy exposing-context/derivation-spine material may help |
| 1191 | Output-type refinement | lemma | `lem:typed-state-uniformity` | Semantic uniformity of a surviving typed state | PENDING | Likely reuse of shared-context semantic kernel after re-statement |
| 1209 | Output-type refinement | lemma | `lem:identity-orientation-propagation` | Identity orientation propagates through normalized rules | PENDING | New v4-facing orientation theorem |
| 1275 | Silent-child compression | lemma | `lem:silent-compression` | Silent-child compression preserves all typed tuple languages | PENDING | Current-v4-specific bridge; do not infer from old binary compiler |
| 1340 | Silent-child compression | lemma | `lem:cs-positive` | The characteristic sample is finite and positive | PENDING | Legacy characteristic-sample files are candidates only |
| 1411 | Sample-bounded rank | lemma | `lem:sample-bounded-rank` | Sample-bounded witness rank | PENDING | Current-v4 arbitrary-rank core |
| 1436 | Sample-bounded rank | lemma | `lem:general-witness-enumeration` | Enumeration of arbitrary-rank witnesses | PENDING | Current-v4 arbitrary-rank core |
| 1476 | Sample-bounded rank | lemma | `lem:exposed-rule-enumerated` | Identity-exposed compressed rules occur in the enumeration | PENDING | Current-v4 arbitrary-rank core |
| 1540 | Sample-bounded rank | lemma | `lem:learner-effective` | Finiteness and effectiveness of the standard hypotheses | PENDING | Legacy finite-enumerator work may supply sublemmas |
| 1611 | Sample-bounded rank | proposition | `prop:cs-cardinality` | Cardinality of the presentation-relative characteristic sample | PENDING | Quantitative paper-facing theorem |
| 1663 | Soundness | lemma | `lem:filling-identity` | Induced child context and its orientation | PENDING | `MCFG2/FillingIdentity.lean` is a legacy candidate |
| 1691 | Soundness | lemma | `lem:witnessed-composition` | Witnessed oriented composition preserves equivalence | PENDING | `MCFG2/WitnessedComposition.lean` is a legacy candidate |
| 1725 | Soundness | proposition | `prop:learner-soundness` | Soundness of every capped hypothesis | PENDING | Legacy `LearnerSoundnessCore` / `LearnerDerivationSoundness` candidates |
| 1763 | Completeness | proposition | `prop:completeness` | Completeness for a fixed normalized presentation | PENDING | Legacy completeness chain is only a candidate |
| 1845 | Exact reconstruction | theorem | `thm:exact-reconstruction` | Exact reconstruction for fixed-observation MCFGs | PENDING | Main V4-C target; no old result counts automatically |
| 1886 | Exact reconstruction | corollary | `cor:finite-telltales` | Finite tell-tales inside a fixed observation slice | PENDING | Derive only after exact reconstruction is current-v4 verified |
| 1916 | Exact reconstruction | corollary | `cor:semantic-identification` | TxtBc identification from positive data | PENDING | Derive only after reconstruction/current learner interface |
| 1933 | Exact reconstruction | corollary | `cor:gold-explanatory` | TxtEx identification by a conservative wrapper | PENDING | Current-v4 wrapper theorem |
| 1987 | Fixed-rank construction | theorem | `thm:poly` | Slicewise-polynomial construction under a fixed rule-rank cap | PENDING | Old quantitative/enumerator assets may help; re-prove current bound |
| 2023 | Fixed-rank construction | corollary | `cor:fixed-rank-polytime` | Polynomial-time identification on a fixed-rank slice | PENDING | Depends on current-v4 construction theorem |
| 2109 | Boundary comparison | lemma | `lem:boundary-congruence` | Boundary equivalence is a finite monoid congruence | PENDING | Fresh finite-monoid boundary module likely preferable |
| 2124 | Boundary comparison | proposition | `prop:kl-boundary-comparison` | Fan-out-one relation to (k,l)-substitutability | PENDING | Fresh comparison bridge |
| 2164 | Boundary comparison | proposition | `prop:yoshinaka-inclusion` | Yoshinaka's class embeds into a one-sided boundary slice | PENDING | Fresh comparison theorem |
| 2218 | Strictness | lemma | `lem:block-order-boundary-control` | Boundary types control the block-order envelope | PENDING | Fresh combinatorial lemma |
| 2238 | Strictness | theorem | `thm:canonical-boundary-strictness` | Strictness of the symmetric boundary slice | PENDING | Depends on explicit witness construction |
| 2318 | Strictness | corollary | `cor:yoshinaka-fixed-rank-poly-strict` | Polynomial-time learning on a strict fixed-rank extension | PENDING | Derived comparison + complexity result |
| 2387 | Finite-kernel comparison | proposition | `prop:observation-implies-fkp` | Fixed observation induces bounded common-context kernels | PENDING | Fresh semantic implication |
| 2451 | Bounded advice | proposition | `prop:bounded-union-identifiable` | Universal bounded observation | PENDING | Class-level advice theorem |
| 2503 | Locking lower bound | theorem | `thm:bounded-latent-locking-lower-bound` | Learner-uniform 2^{Omega(sqrt(k))} locking lower bound | PENDING | New negative/quantitative module |
| 2578 | Unbounded advice | corollary | `thm:no-advice-nonidentifiability` | Gold-superfinite obstruction for unbounded latent observation | PENDING | Final negative boundary result |

## Counts

- theorem-like manuscript items (`lemma`, `proposition`, `theorem`, `corollary`): **42**
- current-v4 items marked `VERIFIED`: **0** at initialization
- legacy items counted as current-v4 verification: **0**

The first milestone is not to maximize this count quickly. It is to establish a trustworthy arbitrary-rank semantic foundation and then promote items one by one with exact source correspondence.
