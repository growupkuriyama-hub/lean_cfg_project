# TCS v49 Lean 4 verification matrix

Authoritative manuscript baseline: `TCS-D-26-00494_major_revision_working_v49(1).tex`.

Lean branch: `tcs-v49-verification`.

Last fully green dedicated **linear/source-learning** CI snapshot used for this audit:

- Lean commit `2fef0a9c9bbe1ecc4282895217b1b4280f3479c3`
- workflow run `34929491945`
- all dedicated v49 linear-normalization/source-learning steps succeeded, including retained-state finiteness, source-level characteristic-data polynomial bounds, the source-level exact-reconstruction/Gold-learning package, the complete Appendix A normalization stack, and the placeholder scan (`sorry|admit` absent from that layer)

The broad `verify-tcs-v49` workflow is tracked separately.  This matrix does not infer that every manuscript statement has been formalized merely from a green workflow; it records theorem-by-theorem coverage.

## Status legend

- **✅ Direct** — the manuscript claim is represented essentially directly by a checked Lean theorem (possibly through a thin v49 wrapper around an older stable core).
- **🟨 Partial/core** — a substantial mathematical core is checked, but some theorem-level packaging, external characterization, or executable complexity semantics is still missing.
- **⬜ Open** — no manuscript-faithful Lean formalization has yet been identified in the current v49 branch.

## Theorem-by-theorem matrix

| Manuscript item | Manuscript claim / role | Lean correspondence | Status | Remaining gap / caution |
|---|---|---|---|---|
| `def:hsubst` | Fixed-`h` substitutability on **nonempty** internal fragments; `λ` handled separately at the start symbol | `Language.lean`: `Internal`, `InDistribution`, `SameDistribution`, `ShareContext`, `HSubstitutable` | ✅ Direct | This is the semantic definition used throughout the checked development. |
| `prop:regular-auto` | Regular iff recognized by a finite monoid; every `h^{-1}(Acc)` is `~_h`-substitutable; hence every regular language is in `RS` | No v49-facing theorem found | ⬜ Open | Formalize finite-monoid recognition / regular-language equivalence and the immediate substitutability argument. |
| `prop:ce-special` | Every Clark--Eyraud substitutable language belongs to `RS` | No v49-facing theorem found | ⬜ Open | Requires a formal definition of the Clark--Eyraud class and its embedding into a finite-monoid slice. |
| `prop:yl-special` | For fixed `k,l`, a finite monoid `h_{k,l}` makes every `(k,l)`-substitutable language `~_{h_{k,l}}`-substitutable | No v49-facing theorem found | ⬜ Open | Requires the `(k,l)` equivalence/typing construction and proof that it is a finite-monoid homomorphism. |
| `thm:main` | Existence of set-driven `B_h` and conservative `A_h`: sample consistency + polynomial build; finite characteristic reconstruction sample; Gold identification of every nonempty target + polynomial updates | `MainTheoremCoreV49.lean`, `SequentialOneChangeV49.lean`, `WitnessSetV49.lean`, `CompletenessV49.lean`; v49 wrappers in `ManuscriptSyncV49.lean` | 🟨 Partial/core | Semantic learning/reconstruction content is strongly checked. Complexity is an arithmetic degree-five envelope/update dichotomy, **not** a machine-level parser/string-table runtime verification. The full class-level statement is not packaged as one theorem over `C_h^cf`. |
| `lem:sample-consistency` | `K ⊆ L(B_h(K))` | `lemma_sample_consistency_v49` | ✅ Direct | Thin manuscript-facing wrapper over the checked reconstruction kernel. |
| `thm:soundness` | If `K⊆L` and `L` is `~_h`-substitutable, then `L(Ĝ(K))⊆L` | `theorem_soundness_v49` | ✅ Direct | Matches the manuscript soundness direction. |
| `prop:typed-core` | Yield-typed refinement preserves the target language and every typed non-start derivation has the declared `h`-yield | `YieldTypedCore.lean`, `YieldTypedTrimmed.lean`; wrapper `proposition_typed_core_v49` | ✅ Direct | Uses yield type only; no obsolete outer-context type is present. |
| `thm:complete` | For reduced SSBNF nonempty target, `W(G~)⊆K` implies `L⊆L(Ĝ(K))` | `CompletenessV49.lean`: `theorem_complete_v49` | ✅ Direct | This is the finite-witness completeness kernel; it intentionally does not need soundness assumptions. |
| `thm:reconstruction-fixed-h` | If `W(G~)⊆K⊆L`, then `L(B_h(K))=L` | `theorem_reconstruction_fixed_h_v49` | ✅ Direct | Combines completeness and soundness in manuscript-facing form. |
| `cor:ilt` | Gold identification for nonempty fixed-`h` targets; after witness coverage, at most one further hypothesis change | `corollary_ilt_v49`, `corollary_ilt_one_change_v49`; core in `SequentialOneChangeV49.lean` | ✅ Direct | The strengthened “at most one further change” statement is explicitly checked. |
| `thm:poly-build` | For fixed efficiently computable `h`, `B_h(K)` is constructible in polynomial time in `||K||` | `MainTheoremCoreV49.lean`: fifth-degree arithmetic build envelope | 🟨 Partial/core | Checks the combinatorial/arithmetic `O(n^5)` envelope. It does **not** formalize a concrete RAM/Turing-machine implementation, substring table, parser, allocation, or output-cost model. |
| `cor:poly-update` | Each conservative update is polynomial in accumulated encoded data | `MainTheoremCoreV49.lean`: polynomial update dichotomy, together with conservative learner equations | 🟨 Partial/core | Same machine-cost caveat as `thm:poly-build`; semantic keep/rebuild behavior is checked. |
| `prop:linear-normal` | Polynomial conversion of every finite linear CFG to an equivalent reduced linear-spine SSBNF of polynomial size | `LinearPreprocessing*V49.lean`, `LinearNormalizationSSBNF*V49.lean`, `Untyped*V49.lean`, `LinearNormalizationTrimmedV49.lean`, `LinearNormalizationEndToEndV49.lean`, `LinearNormalizationSourceSizeV49.lean`, `LinearNormalizationManuscriptV49.lean` | 🟨 Partial/core | **Mathematical normalization gap is now closed:** source preprocessing, explicit reification, exact language preservation, trimming/reducedness, single-spine shape, and polynomial output-size budgets are checked from arbitrary finite source linear CFGs. Remaining caveat is only the manuscript phrase “computed in polynomial time”: no machine-level cost model for the preprocessing/construction has been formalized. |
| `lem:linear-short` | In the normalized typed grammar, `|ω(X)|≤n_t`, `|u_X|+|v_X|≤2n_t`, hence every witness has `O(n_t)` length | `LinearShortWitness.lean`, `LinearSpine*V47.lean`, `LinearNormalizationTypedShapeV49.lean`, `LinearNormalizationActiveStatesV49.lean` | ✅ Direct | The former external shape assumption is now discharged by the explicit source normalization via `sourceNormalizedTypedLinearSpineShapeV49`; retained-state finiteness is constructed without assuming finite ambient `LinearNormNT`. |
| `thm:linear-poly` | Polynomial-size characteristic reconstruction data for linear target representations; sample consistency; Gold ID; polynomial batch/update bounds | `LinearCharacteristicRetainedV49.lean`, `LinearCharacteristicSourceV49.lean`, `LinearLearningSourceV49.lean`; older stable cores `LinearCharacteristic*V47.lean`, `LinearBatchTheoremV47.lean`, `LinearManuscriptTheoremV47.lean` | 🟨 Partial/core | The source-level semantic theorem is now checked from arbitrary finite source linear CFGs: exact finite characteristic set, source-polynomial characteristic-data norm, sample consistency, exact reconstruction, and conservative Gold identification. What remains partial is the **machine-level** interpretation of polynomial batch construction/update time; the current formalization proves arithmetic/combinatorial size envelopes rather than an executable cost model. |
| `prop:linear-separator-example` | `L_{±,e}` is linear, nonregular, fixed-`h` substitutable, but neither Clark--Eyraud nor any fixed `(k,l)`-substitutable | No concrete `L_{±,e}` formalization found | ⬜ Open | High-value example proof: define the language/homomorphism and formalize all four properties. |
| `prop:nonlinear-rs-example` | Concrete `L*` is CFL, nonregular, nonlinear, and fixed-`h*` substitutable | No concrete target formalization found | ⬜ Open | Would verify the claimed genuinely nonlinear reach of the class. |
| `prop:ctr-regular` | Every capped counter language `CTR_ρ` is regular, hence in `RS` | No concrete `CTR_ρ` formalization found | ⬜ Open | Can reuse `prop:regular-auto` once that theorem is available, after formalizing the capped automaton/language. |
| `thm:ctr-non-kl` | For `ρ≥2`, `CTR_ρ` is not `(k,l)`-substitutable for any `k,l` | No concrete proof found | ⬜ Open | Depends on formal `(k,l)` substitutability and the manuscript separator argument. |
| `lem:finite-monoid-obstruction` | Infinite family of nonempty fragments with intersecting but unequal distributions excludes membership in `RS` | `BoundaryObstructionsV47.lean`; wrapper `lemma_finite_monoid_obstruction_v49` | ✅ Direct | The finite-pigeonhole obstruction is checked and reused by the Dyck proof. |
| uncapped counter boundary argument | The uncapped counter CFL is outside `RS` by an infinite obstruction family | General obstruction lemma exists; no concrete uncapped-counter instantiation found | ⬜ Open | Define the uncapped counter language/family and instantiate the checked obstruction theorem. |
| `cor:dyck-not-rs` | One-bracket Dyck language `D_1` is not in `RS({a,b})` | `DyckObstructionV47.lean`; wrapper `corollary_dyck_not_rs_v49` | ✅ Direct | Uses the operational deterministic-depth presentation and manuscript family `b^i a^i`. |
| `lem:rs-fixed-quotient` | Fixed-word right quotient preserves `~_h` substitutability | `BoundaryObstructionsV47.lean`; wrapper `lemma_rs_fixed_quotient_v49` | ✅ Direct | Direct language-theoretic closure lemma. |
| Łukasiewicz obstruction following quotient lemma | `L_Luk` is outside `RS`, using `L_Luk = D_1 b` and quotient by `b` | `LukasiewiczObstructionV47.lean`; wrapper `corollary_lukasiewicz_not_rs_v49` | 🟨 Partial/core | Quotient/coding argument is checked for the suffix-extension language. Missing: prove that manuscript grammar `S→aSS | b` generates exactly `D_1 b`. |
| `prop:clark-congruential-comparison` — inclusion | `RS(Γ)∩CFL ⊆ CONG(Γ)` | `ClarkCongruentialCoreV49.lean`, `ClarkCongruentialInitialSetV49.lean`; wrapper `proposition_clark_congruential_inclusion_core_v49` | 🟨 Partial/core | Strong semantic core is checked: each retained typed state language lies in one syntactic class; the typed initial family is finite; optional epsilon component is homogeneous; their union is exactly the target. Missing: a general formal `CONG(Γ)` CFG-family object and explicit congruential grammar witness. |
| `prop:clark-congruential-comparison` — properness | Proper for `Γ={a,b}` via Dyck | `ClarkDyckStrictnessV49.lean`; wrapper `proposition_clark_congruential_strictness_core_v49` plus `corollary_dyck_not_rs_v49` | 🟨 Partial/core | Balanced-factor replacement / syntactic homogeneity and `D_1∉RS` are checked. Missing: grammar-object proof that `S→aSbS | λ` generates operational `Dyck1`, and packaging into the abstract `CONG` family. |
| Appendix A | Detailed proof of linear-spine normalization | Full `LinearPreprocessing*V49` + `LinearNormalization*V49` + `Untyped*V49` stack | 🟨 Partial/core | Semantic/structural Appendix A is now end-to-end: preprocessing, prepared enumeration, fresh-state SSBNF reification, exact semantics, single-spine shape, trimming/reducedness, source-size bounds. Only an executable polynomial-time cost semantics remains outside the formalization. |
| Appendix B | Detailed short canonical-witness proof | `LinearShortWitness.lean`, `LinearSpineContextCoreV47.lean`, `LinearSpineWrapperContextV47.lean`, `LinearWitnessEndToEndV47.lean`, source bridge in `LinearNormalizationTypedShapeV49.lean` | ✅ Direct | The source normalization now automatically supplies the needed typed single-spine certificate and finite retained state space. |

## Current coverage assessment

The proof-critical learning spine

`fixed-h substitutability → sample consistency/soundness → yield-only typed refinement → finite witness completeness → exact reconstruction → conservative Gold identification (including one-change)`

is checked end-to-end.

The **linear subclass is now also connected end-to-end at the mathematical level from an arbitrary finite source linear CFG**:

`source linear CFG → epsilon/unit preprocessing → prepared finite enumeration → explicit single-spine SSBNF reification → exact language preservation → trimming/reducedness → yield-typed single-spine certificate → finite retained-state space → short canonical witnesses → source-polynomial characteristic-data norm → exact reconstruction → conservative Gold identification`.

Thus the previous structural hypothesis gap under `thm:linear-poly` has been removed.  The remaining “partial” label on `prop:linear-normal` / `thm:linear-poly` / Appendix A is now specifically a **complexity-semantics caveat**: the manuscript says polynomial-time construction/update, whereas Lean currently checks explicit finite constructions and polynomial arithmetic/output-size envelopes, not a RAM/Turing-machine execution-cost theorem.

The largest remaining mathematical packaging gap is now the Clark congruential comparison, followed by the Section 3 class-bridge propositions and the concrete separator/boundary examples.

## Recommended next order

1. **Full `CONG(Γ)` packaging** — introduce a finite congruential-CFG structure/family, turn the existing finite typed-initial-set construction into an actual membership theorem, and prove that `S→aSbS | λ` generates operational `Dyck1`. This closes both halves of `prop:clark-congruential-comparison` at theorem-family level.
2. **Section 3 bridge propositions** — `prop:regular-auto`, then `prop:ce-special`, then `prop:yl-special`.
3. **Concrete examples/boundaries** — `L_{±,e}`, nonlinear `L*`, capped `CTR_ρ`, uncapped counter obstruction, then the `(k,l)` separation.
4. **Łukasiewicz grammar identity** — prove `L(S→aSS|b)=D_1 b`; the quotient obstruction itself is already checked.
5. **Complexity semantics, optional final layer** — define an executable reconstruction/normalization implementation and cost model only if machine-level polynomial-time certification is desired.

## Interpretation for the manuscript

A green CI does **not** mean every statement in v49 has been formalized. It means every theorem represented by the checked package compiles without proof placeholders. The matrix above is the audit boundary: it records what the badge certifies directly, what is mathematical-core-plus-complexity-caveat, and what still lies outside the formalization.
