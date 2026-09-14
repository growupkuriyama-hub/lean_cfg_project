# TCS v49 Lean 4 verification matrix

Authoritative manuscript baseline: `TCS-D-26-00494_major_revision_working_v49(1).tex`.

Lean branch: `tcs-v49-verification`.

Last fully green dedicated CI snapshot used for this audit:

- commit `d745bfd57afe25ee455f7414d47786bc704b5088`
- workflow run `34809946915`
- all v49 verification steps succeeded, including the placeholder scan (`sorry|admit` absent from the current v49 synchronization sources)

This document deliberately distinguishes a theorem whose mathematical content is directly formalized from a theorem for which only the semantic core, an arithmetic complexity envelope, or a representation-dependent subclaim has been formalized.

## Status legend

- **✅ Direct** — the manuscript claim is represented essentially directly by a checked Lean theorem (possibly through a thin v49 wrapper around an older stable core).
- **🟨 Partial/core** — a substantial mathematical core is checked, but some theorem-level packaging, representation theorem, external characterization, or executable complexity semantics is still missing.
- **⬜ Open** — no manuscript-faithful Lean formalization has yet been identified in the current v49 branch.

## Theorem-by-theorem matrix

| Manuscript item | Manuscript claim / role | Lean correspondence | Status | Remaining gap / caution |
|---|---|---|---|---|
| `def:hsubst` | Fixed-`h` substitutability on **nonempty** internal fragments; `λ` handled separately at the start symbol | `Language.lean`: `Internal`, `InDistribution`, `SameDistribution`, `ShareContext`, `HSubstitutable` | ✅ Direct | This is the semantic definition used throughout the checked development. |
| `prop:regular-auto` | Regular iff recognized by a finite monoid; every `h^{-1}(Acc)` is `~_h`-substitutable; hence every regular language is in `RS` | No v49-facing theorem found | ⬜ Open | Formalize finite-monoid recognition / syntactic-recognition direction and the immediate substitutability argument. |
| `prop:ce-special` | Every Clark--Eyraud substitutable language belongs to `RS` | No v49-facing theorem found | ⬜ Open | Requires a formal definition of the Clark--Eyraud class and its embedding into a finite-monoid slice. |
| `prop:yl-special` | For fixed `k,l`, a finite monoid `h_{k,l}` makes every `(k,l)`-substitutable language `~_{h_{k,l}}`-substitutable | No v49-facing theorem found | ⬜ Open | Requires the `(k,l)` equivalence/typing construction and proof that it is a finite-monoid homomorphism. |
| `thm:main` | Existence of set-driven `B_h` and conservative `A_h`: sample consistency + polynomial build; finite characteristic reconstruction sample; Gold identification of every nonempty target + polynomial updates | `MainTheoremCoreV49.lean`, `SequentialOneChangeV49.lean`, `WitnessSetV49.lean`, `CompletenessV49.lean`; v49 wrappers in `ManuscriptSyncV49.lean` | 🟨 Partial/core | Semantic learning/reconstruction content is strongly checked. Complexity is an arithmetic degree-five envelope/update dichotomy, **not** a machine-level parser/string-table runtime verification. The paper-level theorem is not packaged as one single Lean theorem quantifying over the full class notation `C_h^cf`. |
| `lem:sample-consistency` | `K ⊆ L(B_h(K))` | `lemma_sample_consistency_v49` | ✅ Direct | Thin manuscript-facing wrapper over the checked reconstruction kernel. |
| `thm:soundness` | If `K⊆L` and `L` is `~_h`-substitutable, then `L(Ĝ(K))⊆L` | `theorem_soundness_v49` | ✅ Direct | Matches the manuscript soundness direction. |
| `prop:typed-core` | Yield-typed refinement preserves the target language and every typed non-start derivation has the declared `h`-yield | `YieldTypedCore.lean`, `YieldTypedTrimmed.lean`; wrapper `proposition_typed_core_v49` | ✅ Direct | Uses yield type only; no obsolete outer-context type is present. |
| `thm:complete` | For reduced SSBNF nonempty target, `W(G~)⊆K` implies `L⊆L(Ĝ(K))` | `CompletenessV49.lean`: `theorem_complete_v49` | ✅ Direct | This is the finite-witness completeness kernel; it intentionally does not need soundness assumptions. |
| `thm:reconstruction-fixed-h` | If `W(G~)⊆K⊆L`, then `L(B_h(K))=L` | `theorem_reconstruction_fixed_h_v49` | ✅ Direct | Combines completeness and soundness in the manuscript-facing form. |
| `cor:ilt` | Gold identification for nonempty fixed-`h` targets; after witness coverage, at most one further hypothesis change | `corollary_ilt_v49`, `corollary_ilt_one_change_v49`; core in `SequentialOneChangeV49.lean` | ✅ Direct | The strengthened “at most one further change” statement is explicitly checked. |
| `thm:poly-build` | For fixed efficiently computable `h`, `B_h(K)` is constructible in polynomial time in `||K||` | `MainTheoremCoreV49.lean`: fifth-degree arithmetic build envelope | 🟨 Partial/core | Checks the combinatorial/arithmetic `O(n^5)` envelope. It does **not** formalize a concrete RAM/Turing-machine implementation, substring table, parser, allocation, or output-cost model. |
| `cor:poly-update` | Each conservative update is polynomial in accumulated encoded data | `MainTheoremCoreV49.lean`: polynomial update dichotomy, together with conservative learner equations | 🟨 Partial/core | Same machine-cost caveat as `thm:poly-build`; the semantic keep/rebuild dichotomy is checked. |
| `prop:linear-normal` | Polynomial conversion of every linear CFG to equivalent reduced linear-spine SSBNF of polynomial size | Linear files consume `TypedLinearSpineShape` / certified spine structure; no full conversion theorem found | 🟨 Partial/core | **Largest structural gap in Section 7.** The target normal-form consumer and its consequences are formalized, but the actual arbitrary-linear-CFG → normalized-grammar construction, language preservation, reduction, and polynomial size/time proof are not. |
| `lem:linear-short` | In the normalized typed grammar, `|ω(X)|≤n_t`, `|u_X|+|v_X|≤2n_t`, hence every witness has `O(n_t)` length | `LinearShortWitness.lean`, `LinearSpine*V47.lean`, `LinearWitnessEndToEndV47.lean` | ✅ Direct (conditional on spine certificate) | The short-witness mathematics is checked for the certified normalized shape. Its use for *arbitrary* linear CFGs still depends on the missing normalization theorem. |
| `thm:linear-poly` | Polynomial-size characteristic reconstruction data for linear target representations; sample consistency; polynomial batch build; Gold ID with polynomial updates | `LinearCharacteristicSizeV47.lean`, `LinearBatchTheoremV47.lean`, `LinearManuscriptTheoremV47.lean`; wrapper `theorem_linear_poly_v49` | 🟨 Partial/core | The full package is checked **under the linear-spine shape certificate**. To obtain the exact manuscript statement from arbitrary linear target representations, `prop:linear-normal` must be formalized. Complexity retains the arithmetic-vs-machine caveat. |
| `prop:linear-separator-example` | `L_{±,e}` is linear, nonregular, fixed-`h` substitutable, but neither Clark--Eyraud nor any fixed `(k,l)`-substitutable | No concrete `L_{±,e}` formalization found | ⬜ Open | High-value example proof: define the language/homomorphism and formalize all four properties. |
| `prop:nonlinear-rs-example` | Concrete `L*` is CFL, nonregular, nonlinear, and fixed-`h*` substitutable | No concrete target formalization found | ⬜ Open | Would verify the claimed genuinely nonlinear reach of the class. |
| `prop:ctr-regular` | Every capped counter language `CTR_ρ` is regular, hence in `RS` | No concrete `CTR_ρ` formalization found | ⬜ Open | Can reuse `prop:regular-auto` once that theorem is available, after formalizing the capped automaton/language. |
| `thm:ctr-non-kl` | For `ρ≥2`, `CTR_ρ` is not `(k,l)`-substitutable for any `k,l` | No concrete proof found | ⬜ Open | Depends on formal `(k,l)` substitutability and the manuscript separator argument. |
| `lem:finite-monoid-obstruction` | Infinite family of nonempty fragments with intersecting but unequal distributions excludes membership in `RS` | `BoundaryObstructionsV47.lean`; wrapper `lemma_finite_monoid_obstruction_v49` | ✅ Direct | The finite-pigeonhole obstruction is checked and reused by the Dyck proof. |
| uncapped counter boundary argument | The uncapped counter CFL is outside `RS` by an infinite obstruction family | General obstruction lemma exists; no concrete uncapped-counter instantiation found | ⬜ Open | Define the uncapped counter language/family and instantiate the already checked obstruction theorem. |
| `cor:dyck-not-rs` | One-bracket Dyck language `D_1` is not in `RS({a,b})` | `DyckObstructionV47.lean`; wrapper `corollary_dyck_not_rs_v49` | ✅ Direct | Uses an operational deterministic-depth presentation and the manuscript family `b^i a^i`. |
| `lem:rs-fixed-quotient` | Fixed-word right quotient preserves `~_h` substitutability | `BoundaryObstructionsV47.lean`; wrapper `lemma_rs_fixed_quotient_v49` | ✅ Direct | Direct language-theoretic closure lemma. |
| Łukasiewicz obstruction following quotient lemma | `L_Luk` is outside `RS`, using `L_Luk = D_1 b` and quotient by `b` | `LukasiewiczObstructionV47.lean`; wrapper `corollary_lukasiewicz_not_rs_v49` | 🟨 Partial/core | The quotient/coding argument is checked for the suffix-extension language. Missing: prove that the manuscript grammar `S→aSS | b` generates exactly that coded language `D_1 b`. |
| `prop:clark-congruential-comparison` — inclusion | `RS(Γ)∩CFL ⊆ CONG(Γ)` | `ClarkCongruentialCoreV49.lean`, `ClarkCongruentialInitialSetV49.lean`; wrapper `proposition_clark_congruential_inclusion_core_v49` | 🟨 Partial/core | Strong semantic core is checked: same typed state ⇒ one syntactic class; finite typed initial set; optional epsilon component; exact target union. Missing: a general Lean definition of Clark's `CONG(Γ)` as a CFG family and an explicit constructed congruential grammar object witnessing class membership. |
| `prop:clark-congruential-comparison` — properness | Proper for `Γ={a,b}` via Dyck | `ClarkDyckStrictnessV49.lean`; wrapper `proposition_clark_congruential_strictness_core_v49` plus `corollary_dyck_not_rs_v49` | 🟨 Partial/core | Balanced-factor replacement / syntactic homogeneity and `D_1∉RS` are checked. Missing: formal grammar-object proof that `S→aSbS | λ` generates the operational `Dyck1`, and packaging into the abstract `CONG` family. |
| Appendix A | Detailed proof of linear-spine normalization | No full transformation theorem | 🟨 Partial/core | Same gap as `prop:linear-normal`: downstream certified-spine theory exists, but normalization itself is not yet checked. |
| Appendix B | Detailed short canonical-witness proof | `LinearShortWitness.lean`, `LinearSpineContextCoreV47.lean`, `LinearSpineWrapperContextV47.lean`, `LinearWitnessEndToEndV47.lean` | ✅ Direct (conditional on spine certificate) | Core short-witness proof is checked; dependence on Appendix A remains for arbitrary linear input grammars. |

## Current coverage assessment

The proof-critical learning spine is already in unusually strong shape:

`fixed-h substitutability → sample consistency/soundness → yield-only typed refinement → finite witness completeness → exact reconstruction → conservative Gold identification (including the one-change refinement)`

is checked end-to-end.  The finite-monoid obstruction, Dyck non-membership, fixed-word quotient, and the substantive semantic core of the new Clark congruential comparison are also checked.  The linear short-witness / polynomial characteristic-data package is checked once the linear-spine normal-form certificate is supplied.

The remaining gaps are concentrated less in the central learning proof than in **bridge theorems and examples**: normalizing an arbitrary linear CFG, packaging the Clark result into a general `CONG` grammar family, formalizing the comparison classes used in Section 3, and instantiating the concrete Section 7/8 separator languages.

## Recommended next order

1. **`prop:linear-normal` / Appendix A** — formalize the actual polynomial normalization transformation.  This removes the most important hypothesis gap under `thm:linear-poly` and Appendix B.
2. **Full `CONG(Γ)` packaging** — introduce a minimal congruential-CFG structure/family, turn `clark_congruential_inclusion_package_v49` into an actual membership theorem, and prove that `S→aSbS | λ` generates the operational `Dyck1`.  This closes `prop:clark-congruential-comparison` at theorem-family level.
3. **Section 3 bridge propositions** — `prop:regular-auto`, then `prop:ce-special`, then `prop:yl-special`.  These make the class-comparison claims independently machine checked and will support later examples such as `CTR_ρ`.
4. **Concrete examples/boundaries** — `L_{±,e}`, the nonlinear `L*`, capped `CTR_ρ`, uncapped counter obstruction, then the `(k,l)` non-membership proof.
5. **Łukasiewicz grammar identity** — prove `L(S→aSS|b)=D_1 b`; the quotient obstruction itself is already done.
6. **Complexity semantics, optional final layer** — only if desired, define an executable reconstruction implementation/cost model to upgrade the current arithmetic `O(n^5)` envelope to a machine-level polynomial-time theorem.  This is useful for maximal formal completeness but is not the highest mathematical-risk item.

## Interpretation for the manuscript

A green CI does **not** mean every statement in v49 has been formalized.  It means every theorem currently represented in the v49 Lean synchronization package checks without proof placeholders.  The matrix above is therefore the intended audit boundary: it records what the green badge certifies, what it certifies only conditionally, and what remains outside the formalization.
