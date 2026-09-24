import LeanCfgProject.TCS1.V79TheoremSurfaceAudit

/-!
# TCS #1 v79: manuscript-label claim audit

This file is a one-to-one compile-time crosswalk from every numbered
theorem/lemma/proposition/corollary in manuscript Sections 3--9 to the Lean
declarations that discharge its mathematical content.

The existing `V79TheoremSurfaceAudit` is organized by formal subsystem.
This file is organized instead in manuscript order, so that a final paper
audit can be performed label-by-label.

Some manuscript statements bundle several logically distinct claims.  In
those cases all corresponding Lean declarations are checked together.  For
class-level prose such as KL ⊊ RS, the formal development checks the inclusion
mechanism and an explicit separating witness rather than introducing a
separate Lean definition of the class union.
-/

namespace LeanCfgProject
namespace TCS1

-- ---------------------------------------------------------------------------
-- Section 3: Fixed Recognizable Substitutability
-- ---------------------------------------------------------------------------

-- Proposition 3.1 / prop:regular-auto.
#check regular_auto_proposition_package

-- Proposition 3.2 / prop:ce-special.
#check clarkEyraud_special_case

-- Proposition 3.3 / prop:yl-special.
#check fixedWindowSubstitutable_iff_fixedHSubstitutable

-- Theorem 3.4 / thm:main.
-- Main fixed-h learning statement, polynomial update, fixed-window data,
-- and linear-target data are packaged separately and checked together.
#check indexedFixedH_learning_materialized_core
#check corollary_poly_update_materialized
#check indexedClassicalFixedWindowSection7_package
#check indexedLinear_characteristic_package

-- ---------------------------------------------------------------------------
-- Section 4: Reconstruction Operator and Sequential Learner
-- ---------------------------------------------------------------------------

-- Lemma 4.1 / lem:sample-consistency.
#check sample_consistency

-- Theorem 4.2 / thm:soundness.
#check batchLanguage_sound

-- ---------------------------------------------------------------------------
-- Section 5: Completeness via Yield-Typed Refinement and Finite Witnesses
-- ---------------------------------------------------------------------------

-- Proposition 5.1 / prop:typed-core:
-- exact language preservation plus the typed-yield invariant.
#check concreteTypedActive_language_eq_untyped
#check typedDerives_yield_type

-- Theorem 5.2 / thm:complete.
#check canonicalWitnessWords_completeness

-- Theorem 5.3 / thm:reconstruction-fixed-h.
#check exact_reconstruction_of_qualitative_reducedness

-- Corollary 5.4 / cor:ilt.
#check indexedFixedH_concreteGold_identification_nonempty
#check materializedConservative_gold_identification_explicit

-- ---------------------------------------------------------------------------
-- Section 6: Complexity of the Reconstruction Step
-- ---------------------------------------------------------------------------

-- Theorem 6.1 / thm:poly-build.
-- Quartic rule-candidate space, quadratic cache, and degree-five explicit
-- output/scan envelopes are the arithmetic content of the paper proof.
#check reconstructionFactorSlotCount_le_sq
#check reconstructionSplitSlotCount_le_cube
#check reconstructionFactorPairCount_le_fourth
#check reconstructionRuleCandidateSpace_card_le_fourth
#check reconstructionOutputEncodingEnvelope_le_degreeFive
#check concreteAccumulated_directCandidateScan_le_prefix_degreeFive

-- Corollary 6.2 / cor:poly-update.
-- This is the strongest materialized version: finite table construction,
-- unit closure, CYK membership, and a possible rebuild are all included.
#check reconstructionProductionTableScanEnvelope_polynomial_form
#check materializedConservative_productionCard_le_prefix
#check materializedConservative_update_work_le_prefix
#check conservativeMaterializedUpdateWorkEnvelope_polynomial_form
#check corollary_poly_update_materialized

-- ---------------------------------------------------------------------------
-- Section 7: Fixed-Window Thick Data
-- ---------------------------------------------------------------------------

-- Lemma 7.1 / lem:window-typed-yield.
#check fixedWindow_reduced_minimal_typed_yield_length_le

-- Lemma 7.2 / lem:window-context.
-- First displayed context bound and the resulting witness-length bound.
#check exists_fixedWindow_reduced_short_reaching_context
#check canonicalWitnessWords_length_le_fixedWindow_of_structural_reachability

-- Theorem 7.3 / thm:window-thick.
#check concreteFixedWindowSection7_package
#check classicalFixedWindowSection7_package

-- Proposition 7.4 / prop:thick-ssbnf-normal.
#check indexed_proposition74_full_package
#check proposition74_thickness_from_yieldBound

-- Corollary 7.5 / cor:window-transfer.
#check indexedFixedWindowSection7_package
#check indexedClassicalFixedWindowSection7_package
#check indexedZeroWindowSection7_package

-- ---------------------------------------------------------------------------
-- Section 8: The Linear Subclass
-- ---------------------------------------------------------------------------

-- Proposition 8.1 / prop:linear-normal.
#check indexedLinear_normalization_source_package
#check indexedLinear_normalization_language_eq
#check indexedLinear_normalization_shape
#check indexedLinear_normalization_size_le

-- Lemma 8.2 / lem:linear-short.
#check minimumCanonicalYield_linear_length_le
#check minimumCanonicalContext_linear_length_le
#check mem_canonicalWitnessFinset_linear_length_le

-- Theorem 8.3 / thm:linear-poly.
#check indexedLinear_characteristic_package

-- Proposition 8.4 (manuscript label prop:linear-separator-example).
#check lpm_proposition86_full_semantic

-- ---------------------------------------------------------------------------
-- Section 9: Expressiveness and Boundaries
-- ---------------------------------------------------------------------------

-- Proposition 9.1 / prop:nonlinear-rs-example.
#check DeltaStar.nonlinear_rs_example_full

-- Proposition 9.2 / prop:ctr-regular.
#check CappedCounter.proposition_ctr_regular

-- Theorem 9.3 / thm:ctr-non-kl.
#check CappedCounter.theorem_ctr_non_kl

-- Corollary 9.4 / regular separation KL ⊊ RS.
#check CappedCounter.regular_fixedH_outside_every_fixedWindow
#check fixedWindowSubstitutable_iff_fixedHSubstitutable

-- Lemma 9.5 / lem:finite-monoid-obstruction.
#check finiteMonoid_obstruction
#check finiteMonoid_obstruction_uniform

-- Corollary 9.6 / uncapped counter obstruction.
#check UncappedCounter.not_fixedH

-- Corollary 9.7 / cor:dyck-not-rs.
#check DyckOne.not_fixedH

-- Lemma 9.8 / lem:rs-fixed-quotient.
#check fixedHSubstitutable_fixedRightQuotient

-- Proposition 9.9 / prop:clark-congruential-comparison.
#check proposition99_fixedH_inclusion
#check proposition99_dyck_properness

/--
Marker theorem: every numbered manuscript claim in Sections 3--9 has a
compile-checked Lean cross-reference in this audit.
-/
theorem v79_numbered_manuscript_claims_audited : True :=
  True.intro

end TCS1
end LeanCfgProject
