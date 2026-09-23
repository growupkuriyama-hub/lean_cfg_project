import LeanCfgProject.TCS1.RegularRecognition
import LeanCfgProject.TCS1.ClarkEyraudSpecialCase
import LeanCfgProject.TCS1.FixedWindowExactEquivalence
import LeanCfgProject.TCS1.MainTheoremSemanticPackage
import LeanCfgProject.TCS1.ConcreteLearnerComplexity
import LeanCfgProject.TCS1.BinaryMembershipDecision
import LeanCfgProject.TCS1.ConservativeMembershipCost
import LeanCfgProject.TCS1.FixedWindowLemma71ReducedFacade
import LeanCfgProject.TCS1.FixedWindowLemma72Facade
import LeanCfgProject.TCS1.FixedWindowSection7Package
import LeanCfgProject.TCS1.Proposition74IndexedPackage
import LeanCfgProject.TCS1.IndexedLinearNormalizationTheorem
import LeanCfgProject.TCS1.IndexedLinearReducedNormalization
import LeanCfgProject.TCS1.LinearReducedWitnessBridge
import LeanCfgProject.TCS1.IndexedLinearCharacteristicData
import LeanCfgProject.TCS1.LinearSeparatorProposition86
import LeanCfgProject.TCS1.DeltaStarProposition
import LeanCfgProject.TCS1.CappedCounterProposition
import LeanCfgProject.TCS1.FiniteMonoidObstructionKernel
import LeanCfgProject.TCS1.UncappedCounterObstruction
import LeanCfgProject.TCS1.DyckOneBracketKernel
import LeanCfgProject.TCS1.FixedHRightQuotient
import LeanCfgProject.TCS1.ClarkCongruentialComparison

/-!
# TCS #1 v79: theorem-surface audit

This file is a compile-time index from the numbered theorem surface of the
v79 manuscript to the Lean declarations that discharge it.

It distinguishes theorem-level mathematical verification from the remaining
representation-level cost bookkeeping.  The repository now includes an
executable CYK kernel for the separated-start SSBNF shape, exact semantic
correctness, explicit polynomial candidate/comparison envelopes, and a bridge
from those envelopes to the concrete conservative learner's positive-data
prefix bounds.  The only explicit cost-side premise left in that bridge is the
standard encoding sanity condition that the number of non-start symbols is at
most the stored grammar encoding envelope.

The former external Double-Delta non-linearity fact is no longer external:
the repository now proves its own bounded linear pumping lemma and derives
the obstruction internally.

Every declaration below is checked by the Lean compiler.  Keeping this file in
the full facade makes accidental theorem renaming or loss of a paper-facing
bridge an integration failure.
-/

namespace LeanCfgProject
namespace TCS1

-- Section 3: finite-monoid recognition and classical special cases.
#check regular_auto_proposition_package
#check clarkEyraud_special_case
#check fixedWindowSubstitutable_iff_fixedHSubstitutable
#check fixedWindowSubstitutable_of_fixedHSubstitutable

-- Main qualitative learning theorem and Sections 4--5.
#check sample_consistency
#check batchLanguage_sound
#check typedDerives_yield_type
#check concreteTypedActive_language_eq_untyped
#check canonicalWitnessWords_completeness
#check exact_reconstruction_of_qualitative_reducedness
#check indexedFixedH_exists_characteristic_sample
#check indexedFixedH_learning_semantic_core
#check indexedFixedH_concreteGold_identification_nonempty

-- Section 6: polynomial reconstruction/update bookkeeping.
#check reconstructionRuleCandidateSpace_card_le_fourth
#check concreteAccumulated_directCandidateScan_le_prefix_degreeFive
#check concreteConservative_update_size_certificate
#check cykStartMember_eq_true_iff
#check cykMembershipCandidateEnvelope_exact
#check cykNaiveComparisonEnvelope_polynomial_form
#check conservativeCYKPrefixEnvelope_polynomial_form
#check concreteConservative_membershipComparison_le_prefix
#check concreteConservative_update_work_le_prefix

-- Section 7: fixed-window quantitative bounds and normalization transfer.
#check omittedSibling_contribution_le
#check boundaryAssembly_typed_lift_of_fixedWindowSummary
#check terminalIsolation_then_binarization_language_eq
#check frontEndBinary_active_short_derivation_envelope
#check fixedWindow_reduced_minimal_typed_yield_length_le
#check canonicalWitnessWords_length_le_fixedWindow
#check concreteFixedWindowSection7_package
#check classicalFixedWindowSection7_package
#check indexedClassicalFixedWindowSection7_package
#check indexedZeroWindowSection7_package
#check indexed_proposition74_full_package
#check proposition74_thickness_from_yieldBound

-- Section 8: arbitrary linear normalization, short witnesses, and data bound.
#check indexedLinear_normalization_source_package
#check indexedLinear_reduced_normalization_semantic_package
#check minimumCanonicalYield_linear_length_le
#check minimumCanonicalContext_linear_length_le
#check indexedLinear_characteristic_package
#check lpm_proposition86_full_semantic

-- Section 9.1: nonlinear Delta-star example.
#check DeltaStar.nonlinear_rs_example_verified_core
#check DeltaStar.doubleDelta_not_rawLinearInitialRepresentable
#check DeltaStar.deltaStar_not_rawLinearRepresentable
#check DeltaStar.deltaStar_no_indexedLinear_presentation
#check DeltaStar.nonlinear_rs_example_nonlinearity_reduction
#check DeltaStar.nonlinear_rs_example_full

-- Section 9.2: regular separation from all fixed windows.
#check CappedCounter.proposition_ctr_regular
#check CappedCounter.theorem_ctr_non_kl
#check CappedCounter.regular_fixedH_outside_every_fixedWindow

-- Section 9.3: finite-monoid obstructions and quotient closure.
#check finiteMonoid_obstruction
#check finiteMonoid_obstruction_uniform
#check UncappedCounter.not_fixedH
#check DyckOne.not_fixedH
#check fixedHSubstitutable_fixedRightQuotient

-- Proposition 9.9: comparison with Clark's congruential family.
#check proposition99_fixedH_inclusion
#check proposition99_dyck_properness

/-- Marker theorem: the current v79 theorem-surface audit compiles. -/
theorem v79_theorem_surface_audited : True :=
  True.intro

end TCS1
end LeanCfgProject
