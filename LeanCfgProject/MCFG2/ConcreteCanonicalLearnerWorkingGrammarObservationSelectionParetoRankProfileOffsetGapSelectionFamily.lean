/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapAlternative

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankProfileOffsetGapSelectionFamily.lean

The preceding file packages the finite offset spectrum as a proof-carrying
gap-free/least-gap alternative.

This file lifts individual offset selectors to finite indexed families.

## Offset-indexed selection families

For a finite domain of realized normalized offsets, a selection family stores
one actual selected observation interface at every domain offset.

For every family index `d`, the selected interface has profile

```text
(c_min + d, a_max - d).
```

It belongs to the finite rank-minimizing Pareto selection set.

No uniqueness of the selected subset is required or asserted.

## Complete family

In the gap-free branch, the domain is

```text
range (width + 1).
```

Thus one actual selected interface is available at every affine profile
between the two endpoints.

The family has exactly `width + 1` indices.

## Obstructed family

In the non-gap-free branch, the domain is

```text
range firstGap ∪ {width}.
```

This consists of the complete realized prefix before the least missing offset,
together with the always-realized maximum endpoint.

The family has exactly `firstGap + 1` indices.

Its least missing certificate remains outside the family domain.

## Uniform semantic and learning guarantees

Every family member

* represents the target;
* is Pareto optimal;
* attains the exact positive additive rank;
* is inclusion-irredundant;
* has every selected coordinate essential; and
* has its own certified learner identifying the target.

For two family indices, offset order is exactly selected-cardinality order and
reverse additive-cost order.  Ordered offset differences are preserved
exactly.

## Boundary

The family is constructed from the already available finite semantic offset
table.  It does not assert an external polynomial-time procedure for producing
that table from an arbitrary language presentation.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section OffsetSelectionFamilyDefinition

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)
variable (language : Set (Word α))
variable
  (hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f)
variable
  (minimumCardinalityResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)
variable
  (minimumAdditiveResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)
variable
  (domain : Finset Nat)

/-- One actual rank-minimizing Pareto selected interface for every offset in a
finite realized domain. -/
structure
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionFamily where

  domain_subset_offsets :
    domain ⊆
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
        minimumCardinalityResult

  selected :
    {offset : Nat // offset ∈ domain} →
      Finset ι

  selected_mem :
    ∀ offset,
      selected offset ∈
        correctedConcreteObservationPositiveAdditiveRankMinimizingParetoSelections
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget

  selected_profile_eq :
    ∀ offset,
      (selected offset).card,
          correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight
            (selected offset) =
        correctedConcreteObservationPositiveAdditiveParetoProfileOfOffset
          minimumCardinalityResult
          offset.1

/-- Construct a finite selected-interface family over any verified realized
offset domain. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionFamilyOfDomain
    (hDomain :
      domain ⊆
        correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsets
          minimumCardinalityResult) :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionFamily
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      minimumCardinalityResult
      minimumAdditiveResult
      domain := by

  classical

  let result :
      ∀ offset : {offset : Nat // offset ∈ domain},
        CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget
          minimumCardinalityResult
          minimumAdditiveResult
          offset.1
          (hDomain offset.2) :=
    fun offset =>
      correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language
        hTarget
        minimumCardinalityResult
        minimumAdditiveResult
        offset.1
        (hDomain offset.2)

  exact
    ⟨hDomain,
      fun offset =>
        (result offset).selected,
      fun offset =>
        (result offset).selected_mem,
      fun offset =>
        (result offset).selected_profile_eq⟩

end OffsetSelectionFamilyDefinition


namespace CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionFamily

section FamilyMemberProperties

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable
  {hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f}
variable
  {minimumCardinalityResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget}
variable
  {minimumAdditiveResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget}
variable
  {domain : Finset Nat}
variable
  (family :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionFamily
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      minimumCardinalityResult
      minimumAdditiveResult
      domain)

/-- Regard one family member as the previously constructed single-offset
selection result. -/
def toOffsetSelectionResult
    (offset : {offset : Nat // offset ∈ domain}) :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      minimumCardinalityResult
      minimumAdditiveResult
      offset.1
      (family.domain_subset_offsets offset.2) :=
  ⟨family.selected offset,
    family.selected_mem offset,
    family.selected_profile_eq offset⟩

/-- Every family member is Pareto optimal. -/
theorem selected_pareto
    (offset : {offset : Nat // offset ∈ domain}) :
    CorrectedConcreteObservationSelectionParetoOptimal
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language
      (family.selected offset) := by

  exact
    (family.toOffsetSelectionResult offset).selected_pareto

/-- Every family member lies inside the ambient candidate set. -/
theorem selected_subset
    (offset : {offset : Nat // offset ∈ domain}) :
    family.selected offset ⊆ U := by

  exact
    (family.toOffsetSelectionResult offset).selected_subset

/-- Every family member represents the target. -/
theorem selected_target
    (offset : {offset : Nat // offset ∈ domain}) :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥(family.selected offset) → M)
        (selectedObservationProduct
          obsFamily
          (family.selected offset))
        f := by

  exact
    (family.toOffsetSelectionResult offset).selected_target

/-- Every family member attains the exact ambient positive additive rank. -/
theorem selected_cost_eq_rank
    (offset : {offset : Nat // offset ∈ domain}) :
    correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight
          (family.selected offset) =
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget := by

  exact
    (family.toOffsetSelectionResult offset).selected_cost_eq_rank

/-- Exact selected cardinality at one family offset. -/
theorem selected_card_eq
    (offset : {offset : Nat // offset ∈ domain}) :
    (family.selected offset).card =
      minimumCardinalityResult.profile.1 + offset.1 := by

  exact
    (family.toOffsetSelectionResult offset).selected_card_eq

/-- Exact additive coordinate cost at one family offset. -/
theorem selected_additiveCost_eq
    (offset : {offset : Nat // offset ∈ domain}) :
    correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight
          (family.selected offset) =
      minimumCardinalityResult.profile.2 - offset.1 := by

  exact
    (family.toOffsetSelectionResult offset).selected_additiveCost_eq

/-- Every family member is inclusion-irredundant. -/
theorem selected_irredundant
    (offset : {offset : Nat // offset ∈ domain}) :
    CorrectedConcreteObservationSelectionIrredundant
      (z := z)
      α
      ι
      M
      obsFamily
      f
      language
      (family.selected offset) := by

  exact
    (family.toOffsetSelectionResult offset).selected_irredundant

/-- Every coordinate selected by a family member is essential. -/
theorem selected_coordinateEssential
    (offset : {offset : Nat // offset ∈ domain})
    {index : ι}
    (hindex : index ∈ family.selected offset) :
    CorrectedConcreteSelectedObservationCoordinateEssential
      (z := z)
      α
      ι
      M
      obsFamily
      f
      language
      (family.selected offset)
      index := by

  exact
    (family.toOffsetSelectionResult offset).selected_coordinateEssential
      hindex

/-- Semantic package for every indexed family member. -/
theorem selected_semantic_package
    (offset : {offset : Nat // offset ∈ domain}) :
    family.selected offset ⊆ U ∧
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥(family.selected offset) → M)
          (selectedObservationProduct
            obsFamily
            (family.selected offset))
          f ∧
      (family.selected offset).card =
        minimumCardinalityResult.profile.1 + offset.1 ∧
      correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight
          (family.selected offset) =
        minimumCardinalityResult.profile.2 - offset.1 ∧
      correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight
          (family.selected offset) =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget ∧
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language
        (family.selected offset) ∧
      CorrectedConcreteObservationSelectionIrredundant
        (z := z)
        α
        ι
        M
        obsFamily
        f
        language
        (family.selected offset) := by

  exact
    ⟨family.selected_subset offset,
      family.selected_target offset,
      family.selected_card_eq offset,
      family.selected_additiveCost_eq offset,
      family.selected_cost_eq_rank offset,
      family.selected_pareto offset,
      family.selected_irredundant offset⟩

end FamilyMemberProperties


section FamilyOrderProperties

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable
  {hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f}
variable
  {minimumCardinalityResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget}
variable
  {minimumAdditiveResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget}
variable
  {domain : Finset Nat}
variable
  (family :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionFamily
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      minimumCardinalityResult
      minimumAdditiveResult
      domain)

/-- Offset order is exactly selected-cardinality order inside a family. -/
theorem selected_card_le_iff_offset_le
    (offset₀ offset₁ : {offset : Nat // offset ∈ domain}) :
    (family.selected offset₀).card <=
        (family.selected offset₁).card ↔
      offset₀.1 <= offset₁.1 := by

  exact
    (family.toOffsetSelectionResult offset₀).selected_card_le_iff_offset_le
      (family.toOffsetSelectionResult offset₁)

/-- Strict offset order is exactly strict selected-cardinality order. -/
theorem selected_card_lt_iff_offset_lt
    (offset₀ offset₁ : {offset : Nat // offset ∈ domain}) :
    (family.selected offset₀).card <
        (family.selected offset₁).card ↔
      offset₀.1 < offset₁.1 := by

  exact
    (family.toOffsetSelectionResult offset₀).selected_card_lt_iff_offset_lt
      (family.toOffsetSelectionResult offset₁)

/-- Offset order is exactly reverse additive-coordinate order. -/
theorem selected_additiveCost_reverse_le_iff_offset_le
    (offset₀ offset₁ : {offset : Nat // offset ∈ domain}) :
    correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight
          (family.selected offset₁) <=
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight
          (family.selected offset₀) ↔
      offset₀.1 <= offset₁.1 := by

  exact
    (family.toOffsetSelectionResult offset₀).selected_additiveCost_reverse_le_iff_offset_le
      (family.toOffsetSelectionResult offset₁)

/-- Ordered family offsets preserve exact cardinality and additive-cost
differences. -/
theorem selected_exactTradeoff_package
    (offset₀ offset₁ : {offset : Nat // offset ∈ domain})
    (hOrder : offset₀.1 <= offset₁.1) :
    (family.selected offset₀).card <=
        (family.selected offset₁).card ∧
      correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight
          (family.selected offset₁) <=
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight
          (family.selected offset₀) ∧
      (family.selected offset₁).card -
          (family.selected offset₀).card =
        offset₁.1 - offset₀.1 ∧
      correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight
            (family.selected offset₀) -
          correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight
            (family.selected offset₁) =
        offset₁.1 - offset₀.1 ∧
      correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight
          (family.selected offset₀) =
        correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight
          (family.selected offset₁) := by

  exact
    (family.toOffsetSelectionResult offset₀).selected_exactTradeoff_package
      (family.toOffsetSelectionResult offset₁)
      hOrder

/-- Equality of family-member profiles is equivalent to equality of their
natural-number offsets. -/
theorem selected_profile_eq_iff_offset_eq
    (offset₀ offset₁ : {offset : Nat // offset ∈ domain}) :
    ((family.selected offset₀).card,
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight
          (family.selected offset₀)) =
      ((family.selected offset₁).card,
        correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight
          (family.selected offset₁)) ↔
      offset₀.1 = offset₁.1 := by

  exact
    (family.toOffsetSelectionResult offset₀).selected_profile_eq_iff_offset_eq
      (family.toOffsetSelectionResult offset₁)

end FamilyOrderProperties


section FamilyCertifiedLearner

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq ι]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable
  {hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f}
variable
  {minimumCardinalityResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget}
variable
  {minimumAdditiveResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget}
variable
  {domain : Finset Nat}
variable
  (family :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionFamily
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      minimumCardinalityResult
      minimumAdditiveResult
      domain)

/-- Every member of a finite selection family has its own certified learner
and an exact checked output at minimum certified-description rank. -/
theorem selected_certified_package
    (offset : {offset : Nat // offset ∈ domain}) :
    IdentifiesLanguageFromPositiveData
        (correctedConcreteCertifiedWorkingGrammarHypLanguage
          (selectedObservationProduct
            obsFamily
            (family.selected offset))
          f)
        (correctedConcreteCertifiedWorkingGrammarLearner
          hα
          (selectedObservationProduct
            obsFamily
            (family.selected offset))
          f)
        language ∧
      language ∈
        CorrectedConcreteCertifiedRankProfileClass
          (α := α)
          (M := ↥(family.selected offset) → M)
          (selectedObservationProduct
            obsFamily
            (family.selected offset))
          f
          (startRootedTargetCertifiedDescriptionRank
            (v := z)
            hα
            (selectedObservationProduct
              obsFamily
              (family.selected offset))
            f
            (family.selected_target offset)) ∧
      ∃
        C :
          CorrectedConcreteCertifiedWorkingGrammarHypothesis
            α
            (↥(family.selected offset) → M)
            (selectedObservationProduct
              obsFamily
              (family.selected offset))
            f,
        C.output.grammar.StringLanguage =
            language ∧
          C.bits.length <=
            correctedConcreteCertifiedRankBitBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z)
                hα
                (selectedObservationProduct
                  obsFamily
                  (family.selected offset))
                f
                (family.selected_target offset))
              f ∧
          C.canonicalSearch.length <=
            correctedConcreteCertifiedRankSearchBudget
              (startRootedTargetCertifiedDescriptionRank
                (v := z)
                hα
                (selectedObservationProduct
                  obsFamily
                  (family.selected offset))
                f
                (family.selected_target offset))
              f := by

  exact
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionResult.certified_package
      (z := z)
      hα
      (family.toOffsetSelectionResult offset)

end FamilyCertifiedLearner

end CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionFamily


section CompleteSelectionFamily

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable
  {hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f}
variable
  (minimumCardinalityResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)
variable
  (minimumAdditiveResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)
variable
  (hGapFree :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
      minimumCardinalityResult
      minimumAdditiveResult)

/-- Complete offset-indexed selected-interface family in the gap-free branch. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoRankProfileCompleteSelectionFamily :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionFamily
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      minimumCardinalityResult
      minimumAdditiveResult
      (Finset.range
        (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
            minimumCardinalityResult
            minimumAdditiveResult +
          1)) := by

  apply
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionFamilyOfDomain
      minimumCardinalityResult
      minimumAdditiveResult

  intro offset hOffset

  have hLt :=
    Finset.mem_range.mp
      hOffset

  exact
    hGapFree
      offset
      (by omega)

/-- The complete family has exactly `width + 1` indices. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankProfileCompleteSelectionFamily_domain_card :
    (Finset.range
      (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult +
        1)).card =
      correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
          minimumCardinalityResult
          minimumAdditiveResult +
        1 := by

  simp

end CompleteSelectionFamily


section FirstGapSelectionFamily

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable
  {hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f}
variable
  (minimumCardinalityResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)
variable
  (minimumAdditiveResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)
variable
  (hNotGapFree :
    ¬
      CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
        minimumCardinalityResult
        minimumAdditiveResult)

/-- Selected-interface family on the complete realized prefix before the first
gap, together with the maximum endpoint. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapSelectionFamily :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionFamily
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      minimumCardinalityResult
      minimumAdditiveResult
      (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree) := by

  apply
    correctedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionFamilyOfDomain
      minimumCardinalityResult
      minimumAdditiveResult

  exact
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum_subset_offsets
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree

/-- The obstructed-branch family has exactly `firstGap + 1` indices. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapSelectionFamily_domain_card :
    (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree).card =
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree +
        1 := by

  exact
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum_card
      minimumCardinalityResult
      minimumAdditiveResult
      hNotGapFree

/-- The canonical first gap is outside the obstructed family domain. -/
theorem
    positiveAdditiveParetoRankProfileFirstGap_not_mem_selectionFamilyDomain :
    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
          minimumCardinalityResult
          minimumAdditiveResult
          hNotGapFree ∉
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree := by

  intro hMember

  rcases Finset.mem_insert.mp hMember with
    hMaximum | hPrefix

  · have hStrict :=
      positiveAdditiveParetoRankProfileFirstGap_lt_width
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree

    omega

  · exact
      positiveAdditiveParetoRankProfileFirstGap_not_mem_prefix
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree
        hPrefix

end FirstGapSelectionFamily


section SelectionFamilyAlternative

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq ι]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable
  {hTarget :
    language ∈
      StartRootedCorrectedConcreteTargetClass
        (v := z)
        α
        (↥U → M)
        (selectedObservationProduct obsFamily U)
        f}
variable
  (minimumCardinalityResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)
variable
  (minimumAdditiveResult :
    CorrectedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget)
variable
  (result :
    CorrectedConcreteObservationPositiveAdditiveParetoRankProfileGapAlternativeResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      minimumCardinalityResult
      minimumAdditiveResult)

/-- Proof-carrying finite family alternative selected by the Boolean result. -/
theorem selectionFamily_alternative :
    (∃
      hGapFree :
        CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
          minimumCardinalityResult
          minimumAdditiveResult,
      result.decision = true ∧
        ∃ family :
          CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionFamily
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            language
            hTarget
            minimumCardinalityResult
            minimumAdditiveResult
            (Finset.range
              (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
                  minimumCardinalityResult
                  minimumAdditiveResult +
                1)),
          ∀ offset,
            IdentifiesLanguageFromPositiveData
              (correctedConcreteCertifiedWorkingGrammarHypLanguage
                (selectedObservationProduct
                  obsFamily
                  (family.selected offset))
                f)
              (correctedConcreteCertifiedWorkingGrammarLearner
                hα
                (selectedObservationProduct
                  obsFamily
                  (family.selected offset))
                f)
              language) ∨
      (∃
        hNotGapFree :
          ¬
            CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
              minimumCardinalityResult
              minimumAdditiveResult,
        result.decision = false ∧
          ∃
            certificate :
              CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCertificate
                minimumCardinalityResult
                minimumAdditiveResult,
            certificate.offset =
                correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
                  minimumCardinalityResult
                  minimumAdditiveResult
                  hNotGapFree ∧
              ∃ family :
                CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionFamily
                  (z := z)
                  obsFamily
                  f
                  coordinateWeight
                  U
                  language
                  hTarget
                  minimumCardinalityResult
                  minimumAdditiveResult
                  (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum
                    minimumCardinalityResult
                    minimumAdditiveResult
                    hNotGapFree),
                ∀ offset,
                  IdentifiesLanguageFromPositiveData
                    (correctedConcreteCertifiedWorkingGrammarHypLanguage
                      (selectedObservationProduct
                        obsFamily
                        (family.selected offset))
                      f)
                    (correctedConcreteCertifiedWorkingGrammarLearner
                      hα
                      (selectedObservationProduct
                        obsFamily
                        (family.selected offset))
                      f)
                    language) := by

  rcases result.decision_dichotomy with
    hPositive | hNegative

  · rcases hPositive with
      ⟨hDecisionTrue, hGapFree⟩

    let family :=
      correctedConcreteObservationPositiveAdditiveParetoRankProfileCompleteSelectionFamily
        minimumCardinalityResult
        minimumAdditiveResult
        hGapFree

    exact
      Or.inl
        ⟨hGapFree,
          hDecisionTrue,
          family,
          fun offset =>
            (family.selected_certified_package
              hα
              offset).1⟩

  · rcases hNegative with
      ⟨hDecisionFalse, hNotGapFree⟩

    let certificate :=
      result.negativeCertificate
        hDecisionFalse

    let family :=
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapSelectionFamily
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree

    exact
      Or.inr
        ⟨hNotGapFree,
          hDecisionFalse,
          certificate,
          rfl,
          family,
          fun offset =>
            (family.selected_certified_package
              hα
              offset).1⟩

end SelectionFamilyAlternative


section SelectionFamilyFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq ι]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final complete-family/least-gap-family alternative with exact domain
cardinality and certified learning for every indexed selected product. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankProfileOffsetGapSelectionFamily_package :
    ∀
      language : Set (Word α),
      ∀ hTarget :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥U → M)
            (selectedObservationProduct obsFamily U)
            f,
      let minimumCardinalityResult :=
        correctedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget
      let minimumAdditiveResult :=
        correctedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget
      let result :=
        correctedConcreteObservationPositiveAdditiveParetoRankProfileGapAlternativeResult
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language
          hTarget
          minimumCardinalityResult
          minimumAdditiveResult
      (result.decision = true →
        ∃
          hGapFree :
            CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
              minimumCardinalityResult
              minimumAdditiveResult,
          ∃ family :
            CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionFamily
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language
              hTarget
              minimumCardinalityResult
              minimumAdditiveResult
              (Finset.range
                (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
                    minimumCardinalityResult
                    minimumAdditiveResult +
                  1)),
            (Finset.range
              (correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
                  minimumCardinalityResult
                  minimumAdditiveResult +
                1)).card =
                correctedConcreteObservationPositiveAdditiveParetoProfileTradeoffWidth
                    minimumCardinalityResult
                    minimumAdditiveResult +
                  1 ∧
              ∀ offset,
                family.selected offset ⊆ U ∧
                  CorrectedConcreteObservationSelectionParetoOptimal
                    (z := z)
                    obsFamily
                    f
                    (correctedConcreteObservationSelectionAdditiveCost
                      coordinateWeight)
                    U
                    language
                    (family.selected offset) ∧
                  CorrectedConcreteObservationSelectionIrredundant
                    (z := z)
                    α
                    ι
                    M
                    obsFamily
                    f
                    language
                    (family.selected offset) ∧
                  IdentifiesLanguageFromPositiveData
                    (correctedConcreteCertifiedWorkingGrammarHypLanguage
                      (selectedObservationProduct
                        obsFamily
                        (family.selected offset))
                      f)
                    (correctedConcreteCertifiedWorkingGrammarLearner
                      hα
                      (selectedObservationProduct
                        obsFamily
                        (family.selected offset))
                      f)
                    language) ∧
        (result.decision = false →
          ∃
            hNotGapFree :
              ¬
                CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetsGapFree
                  minimumCardinalityResult
                  minimumAdditiveResult,
            ∃
              certificate :
                CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetGapCertificate
                  minimumCardinalityResult
                  minimumAdditiveResult,
              ∃ family :
                CorrectedConcreteObservationPositiveAdditiveParetoRankProfileOffsetSelectionFamily
                  (z := z)
                  obsFamily
                  f
                  coordinateWeight
                  U
                  language
                  hTarget
                  minimumCardinalityResult
                  minimumAdditiveResult
                  (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum
                    minimumCardinalityResult
                    minimumAdditiveResult
                    hNotGapFree),
                certificate.offset =
                    correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGap
                      minimumCardinalityResult
                      minimumAdditiveResult
                      hNotGapFree ∧
                  (correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapPrefixWithMaximum
                    minimumCardinalityResult
                    minimumAdditiveResult
                    hNotGapFree).card =
                      certificate.offset + 1 ∧
                  ∀ offset,
                    family.selected offset ⊆ U ∧
                      CorrectedConcreteObservationSelectionParetoOptimal
                        (z := z)
                        obsFamily
                        f
                        (correctedConcreteObservationSelectionAdditiveCost
                          coordinateWeight)
                        U
                        language
                        (family.selected offset) ∧
                      CorrectedConcreteObservationSelectionIrredundant
                        (z := z)
                        α
                        ι
                        M
                        obsFamily
                        f
                        language
                        (family.selected offset) ∧
                      IdentifiesLanguageFromPositiveData
                        (correctedConcreteCertifiedWorkingGrammarHypLanguage
                          (selectedObservationProduct
                            obsFamily
                            (family.selected offset))
                          f)
                        (correctedConcreteCertifiedWorkingGrammarLearner
                          hα
                          (selectedObservationProduct
                            obsFamily
                            (family.selected offset))
                          f)
                        language) := by

  intro language hTarget

  let minimumCardinalityResult :=
    correctedConcreteObservationPositiveAdditiveParetoMinimumCardinalityProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  let minimumAdditiveResult :=
    correctedConcreteObservationPositiveAdditiveParetoMinimumAdditiveProfileResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  let result :=
    correctedConcreteObservationPositiveAdditiveParetoRankProfileGapAlternativeResult
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget
      minimumCardinalityResult
      minimumAdditiveResult

  constructor

  · intro hDecisionTrue

    let hGapFree :=
      (result.decision_eq_true_iff_gapFree).mp
        hDecisionTrue

    let family :=
      correctedConcreteObservationPositiveAdditiveParetoRankProfileCompleteSelectionFamily
        minimumCardinalityResult
        minimumAdditiveResult
        hGapFree

    exact
      ⟨hGapFree,
        family,
        correctedConcreteObservationPositiveAdditiveParetoRankProfileCompleteSelectionFamily_domain_card
          minimumCardinalityResult
          minimumAdditiveResult,
        fun offset =>
          ⟨family.selected_subset offset,
            family.selected_pareto offset,
            family.selected_irredundant offset,
            (family.selected_certified_package
              hα
              offset).1⟩⟩

  · intro hDecisionFalse

    let hNotGapFree :=
      (result.decision_eq_false_iff_not_gapFree).mp
        hDecisionFalse

    let certificate :=
      result.negativeCertificate
        hDecisionFalse

    let family :=
      correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapSelectionFamily
        minimumCardinalityResult
        minimumAdditiveResult
        hNotGapFree

    exact
      ⟨hNotGapFree,
        certificate,
        family,
        rfl,
        by
          rw [
            correctedConcreteObservationPositiveAdditiveParetoRankProfileFirstGapSelectionFamily_domain_card
              minimumCardinalityResult
              minimumAdditiveResult
              hNotGapFree
          ],
        fun offset =>
          ⟨family.selected_subset offset,
            family.selected_pareto offset,
            family.selected_irredundant offset,
            (family.selected_certified_package
              hα
              offset).1⟩⟩

end SelectionFamilyFinalPackage

end MCFG
