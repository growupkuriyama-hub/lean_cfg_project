/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionPositiveAdditiveRank

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionParetoRankEnvelope.lean

The preceding file gives a direct arbitrary-rank characterization for positive
additive observation-selection cost.

This file identifies that scalar rank as the lower envelope of the finite
two-objective Pareto frontier.

## Two objectives and their scalarization

For a coordinate-weight function `coordinateWeight`, use the profile

```text
(number of selected coordinates,
 total extra coordinate weight).
```

The Pareto frontier is formed using

```lean
correctedConcreteObservationSelectionAdditiveCost coordinateWeight
```

as the second objective.

Its scalar profile total is

```text
S.card + AdditiveCost(weight,S),
```

which is exactly the positive additive observation-selection cost.

Therefore every exact positive-additive minimum is Pareto optimal for the two
objectives.

## Exact Pareto-rank class

Define the exact positive-additive Pareto-rank class by requiring an actual
Pareto-optimal selected subset `S` whose positive additive cost is exactly
`rank`, together with the global lower-bound certificate

```text
rank ≤ PositiveAdditiveCost(R)
```

for every representing ambient selection `R`.

This class is proved equal to

```text
CorrectedConcreteObservationSelectionExactCostRankClass
```

for positive additive cost.

Thus every exact scalar-rank shell has a Pareto-optimal witness.

## Finite Pareto rank values

Map every member of the explicit finite additive Pareto frontier to its positive
additive scalar value.  This gives a finite set

```lean
correctedConcreteObservationPositiveAdditiveParetoRankValues.
```

It has at most `2^|U|` elements.

For every full ambient-product target, its positive additive rank

* belongs to this finite set; and
* is no greater than every other value in the set.

Hence the observation-selection rank is exactly the minimum scalar total on the
finite Pareto frontier.

## Pareto-envelope class

The Pareto-envelope rank-`r` class says that

```text
r occurs on the finite Pareto frontier
and
r is no greater than every Pareto scalar value.
```

This class is proved equal to the exact positive-additive rank shell.

## Pareto obstruction

For a full ambient-product target,

```text
budget < positive-additive rank
```

is equivalent to

```text
budget < every scalar value achieved on the additive Pareto frontier.
```

Thus a rank lower bound can be checked purely against Pareto candidates.

## Certified Pareto-rank witness

Every target has an actual selected subset that simultaneously

* attains the exact positive-additive rank;
* is Pareto optimal for coordinate count and added weight;
* is inclusion-irredundant;
* has every selected coordinate essential; and
* carries its own certified learner and exact checked grammar output.

No comparison between observation-selection rank and grammar-description rank
is asserted.

No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


section PositiveAdditiveAsParetoScalar

variable {ι : Type v}

/-- Positive additive cost is exactly the scalar sum of cardinality and
unshifted additive coordinate cost. -/
theorem observationSelectionPositiveAdditiveCost_eq_additiveParetoScalarCost
    (coordinateWeight : ι → Nat)
    (S : Finset ι) :
    correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight S =
      correctedConcreteObservationSelectionParetoScalarCost
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        S := by

  rfl

end PositiveAdditiveAsParetoScalar


section ExactPositiveAdditiveMinimumIsPareto

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}

/-- Every exact positive-additive minimum is Pareto optimal for the profile

```text
(selected-set cardinality, total extra coordinate weight).
``` -/
theorem
    observationSelection_exactPositiveAdditiveMinimum_is_additivePareto
    (hSelection :
      HasCorrectedConcreteObservationSelectionCost
        (obsFamily := obsFamily)
        (f := f)
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        U
        language)
    {S : Finset ι}
    (hSU : S ⊆ U)
    (hMinimum :
      correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight S =
        correctedConcreteObservationSelectionMinimumCost
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          hSelection)
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f) :
    CorrectedConcreteObservationSelectionParetoOptimal
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language
      S := by

  refine
    ⟨hSU,
      hTarget,
      ?_⟩

  intro R hRU hRTarget hDominates

  have hMinimumLe :
      correctedConcreteObservationSelectionMinimumCost
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          hSelection <=
        correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight R := by

    apply
      hSelection.minimumCost_le_of_selection

    exact
      ⟨R,
        hRU,
        Nat.le_refl _,
        hRTarget⟩

  have hStrictScalar :
      correctedConcreteObservationSelectionParetoScalarCost
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          R <
        correctedConcreteObservationSelectionParetoScalarCost
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          S :=
    observationSelection_strictDominance_implies_scalarCost_lt
      hDominates

  have hStrict :
      correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight R <
        correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight S := by

    simpa [
      observationSelectionPositiveAdditiveCost_eq_additiveParetoScalarCost
    ] using
      hStrictScalar

  rw [hMinimum] at hStrict

  omega

end ExactPositiveAdditiveMinimumIsPareto


section AmbientPositiveAdditiveMinimumIsPareto

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Every selected subset attaining the ambient positive-additive minimum is
Pareto optimal for cardinality and additive coordinate weight. -/
theorem ambientTarget_positiveAdditiveMinimumSelection_is_additivePareto
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    {S : Finset ι}
    (hSU : S ⊆ U)
    (hCost :
      correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight S =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget)
    (hSelected :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f) :
    CorrectedConcreteObservationSelectionParetoOptimal
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language
      S := by

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      hTarget

  have hMinimum :
      correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight S =
        correctedConcreteObservationSelectionMinimumCost
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          hSelection := by

    simpa [
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost,
      ambientTargetObservationSelectionMinimumCost,
      hSelection
    ] using
      hCost

  exact
    observationSelection_exactPositiveAdditiveMinimum_is_additivePareto
      (z := z)
      hSelection
      hSU
      hMinimum
      hSelected

end AmbientPositiveAdditiveMinimumIsPareto


section ExactPositiveAdditiveParetoRankClassDefinition

variable (α : Type u)
variable (ι : Type v)
variable (M : Type w)
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Exact positive-additive rank represented by a Pareto-optimal selected
subset, together with a global scalar lower-bound certificate. -/
def CorrectedConcreteObservationSelectionExactPositiveAdditiveParetoRankClass
    (rank : Nat) :
    Set (Set (Word α)) :=
  {language |
    ∃ S : Finset ι,
      CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language
          S ∧
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S =
          rank ∧
        ∀ R : Finset ι,
          R ⊆ U →
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥R → M)
              (selectedObservationProduct obsFamily R)
              f →
          rank <=
            correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight R}

end ExactPositiveAdditiveParetoRankClassDefinition


section ExactPositiveAdditiveParetoRankClassMembership

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}
variable {language : Set (Word α)}
variable {rank : Nat}

/-- Exact membership theorem for the positive-additive Pareto-rank class. -/
theorem
    mem_observationSelectionExactPositiveAdditiveParetoRankClass_iff :
    language ∈
        CorrectedConcreteObservationSelectionExactPositiveAdditiveParetoRankClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          coordinateWeight
          U
          rank ↔
      ∃ S : Finset ι,
        CorrectedConcreteObservationSelectionParetoOptimal
            (z := z)
            obsFamily
            f
            (correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight)
            U
            language
            S ∧
          correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight S =
            rank ∧
          ∀ R : Finset ι,
            R ⊆ U →
            language ∈
              StartRootedCorrectedConcreteTargetClass
                (v := z)
                α
                (↥R → M)
                (selectedObservationProduct obsFamily R)
                f →
            rank <=
              correctedConcreteObservationSelectionPositiveAdditiveCost
                coordinateWeight R := by

  rfl

end ExactPositiveAdditiveParetoRankClassMembership


section WitnessClassEqualsParetoRankClass

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}

/-- The direct arbitrary-rank positive-additive witness class is exactly its
Pareto-certified refinement. -/
theorem
    exactPositiveAdditiveRankWitnessClass_eq_paretoRankClass
    (rank : Nat) :
    CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        coordinateWeight
        U
        rank =
      CorrectedConcreteObservationSelectionExactPositiveAdditiveParetoRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        coordinateWeight
        U
        rank := by

  ext language

  constructor

  · intro hWitness

    rcases hWitness with
      ⟨S,
        hSU,
        hCostDecomposition,
        hTarget,
        hMinimum⟩

    have hCost :
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S =
          rank := by

      simpa [
        correctedConcreteObservationSelectionPositiveAdditiveCost
      ] using
        hCostDecomposition

    have hPareto :
        CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language
          S := by

      refine
        ⟨hSU,
          hTarget,
          ?_⟩

      intro R hRU hRTarget hDominates

      have hStrictScalar :
          correctedConcreteObservationSelectionParetoScalarCost
              (correctedConcreteObservationSelectionAdditiveCost
                coordinateWeight)
              R <
            correctedConcreteObservationSelectionParetoScalarCost
              (correctedConcreteObservationSelectionAdditiveCost
                coordinateWeight)
              S :=
        observationSelection_strictDominance_implies_scalarCost_lt
          hDominates

      have hStrict :
          correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight R <
            correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight S := by

        simpa [
          observationSelectionPositiveAdditiveCost_eq_additiveParetoScalarCost
        ] using
          hStrictScalar

      have hLower :
          rank <=
            correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight R := by

        simpa [
          correctedConcreteObservationSelectionPositiveAdditiveCost
        ] using
          hMinimum
            R
            hRU
            hRTarget

      rw [hCost] at hStrict

      omega

    exact
      ⟨S,
        hPareto,
        hCost,
        fun R hRU hRTarget => by
          simpa [
            correctedConcreteObservationSelectionPositiveAdditiveCost
          ] using
            hMinimum
              R
              hRU
              hRTarget⟩

  · intro hParetoRank

    rcases hParetoRank with
      ⟨S,
        hPareto,
        hCost,
        hMinimum⟩

    exact
      ⟨S,
        hPareto.1,
        by
          simpa [
            correctedConcreteObservationSelectionPositiveAdditiveCost
          ] using hCost,
        hPareto.2.1,
        fun R hRU hRTarget => by
          simpa [
            correctedConcreteObservationSelectionPositiveAdditiveCost
          ] using
            hMinimum
              R
              hRU
              hRTarget⟩

end WitnessClassEqualsParetoRankClass


section ExactShellEqualsParetoRankClass

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}

/-- Every exact positive-additive scalar-rank shell is exactly the class of
targets having a Pareto-optimal exact-rank witness. -/
theorem
    positiveAdditiveExactCostRankClass_eq_paretoRankClass
    (rank : Nat) :
    CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        U
        rank =
      CorrectedConcreteObservationSelectionExactPositiveAdditiveParetoRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        coordinateWeight
        U
        rank := by

  calc
    CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        U
        rank =
      CorrectedConcreteObservationSelectionExactPositiveAdditiveRankWitnessClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        coordinateWeight
        U
        rank :=
          positiveAdditiveObservationSelectionExactRankClass_eq_witnessClass
            (z := z)
            rank

    _ =
      CorrectedConcreteObservationSelectionExactPositiveAdditiveParetoRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        coordinateWeight
        U
        rank :=
          exactPositiveAdditiveRankWitnessClass_eq_paretoRankClass
            (z := z)
            rank

end ExactShellEqualsParetoRankClass


section FinitePositiveAdditiveParetoRankValues

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)
variable (language : Set (Word α))

/-- Finite set of positive-additive scalar values achieved by the explicit
additive-cost Pareto frontier. -/
noncomputable def
    correctedConcreteObservationPositiveAdditiveParetoRankValues :
    Finset Nat := by

  classical

  exact
    (correctedConcreteObservationParetoSelections
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language).image
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)

/-- Exact membership theorem for finite Pareto scalar values. -/
theorem
    mem_correctedConcreteObservationPositiveAdditiveParetoRankValues_iff
    [DecidableEq ι]
    {rank : Nat} :
    rank ∈
        correctedConcreteObservationPositiveAdditiveParetoRankValues
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language ↔
      ∃ S : Finset ι,
        CorrectedConcreteObservationSelectionParetoOptimal
            (z := z)
            obsFamily
            f
            (correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight)
            U
            language
            S ∧
          rank =
            correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight S := by

  classical

  constructor

  · intro hRank

    rcases Finset.mem_image.mp hRank with
      ⟨S, hS, hEq⟩

    exact
      ⟨S,
        (mem_correctedConcreteObservationParetoSelections_iff
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language).mp
          hS,
        hEq.symm⟩

  · intro hRank

    rcases hRank with
      ⟨S, hPareto, hEq⟩

    exact
      Finset.mem_image.mpr
        ⟨S,
          (mem_correctedConcreteObservationParetoSelections_iff
            (z := z)
            obsFamily
            f
            (correctedConcreteObservationSelectionAdditiveCost
              coordinateWeight)
            U
            language).mpr
            hPareto,
          hEq.symm⟩

/-- The number of distinct positive-additive values on the Pareto frontier is
at most `2^|U|`. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankValues_card_le_two_pow
    [DecidableEq ι] :
    (correctedConcreteObservationPositiveAdditiveParetoRankValues
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language).card <=
      2 ^ U.card := by

  calc
    (correctedConcreteObservationPositiveAdditiveParetoRankValues
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language).card <=
      (correctedConcreteObservationParetoSelections
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language).card :=
          Finset.card_image_le

    _ <=
      2 ^ U.card :=
        correctedConcreteObservationParetoSelections_card_le_two_pow
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language

end FinitePositiveAdditiveParetoRankValues


section PositiveAdditiveParetoEnvelopeClassDefinition

variable (α : Type u)
variable (ι : Type v)
variable (M : Type w)
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Languages whose finite additive Pareto frontier achieves scalar value
`rank`, with `rank` minimal among all frontier values. -/
def CorrectedConcreteObservationSelectionPositiveAdditiveParetoEnvelopeRankClass
    (rank : Nat) :
    Set (Set (Word α)) :=
  {language |
    rank ∈
        correctedConcreteObservationPositiveAdditiveParetoRankValues
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language ∧
      ∀ value : Nat,
        value ∈
            correctedConcreteObservationPositiveAdditiveParetoRankValues
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language →
          rank <= value}

end PositiveAdditiveParetoEnvelopeClassDefinition


section ExactShellEqualsParetoEnvelopeClass

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable {obsFamily : ι → α → M}
variable {f : Nat}
variable {coordinateWeight : ι → Nat}
variable {U : Finset ι}

/-- Exact positive-additive rank is exactly the minimum scalar value on the
finite additive Pareto frontier. -/
theorem
    positiveAdditiveExactCostRankClass_eq_paretoEnvelopeRankClass
    (rank : Nat) :
    CorrectedConcreteObservationSelectionExactCostRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        (correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight)
        U
        rank =
      CorrectedConcreteObservationSelectionPositiveAdditiveParetoEnvelopeRankClass
        (z := z)
        α
        ι
        M
        obsFamily
        f
        coordinateWeight
        U
        rank := by

  ext language

  constructor

  · intro hExact

    have hParetoRank :
        language ∈
          CorrectedConcreteObservationSelectionExactPositiveAdditiveParetoRankClass
            (z := z)
            α
            ι
            M
            obsFamily
            f
            coordinateWeight
            U
            rank := by

      rw [
        ← positiveAdditiveExactCostRankClass_eq_paretoRankClass
            (z := z)
            rank
      ]

      exact hExact

    rcases hParetoRank with
      ⟨S,
        hPareto,
        hCost,
        hMinimum⟩

    refine
      ⟨(mem_correctedConcreteObservationPositiveAdditiveParetoRankValues_iff
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language).mpr
          ⟨S,
            hPareto,
            hCost.symm⟩,
        ?_⟩

    intro value hValue

    rcases
        (mem_correctedConcreteObservationPositiveAdditiveParetoRankValues_iff
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language).mp
          hValue with
      ⟨R, hRPareto, hValueEq⟩

    have hLower :=
      hMinimum
        R
        hRPareto.1
        hRPareto.2.1

    simpa [hValueEq] using
      hLower

  · intro hEnvelope

    rcases
        (mem_correctedConcreteObservationPositiveAdditiveParetoRankValues_iff
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language).mp
          hEnvelope.1 with
      ⟨S, hPareto, hRankEq⟩

    let hSelection :
        HasCorrectedConcreteObservationSelectionCost
          (obsFamily := obsFamily)
          (f := f)
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          U
          language :=
      ⟨rank,
        S,
        hPareto.1,
        by
          exact
            Nat.le_of_eq
              hRankEq.symm,
        hPareto.2.1⟩

    rcases hSelection.exists_selection_exact_minimumCost with
      ⟨T, hTU, hTCost, hTTarget⟩

    have hTPareto :
        CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language
          T :=
      observationSelection_exactPositiveAdditiveMinimum_is_additivePareto
        (z := z)
        hSelection
        hTU
        hTCost
        hTTarget

    have hMinimumValueMem :
        correctedConcreteObservationSelectionMinimumCost
            (correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight)
            hSelection ∈
          correctedConcreteObservationPositiveAdditiveParetoRankValues
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            language := by

      apply
        (mem_correctedConcreteObservationPositiveAdditiveParetoRankValues_iff
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language).mpr

      exact
        ⟨T,
          hTPareto,
          hTCost.symm⟩

    have hRankLeMinimum :
        rank <=
          correctedConcreteObservationSelectionMinimumCost
            (correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight)
            hSelection :=
      hEnvelope.2
        (correctedConcreteObservationSelectionMinimumCost
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          hSelection)
        hMinimumValueMem

    have hMinimumLeRank :
        correctedConcreteObservationSelectionMinimumCost
            (correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight)
            hSelection <=
          rank := by

      have hMinimumLeSelected :
          correctedConcreteObservationSelectionMinimumCost
              (correctedConcreteObservationSelectionPositiveAdditiveCost
                coordinateWeight)
              hSelection <=
            correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight S := by

        apply
          hSelection.minimumCost_le_of_selection

        exact
          ⟨S,
            hPareto.1,
            Nat.le_refl _,
            hPareto.2.1⟩

      omega

    have hRankEqMinimum :
        rank =
          correctedConcreteObservationSelectionMinimumCost
            (correctedConcreteObservationSelectionPositiveAdditiveCost
              coordinateWeight)
            hSelection :=
      Nat.le_antisymm
        hRankLeMinimum
        hMinimumLeRank

    exact
      (observationSelection_mem_exactCostRankClass_iff_rank_eq_minimum
        (z := z)
        hSelection
        rank).mpr
        hRankEqMinimum

end ExactShellEqualsParetoEnvelopeClass


section AmbientPositiveAdditiveParetoCertifiedSelection

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

/-- Every full-product target has an exact-rank selected subset that is Pareto
optimal for cardinality and additive coordinate weight, and carries its own
certified learner. -/
theorem
    ambientTarget_exists_positiveAdditiveRankParetoCertifiedSelection
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ∃
      (rank : Nat)
      (S : Finset ι)
      (hSelected :
        language ∈
          StartRootedCorrectedConcreteTargetClass
            (v := z)
            α
            (↥S → M)
            (selectedObservationProduct obsFamily S)
            f),
      rank =
          ambientTargetObservationSelectionPositiveAdditiveMinimumCost
            (z := z)
            obsFamily
            f
            coordinateWeight
            U
            hTarget ∧
        correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight S =
          rank ∧
        CorrectedConcreteObservationSelectionParetoOptimal
          (z := z)
          obsFamily
          f
          (correctedConcreteObservationSelectionAdditiveCost
            coordinateWeight)
          U
          language
          S ∧
        CorrectedConcreteObservationSelectionIrredundant
          (z := z)
          α
          ι
          M
          obsFamily
          f
          language
          S ∧
        (∀ index : ι,
          index ∈ S →
          CorrectedConcreteObservationRefinementEssential
            (z := z)
            α
            (↥(S.erase index) → M)
            (↥S → M)
            (selectedObservationProduct obsFamily (S.erase index))
            (selectedObservationProduct obsFamily S)
            f) ∧
        IdentifiesLanguageFromPositiveData
          (correctedConcreteCertifiedWorkingGrammarHypLanguage
            (selectedObservationProduct obsFamily S)
            f)
          (correctedConcreteCertifiedWorkingGrammarLearner
            hα
            (selectedObservationProduct obsFamily S)
            f)
          language ∧
        ∃
          C :
            CorrectedConcreteCertifiedWorkingGrammarHypothesis
              α
              (↥S → M)
              (selectedObservationProduct obsFamily S)
              f,
          C.output.grammar.StringLanguage =
              language ∧
            C.bits.length <=
              correctedConcreteCertifiedRankBitBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := z)
                  hα
                  (selectedObservationProduct obsFamily S)
                  f
                  hSelected)
                f ∧
            C.canonicalSearch.length <=
              correctedConcreteCertifiedRankSearchBudget
                (startRootedTargetCertifiedDescriptionRank
                  (v := z)
                  hα
                  (selectedObservationProduct obsFamily S)
                  f
                  hSelected)
                f := by

  rcases
      ambientTarget_exists_positiveAdditiveRankCertifiedSelection
        (z := z)
        hα
        obsFamily
        f
        coordinateWeight
        U
        hTarget with
    ⟨rank,
      S,
      hSelected,
      hRank,
      hSU,
      hCostDecomposition,
      hCardLe,
      hAdditiveLe,
      hRankWitness,
      hIrredundant,
      hEssential,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

  have hCost :
      correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight S =
        rank := by

    simpa [
      correctedConcreteObservationSelectionPositiveAdditiveCost
    ] using
      hCostDecomposition

  have hMinimumCost :
      correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight S =
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget := by

    rw [hCost, hRank]

  have hPareto :
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language
        S :=
    ambientTarget_positiveAdditiveMinimumSelection_is_additivePareto
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget
      hSU
      hMinimumCost
      hSelected

  exact
    ⟨rank,
      S,
      hSelected,
      hRank,
      hCost,
      hPareto,
      hIrredundant,
      hEssential,
      hIdentifies,
      C,
      hLanguage,
      hBits,
      hSearch⟩

end AmbientPositiveAdditiveParetoCertifiedSelection


section AmbientParetoRankEnvelope

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- The ambient positive-additive rank belongs to the finite Pareto scalar set
and is its minimum element. -/
theorem
    ambientTarget_positiveAdditiveRank_isMinimum_paretoRankValue
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget ∈
        correctedConcreteObservationPositiveAdditiveParetoRankValues
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language ∧
      ∀ value : Nat,
        value ∈
            correctedConcreteObservationPositiveAdditiveParetoRankValues
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language →
          ambientTargetObservationSelectionPositiveAdditiveMinimumCost
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              hTarget <=
            value := by

  let hSelection :=
    hasCorrectedConcreteObservationSelectionCost_of_fullProductTarget
      (obsFamily := obsFamily)
      (f := f)
      (correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight)
      hTarget

  rcases
      ambientTarget_exists_positiveAdditiveMinimumIrredundantSelection
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget with
    ⟨S,
      hSU,
      hCost,
      hIrredundant,
      hEssential⟩

  have hSelected :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥S → M)
          (selectedObservationProduct obsFamily S)
          f :=
    hIrredundant.1

  have hPareto :
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language
        S :=
    ambientTarget_positiveAdditiveMinimumSelection_is_additivePareto
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget
      hSU
      hCost
      hSelected

  refine
    ⟨(mem_correctedConcreteObservationPositiveAdditiveParetoRankValues_iff
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language).mpr
        ⟨S,
          hPareto,
          hCost.symm⟩,
      ?_⟩

  intro value hValue

  rcases
      (mem_correctedConcreteObservationPositiveAdditiveParetoRankValues_iff
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        language).mp
        hValue with
    ⟨R, hRPareto, hValueEq⟩

  have hMinimumLe :
      correctedConcreteObservationSelectionMinimumCost
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          hSelection <=
        correctedConcreteObservationSelectionPositiveAdditiveCost
          coordinateWeight R := by

    apply
      hSelection.minimumCost_le_of_selection

    exact
      ⟨R,
        hRPareto.1,
        Nat.le_refl _,
        hRPareto.2.1⟩

  simpa [
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost,
    ambientTargetObservationSelectionMinimumCost,
    hSelection,
    hValueEq
  ] using
    hMinimumLe

/-- The finite Pareto scalar-value set is nonempty for every full ambient
target. -/
theorem
    correctedConcreteObservationPositiveAdditiveParetoRankValues_nonempty_of_fullProductTarget
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    (correctedConcreteObservationPositiveAdditiveParetoRankValues
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language).Nonempty := by

  exact
    ⟨ambientTargetObservationSelectionPositiveAdditiveMinimumCost
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget,
      (ambientTarget_positiveAdditiveRank_isMinimum_paretoRankValue
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget).1⟩

/-- A strict positive-additive rank lower bound is equivalent to lying below
every finite Pareto scalar value. -/
theorem
    ambientTarget_positiveAdditiveRank_gt_iff_lt_all_paretoRankValues
    {language : Set (Word α)}
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f)
    (costBudget : Nat) :
    costBudget <
        ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget ↔
      ∀ value : Nat,
        value ∈
            correctedConcreteObservationPositiveAdditiveParetoRankValues
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language →
          costBudget < value := by

  let hEnvelope :=
    ambientTarget_positiveAdditiveRank_isMinimum_paretoRankValue
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

  constructor

  · intro hBudget value hValue

    exact
      lt_of_lt_of_le
        hBudget
        (hEnvelope.2
          value
          hValue)

  · intro hAll

    exact
      hAll
        (ambientTargetObservationSelectionPositiveAdditiveMinimumCost
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget)
        hEnvelope.1

end AmbientParetoRankEnvelope


section ParetoRankEnvelopeCertifiedPackage

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

/-- Final exact-shell/Pareto-envelope equality, finite envelope, obstruction,
and certified Pareto-rank witness package. -/
theorem
    correctedConcreteCertifiedWorkingGrammar_observationSelectionParetoRankEnvelope_package :
    (∀ rank : Nat,
      CorrectedConcreteObservationSelectionExactCostRankClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          (correctedConcreteObservationSelectionPositiveAdditiveCost
            coordinateWeight)
          U
          rank =
        CorrectedConcreteObservationSelectionPositiveAdditiveParetoEnvelopeRankClass
          (z := z)
          α
          ι
          M
          obsFamily
          f
          coordinateWeight
          U
          rank) ∧
      (∀
        language : Set (Word α),
        ∀ hTarget :
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥U → M)
              (selectedObservationProduct obsFamily U)
              f,
          (correctedConcreteObservationPositiveAdditiveParetoRankValues
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language).Nonempty ∧
            (correctedConcreteObservationPositiveAdditiveParetoRankValues
              (z := z)
              obsFamily
              f
              coordinateWeight
              U
              language).card <=
                2 ^ U.card ∧
            ambientTargetObservationSelectionPositiveAdditiveMinimumCost
                (z := z)
                obsFamily
                f
                coordinateWeight
                U
                hTarget ∈
              correctedConcreteObservationPositiveAdditiveParetoRankValues
                (z := z)
                obsFamily
                f
                coordinateWeight
                U
                language ∧
            ∀ value : Nat,
              value ∈
                  correctedConcreteObservationPositiveAdditiveParetoRankValues
                    (z := z)
                    obsFamily
                    f
                    coordinateWeight
                    U
                    language →
                ambientTargetObservationSelectionPositiveAdditiveMinimumCost
                    (z := z)
                    obsFamily
                    f
                    coordinateWeight
                    U
                    hTarget <=
                  value) ∧
      (∀
        language : Set (Word α),
        ∀ hTarget :
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥U → M)
              (selectedObservationProduct obsFamily U)
              f,
        ∀ costBudget : Nat,
          (costBudget <
              ambientTargetObservationSelectionPositiveAdditiveMinimumCost
                (z := z)
                obsFamily
                f
                coordinateWeight
                U
                hTarget ↔
            ∀ value : Nat,
              value ∈
                  correctedConcreteObservationPositiveAdditiveParetoRankValues
                    (z := z)
                    obsFamily
                    f
                    coordinateWeight
                    U
                    language →
                costBudget < value)) ∧
      (∀
        language : Set (Word α),
        ∀ hTarget :
          language ∈
            StartRootedCorrectedConcreteTargetClass
              (v := z)
              α
              (↥U → M)
              (selectedObservationProduct obsFamily U)
              f,
        ∃
          (rank : Nat)
          (S : Finset ι)
          (hSelected :
            language ∈
              StartRootedCorrectedConcreteTargetClass
                (v := z)
                α
                (↥S → M)
                (selectedObservationProduct obsFamily S)
                f),
          rank =
              ambientTargetObservationSelectionPositiveAdditiveMinimumCost
                (z := z)
                obsFamily
                f
                coordinateWeight
                U
                hTarget ∧
            correctedConcreteObservationSelectionPositiveAdditiveCost
                coordinateWeight S =
              rank ∧
            CorrectedConcreteObservationSelectionParetoOptimal
              (z := z)
              obsFamily
              f
              (correctedConcreteObservationSelectionAdditiveCost
                coordinateWeight)
              U
              language
              S ∧
            CorrectedConcreteObservationSelectionIrredundant
              (z := z)
              α
              ι
              M
              obsFamily
              f
              language
              S ∧
            IdentifiesLanguageFromPositiveData
              (correctedConcreteCertifiedWorkingGrammarHypLanguage
                (selectedObservationProduct obsFamily S)
                f)
              (correctedConcreteCertifiedWorkingGrammarLearner
                hα
                (selectedObservationProduct obsFamily S)
                f)
              language) := by

  refine
    ⟨?_,
      ?_,
      ?_,
      ?_⟩

  · intro rank

    exact
      positiveAdditiveExactCostRankClass_eq_paretoEnvelopeRankClass
        (z := z)
        rank

  · intro language hTarget

    let hEnvelope :=
      ambientTarget_positiveAdditiveRank_isMinimum_paretoRankValue
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget

    exact
      ⟨correctedConcreteObservationPositiveAdditiveParetoRankValues_nonempty_of_fullProductTarget
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          hTarget,
        correctedConcreteObservationPositiveAdditiveParetoRankValues_card_le_two_pow
          (z := z)
          obsFamily
          f
          coordinateWeight
          U
          language,
        hEnvelope.1,
        hEnvelope.2⟩

  · intro language hTarget costBudget

    exact
      ambientTarget_positiveAdditiveRank_gt_iff_lt_all_paretoRankValues
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget
        costBudget

  · intro language hTarget

    rcases
        ambientTarget_exists_positiveAdditiveRankParetoCertifiedSelection
          (z := z)
          hα
          obsFamily
          f
          coordinateWeight
          U
          hTarget with
      ⟨rank,
        S,
        hSelected,
        hRank,
        hCost,
        hPareto,
        hIrredundant,
        hEssential,
        hIdentifies,
        C,
        hLanguage,
        hBits,
        hSearch⟩

    exact
      ⟨rank,
        S,
        hSelected,
        hRank,
        hCost,
        hPareto,
        hIrredundant,
        hIdentifies⟩

end ParetoRankEnvelopeCertifiedPackage

end MCFG
