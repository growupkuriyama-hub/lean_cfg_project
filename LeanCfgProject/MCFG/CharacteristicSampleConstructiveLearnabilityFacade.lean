/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleConstructiveLearningTheorem

/-!
# CharacteristicSampleConstructiveLearnabilityFacade.lean

One-hundred-fourteenth clean Lean experiment for the fixed-observation MCFG
project.

`CharacteristicSampleConstructiveLearningTheorem.lean` packaged the final
constructive consequences:

```text
positive characteristic sample
+
eventual prefix exactness
+
Gold-style identification.
```

This file gives the shortest theorem-facing names for the constructive route.

The key facade names are:

```lean
ConstructivelyLearnableByFlatRoutes
ConstructivelyIdentifiedByReachableLearner
ConstructiveCharacteristicSampleAvailable
ConstructivePrefixExactIdentificationAvailable
```

The key theorem is:

```lean
constructivelyLearnableByFlatRoutes_identified
```

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ConstructiveLearnabilityFacade

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Short name: the target has one of the verified flat construction routes. -/
def ConstructivelyLearnableByFlatRoutes
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ExistsConstructiveFlatRoute G obs

/-- Short name: a finite positive characteristic sample is available at some
bound. -/
def ConstructiveCharacteristicSampleAvailable
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ExistsBoundedPositiveCharacteristicSample G obs

/-- Short name: prefix-exact identification is available at some bound. -/
def ConstructivePrefixExactIdentificationAvailable
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ExistsBoundedPrefixExactIdentification G obs

/-- Short name: the reachable learner identifies the target at some bound. -/
def ConstructivelyIdentifiedByReachableLearner
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ExistsBoundedReachableIdentification G obs

/-- Short name for the complete constructive conclusion package. -/
def ConstructiveLearnabilitySummary
    (G : WorkingMCFG N α) (obs : α → M) : Prop :=
  ConstructiveCharacteristicSampleAvailable G obs ∧
  ConstructivePrefixExactIdentificationAvailable G obs ∧
  ConstructivelyIdentifiedByReachableLearner G obs

/-- The short summary facade is definitionally supplied by the previous
consequence package. -/
theorem constructiveLearnabilitySummary_of_consequences
    (h : ConstructiveLearningConsequences G obs) :
    ConstructiveLearnabilitySummary G obs :=
  h

/-- The short summary facade implies the previous consequence package. -/
theorem consequences_of_constructiveLearnabilitySummary
    (h : ConstructiveLearnabilitySummary G obs) :
    ConstructiveLearningConsequences G obs :=
  h

/-- Constructive flat-route learnability gives the short summary conclusion. -/
theorem constructivelyLearnableByFlatRoutes_summary
    (h : ConstructivelyLearnableByFlatRoutes G obs) :
    ConstructiveLearnabilitySummary G obs :=
  constructiveLearnabilitySummary_of_consequences
    (trimmed_constructive_learning_consequences_of_constructive_flat_route h)

/-- Constructive flat-route learnability gives a finite positive characteristic
sample. -/
theorem constructivelyLearnableByFlatRoutes_characteristic_sample
    (h : ConstructivelyLearnableByFlatRoutes G obs) :
    ConstructiveCharacteristicSampleAvailable G obs :=
  (constructivelyLearnableByFlatRoutes_summary h).1

/-- Constructive flat-route learnability gives eventual prefix exactness. -/
theorem constructivelyLearnableByFlatRoutes_prefix_exact
    (h : ConstructivelyLearnableByFlatRoutes G obs) :
    ConstructivePrefixExactIdentificationAvailable G obs :=
  (constructivelyLearnableByFlatRoutes_summary h).2.1

/-- Constructive flat-route learnability gives Gold-style identification by the
reachable learner. -/
theorem constructivelyLearnableByFlatRoutes_identified
    (h : ConstructivelyLearnableByFlatRoutes G obs) :
    ConstructivelyIdentifiedByReachableLearner G obs :=
  (constructivelyLearnableByFlatRoutes_summary h).2.2

/-- Final constructive assumptions give the short learnability summary. -/
theorem constructiveAssumptions_summary
    (A :
      TrimmedPresentationConstructiveMainAssumptions
        (G := G) (obs := obs)) :
    ConstructiveLearnabilitySummary G obs :=
  constructiveLearnabilitySummary_of_consequences
    (trimmed_constructive_learning_consequences A)

/-- Final constructive assumptions give the short identification conclusion. -/
theorem constructiveAssumptions_identified
    (A :
      TrimmedPresentationConstructiveMainAssumptions
        (G := G) (obs := obs)) :
    ConstructivelyIdentifiedByReachableLearner G obs :=
  (constructiveAssumptions_summary A).2.2

/-- The route disjunction gives the short learnability summary. -/
theorem routeDisjunction_summary
    (h : ExistsFlatConstructionRouteDisjunction G obs) :
    ConstructiveLearnabilitySummary G obs :=
  constructiveLearnabilitySummary_of_consequences
    (trimmed_constructive_learning_consequences_of_route_disjunction h)

/-- The route disjunction gives the short identification conclusion. -/
theorem routeDisjunction_identified
    (h : ExistsFlatConstructionRouteDisjunction G obs) :
    ConstructivelyIdentifiedByReachableLearner G obs :=
  (routeDisjunction_summary h).2.2

/-- The any-flat facade gives the short learnability summary. -/
theorem anyFlatConstruction_summary
    (h : ExistsAnyFlatConstruction G obs) :
    ConstructiveLearnabilitySummary G obs :=
  constructiveLearnabilitySummary_of_consequences
    (trimmed_constructive_learning_consequences_of_any_flat h)

/-- The any-flat facade gives the short identification conclusion. -/
theorem anyFlatConstruction_identified
    (h : ExistsAnyFlatConstruction G obs) :
    ConstructivelyIdentifiedByReachableLearner G obs :=
  (anyFlatConstruction_summary h).2.2

end ConstructiveLearnabilityFacade


section ConstructiveLearnabilityFacadeTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Top-level short theorem: constructive flat-route learnability gives
identification by the reachable learner. -/
theorem trimmed_constructively_learnable_identified
    (h : ConstructivelyLearnableByFlatRoutes G obs) :
    ConstructivelyIdentifiedByReachableLearner G obs :=
  constructivelyLearnableByFlatRoutes_identified h

/-- Top-level short summary theorem: constructive flat-route learnability gives
all three constructive conclusions. -/
theorem trimmed_constructively_learnable_summary
    (h : ConstructivelyLearnableByFlatRoutes G obs) :
    ConstructiveLearnabilitySummary G obs :=
  constructivelyLearnableByFlatRoutes_summary h

/-- Top-level short theorem: constructive flat-route learnability gives a
positive characteristic sample. -/
theorem trimmed_constructively_learnable_characteristic_sample
    (h : ConstructivelyLearnableByFlatRoutes G obs) :
    ConstructiveCharacteristicSampleAvailable G obs :=
  constructivelyLearnableByFlatRoutes_characteristic_sample h

/-- Top-level short theorem: constructive flat-route learnability gives prefix
exactness. -/
theorem trimmed_constructively_learnable_prefix_exact
    (h : ConstructivelyLearnableByFlatRoutes G obs) :
    ConstructivePrefixExactIdentificationAvailable G obs :=
  constructivelyLearnableByFlatRoutes_prefix_exact h

/-- Top-level short theorem from final constructive assumptions. -/
theorem trimmed_constructive_assumptions_identified
    (A :
      TrimmedPresentationConstructiveMainAssumptions
        (G := G) (obs := obs)) :
    ConstructivelyIdentifiedByReachableLearner G obs :=
  constructiveAssumptions_identified A

/-- Top-level short theorem from the route disjunction. -/
theorem trimmed_route_disjunction_identified
    (h : ExistsFlatConstructionRouteDisjunction G obs) :
    ConstructivelyIdentifiedByReachableLearner G obs :=
  routeDisjunction_identified h

/-- Top-level short theorem from the any-flat facade. -/
theorem trimmed_any_flat_identified
    (h : ExistsAnyFlatConstruction G obs) :
    ConstructivelyIdentifiedByReachableLearner G obs :=
  anyFlatConstruction_identified h

end ConstructiveLearnabilityFacadeTopLevel

end MCFG
