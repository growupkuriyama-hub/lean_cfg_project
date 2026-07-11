/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleExactOnceFiniteDerivationalExposureRoute

/-!
# CharacteristicSampleExactOnceFiniteNonterminalDerivationalExposureRoute.lean

`CharacteristicSampleExactOnceFiniteDerivationalExposureRoute.lean` constructs
the finite anchor sample from `Finset.univ`, but its public statements require
a computational enumeration instance `[Fintype N]`.

For the paper, the natural presentation assumption is only that the
nonterminal type is finite.  This file weakens the public assumption to
`[Finite N]`.  A `Fintype` and decidable equality are installed internally by
classical choice, and the previously verified finite derivational-exposure
route is then reused unchanged.

Thus the paper-facing theorem no longer asks the caller to supply a particular
enumeration of the finite nonterminal set.
-/

namespace MCFG

universe u v w

section FiniteNonterminalDerivationalExposure

variable {N : Type v} {α : Type u} {M : Type w}
variable [Finite N]
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

namespace TrimmedPresentationDerivationalExposure

variable {D : TrimmedPresentationPreCoreData T f}

/-- Construct the finite grammar-rule data from the propositional finiteness of
the nonterminal type.

The particular `Fintype` enumeration and decidable equality on `N` are internal
implementation choices and do not occur in the theorem assumptions. -/
noncomputable def toFiniteDataOfFinite
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.BasicWorkingConditions) :
    TrimmedPresentationDerivationalExposureData D := by
  letI : Fintype N := Fintype.ofFinite N
  letI : DecidableEq N := Classical.decEq N
  exact E.toFiniteData hworking

/-- The concrete characteristic-sample candidate obtained from a finite
nonterminal type without requiring a caller-supplied enumeration. -/
noncomputable def finiteSampleOfFinite
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.BasicWorkingConditions) :
    Finset (Word α) :=
  (E.toFiniteDataOfFinite hworking).sample

/-- The automatically constructed sample is positive. -/
theorem finiteSampleOfFinite_positive
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.BasicWorkingConditions) :
    (E.finiteSampleOfFinite hworking : Set (Word α)) ⊆
      G.StringLanguage :=
  (E.toFiniteDataOfFinite hworking).sample_positive

/-- The automatically constructed sample contains all witness words required
by the trimmed pre-core. -/
theorem finiteSampleOfFinite_contains_witnesses
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.BasicWorkingConditions) :
    TrimmedPresentationWitnessWordSet D ⊆
      (E.finiteSampleOfFinite hworking : Set (Word α)) :=
  (E.toFiniteDataOfFinite hworking).contains_witnesses

/-- The generated finite positive sample is characteristic for the reachable
learner. -/
theorem finite_nonterminal_characteristic_sample
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      (E.finiteSampleOfFinite hworking.basic)
      G.StringLanguage :=
  (E.toFiniteDataOfFinite hworking.basic).exact_characteristic_sample
    hworking.2 hfan hL

/-- Exact reconstruction on every positive finite superset of the generated
sample. -/
theorem exact_for_positive_superset_of_finite_nonterminal_type
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hEK :
      (E.finiteSampleOfFinite hworking.basic : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  (E.toFiniteDataOfFinite hworking.basic).exact_for_positive_superset
    hworking.2 hfan hL hEK hKpos

/-- Eventual prefix-exact reconstruction from the propositional finiteness of
the nonterminal type. -/
theorem exact_prefix_reconstruction_of_finite_nonterminal_type
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (E.toFiniteDataOfFinite hworking.basic).exact_prefix_reconstruction
    hworking.2 hfan hL

/-- Gold identification from derivational exposure for a finite nonterminal
type, without a caller-supplied `Fintype` enumeration. -/
theorem identifies_from_positive_text_of_finite_nonterminal_type
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (E.toFiniteDataOfFinite hworking.basic).exact_identifies_from_positive_text
    hworking.2 hfan hL

/-- Corrected paper-facing identification theorem under the natural finite
nonterminal assumption `[Finite N]`.

No enumeration of `N`, finite cover, rule-arity package, unrestricted splicing
constructor, or unconditional exposing transport is supplied by the caller. -/
theorem finite_nonterminal_exact_working_paper_main_theorem
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  (E.toFiniteDataOfFinite hworking.basic).exact_working_paper_main_theorem
    hworking hfan hL

/-- Full characteristic-sample, prefix-exact, and identification conclusion
package under `[Finite N]`. -/
theorem finite_nonterminal_exact_working_paper_conclusion_package
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  (E.toFiniteDataOfFinite hworking.basic).
    exact_working_paper_conclusion_package hworking hfan hL

end TrimmedPresentationDerivationalExposure

end FiniteNonterminalDerivationalExposure


section FiniteNonterminalDerivationalExposureTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [Finite N]
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable paper-facing endpoint under the natural finite-nonterminal
assumption. -/
theorem trimmed_finite_nonterminal_derivational_exposure_exact_working_main_theorem
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  E.finite_nonterminal_exact_working_paper_main_theorem
    hworking hfan hL

/-- Stable full conclusion package under `[Finite N]`. -/
theorem trimmed_finite_nonterminal_derivational_exposure_exact_working_conclusion_package
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  E.finite_nonterminal_exact_working_paper_conclusion_package
    hworking hfan hL

end FiniteNonterminalDerivationalExposureTopLevel

end MCFG
