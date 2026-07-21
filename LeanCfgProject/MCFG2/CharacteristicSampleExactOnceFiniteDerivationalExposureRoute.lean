/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleExactOnceDerivationalExposureRoute

/-!
# CharacteristicSampleExactOnceFiniteDerivationalExposureRoute.lean

The preceding derivational-exposure route still asked the caller to package:

* a finite set containing every base nonterminal;
* terminal-rule arity proofs;
* start-rule arity proofs.

For an ordinary finite grammar these are not genuine semantic assumptions.
When the nonterminal type is finite, the covering set is `Finset.univ`; and the
arity proofs are projections of `WorkingMCFG.BasicWorkingConditions`.

This file performs those constructions explicitly.  The resulting corrected
paper-facing route requires only:

* paper-faithful derivational exposure;
* exact working conditions;
* a fan-out bound;
* fixed-observation tuple substitutability.

The false unrestricted `NamedContextSplicingConstructor` and the overly strong
unconditional exposing-transport premise are not used.
-/

namespace MCFG

universe u v w

section FiniteDerivationalExposure

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq N] [Fintype N]
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- The rule-arity selectors required by the finite witness builder are already
contained in the ordinary working-grammar side conditions. -/
def trimmedRuleAritySelectorsOfBasicWorkingConditions
    (D : TrimmedPresentationPreCoreData T f)
    (hworking : G.BasicWorkingConditions) :
    TrimmedPresentationRuleAritySelectors D where
  terminal_arity := by
    intro ρ hρ
    exact hworking.2.2.1 ρ hρ

  start_arity := by
    intro ρ hρ
    exact hworking.2.1 ρ hρ

namespace TrimmedPresentationDerivationalExposure

variable {D : TrimmedPresentationPreCoreData T f}

/-- Package derivational exposure into the finite grammar-rule data used by the
exact-once characteristic-sample route.

The finite base-nonterminal cover is constructed as `Finset.univ`, and the rule
arity selectors are extracted from the basic working conditions. -/
def toFiniteData
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.BasicWorkingConditions) :
    TrimmedPresentationDerivationalExposureData D where
  baseNonterminals := Finset.univ
  base_covers := by
    intro A
    simp
  arities := trimmedRuleAritySelectorsOfBasicWorkingConditions D hworking
  semantics := E

/-- The concrete finite witness sample associated with derivational exposure. -/
def finiteSample
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.BasicWorkingConditions) :
    Finset (Word α) :=
  (E.toFiniteData hworking).sample

/-- The automatically generated finite sample is positive. -/
theorem finiteSample_positive
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.BasicWorkingConditions) :
    (E.finiteSample hworking : Set (Word α)) ⊆ G.StringLanguage :=
  (E.toFiniteData hworking).sample_positive

/-- The automatically generated finite sample contains every witness word
required by the trimmed pre-core. -/
theorem finiteSample_contains_witnesses
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.BasicWorkingConditions) :
    TrimmedPresentationWitnessWordSet D ⊆
      (E.finiteSample hworking : Set (Word α)) :=
  (E.toFiniteData hworking).contains_witnesses

/-- Exact reconstruction on every positive finite superset of the automatically
generated sample. -/
theorem exact_for_positive_superset_of_finite_nonterminals
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hEK :
      (E.finiteSample hworking.basic : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  (E.toFiniteData hworking.basic).exact_for_positive_superset
    hworking.2 hfan hL hEK hKpos

/-- Eventual prefix-exact reconstruction on every positive text, with the
finite grammar data generated automatically. -/
theorem exact_prefix_reconstruction_of_finite_nonterminals
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (E.toFiniteData hworking.basic).exact_prefix_reconstruction
    hworking.2 hfan hL

/-- Gold identification for finite-nonterminal exact working grammars from the
paper-faithful derivational exposure invariant. -/
theorem identifies_from_positive_text_of_finite_nonterminals
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (E.toFiniteData hworking.basic).exact_identifies_from_positive_text
    hworking.2 hfan hL

/-- Paper-facing characteristic-sample conclusion with the finite grammar data
constructed internally. -/
theorem finite_exact_working_characteristic_sample_theorem
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveCharacteristicSampleConclusion G obs :=
  (E.toFiniteData hworking.basic).exact_paper_characteristic_sample_theorem
    hworking.2 hfan hL

/-- Paper-facing eventual prefix-exact conclusion with all finite grammar data
constructed internally. -/
theorem finite_exact_working_prefix_exact_theorem
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructivePrefixExactConclusion G obs :=
  (E.toFiniteData hworking.basic).exact_paper_prefix_exact_theorem
    hworking.2 hfan hL

/-- Corrected paper-facing identification theorem for finite-nonterminal exact
working grammars.

No finite cover, arity-selector package, unrestricted splicing constructor, or
unconditional exposing transport is supplied by the caller. -/
theorem finite_exact_working_paper_main_theorem
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  (E.toFiniteData hworking.basic).exact_working_paper_main_theorem
    hworking hfan hL

/-- Full paper-facing learning conclusion package for finite-nonterminal exact
working grammars. -/
theorem finite_exact_working_paper_conclusion_package
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  (E.toFiniteData hworking.basic).exact_working_paper_conclusion_package
    hworking hfan hL

end TrimmedPresentationDerivationalExposure

end FiniteDerivationalExposure


section FiniteDerivationalExposureTopLevel

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq N] [Fintype N]
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable corrected endpoint requiring only derivational exposure and the
paper's ordinary finite exact-working assumptions. -/
theorem trimmed_finite_derivational_exposure_exact_working_main_theorem
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  E.finite_exact_working_paper_main_theorem hworking hfan hL

/-- Stable full conclusion package for the finite derivational-exposure route. -/
theorem trimmed_finite_derivational_exposure_exact_working_conclusion_package
    (E : TrimmedPresentationDerivationalExposure D)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  E.finite_exact_working_paper_conclusion_package hworking hfan hL

end FiniteDerivationalExposureTopLevel

end MCFG
