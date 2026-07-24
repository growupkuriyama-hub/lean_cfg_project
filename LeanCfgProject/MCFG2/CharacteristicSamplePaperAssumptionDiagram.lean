/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSamplePaperMainVariants

/-!
# CharacteristicSamplePaperAssumptionDiagram.lean

Ninety-first clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSamplePaperMainTheorem.lean` and
`CharacteristicSamplePaperMainVariants.lean` introduced three paper-facing
assumption packages:

* `TrimmedPresentationPaperMainAssumptions`;
* `TrimmedPresentationPaperExposingAssumptions`;
* `TrimmedPresentationPaperSameContextAssumptions`.

This file records the paper-facing conversion diagram between them.

The main conversion in this file is:

```text
PaperMainAssumptions
⇒ PaperExposingAssumptions.
```

That is, the preferred common-context assumption package also gives the direct
exposing-transport variant, through the already verified common-to-exposing
transport route.

No new mathematical principle is introduced here.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PaperAssumptionDiagram

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

namespace TrimmedPresentationPaperMainAssumptions

/-- The preferred paper main assumptions also provide the paper exposing
variant, via the common-context-to-exposing transport route. -/
def toPaperExposingAssumptions
    (A : TrimmedPresentationPaperMainAssumptions D) :
    TrimmedPresentationPaperExposingAssumptions D where
  builder := A.builder
  exposingTransport :=
    (A.toGrammarBuilderCommonTransportTarget.toExposingTransportObligations).exposingTransport
  splicingConstructor := A.splicingConstructor
  fanout := A.fanout
  promise := A.promise

/-- The preferred paper main assumptions identify through the exposing variant. -/
theorem identifies_from_positive_text_via_exposing
    (A : TrimmedPresentationPaperMainAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  A.toPaperExposingAssumptions.identifies_from_positive_text

/-- Prefix exactness through the exposing variant. -/
theorem prefix_exact_eventually_via_exposing
    (A : TrimmedPresentationPaperMainAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  A.toPaperExposingAssumptions.prefix_exact_eventually

/-- A positive characteristic sample obtained through the exposing variant. -/
theorem exists_positive_characteristic_sample_via_exposing
    (A : TrimmedPresentationPaperMainAssumptions D) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  A.toPaperExposingAssumptions.exists_positive_characteristic_sample

/-- Finite positive-superset exactness through the exposing variant. -/
theorem exact_for_positive_superset_via_exposing
    (A : TrimmedPresentationPaperMainAssumptions D)
    {K : Finset (Word α)}
    (hAK :
      (A.toPaperExposingAssumptions.sample : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  A.toPaperExposingAssumptions.exact_for_positive_superset hAK hKpos

end TrimmedPresentationPaperMainAssumptions


namespace TrimmedPresentationPaperSameContextAssumptions

/-- Same-context paper assumptions identify through the exposing variant.  This
is the paper-facing counterpart of the same-to-exposing target diagram. -/
theorem identifies_from_positive_text_via_exposing
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  A.toPaperExposingAssumptions.identifies_from_positive_text

/-- Same-context paper assumptions are prefix-exact through the exposing
variant. -/
theorem prefix_exact_eventually_via_exposing
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  A.toPaperExposingAssumptions.prefix_exact_eventually

/-- Same-context paper assumptions provide a positive characteristic sample
through the exposing variant. -/
theorem exists_positive_characteristic_sample_via_exposing
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  A.toPaperExposingAssumptions.exists_positive_characteristic_sample

/-- Same-context paper assumptions give finite positive-superset exactness
through the exposing variant. -/
theorem exact_for_positive_superset_via_exposing
    (A : TrimmedPresentationPaperSameContextAssumptions D)
    {K : Finset (Word α)}
    (hAK :
      (A.toPaperExposingAssumptions.sample : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  A.toPaperExposingAssumptions.exact_for_positive_superset hAK hKpos

end TrimmedPresentationPaperSameContextAssumptions

end PaperAssumptionDiagram


section PaperDiagramTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Paper-facing diagram theorem: the preferred common-context assumptions
identify through the exposing variant. -/
theorem trimmed_paper_main_via_exposing_theorem
    (A : TrimmedPresentationPaperMainAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  A.identifies_from_positive_text_via_exposing

/-- Paper-facing diagram theorem: the preferred common-context assumptions are
prefix-exact through the exposing variant. -/
theorem trimmed_paper_main_via_exposing_prefix_exact
    (A : TrimmedPresentationPaperMainAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  A.prefix_exact_eventually_via_exposing

/-- Paper-facing diagram theorem: the preferred common-context assumptions
produce a positive characteristic sample through the exposing variant. -/
theorem trimmed_paper_main_via_exposing_exists_positive_characteristic_sample
    (A : TrimmedPresentationPaperMainAssumptions D) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  A.exists_positive_characteristic_sample_via_exposing

/-- Paper-facing diagram theorem: same-context assumptions identify through the
exposing variant. -/
theorem trimmed_paper_same_context_via_exposing_theorem
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  A.identifies_from_positive_text_via_exposing

/-- Paper-facing diagram theorem: same-context assumptions are prefix-exact
through the exposing variant. -/
theorem trimmed_paper_same_context_via_exposing_prefix_exact
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  A.prefix_exact_eventually_via_exposing

/-- Paper-facing diagram theorem: same-context assumptions produce a positive
characteristic sample through the exposing variant. -/
theorem trimmed_paper_same_context_via_exposing_exists_positive_characteristic_sample
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  A.exists_positive_characteristic_sample_via_exposing

end PaperDiagramTheorems

end MCFG
