/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSamplePaperMainTheorem

/-!
# CharacteristicSamplePaperMainVariants.lean

Ninetieth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSamplePaperMainTheorem.lean` introduced the preferred paper-facing
assumption package:

```text
GrammarRuleBuilder
+ AnchorCommonContextTransport
+ splicing/fanout/promise.
```

This file records two useful paper-facing variants:

* direct exposing-context transport;
* stronger same-context transport.

These variants are not new results.  They are facades over the already verified
transport targets, intended for use in the paper, appendix, and formalization
status file.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PaperExposingAssumptions

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Paper-facing variant using direct exposing-context transport. -/
structure TrimmedPresentationPaperExposingAssumptions
    (D : TrimmedPresentationPreCoreData T f) where
  builder : TrimmedPresentationGrammarRuleBuilder D
  exposingTransport : TrimmedPresentationExposingContextTransport D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationPaperExposingAssumptions

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert the paper-facing exposing assumptions to the verified exposing
transport target. -/
def toGrammarBuilderExposingTransportTarget
    (A : TrimmedPresentationPaperExposingAssumptions D) :
    TrimmedPresentationGrammarBuilderExposingTransportTarget D where
  builder := A.builder
  exposingTransport := A.exposingTransport
  splicingConstructor := A.splicingConstructor
  fanout := A.fanout
  promise := A.promise

/-- The finite sample constructed by the exposing target. -/
noncomputable def sample
    (A : TrimmedPresentationPaperExposingAssumptions D) :
    Finset (Word α) :=
  A.toGrammarBuilderExposingTransportTarget.sample

/-- The constructed sample is positive. -/
theorem sample_positive
    (A : TrimmedPresentationPaperExposingAssumptions D) :
    (A.sample : Set (Word α)) ⊆ G.StringLanguage :=
  A.toGrammarBuilderExposingTransportTarget.sample_positive

/-- The constructed sample contains all trimmed-presentation witness words. -/
theorem contains_witnesses
    (A : TrimmedPresentationPaperExposingAssumptions D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (A.sample : Set (Word α)) :=
  A.toGrammarBuilderExposingTransportTarget.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (A : TrimmedPresentationPaperExposingAssumptions D) :
    FinalReachableData G A.sample obs f :=
  A.toGrammarBuilderExposingTransportTarget.toFinalReachableData

/-- The constructed sample is characteristic for the reachable learner. -/
theorem characteristic_sample
    (A : TrimmedPresentationPaperExposingAssumptions D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      A.sample
      G.StringLanguage :=
  A.toGrammarBuilderExposingTransportTarget.characteristic_sample

/-- Existence form for a positive characteristic sample from direct exposing
transport. -/
theorem exists_positive_characteristic_sample
    (A : TrimmedPresentationPaperExposingAssumptions D) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  ⟨A.sample, A.sample_positive, A.characteristic_sample⟩

/-- Exact reconstruction from every positive finite superset of the constructed
sample. -/
theorem exact_for_positive_superset
    (A : TrimmedPresentationPaperExposingAssumptions D)
    {K : Finset (Word α)}
    (hAK : (A.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  A.toGrammarBuilderExposingTransportTarget.exact_for_positive_superset hAK hKpos

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (A : TrimmedPresentationPaperExposingAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  A.toGrammarBuilderExposingTransportTarget.prefix_exact_eventually

/-- Gold-style identification in the limit from every positive text. -/
theorem identifies_from_positive_text
    (A : TrimmedPresentationPaperExposingAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  A.toGrammarBuilderExposingTransportTarget.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (A : TrimmedPresentationPaperExposingAssumptions D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  A.identifies_from_positive_text Ttxt

end TrimmedPresentationPaperExposingAssumptions

end PaperExposingAssumptions


section PaperSameContextAssumptions

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Paper-facing variant using the stronger same-context transport assumption. -/
structure TrimmedPresentationPaperSameContextAssumptions
    (D : TrimmedPresentationPreCoreData T f) where
  builder : TrimmedPresentationGrammarRuleBuilder D
  sameContextTransport : TrimmedPresentationSameContextTransport D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationPaperSameContextAssumptions

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert the paper-facing same-context assumptions to the verified
same-context transport target. -/
def toGrammarBuilderSameContextTransportTarget
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    TrimmedPresentationGrammarBuilderSameContextTransportTarget D where
  builder := A.builder
  sameContextTransport := A.sameContextTransport
  splicingConstructor := A.splicingConstructor
  fanout := A.fanout
  promise := A.promise

/-- Same-context assumptions also give direct exposing assumptions. -/
def toPaperExposingAssumptions
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    TrimmedPresentationPaperExposingAssumptions D where
  builder := A.builder
  exposingTransport :=
    TrimmedPresentationExposingContextTransport.ofSameContextTransport
      A.sameContextTransport
  splicingConstructor := A.splicingConstructor
  fanout := A.fanout
  promise := A.promise

/-- The finite sample constructed by the same-context target. -/
noncomputable def sample
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    Finset (Word α) :=
  A.toGrammarBuilderSameContextTransportTarget.sample

/-- The constructed sample is positive. -/
theorem sample_positive
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    (A.sample : Set (Word α)) ⊆ G.StringLanguage :=
  A.toGrammarBuilderSameContextTransportTarget.sample_positive

/-- The constructed sample contains all trimmed-presentation witness words. -/
theorem contains_witnesses
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (A.sample : Set (Word α)) :=
  A.toGrammarBuilderSameContextTransportTarget.contains_witnesses

/-- Convert directly to final reachable data. -/
noncomputable def toFinalReachableData
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    FinalReachableData G A.sample obs f :=
  A.toGrammarBuilderSameContextTransportTarget.toFinalReachableData

/-- The constructed sample is characteristic for the reachable learner. -/
theorem characteristic_sample
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      A.sample
      G.StringLanguage :=
  A.toGrammarBuilderSameContextTransportTarget.characteristic_sample

/-- Existence form for a positive characteristic sample from same-context
transport. -/
theorem exists_positive_characteristic_sample
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  ⟨A.sample, A.sample_positive, A.characteristic_sample⟩

/-- Exact reconstruction from every positive finite superset of the constructed
sample. -/
theorem exact_for_positive_superset
    (A : TrimmedPresentationPaperSameContextAssumptions D)
    {K : Finset (Word α)}
    (hAK : (A.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  A.toGrammarBuilderSameContextTransportTarget.exact_for_positive_superset hAK hKpos

/-- Exact reconstruction at a prefix containing the constructed sample. -/
theorem exact_at_seen_prefix
    (A : TrimmedPresentationPaperSameContextAssumptions D)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (A.sample : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  A.toGrammarBuilderSameContextTransportTarget.exact_at_seen_prefix Ttxt hseen

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  A.toGrammarBuilderSameContextTransportTarget.prefix_exact_eventually

/-- Gold-style identification in the limit from every positive text. -/
theorem identifies_from_positive_text
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  A.toGrammarBuilderSameContextTransportTarget.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (A : TrimmedPresentationPaperSameContextAssumptions D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  A.identifies_from_positive_text Ttxt

end TrimmedPresentationPaperSameContextAssumptions

end PaperSameContextAssumptions


section PaperVariantTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Paper-facing exposing-variant characteristic-sample theorem. -/
theorem trimmed_paper_exposing_exists_positive_characteristic_sample
    (A : TrimmedPresentationPaperExposingAssumptions D) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  A.exists_positive_characteristic_sample

/-- Paper-facing exposing-variant Gold identification theorem. -/
theorem trimmed_paper_exposing_main_theorem
    (A : TrimmedPresentationPaperExposingAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  A.identifies_from_positive_text

/-- Paper-facing exposing-variant prefix-exact theorem. -/
theorem trimmed_paper_exposing_prefix_exact_eventually
    (A : TrimmedPresentationPaperExposingAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  A.prefix_exact_eventually

/-- Paper-facing same-context-variant characteristic-sample theorem. -/
theorem trimmed_paper_same_context_exists_positive_characteristic_sample
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  A.exists_positive_characteristic_sample

/-- Paper-facing same-context-variant Gold identification theorem. -/
theorem trimmed_paper_same_context_main_theorem
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  A.identifies_from_positive_text

/-- Paper-facing same-context-variant prefix-exact theorem. -/
theorem trimmed_paper_same_context_prefix_exact_eventually
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  A.prefix_exact_eventually

/-- Same-context assumptions imply the exposing-variant theorem through the
canonical same-to-exposing conversion. -/
theorem trimmed_paper_same_context_main_theorem_via_exposing
    (A : TrimmedPresentationPaperSameContextAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  A.toPaperExposingAssumptions.identifies_from_positive_text

end PaperVariantTheorems

end MCFG
