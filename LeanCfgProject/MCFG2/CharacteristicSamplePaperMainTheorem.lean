/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleSemanticMainTheorems

/-!
# CharacteristicSamplePaperMainTheorem.lean

Eighty-ninth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleSemanticMainTheorems.lean` collected theorem-facing names
for the semantic target hierarchy.  This file gives the paper-facing final
entry point.

The preferred assumption package is renamed as

```lean
TrimmedPresentationPaperMainAssumptions D
```

with fields:

* `builder : TrimmedPresentationGrammarRuleBuilder D`;
* `commonTransport : TrimmedPresentationAnchorCommonContextTransport D`;
* `splicingConstructor : NamedContextSplicingConstructor α`;
* fanout and fixed-observation substitutability promises.

From this package we expose the final theorem in three equivalent forms:

1. a concrete finite characteristic sample;
2. prefix-exact reconstruction on every positive text;
3. Gold-style eventual correctness on every positive text.

No new mathematical principle is introduced here.  This file is a clean
paper-level facade over the already verified semantic target.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PaperMainAssumptions

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- Paper-facing assumption package for the preferred final theorem.

This is only a renamed facade over
`TrimmedPresentationGrammarBuilderCommonTransportTarget`, but it is easier to
cite in the paper and in the formalization status document. -/
structure TrimmedPresentationPaperMainAssumptions
    (D : TrimmedPresentationPreCoreData T f) where
  builder : TrimmedPresentationGrammarRuleBuilder D
  commonTransport : TrimmedPresentationAnchorCommonContextTransport D
  splicingConstructor : NamedContextSplicingConstructor α
  fanout : G.FanoutAtMost f
  promise : FixedNamedTupleSubstitutable f obs G.StringLanguage

namespace TrimmedPresentationPaperMainAssumptions

variable {D : TrimmedPresentationPreCoreData T f}

/-- Convert the paper-facing assumptions to the preferred semantic target. -/
def toGrammarBuilderCommonTransportTarget
    (A : TrimmedPresentationPaperMainAssumptions D) :
    TrimmedPresentationGrammarBuilderCommonTransportTarget D where
  builder := A.builder
  commonTransport := A.commonTransport
  splicingConstructor := A.splicingConstructor
  fanout := A.fanout
  promise := A.promise

/-- The finite sample constructed by the preferred target. -/
def sample
    (A : TrimmedPresentationPaperMainAssumptions D) :
    Finset (Word α) :=
  A.toGrammarBuilderCommonTransportTarget.sample

/-- The constructed sample is positive for the target language. -/
theorem sample_positive
    (A : TrimmedPresentationPaperMainAssumptions D) :
    (A.sample : Set (Word α)) ⊆ G.StringLanguage :=
  A.toGrammarBuilderCommonTransportTarget.sample_positive

/-- The constructed sample contains all witness words required by the trimmed
presentation. -/
theorem contains_witnesses
    (A : TrimmedPresentationPaperMainAssumptions D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (A.sample : Set (Word α)) :=
  A.toGrammarBuilderCommonTransportTarget.contains_witnesses

/-- Convert directly to final reachable data. -/
def toFinalReachableData
    (A : TrimmedPresentationPaperMainAssumptions D) :
    FinalReachableData G A.sample obs f :=
  A.toGrammarBuilderCommonTransportTarget.toFinalReachableData

/-- The constructed finite positive sample is characteristic for the reachable
learner. -/
theorem characteristic_sample
    (A : TrimmedPresentationPaperMainAssumptions D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      A.sample
      G.StringLanguage :=
  A.toGrammarBuilderCommonTransportTarget.characteristic_sample

/-- Existence form: there exists a finite positive characteristic sample.

This is the most compact paper-facing characteristic-sample statement. -/
theorem exists_positive_characteristic_sample
    (A : TrimmedPresentationPaperMainAssumptions D) :
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
    (A : TrimmedPresentationPaperMainAssumptions D)
    {K : Finset (Word α)}
    (hAK : (A.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  A.toGrammarBuilderCommonTransportTarget
    .exact_for_positive_superset hAK hKpos

/-- Exact reconstruction at a positive-text prefix containing the constructed
sample. -/
theorem exact_at_seen_prefix
    (A : TrimmedPresentationPaperMainAssumptions D)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (A.sample : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage :=
  A.toGrammarBuilderCommonTransportTarget
    .toCommonContextTransportObligations
    .exact_at_seen_prefix Ttxt hseen

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem prefix_exact_eventually
    (A : TrimmedPresentationPaperMainAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  A.toGrammarBuilderCommonTransportTarget.prefix_exact_eventually

/-- Gold-style identification in the limit from every positive text. -/
theorem identifies_from_positive_text
    (A : TrimmedPresentationPaperMainAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  A.toGrammarBuilderCommonTransportTarget.identifies_from_positive_text

/-- Pointwise eventual correctness on one positive text. -/
theorem eventually_correct_on_text
    (A : TrimmedPresentationPaperMainAssumptions D)
    (Ttxt : TextFor G.StringLanguage) :
    EventuallyCorrectOnText
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      Ttxt :=
  A.identifies_from_positive_text Ttxt

end TrimmedPresentationPaperMainAssumptions

end PaperMainAssumptions


section PaperMainTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Paper-facing characteristic-sample theorem: the assumptions produce a finite
positive characteristic sample. -/
theorem trimmed_paper_main_exists_positive_characteristic_sample
    (A : TrimmedPresentationPaperMainAssumptions D) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CharacteristicSample
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        S
        G.StringLanguage :=
  A.exists_positive_characteristic_sample

/-- Paper-facing finite positive-superset exactness theorem. -/
theorem trimmed_paper_main_exact_for_positive_superset
    (A : TrimmedPresentationPaperMainAssumptions D)
    {K : Finset (Word α)}
    (hAK : (A.sample : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  A.exact_for_positive_superset hAK hKpos

/-- Paper-facing prefix-exact theorem. -/
theorem trimmed_paper_main_prefix_exact_eventually
    (A : TrimmedPresentationPaperMainAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  A.prefix_exact_eventually

/-- Paper-facing Gold identification theorem. -/
theorem trimmed_paper_main_identifies_from_positive_text
    (A : TrimmedPresentationPaperMainAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  A.identifies_from_positive_text

/-- The preferred one-line theorem name for the formalization status file. -/
theorem trimmed_paper_main_theorem
    (A : TrimmedPresentationPaperMainAssumptions D) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  trimmed_paper_main_identifies_from_positive_text A

end PaperMainTheorems

end MCFG
