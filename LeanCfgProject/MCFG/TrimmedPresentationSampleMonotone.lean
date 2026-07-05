/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.TrimmedPresentationSample

/-!
# TrimmedPresentationSampleMonotone.lean

Forty-fourth clean Lean experiment for the fixed-observation MCFG project.

`TrimmedPresentationSample.lean` packaged the finite sample membership data
needed to turn a trimmed-presentation pre-core into the reachable theorem
interface.

This file proves monotonicity of that package.

If a finite sample `S` contains all anchor, terminal, binary, start, and
distinguished start-word witnesses required by a trimmed-presentation pre-core,
then every larger positive finite sample `K` contains the same witnesses.

Consequently, the final reachable identification and prefix-exact
reconstruction theorems can be applied after transporting the same data from
`S` to any positive finite superset `K`.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section TrimmedPresentationSampleMonotone

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S K : Finset (Word α)}

namespace TrimmedPresentationSampleData

/-- Trimmed-presentation sample data is monotone in the finite sample. -/
def mono
    (H : TrimmedPresentationSampleData D S)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    TrimmedPresentationSampleData D K where
  sample_positive := hKpos
  anchor_mem := by
    intro A
    exact hSK (H.anchor_mem A)
  terminal_mem := by
    intro ρ hρ hwt
    exact hSK (H.terminal_mem ρ hρ hwt)
  binary_mem := by
    intro ρ hρ
    exact hSK (H.binary_mem ρ hρ)
  start_mem := by
    intro ρ hρ hwt
    exact hSK (H.start_mem ρ hρ hwt)
  startWord_mem := hSK H.startWord_mem

@[simp] theorem mono_sample_positive
    (H : TrimmedPresentationSampleData D S)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (H.mono hSK hKpos).sample_positive = hKpos :=
  rfl

/-- Monotonicity agrees with the reachable finite-sample package conversion. -/
theorem toReachablePreCoreFiniteSample_mono
    (H : TrimmedPresentationSampleData D S)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (H.mono hSK hKpos).toReachablePreCoreFiniteSample =
      H.toReachablePreCoreFiniteSample.mono hSK hKpos := by
  rfl

/-- Monotonicity agrees with the finite splicing-package conversion. -/
theorem toSplicingPackage_mono
    (H : TrimmedPresentationSampleData D S)
    (U : NamedContextSplicingConstructor α)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (H.mono hSK hKpos).toSplicingPackage U =
      (H.toSplicingPackage U).mono hSK hKpos := by
  rfl

/-- The monotone trimmed sample data gives exact reconstruction on the larger
positive finite sample. -/
theorem exact_after_mono
    (H : TrimmedPresentationSampleData D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  ((H.mono hSK hKpos).toFinalReachableData U hfan hL).exact_for_positive_superset
    (fun word hword => hword) hKpos

/-- At a positive-text prefix containing `S`, monotonicity transports the
trimmed sample data to that prefix and yields exact reconstruction. -/
theorem exact_at_prefix_via_mono
    (H : TrimmedPresentationSampleData D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (Ttxt : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (S : Set (Word α)) ⊆
      (Ttxt.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
      G.StringLanguage := by
  have hKpos :
      (Ttxt.prefixSample n : Set (Word α)) ⊆ G.StringLanguage := by
    intro word hword
    exact Ttxt.prefixSample_subset n hword
  exact H.exact_after_mono U hfan hL hseen hKpos

/-- Eventual prefix-exact reconstruction derived directly from monotonicity of
trimmed-presentation sample data. -/
theorem prefix_exact_via_mono
    (H : TrimmedPresentationSampleData D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage := by
  intro Ttxt
  rcases Ttxt.eventuallyContains_of_subset S
      H.sample_positive with ⟨n0, hcontains⟩
  refine ⟨n0, ?_⟩
  intro n hn
  exact H.exact_at_prefix_via_mono U hfan hL Ttxt (hcontains n hn)

/-- Reachable Gold identification derived directly from monotonicity of
trimmed-presentation sample data. -/
theorem identifies_via_mono
    (H : TrimmedPresentationSampleData D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt := by
  intro Ttxt
  rcases H.prefix_exact_via_mono U hfan hL Ttxt with ⟨n0, hcorr⟩
  refine ⟨n0, ?_⟩
  intro n hn
  simpa [reachableHypLanguage, reachableSampleLearner] using hcorr n hn

end TrimmedPresentationSampleData

end TrimmedPresentationSampleMonotone


section MainTheoremsFromTrimmedSampleMonotone

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

/-- Main reachable identification theorem from monotone trimmed-presentation
sample data. -/
theorem main_reachable_identification_from_trimmed_sample_mono
    (H : TrimmedPresentationSampleData D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  H.identifies_via_mono U hfan hL

/-- Main reachable prefix-exact theorem from monotone trimmed-presentation
sample data. -/
theorem main_reachable_prefix_exact_from_trimmed_sample_mono
    (H : TrimmedPresentationSampleData D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  H.prefix_exact_via_mono U hfan hL

end MainTheoremsFromTrimmedSampleMonotone

end MCFG
