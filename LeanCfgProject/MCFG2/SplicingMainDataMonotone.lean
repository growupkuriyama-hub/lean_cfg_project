/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.SplicingMainTheorem

/-!
# SplicingMainDataMonotone.lean

Thirty-first clean Lean experiment for the fixed-observation MCFG project.

`SplicingMainTheorem.lean` packaged the current reachable main theorem in the
record

```lean
ReachableSplicingMainData
```

This file adds monotonicity for that package.

If the finite sample `S` has all characteristic witnesses, then every larger
positive finite sample `K` has the same witnesses.  The pre-core and universal
splicing constructor are unchanged; only the finite-sample membership facts are
transported along `S ⊆ K`.

This is useful for the eventual positive-text argument, because once the
characteristic sample has appeared in the text prefix, all later prefixes inherit
the same data.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PreCoreFiniteSampleMonotone

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α}
variable {S K : Finset (Word α)}
variable {obs : α → M} {f : Nat}
variable {C : ReachableBlueprintPreCore G obs f}

namespace ReachablePreCoreFiniteSample

/-- Pre-core finite-sample membership data is monotone in the finite sample. -/
def mono
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachablePreCoreFiniteSample G K obs f C where
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
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (H.mono hSK hKpos).sample_positive = hKpos :=
  rfl

/-- Monotonicity is compatible with adding filling witnesses. -/
theorem toFiniteSample_mono
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (W : BinaryFillingWitnessFamily G C)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (H.mono hSK hKpos).toFiniteSample W =
      (H.toFiniteSample W).mono hSK hKpos := by
  rfl

end ReachablePreCoreFiniteSample

end PreCoreFiniteSampleMonotone


section SplicingMainDataMonotone

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α}
variable {S K : Finset (Word α)}
variable {obs : α → M} {f : Nat}

namespace ReachableSplicingMainData

/-- `ReachableSplicingMainData` is monotone in the finite sample.

The global target assumptions, pre-core, and splicing constructor are unchanged.
Only the finite-sample membership facts are transported from `S` to `K`. -/
def mono
    (A : ReachableSplicingMainData G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSplicingMainData G K obs f where
  fanout := A.fanout
  promise := A.promise
  preCore := A.preCore
  finiteSample := A.finiteSample.mono hSK hKpos
  splicingConstructor := A.splicingConstructor

@[simp] theorem mono_preCore
    (A : ReachableSplicingMainData G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (A.mono hSK hKpos).preCore = A.preCore :=
  rfl

@[simp] theorem mono_splicingConstructor
    (A : ReachableSplicingMainData G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (A.mono hSK hKpos).splicingConstructor = A.splicingConstructor :=
  rfl

/-- The monotone package reconstructs the target exactly on the larger sample. -/
theorem exact_after_mono
    (A : ReachableSplicingMainData G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  (A.mono hSK hKpos).exact_for_positive_superset
    (fun word hword => hword) hKpos

/-- At a text prefix containing `S`, the monotone data over that prefix gives
exact reconstruction. -/
theorem exact_at_prefix_via_mono
    (A : ReachableSplicingMainData G S obs f)
    (T : TextFor G.StringLanguage)
    {n : Nat}
    (hseen : (S : Set (Word α)) ⊆
      (T.prefixSample n : Set (Word α))) :
    ReachableSampleStringLanguage (T.prefixSample n) obs f =
      G.StringLanguage := by
  have hKpos :
      (T.prefixSample n : Set (Word α)) ⊆ G.StringLanguage := by
    intro word hword
    exact T.prefixSample_subset n hword
  exact A.exact_after_mono hseen hKpos

/-- Eventual prefix exactness can also be derived by first transporting the
whole data package to the current prefix. -/
theorem prefix_exact_eventually_via_mono
    (A : ReachableSplicingMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage := by
  intro T
  rcases T.eventuallyContains_of_subset S
      A.finiteSample.sample_positive with ⟨n0, hcontains⟩
  refine ⟨n0, ?_⟩
  intro n hn
  exact A.exact_at_prefix_via_mono T (hcontains n hn)

end ReachableSplicingMainData

end SplicingMainDataMonotone


section MainTheorems

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Main prefix-exact theorem using monotonicity of the splicing-main data. -/
theorem main_reachable_prefix_exact_from_splicing_data_mono
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (A : ReachableSplicingMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  A.prefix_exact_eventually_via_mono

/-- Main identification theorem using monotonicity of the splicing-main data. -/
theorem main_reachable_identification_from_splicing_data_mono
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (A : ReachableSplicingMainData G S obs f) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T := by
  intro T
  rcases A.prefix_exact_eventually_via_mono T with ⟨n0, hcorr⟩
  exact ⟨n0, by
    intro n hn
    simpa [reachableHypLanguage, reachableSampleLearner] using hcorr n hn⟩

end MainTheorems

end MCFG
