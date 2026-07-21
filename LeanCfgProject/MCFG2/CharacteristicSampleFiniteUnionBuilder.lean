/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicSampleFiniteBuilder

/-!
# CharacteristicSampleFiniteUnionBuilder.lean

Fiftieth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleFiniteBuilder.lean` introduced the abstract finite-builder
interface:

```lean
TrimmedPresentationFiniteSampleBuilder D
```

This file adds a slightly more concrete construction pattern.  Instead of
supplying one finite sample at once, we supply four finite subsamples:

* anchor witness words;
* terminal-rule witness words;
* binary-rule witness words;
* start-rule witness words;

and then add the distinguished start word by singleton union.

Their union gives a `TrimmedPresentationFiniteSampleBuilder`.

This is still a skeleton: the finite subsamples are supplied as data.  A later
file can construct them from explicit finite enumerations of nonterminals and
rules.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section FiniteUnionBuilder

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}

/-- A finite union builder for the trimmed-presentation characteristic sample.

It separates the future characteristic sample into finite parts corresponding
to the different witness-word classes. -/
structure TrimmedPresentationFiniteUnionBuilder
    (D : TrimmedPresentationPreCoreData T f) where
  anchorSample : Finset (Word α)
  terminalSample : Finset (Word α)
  binarySample : Finset (Word α)
  startSample : Finset (Word α)

  anchor_mem :
    ∀ A : N,
      D.anchorWitnessWord A ∈ anchorSample

  terminal_mem :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        D.terminalWitnessWord ρ hwt ∈ terminalSample

  binary_mem :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        D.binaryWitnessWord ρ ∈ binarySample

  start_mem :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        D.startWitnessWord ρ hwt ∈ startSample

namespace TrimmedPresentationFiniteUnionBuilder

variable {D : TrimmedPresentationPreCoreData T f}

/-- The finite sample obtained by taking the union of all finite witness parts,
plus the distinguished start word. -/
def sample
    (B : TrimmedPresentationFiniteUnionBuilder D) : Finset (Word α) :=
  B.anchorSample ∪
    (B.terminalSample ∪
      (B.binarySample ∪
        (B.startSample ∪ {D.startWord})))

/-- Anchor witness words are contained in the union sample. -/
theorem anchor_mem_sample
    (B : TrimmedPresentationFiniteUnionBuilder D)
    (A : N) :
    D.anchorWitnessWord A ∈ B.sample := by
  unfold sample
  exact Finset.mem_union.mpr (Or.inl (B.anchor_mem A))

/-- Terminal witness words are contained in the union sample. -/
theorem terminal_mem_sample
    (B : TrimmedPresentationFiniteUnionBuilder D)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    D.terminalWitnessWord ρ hwt ∈ B.sample := by
  unfold sample
  exact Finset.mem_union.mpr
    (Or.inr
      (Finset.mem_union.mpr
        (Or.inl (B.terminal_mem ρ hρ hwt))))

/-- Binary witness words are contained in the union sample. -/
theorem binary_mem_sample
    (B : TrimmedPresentationFiniteUnionBuilder D)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    D.binaryWitnessWord ρ ∈ B.sample := by
  unfold sample
  exact Finset.mem_union.mpr
    (Or.inr
      (Finset.mem_union.mpr
        (Or.inr
          (Finset.mem_union.mpr
            (Or.inl (B.binary_mem ρ hρ))))))

/-- Start-rule witness words are contained in the union sample. -/
theorem start_mem_sample
    (B : TrimmedPresentationFiniteUnionBuilder D)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    D.startWitnessWord ρ hwt ∈ B.sample := by
  unfold sample
  exact Finset.mem_union.mpr
    (Or.inr
      (Finset.mem_union.mpr
        (Or.inr
          (Finset.mem_union.mpr
            (Or.inr
              (Finset.mem_union.mpr
                (Or.inl (B.start_mem ρ hρ hwt))))))))

/-- The distinguished start word is contained in the union sample. -/
theorem startWord_mem_sample
    (B : TrimmedPresentationFiniteUnionBuilder D) :
    D.startWord ∈ B.sample := by
  unfold sample
  exact Finset.mem_union.mpr
    (Or.inr
      (Finset.mem_union.mpr
        (Or.inr
          (Finset.mem_union.mpr
            (Or.inr
              (Finset.mem_union.mpr
                (Or.inr (by simp))))))))

/-- The union sample contains the entire witness-word set. -/
theorem contains_witnesses
    (B : TrimmedPresentationFiniteUnionBuilder D) :
    TrimmedPresentationWitnessWordSet D ⊆
      (B.sample : Set (Word α)) := by
  intro word hword
  rcases hword with hAnchor | hRest
  · rcases hAnchor with ⟨A, rfl⟩
    exact B.anchor_mem_sample A
  rcases hRest with hTerminal | hRest
  · rcases hTerminal with ⟨ρ, hρ, hwt, rfl⟩
    exact B.terminal_mem_sample ρ hρ hwt
  rcases hRest with hBinary | hRest
  · rcases hBinary with ⟨ρ, hρ, rfl⟩
    exact B.binary_mem_sample ρ hρ
  rcases hRest with hStart | hStartWord
  · rcases hStart with ⟨ρ, hρ, hwt, rfl⟩
    exact B.start_mem_sample ρ hρ hwt
  · rw [hStartWord]
    exact B.startWord_mem_sample

/-- Convert the union builder to the abstract finite-sample builder. -/
def toFiniteSampleBuilder
    (B : TrimmedPresentationFiniteUnionBuilder D) :
    TrimmedPresentationFiniteSampleBuilder D where
  sample := B.sample
  contains_witnesses := B.contains_witnesses

@[simp] theorem toFiniteSampleBuilder_sample
    (B : TrimmedPresentationFiniteUnionBuilder D) :
    B.toFiniteSampleBuilder.sample = B.sample :=
  rfl

/-- Positivity data for each finite part of the union builder. -/
structure Positive
    (B : TrimmedPresentationFiniteUnionBuilder D) where
  anchor_positive :
    (B.anchorSample : Set (Word α)) ⊆ G.StringLanguage
  terminal_positive :
    (B.terminalSample : Set (Word α)) ⊆ G.StringLanguage
  binary_positive :
    (B.binarySample : Set (Word α)) ⊆ G.StringLanguage
  start_positive :
    (B.startSample : Set (Word α)) ⊆ G.StringLanguage
  startWord_positive :
    D.startWord ∈ G.StringLanguage

namespace Positive

variable {B : TrimmedPresentationFiniteUnionBuilder D}

/-- Positivity of all finite parts implies positivity of their union sample. -/
theorem sample_positive
    (P : Positive B) :
    (B.sample : Set (Word α)) ⊆ G.StringLanguage := by
  intro word hword
  unfold sample at hword
  rcases Finset.mem_union.mp hword with hAnchor | hRest
  · exact P.anchor_positive hAnchor
  rcases Finset.mem_union.mp hRest with hTerminal | hRest
  · exact P.terminal_positive hTerminal
  rcases Finset.mem_union.mp hRest with hBinary | hRest
  · exact P.binary_positive hBinary
  rcases Finset.mem_union.mp hRest with hStart | hStartWord
  · exact P.start_positive hStart
  · have hEq : word = D.startWord := by
      simpa using hStartWord
    rw [hEq]
    exact P.startWord_positive

/-- A positive union builder gives a witness-sample package. -/
def toWitnessSample
    (P : Positive B) :
    TrimmedPresentationWitnessSample D B.sample :=
  B.toFiniteSampleBuilder.toWitnessSample P.sample_positive

/-- A positive union builder gives a trimmed sample-data package. -/
def toSampleData
    (P : Positive B) :
    TrimmedPresentationSampleData D B.sample :=
  B.toFiniteSampleBuilder.toSampleData P.sample_positive

/-- A positive union builder gives a characteristic-sample object. -/
def toCharacteristicSample
    (P : Positive B) :
    TrimmedPresentationCharacteristicSample D :=
  B.toFiniteSampleBuilder.toCharacteristicSample P.sample_positive

/-- A positive union builder gives trimmed final data after adding the remaining
splicing constructor and global assumptions. -/
def toFinalData
    (P : Positive B)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationFinalData D B.sample :=
  B.toFiniteSampleBuilder.toFinalData P.sample_positive U hfan hL

/-- Eventual prefix-exact reconstruction from a positive union builder. -/
theorem prefix_exact_eventually
    (P : Positive B)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  B.toFiniteSampleBuilder.prefix_exact_eventually
    P.sample_positive U hfan hL

/-- Reachable Gold identification from a positive union builder. -/
theorem identifies_from_positive_text
    (P : Positive B)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  B.toFiniteSampleBuilder.identifies_from_positive_text
    P.sample_positive U hfan hL

end Positive

end TrimmedPresentationFiniteUnionBuilder

end FiniteUnionBuilder


section MainTheoremsFromFiniteUnionBuilder

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem from a positive finite
union builder. -/
theorem trimmed_finite_union_builder_reachable_identification
    (B : TrimmedPresentationFiniteUnionBuilder D)
    (P : B.Positive)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  P.identifies_from_positive_text U hfan hL

/-- Stable top-level prefix-exact theorem from a positive finite union builder. -/
theorem trimmed_finite_union_builder_reachable_prefix_exact
    (B : TrimmedPresentationFiniteUnionBuilder D)
    (P : B.Positive)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually U hfan hL

end MainTheoremsFromFiniteUnionBuilder

end MCFG
