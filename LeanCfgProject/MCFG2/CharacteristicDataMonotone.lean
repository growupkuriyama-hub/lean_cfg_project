/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ReachableGoldTheorem

/-!
# CharacteristicDataMonotone.lean

Nineteenth clean Lean experiment for the fixed-observation MCFG project.

`ReachableGoldTheorem.lean` used the condition that every positive finite
superset `K` of a finite sample `S` supplies characteristic data.

This file proves the main monotonicity lemma behind that condition:

If the characteristic data already exists over `S`, then the same anchors,
contexts, and rule witnesses also exist over every finite `K` with `S ⊆ K`.
All sample-membership fields are transported along the inclusion.

Consequently, one concrete finite characteristic-data package over `S` is
enough to obtain the reachable Gold-identification theorem.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section Monotonicity

variable {N : Type w} {α : Type u} {M : Type v} [Monoid M]
variable {G : WorkingMCFG N α}
variable {S K : Finset (Word α)} {obs : α → M} {f : Nat}

namespace CharacteristicSampleData

/-- Characteristic-sample data is monotone in the finite sample.

If every word of `S` is also in `K`, then all witnesses stored in characteristic
data over `S` are still valid over `K`. -/
def mono
    (D : CharacteristicSampleData G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α))) :
    CharacteristicSampleData G K obs f where
  anchor := D.anchor
  expose := D.expose
  anchor_mem := by
    intro A
    exact hSK (D.anchor_mem A)
  terminal_mem := by
    intro ρ hρ hwt
    exact hSK (D.terminal_mem ρ hρ hwt)
  terminal_type_eq := by
    intro ρ hρ hwt
    exact D.terminal_type_eq ρ hρ hwt
  binary_mem := by
    intro ρ hρ
    exact hSK (D.binary_mem ρ hρ)
  binary_type_eq := by
    intro ρ hρ
    exact D.binary_type_eq ρ hρ
  binary_leftIdentity := by
    intro ρ hρ
    exact D.binary_leftIdentity ρ hρ
  binary_rightIdentity := by
    intro ρ hρ u
    exact D.binary_rightIdentity ρ hρ u
  start_mem := by
    intro ρ hρ hwt
    exact hSK (D.start_mem ρ hρ hwt)
  start_type_eq := by
    intro ρ hρ hwt
    exact D.start_type_eq ρ hρ hwt

@[simp] theorem mono_anchor
    (D : CharacteristicSampleData G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (A : N) :
    (D.mono hSK).anchor A = D.anchor A :=
  rfl

@[simp] theorem mono_expose
    (D : CharacteristicSampleData G S obs f)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (A : N) :
    (D.mono hSK).expose A = D.expose A :=
  rfl

end CharacteristicSampleData


namespace StartAnchorAsSampleWord

/-- The start-anchor bridge is also monotone in the finite sample. -/
def mono
    {D : CharacteristicSampleData G S obs f}
    (B : StartAnchorAsSampleWord D)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α))) :
    StartAnchorAsSampleWord (D.mono hSK) where
  startWord := B.startWord
  start_mem := hSK B.start_mem
  anchor_eq := by
    intro hstart
    exact B.anchor_eq hstart

@[simp] theorem mono_startWord
    {D : CharacteristicSampleData G S obs f}
    (B : StartAnchorAsSampleWord D)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α))) :
    (B.mono hSK).startWord = B.startWord :=
  rfl

end StartAnchorAsSampleWord

end Monotonicity


section ReachableConditionFromSingleData

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- One characteristic-data package over `S` yields the
`ReachableCharacteristicCondition` required in `ReachableGoldTheorem.lean`.

The positivity assumption on the larger `K` is not needed for transporting the
data itself; it is only used later by exact reconstruction soundness. -/
theorem reachableCharacteristicCondition_of_data
    (G : WorkingMCFG N α)
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    (D : CharacteristicSampleData G S obs f)
    (B : StartAnchorAsSampleWord D) :
    ReachableCharacteristicCondition G S obs f := by
  intro K hSK _hKG
  exact ⟨D.mono hSK, B.mono hSK⟩

/-- A single finite characteristic-data package over `S` gives a characteristic
sample for the reachable learner, provided `S` itself is positive for the
target language. -/
theorem reachable_characteristicSample_of_data
    (G : WorkingMCFG N α)
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSpos : (S : Set (Word α)) ⊆ G.StringLanguage)
    (D : CharacteristicSampleData G S obs f)
    (B : StartAnchorAsSampleWord D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      S
      G.StringLanguage :=
  reachable_characteristicSample
    G hfan hL S hSpos
    (reachableCharacteristicCondition_of_data G D B)

/-- Gold identification for the reachable learner from one finite
characteristic-data package over `S`. -/
theorem reachable_identifies_from_characteristic_data
    (G : WorkingMCFG N α)
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSpos : (S : Set (Word α)) ⊆ G.StringLanguage)
    (D : CharacteristicSampleData G S obs f)
    (B : StartAnchorAsSampleWord D) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  reachable_identifies_from_positive_text
    G hfan hL S hSpos
    (reachableCharacteristicCondition_of_data G D B)

/-- Eventual-stage form of `reachable_identifies_from_characteristic_data`. -/
theorem reachable_correct_after_some_stage_from_characteristic_data
    (G : WorkingMCFG N α)
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSpos : (S : Set (Word α)) ⊆ G.StringLanguage)
    (D : CharacteristicSampleData G S obs f)
    (B : StartAnchorAsSampleWord D)
    (T : TextFor G.StringLanguage) :
    ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
      reachableHypLanguage obs f
        (reachableSampleLearner (α := α) (T.prefixSample n)) =
          G.StringLanguage := by
  exact reachable_identifies_from_characteristic_data
    G hfan hL hSpos D B T

end ReachableConditionFromSingleData

end MCFG
