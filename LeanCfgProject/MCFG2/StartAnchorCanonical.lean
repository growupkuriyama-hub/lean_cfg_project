/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CharacteristicDataMonotone

/-!
# StartAnchorCanonical.lean

Twentieth clean Lean experiment for the fixed-observation MCFG project.

`ReachableStartBridge.lean` introduced `StartAnchorAsSampleWord`, whose
`anchor_eq` field is quantified over every proof of the start arity equality

```lean
hstart : 1 = G.arity G.start.
```

For construction, it is often more natural to provide just one such arity proof
together with one transported equality.  This file adds that more convenient
wrapper and shows that it implies `StartAnchorAsSampleWord`.

This is a small but useful interface layer for the later characteristic-sample
construction.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section CanonicalStartAnchor

variable {N : Type w} {α : Type u} {M : Type v} [Monoid M]
variable {G : WorkingMCFG N α}
variable {K : Finset (Word α)} {obs : α → M} {f : Nat}

/-- A construction-friendly form of the start-anchor bridge.

It stores one proof that the start arity is one, and one equality saying that
the characteristic start anchor is the corresponding transported singleton
tuple of a sample word. -/
structure StartAnchorCanonical
    (D : CharacteristicSampleData G K obs f) where
  startWord : Word α
  start_mem : startWord ∈ K
  start_arity : 1 = G.arity G.start
  anchor_eq :
    D.anchor G.start =
      castTuple start_arity (singletonTuple startWord)

namespace StartAnchorCanonical

/-- A canonical start-anchor witness gives the proof-irrelevant bridge required
by `StartAnchorAsSampleWord`. -/
def toStartAnchorAsSampleWord
    {D : CharacteristicSampleData G K obs f}
    (C : StartAnchorCanonical D) :
    StartAnchorAsSampleWord D where
  startWord := C.startWord
  start_mem := C.start_mem
  anchor_eq := by
    intro hstart
    cases C.start_arity
    cases hstart
    simpa using C.anchor_eq

/-- Direct constructor for `StartAnchorAsSampleWord` from one transported
start-anchor equality. -/
def toStartAnchorAsSampleWord_of_eq
    (D : CharacteristicSampleData G K obs f)
    (word : Word α)
    (hmem : word ∈ K)
    (hstart : 1 = G.arity G.start)
    (heq :
      D.anchor G.start =
        castTuple hstart (singletonTuple word)) :
    StartAnchorAsSampleWord D :=
  (StartAnchorCanonical.mk word hmem hstart heq).toStartAnchorAsSampleWord

/-- The canonical start-anchor witness is monotone in the finite sample. -/
def mono
    {S K : Finset (Word α)}
    {D : CharacteristicSampleData G S obs f}
    (C : StartAnchorCanonical D)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α))) :
    StartAnchorCanonical (D.mono hSK) where
  startWord := C.startWord
  start_mem := hSK C.start_mem
  start_arity := C.start_arity
  anchor_eq := by
    simpa [CharacteristicSampleData.mono] using C.anchor_eq

/-- Monotonicity is compatible with the older `StartAnchorAsSampleWord` bridge. -/
theorem toStartAnchorAsSampleWord_mono
    {S K : Finset (Word α)}
    {D : CharacteristicSampleData G S obs f}
    (C : StartAnchorCanonical D)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α))) :
    (C.mono hSK).toStartAnchorAsSampleWord =
      (C.toStartAnchorAsSampleWord).mono hSK := by
  rfl

/-- Reachable exact reconstruction using the construction-friendly start-anchor
witness. -/
theorem exact_reconstruction_reachable
    (D : CharacteristicSampleData G K obs f)
    (C : StartAnchorCanonical D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hK : PositiveSample G K) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  StartAnchorAsSampleWord.exact_reconstruction_reachable
    D C.toStartAnchorAsSampleWord hfan hL hK

/-- Mutual-inclusion form of reachable exact reconstruction using
`StartAnchorCanonical`. -/
theorem exact_reconstruction_reachable_inclusions
    (D : CharacteristicSampleData G K obs f)
    (C : StartAnchorCanonical D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hK : PositiveSample G K) :
    ReachableSampleStringLanguage K obs f ⊆ G.StringLanguage ∧
      G.StringLanguage ⊆ ReachableSampleStringLanguage K obs f :=
  StartAnchorAsSampleWord.exact_reconstruction_reachable_inclusions
    D C.toStartAnchorAsSampleWord hfan hL hK

end StartAnchorCanonical

end CanonicalStartAnchor


section CanonicalGoldConsequences

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- One finite characteristic-data package plus the construction-friendly
start-anchor witness gives a characteristic sample for the reachable learner. -/
theorem reachable_characteristicSample_of_canonical_data
    (G : WorkingMCFG N α)
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSpos : (S : Set (Word α)) ⊆ G.StringLanguage)
    (D : CharacteristicSampleData G S obs f)
    (C : StartAnchorCanonical D) :
    CharacteristicSample
      (reachableHypLanguage obs f)
      (reachableSampleLearner (α := α))
      S
      G.StringLanguage :=
  reachable_characteristicSample_of_data
    G hfan hL hSpos D C.toStartAnchorAsSampleWord

/-- Gold identification for the reachable learner from one finite
characteristic-data package and a canonical start-anchor witness. -/
theorem reachable_identifies_from_canonical_characteristic_data
    (G : WorkingMCFG N α)
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSpos : (S : Set (Word α)) ⊆ G.StringLanguage)
    (D : CharacteristicSampleData G S obs f)
    (C : StartAnchorCanonical D) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  reachable_identifies_from_characteristic_data
    G hfan hL hSpos D C.toStartAnchorAsSampleWord

/-- Eventual-stage form of the canonical-data identification theorem. -/
theorem reachable_correct_after_some_stage_from_canonical_data
    (G : WorkingMCFG N α)
    {S : Finset (Word α)} {obs : α → M} {f : Nat}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSpos : (S : Set (Word α)) ⊆ G.StringLanguage)
    (D : CharacteristicSampleData G S obs f)
    (C : StartAnchorCanonical D)
    (T : TextFor G.StringLanguage) :
    ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
      reachableHypLanguage obs f
        (reachableSampleLearner (α := α) (T.prefixSample n)) =
          G.StringLanguage := by
  exact reachable_identifies_from_canonical_characteristic_data
    G hfan hL hSpos D C T

end CanonicalGoldConsequences

end MCFG
