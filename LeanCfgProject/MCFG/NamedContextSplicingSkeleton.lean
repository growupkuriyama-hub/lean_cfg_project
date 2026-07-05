/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.FillingIdentityConstructionSkeleton

/-!
# NamedContextSplicingSkeleton.lean

Twenty-seventh clean Lean experiment for the fixed-observation MCFG project.

`FillingIdentityConstructionSkeleton.lean` isolated the remaining binary
context-splicing task as a family of witnesses

```lean
BinaryFillingWitnessFamily
```

This file introduces a more concrete construction target:

```lean
BinaryNamedContextSplicing
```

For a parent named context `E` and a binary template `ρ`, it stores the child
named contexts that should satisfy the left and right filling identities.

The file still does not construct those contexts from first principles.  It
packages the exact interface that a future concrete construction must provide,
and proves that such a splicing family yields the filling witnesses needed by
the reachable main theorem.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section BinaryNamedSplicing

variable {α : Type u}

/-- Concrete named-context splicing target for one binary template.

Given a parent named context and a binary template, this record stores:

* for each fixed right tuple `y`, a left child context in which varying `x`
  gives the same filled word as the parent filled with `ρ(x,y)`;
* for each fixed left tuple `u`, a right child context in which varying `v`
  gives the same filled word as the parent filled with `ρ(u,v)`.

This is precisely the concrete content needed to produce
`LeftFillingIdentity` and `RightFillingIdentity` for named contexts. -/
structure BinaryNamedContextSplicing
    {e dB dC : Nat}
    (parent : NamedSentenceContext α e)
    (body : TemplateTuple α e dB dC) where
  leftContext : Tuple α dC → NamedSentenceContext α dB
  left_fill_eq :
    ∀ (y : Tuple α dC) (x : Tuple α dB),
      namedFill dB (leftContext y) x =
        namedFill e parent (evalTemplateTuple body x y)

  rightContext : Tuple α dB → NamedSentenceContext α dC
  right_fill_eq :
    ∀ (u : Tuple α dB) (v : Tuple α dC),
      namedFill dC (rightContext u) v =
        namedFill e parent (evalTemplateTuple body u v)

namespace BinaryNamedContextSplicing

variable {e dB dC : Nat}
variable {parent : NamedSentenceContext α e}
variable {body : TemplateTuple α e dB dC}

/-- A concrete named splicing yields the left filling identity for any fixed
right tuple. -/
def leftIdentity
    (S : BinaryNamedContextSplicing parent body)
    (y : Tuple α dC) :
    LeftFillingIdentity namedFill parent body y where
  ctx := S.leftContext y
  fill_eq := by
    intro x
    exact S.left_fill_eq y x

/-- A concrete named splicing yields the right filling identity for any fixed
left tuple. -/
def rightIdentity
    (S : BinaryNamedContextSplicing parent body)
    (u : Tuple α dB) :
    RightFillingIdentity namedFill parent body u where
  ctx := S.rightContext u
  fill_eq := by
    intro v
    exact S.right_fill_eq u v

@[simp] theorem leftIdentity_ctx
    (S : BinaryNamedContextSplicing parent body)
    (y : Tuple α dC) :
    (S.leftIdentity y).ctx = S.leftContext y :=
  rfl

@[simp] theorem rightIdentity_ctx
    (S : BinaryNamedContextSplicing parent body)
    (u : Tuple α dB) :
    (S.rightIdentity u).ctx = S.rightContext u :=
  rfl

end BinaryNamedContextSplicing

end BinaryNamedSplicing


section SplicingFamily

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- A concrete named-context splicing family for all binary rules, relative to
a reachable blueprint pre-core. -/
structure BinaryNamedSplicingFamily
    (G : WorkingMCFG N α)
    {obs : α → M} {f : Nat}
    (C : ReachableBlueprintPreCore G obs f) where
  splicing :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        BinaryNamedContextSplicing (C.expose ρ.lhs) ρ.body

namespace BinaryNamedSplicingFamily

variable {G : WorkingMCFG N α}
variable {obs : α → M} {f : Nat}
variable {C : ReachableBlueprintPreCore G obs f}

/-- A concrete named-splicing family yields the abstract binary filling witness
family used by the reachable main theorem. -/
def toFillingWitnessFamily
    (F : BinaryNamedSplicingFamily G C) :
    BinaryFillingWitnessFamily G C where
  leftIdentity := by
    intro ρ hρ
    exact (F.splicing ρ hρ).leftIdentity (C.anchor ρ.right)
  rightIdentity := by
    intro ρ hρ u
    exact (F.splicing ρ hρ).rightIdentity u

/-- Build a full blueprint core from a pre-core and a concrete splicing family. -/
def toBlueprintCore
    (F : BinaryNamedSplicingFamily G C) :
    ReachableBlueprintCore G obs f :=
  C.withFillingWitnesses F.toFillingWitnessFamily

/-- Convert pre-core finite-sample data and concrete splicing into the finite
sample data expected by `BlueprintFiniteSample.lean`. -/
def toFiniteSample
    {S : Finset (Word α)}
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (F : BinaryNamedSplicingFamily G C) :
    ReachableBlueprintFiniteSample G S obs f F.toBlueprintCore :=
  H.toFiniteSample F.toFillingWitnessFamily

/-- Build the reachable characteristic blueprint from pre-core finite-sample
data and a concrete named-splicing family. -/
def toBlueprint
    {S : Finset (Word α)}
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (F : BinaryNamedSplicingFamily G C) :
    ReachableCharacteristicBlueprint G S obs f :=
  (F.toFiniteSample H).toBlueprint

/-- Exact reconstruction for any positive finite superset, using a concrete
named-splicing family. -/
theorem exact_for_positive_superset
    {S K : Finset (Word α)}
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (F : BinaryNamedSplicingFamily G C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  H.exact_for_positive_superset
    F.toFillingWitnessFamily hfan hL hSK hKpos

/-- Gold identification for the reachable learner from pre-core data and a
concrete named-splicing family. -/
theorem identifies_from_positive_text
    {S : Finset (Word α)}
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (F : BinaryNamedSplicingFamily G C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  H.identifies_from_positive_text F.toFillingWitnessFamily hfan hL

/-- Eventual prefix-exact reconstruction from pre-core data and a concrete
named-splicing family. -/
theorem prefix_exact_eventually
    {S : Finset (Word α)}
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (F : BinaryNamedSplicingFamily G C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  H.prefix_exact_eventually F.toFillingWitnessFamily hfan hL

end BinaryNamedSplicingFamily

end SplicingFamily


section MainTheoremsFromNamedSplicing

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Main reachable identification theorem from pre-core data, finite-sample
membership facts, and concrete named-context splicing. -/
theorem main_reachable_identification_from_named_splicing
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (C : ReachableBlueprintPreCore G obs f)
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (F : BinaryNamedSplicingFamily G C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  F.identifies_from_positive_text H hfan hL

/-- Main reachable prefix-exact theorem from pre-core data, finite-sample
membership facts, and concrete named-context splicing. -/
theorem main_reachable_prefix_exact_from_named_splicing
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (C : ReachableBlueprintPreCore G obs f)
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (F : BinaryNamedSplicingFamily G C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  F.prefix_exact_eventually H hfan hL

end MainTheoremsFromNamedSplicing

end MCFG
