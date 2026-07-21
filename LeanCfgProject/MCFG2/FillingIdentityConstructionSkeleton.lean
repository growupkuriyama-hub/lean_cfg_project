/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.BlueprintFiniteSample

/-!
# FillingIdentityConstructionSkeleton.lean

Twenty-sixth clean Lean experiment for the fixed-observation MCFG project.

`BlueprintFiniteSample.lean` split the reachable characteristic blueprint into

* a sample-independent core, and
* finite-sample membership facts.

The core still contains the binary filling identities directly.  This file
isolates those identities into their own construction target.

This is useful because the next hard construction task is not the whole
blueprint at once, but specifically the context-splicing lemma:

given a parent named context and a binary template, construct child contexts
witnessing

```lean
LeftFillingIdentity
RightFillingIdentity
```

This file does not yet build those contexts.  Instead, it packages the exact
interface needed by the already-verified reachable main theorem.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section FillingWitnesses

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- The part of a reachable blueprint core that does not mention binary
filling identities.

This is the easier sample-independent data: anchors, exposing contexts,
observation-type equalities, and the start-anchor convention. -/
structure ReachableBlueprintPreCore
    (G : WorkingMCFG N α)
    (obs : α → M) (f : Nat) where
  anchor : ∀ A : N, Tuple α (G.arity A)
  expose : ∀ A : N, NamedSentenceContext α (G.arity A)

  terminal_type_eq :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        tupleType obs (anchor ρ.lhs) =
          tupleType obs (castTuple hwt.symm ρ.outputTuple)

  binary_type_eq :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        tupleType obs (anchor ρ.lhs) =
          tupleType obs (ρ.apply (anchor ρ.left) (anchor ρ.right))

  start_type_eq :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        tupleType obs (anchor G.start) =
          tupleType obs (castTuple hwt (anchor ρ.child))

  startWord : Word α
  start_arity : 1 = G.arity G.start
  start_anchor_eq :
    anchor G.start =
      castTuple start_arity (singletonTuple startWord)

/-- Filling-identity witnesses for all binary rules, relative to a pre-core.

This is the isolated target for the future concrete context-splicing
construction. -/
structure BinaryFillingWitnessFamily
    (G : WorkingMCFG N α)
    {obs : α → M} {f : Nat}
    (C : ReachableBlueprintPreCore G obs f) where
  leftIdentity :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        LeftFillingIdentity namedFill (C.expose ρ.lhs) ρ.body (C.anchor ρ.right)

  rightIdentity :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        ∀ u : Tuple α (G.arity ρ.left),
          RightFillingIdentity namedFill (C.expose ρ.lhs) ρ.body u

namespace ReachableBlueprintPreCore

variable {G : WorkingMCFG N α}
variable {obs : α → M} {f : Nat}

/-- Add binary filling witnesses to a pre-core, producing the core expected by
`BlueprintFiniteSample.lean`. -/
def withFillingWitnesses
    (C : ReachableBlueprintPreCore G obs f)
    (W : BinaryFillingWitnessFamily G C) :
    ReachableBlueprintCore G obs f where
  anchor := C.anchor
  expose := C.expose
  terminal_type_eq := C.terminal_type_eq
  binary_type_eq := C.binary_type_eq
  binary_leftIdentity := W.leftIdentity
  binary_rightIdentity := W.rightIdentity
  start_type_eq := C.start_type_eq
  startWord := C.startWord
  start_arity := C.start_arity
  start_anchor_eq := C.start_anchor_eq

@[simp] theorem withFillingWitnesses_anchor
    (C : ReachableBlueprintPreCore G obs f)
    (W : BinaryFillingWitnessFamily G C)
    (A : N) :
    (C.withFillingWitnesses W).anchor A = C.anchor A :=
  rfl

@[simp] theorem withFillingWitnesses_expose
    (C : ReachableBlueprintPreCore G obs f)
    (W : BinaryFillingWitnessFamily G C)
    (A : N) :
    (C.withFillingWitnesses W).expose A = C.expose A :=
  rfl

@[simp] theorem withFillingWitnesses_startWord
    (C : ReachableBlueprintPreCore G obs f)
    (W : BinaryFillingWitnessFamily G C) :
    (C.withFillingWitnesses W).startWord = C.startWord :=
  rfl

end ReachableBlueprintPreCore


/-- Finite-sample membership data relative to a pre-core.

This avoids mentioning filling identities, so it can be established
independently of the future context-splicing construction. -/
structure ReachablePreCoreFiniteSample
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (C : ReachableBlueprintPreCore G obs f) where
  sample_positive : (S : Set (Word α)) ⊆ G.StringLanguage

  anchor_mem :
    ∀ A : N,
      namedFill (G.arity A) (C.expose A) (C.anchor A) ∈ S

  terminal_mem :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        namedFill (G.arity ρ.lhs) (C.expose ρ.lhs)
          (castTuple hwt.symm ρ.outputTuple) ∈ S

  binary_mem :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        namedFill (G.arity ρ.lhs) (C.expose ρ.lhs)
          (ρ.apply (C.anchor ρ.left) (C.anchor ρ.right)) ∈ S

  start_mem :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        namedFill (G.arity G.start) (C.expose G.start)
          (castTuple hwt (C.anchor ρ.child)) ∈ S

  startWord_mem : C.startWord ∈ S

namespace ReachablePreCoreFiniteSample

variable {G : WorkingMCFG N α}
variable {S : Finset (Word α)} {obs : α → M} {f : Nat}
variable {C : ReachableBlueprintPreCore G obs f}

/-- Once filling witnesses are supplied, pre-core finite-sample data becomes the
finite-sample data expected by `BlueprintFiniteSample.lean`. -/
def toFiniteSample
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (W : BinaryFillingWitnessFamily G C) :
    ReachableBlueprintFiniteSample G S obs f (C.withFillingWitnesses W) where
  sample_positive := H.sample_positive
  anchor_mem := H.anchor_mem
  terminal_mem := H.terminal_mem
  binary_mem := H.binary_mem
  start_mem := H.start_mem
  startWord_mem := H.startWord_mem

/-- Build the full reachable characteristic blueprint from a pre-core,
finite-sample membership data, and filling witnesses. -/
def toBlueprint
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (W : BinaryFillingWitnessFamily G C) :
    ReachableCharacteristicBlueprint G S obs f :=
  (H.toFiniteSample W).toBlueprint

/-- Build the finite reachable characteristic package from pre-core data. -/
def toPackage
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (W : BinaryFillingWitnessFamily G C) :
    ReachableCharacteristicPackage G S obs f :=
  (H.toFiniteSample W).toPackage

/-- Exact reconstruction for any positive finite superset, once filling
witnesses have been constructed. -/
theorem exact_for_positive_superset
    {K : Finset (Word α)}
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (W : BinaryFillingWitnessFamily G C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  (H.toFiniteSample W).exact_for_positive_superset hfan hL hSK hKpos

/-- Gold identification for the reachable learner from pre-core data plus
filling witnesses. -/
theorem identifies_from_positive_text
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (W : BinaryFillingWitnessFamily G C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  (H.toFiniteSample W).identifies_from_positive_text hfan hL

/-- Eventual prefix-exact reconstruction from pre-core data plus filling
witnesses. -/
theorem prefix_exact_eventually
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (W : BinaryFillingWitnessFamily G C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  (H.toFiniteSample W).prefix_exact_eventually hfan hL

end ReachablePreCoreFiniteSample

end FillingWitnesses


section MainTheoremsFromPreCore

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Main reachable identification theorem from pre-core data, finite-sample
membership facts, and binary filling witnesses. -/
theorem main_reachable_identification_from_precore
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (C : ReachableBlueprintPreCore G obs f)
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (W : BinaryFillingWitnessFamily G C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  H.identifies_from_positive_text W hfan hL

/-- Main reachable prefix-exact theorem from pre-core data, finite-sample
membership facts, and binary filling witnesses. -/
theorem main_reachable_prefix_exact_from_precore
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (C : ReachableBlueprintPreCore G obs f)
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (W : BinaryFillingWitnessFamily G C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  H.prefix_exact_eventually W hfan hL

end MainTheoremsFromPreCore

end MCFG
