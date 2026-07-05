/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.BinaryRuleSplicingEvidence

/-!
# NamedContextSplicingConstructor.lean

Twenty-ninth clean Lean experiment for the fixed-observation MCFG project.

This file adds one more interface layer: a universal named-context splicing
constructor.  If every parent named context and every binary template admits a
`BinaryNamedContextSplicing`, then the local and global binary-rule splicing
interfaces from the previous files follow automatically.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section UniversalConstructor

variable {α : Type u}

/-- Universal constructor target for named-context splicing.

A future concrete construction should produce this record by structural
recursion over the parent named context and the binary template. -/
structure NamedContextSplicingConstructor (α : Type u) where
  splice :
    {e dB dC : Nat} →
      (parent : NamedSentenceContext α e) →
      (body : TemplateTuple α e dB dC) →
        BinaryNamedContextSplicing parent body

namespace NamedContextSplicingConstructor

variable {N : Type w} {M : Type v}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α}
variable {obs : α → M} {f : Nat}
variable {C : ReachableBlueprintPreCore G obs f}

/-- A universal splicing constructor gives local evidence for any binary rule. -/
def toRuleSplicingEvidence
    (U : NamedContextSplicingConstructor α)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    BinaryRuleSplicingEvidence (G := G) (C := C) ρ hρ where
  splicing := U.splice (C.expose ρ.lhs) ρ.body

/-- A universal splicing constructor gives a global rule-splicing provider. -/
def toRuleSplicingProvider
    (U : NamedContextSplicingConstructor α)
    (G : WorkingMCFG N α)
    {obs : α → M} {f : Nat}
    (C : ReachableBlueprintPreCore G obs f) :
    BinaryRuleSplicingProvider G C where
  evidence := by
    intro ρ hρ
    exact U.toRuleSplicingEvidence (G := G) (C := C) ρ hρ

/-- A universal splicing constructor gives a global named-splicing family. -/
def toNamedSplicingFamily
    (U : NamedContextSplicingConstructor α)
    (G : WorkingMCFG N α)
    {obs : α → M} {f : Nat}
    (C : ReachableBlueprintPreCore G obs f) :
    BinaryNamedSplicingFamily G C :=
  (U.toRuleSplicingProvider G C).toNamedSplicingFamily

/-- A universal splicing constructor gives the abstract filling-witness family
used by the reachable main theorem. -/
def toFillingWitnessFamily
    (U : NamedContextSplicingConstructor α)
    (G : WorkingMCFG N α)
    {obs : α → M} {f : Nat}
    (C : ReachableBlueprintPreCore G obs f) :
    BinaryFillingWitnessFamily G C :=
  (U.toRuleSplicingProvider G C).toFillingWitnessFamily

/-- A universal splicing constructor upgrades a pre-core to a full blueprint
core. -/
def toBlueprintCore
    (U : NamedContextSplicingConstructor α)
    (G : WorkingMCFG N α)
    {obs : α → M} {f : Nat}
    (C : ReachableBlueprintPreCore G obs f) :
    ReachableBlueprintCore G obs f :=
  (U.toRuleSplicingProvider G C).toBlueprintCore

/-- Exact reconstruction for any positive finite superset, assuming a universal
named-context splicing constructor. -/
theorem exact_for_positive_superset
    (U : NamedContextSplicingConstructor α)
    {S K : Finset (Word α)}
    (G : WorkingMCFG N α)
    {obs : α → M} {f : Nat}
    (C : ReachableBlueprintPreCore G obs f)
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  (U.toRuleSplicingProvider G C).exact_for_positive_superset
    H hfan hL hSK hKpos

/-- Gold identification for the reachable learner, assuming a universal
named-context splicing constructor. -/
theorem identifies_from_positive_text
    (U : NamedContextSplicingConstructor α)
    {S : Finset (Word α)}
    (G : WorkingMCFG N α)
    {obs : α → M} {f : Nat}
    (C : ReachableBlueprintPreCore G obs f)
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  (U.toRuleSplicingProvider G C).identifies_from_positive_text
    H hfan hL

/-- Eventual prefix-exact reconstruction, assuming a universal named-context
splicing constructor. -/
theorem prefix_exact_eventually
    (U : NamedContextSplicingConstructor α)
    {S : Finset (Word α)}
    (G : WorkingMCFG N α)
    {obs : α → M} {f : Nat}
    (C : ReachableBlueprintPreCore G obs f)
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  (U.toRuleSplicingProvider G C).prefix_exact_eventually
    H hfan hL

end NamedContextSplicingConstructor

end UniversalConstructor


section MainTheoremsFromUniversalConstructor

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Main reachable identification theorem from a universal named-context
splicing constructor. -/
theorem main_reachable_identification_from_splicing_constructor
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (C : ReachableBlueprintPreCore G obs f)
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  U.identifies_from_positive_text G C H hfan hL

/-- Main reachable prefix-exact theorem from a universal named-context
splicing constructor. -/
theorem main_reachable_prefix_exact_from_splicing_constructor
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (C : ReachableBlueprintPreCore G obs f)
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  U.prefix_exact_eventually G C H hfan hL

end MainTheoremsFromUniversalConstructor

end MCFG
