/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.NamedContextSplicingSkeleton

/-!
# BinaryRuleSplicingEvidence.lean

Twenty-eighth clean Lean experiment for the fixed-observation MCFG project.

`NamedContextSplicingSkeleton.lean` introduced

```lean
BinaryNamedSplicingFamily
```

as the interface needed to turn concrete child-context splicing into the
filling witnesses required by the reachable main theorem.

This file factors that family into local rule-by-rule evidence.  This is useful
for the next construction phase: rather than constructing a global splicing
family in one step, future files can prove a local splicing lemma for each
binary rule and then assemble the family.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section LocalRuleSplicing

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α}
variable {obs : α → M} {f : Nat}
variable {C : ReachableBlueprintPreCore G obs f}

/-- Local named-context splicing evidence for one binary rule.

This packages the membership proof `ρ ∈ G.binaryRules` together with the
concrete splicing object for that rule. -/
structure BinaryRuleSplicingEvidence
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) where
  splicing : BinaryNamedContextSplicing (C.expose ρ.lhs) ρ.body

namespace BinaryRuleSplicingEvidence

variable {ρ : BinaryRule N α G.arity}
variable {hρ : ρ ∈ G.binaryRules}

/-- Local splicing evidence yields the left filling identity for the rule. -/
def leftIdentity
    (E : BinaryRuleSplicingEvidence (G := G) (C := C) ρ hρ) :
    LeftFillingIdentity namedFill (C.expose ρ.lhs) ρ.body (C.anchor ρ.right) :=
  E.splicing.leftIdentity (C.anchor ρ.right)

/-- Local splicing evidence yields the right filling identity for the rule. -/
def rightIdentity
    (E : BinaryRuleSplicingEvidence (G := G) (C := C) ρ hρ)
    (u : Tuple α (G.arity ρ.left)) :
    RightFillingIdentity namedFill (C.expose ρ.lhs) ρ.body u :=
  E.splicing.rightIdentity u

/-- Local splicing evidence can be viewed as local binary filling evidence. -/
def toFillingEvidence
    (E : BinaryRuleSplicingEvidence (G := G) (C := C) ρ hρ) :
    LeftFillingIdentity namedFill (C.expose ρ.lhs) ρ.body (C.anchor ρ.right) ×
      (∀ u : Tuple α (G.arity ρ.left),
        RightFillingIdentity namedFill (C.expose ρ.lhs) ρ.body u) :=
  ⟨E.leftIdentity, E.rightIdentity⟩

end BinaryRuleSplicingEvidence


/-- A rule-indexed provider of local splicing evidence for every binary rule. -/
structure BinaryRuleSplicingProvider
    (G : WorkingMCFG N α)
    {obs : α → M} {f : Nat}
    (C : ReachableBlueprintPreCore G obs f) where
  evidence :
    ∀ (ρ : BinaryRule N α G.arity),
      ∀ hρ : ρ ∈ G.binaryRules,
        BinaryRuleSplicingEvidence (G := G) (C := C) ρ hρ

namespace BinaryRuleSplicingProvider

/-- Assemble a global named-splicing family from local rule evidence. -/
def toNamedSplicingFamily
    (P : BinaryRuleSplicingProvider G C) :
    BinaryNamedSplicingFamily G C where
  splicing := by
    intro ρ hρ
    exact (P.evidence ρ hρ).splicing

/-- Assemble the abstract filling-witness family from local rule evidence. -/
def toFillingWitnessFamily
    (P : BinaryRuleSplicingProvider G C) :
    BinaryFillingWitnessFamily G C :=
  P.toNamedSplicingFamily.toFillingWitnessFamily

/-- Assemble the full blueprint core from local rule evidence. -/
def toBlueprintCore
    (P : BinaryRuleSplicingProvider G C) :
    ReachableBlueprintCore G obs f :=
  P.toNamedSplicingFamily.toBlueprintCore

/-- Convert pre-core finite-sample data and local rule splicing evidence into
the finite-sample data expected by `BlueprintFiniteSample.lean`. -/
def toFiniteSample
    {S : Finset (Word α)}
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (P : BinaryRuleSplicingProvider G C) :
    ReachableBlueprintFiniteSample G S obs f P.toBlueprintCore :=
  P.toNamedSplicingFamily.toFiniteSample H

/-- Convert pre-core finite-sample data and local rule splicing evidence into
the flat reachable characteristic blueprint. -/
def toBlueprint
    {S : Finset (Word α)}
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (P : BinaryRuleSplicingProvider G C) :
    ReachableCharacteristicBlueprint G S obs f :=
  P.toNamedSplicingFamily.toBlueprint H

/-- Exact reconstruction for any positive finite superset, using local
rule-by-rule splicing evidence. -/
theorem exact_for_positive_superset
    {S K : Finset (Word α)}
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (P : BinaryRuleSplicingProvider G C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f = G.StringLanguage :=
  P.toNamedSplicingFamily.exact_for_positive_superset
    H hfan hL hSK hKpos

/-- Gold identification for the reachable learner from local rule-by-rule
splicing evidence. -/
theorem identifies_from_positive_text
    {S : Finset (Word α)}
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (P : BinaryRuleSplicingProvider G C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  P.toNamedSplicingFamily.identifies_from_positive_text H hfan hL

/-- Eventual prefix-exact reconstruction from local rule-by-rule splicing
evidence. -/
theorem prefix_exact_eventually
    {S : Finset (Word α)}
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (P : BinaryRuleSplicingProvider G C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  P.toNamedSplicingFamily.prefix_exact_eventually H hfan hL

end BinaryRuleSplicingProvider

end LocalRuleSplicing


section MainTheoremsFromRuleSplicing

variable {N : Type w} {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M]

/-- Main reachable identification theorem from local binary-rule splicing
evidence. -/
theorem main_reachable_identification_from_rule_splicing
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (C : ReachableBlueprintPreCore G obs f)
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (P : BinaryRuleSplicingProvider G C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        T :=
  P.identifies_from_positive_text H hfan hL

/-- Main reachable prefix-exact theorem from local binary-rule splicing
evidence. -/
theorem main_reachable_prefix_exact_from_rule_splicing
    (G : WorkingMCFG N α)
    (S : Finset (Word α))
    (obs : α → M) (f : Nat)
    (C : ReachableBlueprintPreCore G obs f)
    (H : ReachablePreCoreFiniteSample G S obs f C)
    (P : BinaryRuleSplicingProvider G C)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ T : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (T.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually H hfan hL

end MainTheoremsFromRuleSplicing

end MCFG
