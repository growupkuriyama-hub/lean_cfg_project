/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.StartRuleSoundness

/-!
# CompletenessSkeleton.lean

Twelfth clean Lean experiment for the fixed-observation MCFG project.

The previous files established soundness of sample-level learner derivations.
This file begins the completeness side.

The full characteristic-sample construction is still postponed.  Instead, this
file proves a reusable induction principle:

If each target grammar rule is simulated by the sample-level learner from a
chosen anchor tuple for every nonterminal, then every target derivation is
simulated by the sample-level learner from the corresponding anchor tuple.

This is the Lean skeleton behind the paper's exact-reconstruction argument:
the characteristic sample will later provide the anchors and the rule
simulations.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section ReachableClosure

variable {α : Type u} {M : Type v} [Monoid M]

/-- Reflexive-transitive, composition-friendly closure of sample-level learner
derivations.

`SampleLearnerDerives` is already enough for soundness, but completeness needs
to concatenate simulations of grammar rules with simulations of their child
derivations.  This closure adds an explicit `trans` constructor while retaining
the same semantic rule forms. -/
inductive SampleLearnerReachable
    (K : Finset (Word α)) (obs : α → M) (f : Nat) :
    {d : Nat} → Tuple α d → Tuple α d → Prop where
  | self {d : Nat} (x : Tuple α d) :
      SampleLearnerReachable K obs f x x
  | step {d : Nat} {x y : Tuple α d}
      (h : SampleLearnerDerives K obs f x y) :
      SampleLearnerReachable K obs f x y
  | unit {d : Nat} {x y u : Tuple α d}
      (hd : d ≤ f)
      (hpos : 0 < d)
      (U : SampleUnitEvidence K obs x y)
      (hyu : SampleLearnerReachable K obs f y u) :
      SampleLearnerReachable K obs f x u
  | binary {e dB dC : Nat}
      {parent : NamedSentenceContext α e}
      {body : TemplateTuple α e dB dC}
      {x u : Tuple α dB}
      {y v : Tuple α dC}
      (he : e ≤ f)
      (hpos : 0 < e)
      (B : SampleBinaryEvidence K parent body x y)
      (hx : SampleLearnerReachable K obs f x u)
      (hy : SampleLearnerReachable K obs f y v) :
      SampleLearnerReachable K obs f
        (evalTemplateTuple body x y)
        (evalTemplateTuple body u v)
  | trans {d : Nat} {x y z : Tuple α d}
      (hxy : SampleLearnerReachable K obs f x y)
      (hyz : SampleLearnerReachable K obs f y z) :
      SampleLearnerReachable K obs f x z

namespace SampleLearnerReachable

variable {K : Finset (Word α)} {obs : α → M} {f : Nat}

/-- Every sample-level learner derivation is reachable. -/
theorem of_derives {d : Nat} {x y : Tuple α d}
    (h : SampleLearnerDerives K obs f x y) :
    SampleLearnerReachable K obs f x y :=
  SampleLearnerReachable.step h

/-- Reachability is reflexive. -/
theorem refl {d : Nat} (x : Tuple α d) :
    SampleLearnerReachable K obs f x x :=
  SampleLearnerReachable.self x

/-- Reachability is transitive. -/
theorem trans' {d : Nat} {x y z : Tuple α d}
    (hxy : SampleLearnerReachable K obs f x y)
    (hyz : SampleLearnerReachable K obs f y z) :
    SampleLearnerReachable K obs f x z :=
  SampleLearnerReachable.trans hxy hyz

/-- Cast reachability across an equality of arities. -/
theorem arityCast {d e : Nat} (hde : d = e)
    {x y : Tuple α d}
    (h : SampleLearnerReachable K obs f x y) :
    SampleLearnerReachable K obs f
      (castTuple hde x) (castTuple hde y) := by
  subst hde
  simpa using h

/-- Soundness of reachable sample-level learner derivations for a grammar
target. -/
theorem sound_for_grammar
    {N : Type w}
    (G : WorkingMCFG N α)
    {d : Nat} {x u : Tuple α d}
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hK : PositiveSample G K)
    (h : SampleLearnerReachable K obs f x u) :
    GrammarNamedDistributionalEquivalent G obs u x := by
  induction h with
  | self x =>
      exact fixedNamedDistributionalEquivalent_refl x
  | step h =>
      exact h.sound_for_grammar G hL hK
  | unit hd hpos U _ ih =>
      have hxy : GrammarNamedDistributionalEquivalent G obs _ _ :=
        U.sound_for_grammar G hL hd hpos hK
      exact fixedNamedDistributionalEquivalent_trans ih
        (fixedNamedDistributionalEquivalent_symm hxy)
  | binary he hpos B _ _ ihx ihy =>
      exact B.sound_for_grammar G hL he hpos hK ihx ihy
  | trans _ _ ihxy ihyz =>
      exact fixedNamedDistributionalEquivalent_trans ihyz ihxy

/-- Reachability preserves componentwise observation type under the grammar
promise. -/
theorem tupleType_eq_for_grammar
    {N : Type w}
    (G : WorkingMCFG N α)
    {d : Nat} {x u : Tuple α d}
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hK : PositiveSample G K)
    (h : SampleLearnerReachable K obs f x u) :
    tupleType obs u = tupleType obs x :=
  (h.sound_for_grammar G hL hK).1

/-- Accepting contexts transport from the source tuple to a reachable tuple. -/
theorem mem_right_for_grammar
    {N : Type w}
    (G : WorkingMCFG N α)
    {d : Nat} {x u : Tuple α d}
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hK : PositiveSample G K)
    (h : SampleLearnerReachable K obs f x u)
    {c : NamedSentenceContext α d}
    (hc : namedFill d c x ∈ G.StringLanguage) :
    namedFill d c u ∈ G.StringLanguage :=
  fixedNamedDistributionalEquivalent_mem_left
    (x := u)
    (y := x)
    (c := c)
    (h.sound_for_grammar G hL hK)
    hc

end SampleLearnerReachable

end ReachableClosure


section AnchorSimulation

variable {N : Type w} {α : Type u} {M : Type v} [Monoid M]

/-- Rule-by-rule simulation data for a target grammar.

For each nonterminal `A`, `anchor A` is the tuple from which the sample learner
will simulate all target derivations rooted at `A`.  The terminal, binary, and
start fields say that every target rule can be simulated from these anchors.

Later, the characteristic sample will be used to construct such data. -/
structure AnchorSimulation
    (G : WorkingMCFG N α)
    (K : Finset (Word α)) (obs : α → M) (f : Nat) where
  anchor : ∀ A : N, Tuple α (G.arity A)
  terminalReachable :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        SampleLearnerReachable K obs f
          (anchor ρ.lhs)
          (castTuple hwt.symm ρ.outputTuple)
  binaryReachable :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        SampleLearnerReachable K obs f
          (anchor ρ.lhs)
          (ρ.apply (anchor ρ.left) (anchor ρ.right))
  binaryEvidence :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        Σ parent : NamedSentenceContext α (G.arity ρ.lhs),
          SampleBinaryEvidence K parent ρ.body
            (anchor ρ.left) (anchor ρ.right)
  startReachable :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        SampleLearnerReachable K obs f
          (anchor G.start)
          (castTuple hwt (anchor ρ.child))

namespace AnchorSimulation

variable {G : WorkingMCFG N α}
variable {K : Finset (Word α)} {obs : α → M} {f : Nat}

/-- A target derivation is simulated by the sample learner from the chosen
anchor tuple, assuming rule-by-rule anchor simulation data. -/
theorem simulates_derivation
    (S : AnchorSimulation G K obs f)
    (hfan : G.FanoutAtMost f)
    {A : N} {x : Tuple α (G.arity A)}
    (h : DerivesTuple G A x) :
    SampleLearnerReachable K obs f (S.anchor A) x := by
  induction h with
  | @terminal ρ hρ hwt =>
      exact S.terminalReachable ρ hρ hwt
  | @binary ρ hρ x y hx hy ihx ihy =>
      have hRule :
          SampleLearnerReachable K obs f
            (S.anchor ρ.lhs)
            (ρ.apply (S.anchor ρ.left) (S.anchor ρ.right)) := by
        exact S.binaryReachable ρ hρ
      rcases S.binaryEvidence ρ hρ with ⟨parent, B⟩
      have hChildren :
          SampleLearnerReachable K obs f
            (ρ.apply (S.anchor ρ.left) (S.anchor ρ.right))
            (ρ.apply x y) := by
        change SampleLearnerReachable K obs f
          (evalTemplateTuple ρ.body (S.anchor ρ.left) (S.anchor ρ.right))
          (evalTemplateTuple ρ.body x y)
        exact SampleLearnerReachable.binary
          (hfan ρ.lhs) (G.arity_pos ρ.lhs) B ihx ihy
      exact SampleLearnerReachable.trans hRule hChildren
  | @start ρ hρ x hx hwt ihx =>
      have hStart :
          SampleLearnerReachable K obs f
            (S.anchor G.start)
            (castTuple hwt (S.anchor ρ.child)) :=
        S.startReachable ρ hρ hwt
      have hChild :
          SampleLearnerReachable K obs f
            (castTuple hwt (S.anchor ρ.child))
            (castTuple hwt x) :=
        SampleLearnerReachable.arityCast hwt ihx
      exact SampleLearnerReachable.trans hStart hChild

end AnchorSimulation

end AnchorSimulation

end MCFG
