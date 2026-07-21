/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.CompletenessSkeleton

/-!
# CharacteristicSampleSkeleton.lean

Thirteenth clean Lean experiment for the fixed-observation MCFG project.

This file packages the characteristic-sample side of the completeness proof.

It still does not construct the characteristic sample algorithmically.  Instead,
it defines a data record saying that a finite sample `K` contains the anchor
and rule-witness examples needed to simulate every target rule.  From such data
we build the `AnchorSimulation` object of `CompletenessSkeleton.lean`.

This is the Lean skeleton of the paper argument:

`CS(G̃₀) ⊆ K`  ⇒  every target rule is simulated by the learner
              ⇒  every target derivation is simulated by the learner.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section CharacteristicData

variable {N : Type w} {α : Type u} {M : Type v} [Monoid M]

/-- Characteristic-sample data sufficient for rule-by-rule anchor simulation.

For each nonterminal `A`, `anchor A` is the chosen representative tuple, and
`expose A` is the named context in which the sample exposes that representative.
The remaining fields say that the sample contains the terminal, binary, and
start-rule comparison examples needed to generate unit steps and binary
witnesses in the sample learner. -/
structure CharacteristicSampleData
    (G : WorkingMCFG N α)
    (K : Finset (Word α)) (obs : α → M) (f : Nat) where
  anchor : ∀ A : N, Tuple α (G.arity A)
  expose : ∀ A : N, NamedSentenceContext α (G.arity A)

  anchor_mem :
    ∀ A : N,
      namedFill (G.arity A) (expose A) (anchor A) ∈ K

  terminal_mem :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        namedFill (G.arity ρ.lhs) (expose ρ.lhs)
          (castTuple hwt.symm ρ.outputTuple) ∈ K

  terminal_type_eq :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        tupleType obs (anchor ρ.lhs) =
          tupleType obs (castTuple hwt.symm ρ.outputTuple)

  binary_mem :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        namedFill (G.arity ρ.lhs) (expose ρ.lhs)
          (ρ.apply (anchor ρ.left) (anchor ρ.right)) ∈ K

  binary_type_eq :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        tupleType obs (anchor ρ.lhs) =
          tupleType obs (ρ.apply (anchor ρ.left) (anchor ρ.right))

  binary_leftIdentity :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        LeftFillingIdentity namedFill (expose ρ.lhs) ρ.body (anchor ρ.right)

  binary_rightIdentity :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        ∀ u : Tuple α (G.arity ρ.left),
          RightFillingIdentity namedFill (expose ρ.lhs) ρ.body u

  start_mem :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        namedFill (G.arity G.start) (expose G.start)
          (castTuple hwt (anchor ρ.child)) ∈ K

  start_type_eq :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        tupleType obs (anchor G.start) =
          tupleType obs (castTuple hwt (anchor ρ.child))

namespace CharacteristicSampleData

variable {G : WorkingMCFG N α}
variable {K : Finset (Word α)} {obs : α → M} {f : Nat}

/-- Terminal-rule sample evidence induced by characteristic-sample data. -/
def terminalUnitEvidence
    (D : CharacteristicSampleData G K obs f)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    SampleUnitEvidence K obs
      (D.anchor ρ.lhs)
      (castTuple hwt.symm ρ.outputTuple) :=
  { context := D.expose ρ.lhs,
    type_eq := D.terminal_type_eq ρ hρ hwt,
    left_mem := D.anchor_mem ρ.lhs,
    right_mem := D.terminal_mem ρ hρ hwt }

/-- Binary-rule unit evidence comparing the parent anchor with the composed
tuple of child anchors. -/
def binaryUnitEvidence
    (D : CharacteristicSampleData G K obs f)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    SampleUnitEvidence K obs
      (D.anchor ρ.lhs)
      (ρ.apply (D.anchor ρ.left) (D.anchor ρ.right)) :=
  { context := D.expose ρ.lhs,
    type_eq := D.binary_type_eq ρ hρ,
    left_mem := D.anchor_mem ρ.lhs,
    right_mem := D.binary_mem ρ hρ }

/-- Binary-rule sample evidence induced by characteristic-sample data. -/
def binaryEvidence
    (D : CharacteristicSampleData G K obs f)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    SampleBinaryEvidence K (D.expose ρ.lhs) ρ.body
      (D.anchor ρ.left) (D.anchor ρ.right) :=
  { parent_mem := D.binary_mem ρ hρ,
    leftIdentity := D.binary_leftIdentity ρ hρ,
    rightIdentity := D.binary_rightIdentity ρ hρ }

/-- Start-rule unit evidence comparing the start anchor with the transported
child anchor. -/
def startUnitEvidence
    (D : CharacteristicSampleData G K obs f)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    SampleUnitEvidence K obs
      (D.anchor G.start)
      (castTuple hwt (D.anchor ρ.child)) :=
  { context := D.expose G.start,
    type_eq := D.start_type_eq ρ hρ hwt,
    left_mem := D.anchor_mem G.start,
    right_mem := D.start_mem ρ hρ hwt }

/-- Characteristic-sample data yields anchor-simulation data. -/
def toAnchorSimulation
    (D : CharacteristicSampleData G K obs f)
    (hfan : G.FanoutAtMost f) :
    AnchorSimulation G K obs f where
  anchor := D.anchor
  terminalReachable := by
    intro ρ hρ hwt
    exact SampleLearnerReachable.unit
      (hfan ρ.lhs) (G.arity_pos ρ.lhs)
      (D.terminalUnitEvidence ρ hρ hwt)
      (SampleLearnerReachable.self
        (castTuple hwt.symm ρ.outputTuple))
  binaryReachable := by
    intro ρ hρ
    exact SampleLearnerReachable.unit
      (hfan ρ.lhs) (G.arity_pos ρ.lhs)
      (D.binaryUnitEvidence ρ hρ)
      (SampleLearnerReachable.self
        (ρ.apply (D.anchor ρ.left) (D.anchor ρ.right)))
  binaryEvidence := by
    intro ρ hρ
    exact ⟨D.expose ρ.lhs, D.binaryEvidence ρ hρ⟩
  startReachable := by
    intro ρ hρ hwt
    exact SampleLearnerReachable.unit
      (hfan G.start) (G.arity_pos G.start)
      (D.startUnitEvidence ρ hρ hwt)
      (SampleLearnerReachable.self
        (castTuple hwt (D.anchor ρ.child)))

/-- Any target derivation is simulated from the corresponding anchor, provided
the finite sample contains the characteristic rule-witness data. -/
theorem simulates_derivation
    (D : CharacteristicSampleData G K obs f)
    (hfan : G.FanoutAtMost f)
    {A : N} {x : Tuple α (G.arity A)}
    (h : DerivesTuple G A x) :
    SampleLearnerReachable K obs f (D.anchor A) x :=
  (D.toAnchorSimulation hfan).simulates_derivation hfan h

/-- A string in the target language is reachable from the start anchor, after
transporting the singleton tuple along the start arity equality supplied by the
language membership witness. -/
theorem reaches_of_string_mem
    (D : CharacteristicSampleData G K obs f)
    (hfan : G.FanoutAtMost f)
    {word : Word α}
    (hword : word ∈ G.StringLanguage) :
    ∃ hstart : 1 = G.arity G.start,
      SampleLearnerReachable K obs f
        (D.anchor G.start)
        (castTuple hstart (singletonTuple word)) := by
  rcases hword with ⟨hstart, hderiv⟩
  exact ⟨hstart, D.simulates_derivation hfan hderiv⟩

/-- If the sample is positive and the target satisfies the fixed-observation
promise, then every reachable target derivation from characteristic-sample data
is sound as well.  This is mainly a convenient combined corollary. -/
theorem simulated_derivation_sound
    (D : CharacteristicSampleData G K obs f)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hK : PositiveSample G K)
    {A : N} {x : Tuple α (G.arity A)}
    (h : DerivesTuple G A x) :
    GrammarNamedDistributionalEquivalent G obs x (D.anchor A) :=
  (D.simulates_derivation hfan h).sound_for_grammar G hL hK

end CharacteristicSampleData

end CharacteristicData

end MCFG
