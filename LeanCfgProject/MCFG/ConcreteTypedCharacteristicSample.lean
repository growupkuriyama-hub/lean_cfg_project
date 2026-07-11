/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteObservationDeterministicClosure

/-!
# ConcreteTypedCharacteristicSample.lean

The base-indexed pre-core route chooses one output type for every base
nonterminal.  That choice requires `TupleTypeDeterministic` and is not valid for
general output-type refinements.

This file removes that restriction instead of strengthening it.

The characteristic construction is indexed directly by the successful typed
nonterminals of a complete finite output-type presentation.  Thus every
terminal and binary rule has exactly the typed parent and child anchors required
by that rule.  Start rules are handled without one global start anchor: for
each typed start rule, the finite sample contains the actual word obtained from
its child anchor.

The file constructs four finite components:

* exposed anchor words for all present typed nonterminals;
* terminal comparison words for all present typed terminal rules;
* binary comparison words for all present typed binary rules;
* one start word for every present typed start rule.

It proves positivity of the concrete finite union, recursively simulates every
`PresentationDerives` derivation from the corresponding typed anchor, and
simulates every `PresentationStringDerives` derivation from its rule-specific
sample start word.

For a complete presentation this yields exact reconstruction of the original
grammar language by `ReachableSampleStringLanguage`.  Instantiating the generic
construction with the concrete successful trim removes all of the following
supplied data:

* a base representative for every base nonterminal;
* `TupleTypeDeterministic`;
* terminal/binary/start parent representative equalities;
* a global start anchor and its output type;
* canonical-rule-closure data.

No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section SmallTransportLemmas

variable {α : Type u}

/-- Undo the transport used in `tupleWordOfArityOne`. -/
theorem singletonTuple_tupleWordOfArityOne
    {d : Nat}
    (h : 1 = d)
    (x : Tuple α d) :
    singletonTuple (tupleWordOfArityOne h x) =
      castTuple h.symm x := by
  cases h
  exact castTuple_singleton_tupleWordOfArityOne rfl x

/-- A singleton-tuple equality transported to arity `d` can be transported
back to an ordinary singleton equality. -/
theorem castTuple_symm_eq_singleton_of_singleton_cast_eq
    {d : Nat}
    (h : 1 = d)
    {word : Word α}
    {x : Tuple α d}
    (hx :
      castTuple h (singletonTuple word) = x) :
    castTuple h.symm x = singletonTuple word := by
  subst x
  cases h
  rfl

end SmallTransportLemmas


section PresentNodeUtilities

variable {N : Type v} {α : Type u} {M : Type w}
variable [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {P : OutputTypeRefinementPresentation G obs}

/-- Present typed nonterminals are equal when their underlying typed nodes are
equal; membership proofs carry no additional data. -/
theorem PresentTypedNonterminal.eq_of_node_eq
    {X Y : PresentTypedNonterminal P}
    (h : X.node = Y.node) :
    X = Y := by
  cases X with
  | mk X hX =>
      cases Y with
      | mk Y hY =>
          cases h
          rfl

namespace PresentationDerives

/-- Every node at the root of a presentation derivation is present. -/
theorem node_present
    {X : TypedNonterminal G M}
    {x : Tuple α (G.arity X.base)}
    (h : PresentationDerives P X x) :
    P.HasNonterminal X := by
  cases h with
  | terminal hτ =>
      exact P.terminal_lhs_present hτ
  | binary hτ hx hy =>
      exact P.binary_lhs_present hτ

/-- Package the root node of a presentation derivation as a present typed
nonterminal. -/
def presentNode
    {X : TypedNonterminal G M}
    {x : Tuple α (G.arity X.base)}
    (h : PresentationDerives P X x) :
    PresentTypedNonterminal P :=
  ⟨X, h.node_present⟩

end PresentationDerives

end PresentNodeUtilities


section TypedCharacteristicWords

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- The present typed lhs of an attached terminal rule. -/
def typedTerminalLHS
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (τ : S.completePresentation.presentation.terminalRules.attach) :
    PresentTypedNonterminal
      S.completePresentation.presentation :=
  ⟨τ.1.lhs obs,
    S.completePresentation.presentation.terminal_lhs_present τ.2⟩

/-- The present typed lhs of an attached binary rule. -/
def typedBinaryLHS
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (τ : S.completePresentation.presentation.binaryRules.attach) :
    PresentTypedNonterminal
      S.completePresentation.presentation :=
  ⟨τ.1.lhs obs,
    S.completePresentation.presentation.binary_lhs_present τ.2⟩

/-- The present typed left child of an attached binary rule. -/
def typedBinaryLeft
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (τ : S.completePresentation.presentation.binaryRules.attach) :
    PresentTypedNonterminal
      S.completePresentation.presentation :=
  ⟨τ.1.left,
    S.completePresentation.presentation.binary_left_present τ.2⟩

/-- The present typed right child of an attached binary rule. -/
def typedBinaryRight
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (τ : S.completePresentation.presentation.binaryRules.attach) :
    PresentTypedNonterminal
      S.completePresentation.presentation :=
  ⟨τ.1.right,
    S.completePresentation.presentation.binary_right_present τ.2⟩

/-- The present typed child of an attached start rule. -/
def typedStartChild
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (σ : S.completePresentation.presentation.startRules.attach) :
    PresentTypedNonterminal
      S.completePresentation.presentation :=
  ⟨σ.1.child,
    S.completePresentation.presentation.start_child_present σ.2⟩

/-- Exposed anchor word of one attached present typed nonterminal. -/
def typedAnchorWord
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (X : S.completePresentation.presentation.nonterminals.attach) :
    Word α :=
  let PX :
      PresentTypedNonterminal
        S.completePresentation.presentation :=
    ⟨X.1, X.2⟩
  let O := S.occurrences.occurrence PX
  namedFill (G.arity PX.node.base)
    O.expose O.anchor

/-- Terminal comparison word attached to a present typed terminal rule. -/
def typedTerminalWord
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (τ : S.completePresentation.presentation.terminalRules.attach) :
    Word α :=
  let O :=
    S.occurrences.occurrence
      (typedTerminalLHS S τ)
  namedFill
    (G.arity τ.1.baseRule.lhs)
    O.expose
    (castTuple τ.1.wellTyped.symm
      τ.1.baseRule.outputTuple)

/-- Binary comparison word attached to a present typed binary rule. -/
def typedBinaryWord
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (τ : S.completePresentation.presentation.binaryRules.attach) :
    Word α :=
  let OL :=
    S.occurrences.occurrence
      (typedBinaryLeft S τ)
  let OR :=
    S.occurrences.occurrence
      (typedBinaryRight S τ)
  let OP :=
    S.occurrences.occurrence
      (typedBinaryLHS S τ)
  namedFill
    (G.arity τ.1.baseRule.lhs)
    OP.expose
    (τ.1.baseRule.apply OL.anchor OR.anchor)

/-- Rule-specific sample start word attached to a present typed start rule.

This replaces the single global start anchor used by the base-indexed route. -/
def typedStartWord
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hstart : 1 = G.arity G.start)
    (σ : S.completePresentation.presentation.startRules.attach) :
    Word α :=
  let O :=
    S.occurrences.occurrence
      (typedStartChild S σ)
  tupleWordOfArityOne hstart
    (castTuple σ.1.wellTyped O.anchor)

end TypedCharacteristicWords


section FiniteTypedCharacteristicSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Finite exposed-anchor component. -/
def typedAnchorSample
    (S : SuccessfulOccurrenceCompletePresentation G obs) :
    Finset (Word α) :=
  S.completePresentation.presentation.nonterminals.attach.image
    (typedAnchorWord S)

/-- Finite terminal-comparison component. -/
def typedTerminalSample
    (S : SuccessfulOccurrenceCompletePresentation G obs) :
    Finset (Word α) :=
  S.completePresentation.presentation.terminalRules.attach.image
    (typedTerminalWord S)

/-- Finite binary-comparison component. -/
def typedBinarySample
    (S : SuccessfulOccurrenceCompletePresentation G obs) :
    Finset (Word α) :=
  S.completePresentation.presentation.binaryRules.attach.image
    (typedBinaryWord S)

/-- Finite start-word component. -/
def typedStartSample
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hstart : 1 = G.arity G.start) :
    Finset (Word α) :=
  S.completePresentation.presentation.startRules.attach.image
    (typedStartWord S hstart)

/-- The concrete typed characteristic sample. -/
def typedCharacteristicSample
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hstart : 1 = G.arity G.start) :
    Finset (Word α) :=
  typedAnchorSample S ∪
    (typedTerminalSample S ∪
      (typedBinarySample S ∪
        typedStartSample S hstart))

theorem typedAnchorWord_mem
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (X : PresentTypedNonterminal
      S.completePresentation.presentation)
    (hstart : 1 = G.arity G.start) :
    let AX :
      S.completePresentation.presentation.nonterminals.attach :=
        ⟨X.node, X.mem⟩
    typedAnchorWord S AX ∈
      typedCharacteristicSample S hstart := by
  dsimp
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_image.mpr
  exact ⟨⟨X.node, X.mem⟩, by simp, rfl⟩

theorem typedTerminalWord_mem
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (τ : S.completePresentation.presentation.terminalRules.attach)
    (hstart : 1 = G.arity G.start) :
    typedTerminalWord S τ ∈
      typedCharacteristicSample S hstart := by
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_image.mpr
  exact ⟨τ, by simp, rfl⟩

theorem typedBinaryWord_mem
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (τ : S.completePresentation.presentation.binaryRules.attach)
    (hstart : 1 = G.arity G.start) :
    typedBinaryWord S τ ∈
      typedCharacteristicSample S hstart := by
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_image.mpr
  exact ⟨τ, by simp, rfl⟩

theorem typedStartWord_mem
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (σ : S.completePresentation.presentation.startRules.attach)
    (hstart : 1 = G.arity G.start) :
    typedStartWord S hstart σ ∈
      typedCharacteristicSample S hstart := by
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_image.mpr
  exact ⟨σ, by simp, rfl⟩

end FiniteTypedCharacteristicSample


section TypedCharacteristicPositivity

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

theorem typedAnchorWord_positive
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (X : PresentTypedNonterminal
      S.completePresentation.presentation) :
    let AX :
      S.completePresentation.presentation.nonterminals.attach :=
        ⟨X.node, X.mem⟩
    typedAnchorWord S AX ∈ G.StringLanguage := by
  dsimp [typedAnchorWord]
  exact (S.occurrences.occurrence X).expose_accepts_anchor

theorem typedTerminalWord_positive
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (τ : S.completePresentation.presentation.terminalRules.attach) :
    typedTerminalWord S τ ∈ G.StringLanguage := by
  let O :=
    S.occurrences.occurrence
      (typedTerminalLHS S τ)
  have hderives :
      DerivesTuple G τ.1.baseRule.lhs
        (castTuple τ.1.wellTyped.symm
          τ.1.baseRule.outputTuple) :=
    DerivesTuple.terminal
      τ.1.inGrammar τ.1.wellTyped
  exact O.expose_accepts_derives hderives

theorem typedBinaryWord_positive
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (τ : S.completePresentation.presentation.binaryRules.attach) :
    typedBinaryWord S τ ∈ G.StringLanguage := by
  let OL :=
    S.occurrences.occurrence
      (typedBinaryLeft S τ)
  let OR :=
    S.occurrences.occurrence
      (typedBinaryRight S τ)
  let OP :=
    S.occurrences.occurrence
      (typedBinaryLHS S τ)
  have hderives :
      DerivesTuple G τ.1.baseRule.lhs
        (τ.1.baseRule.apply OL.anchor OR.anchor) :=
    DerivesTuple.binary
      τ.1.inGrammar
      OL.anchorDerives
      OR.anchorDerives
  exact OP.expose_accepts_derives hderives

theorem typedStartWord_positive
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hstart : 1 = G.arity G.start)
    (σ : S.completePresentation.presentation.startRules.attach) :
    typedStartWord S hstart σ ∈ G.StringLanguage := by
  let O :=
    S.occurrences.occurrence
      (typedStartChild S σ)
  have hderives :
      DerivesTuple G G.start
        (castTuple σ.1.wellTyped O.anchor) :=
    DerivesTuple.start
      σ.1.inGrammar
      O.anchorDerives
      σ.1.wellTyped
  apply mem_StringLanguage_of_start_derives
    G (typedStartWord S hstart σ) hstart
  rw [castTuple_singleton_tupleWordOfArityOne]
  exact hderives

/-- The concrete finite typed characteristic sample is positive. -/
theorem typedCharacteristicSample_positive
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hstart : 1 = G.arity G.start) :
    (typedCharacteristicSample S hstart : Set (Word α)) ⊆
      G.StringLanguage := by
  intro word hword
  simp only [typedCharacteristicSample,
    Finset.mem_union] at hword
  rcases hword with hA | hT | hB | hS
  · have hA' :
        word ∈
          S.completePresentation.presentation.nonterminals.attach.image
            (typedAnchorWord S) := by
      simpa [typedAnchorSample] using hA
    rcases Finset.mem_image.mp hA' with ⟨X, _hX, hEq⟩
    rw [← hEq]
    let PX :
        PresentTypedNonterminal
          S.completePresentation.presentation :=
      ⟨X.1, X.2⟩
    simpa [PX, typedAnchorWord] using
      (typedAnchorWord_positive S PX)
  · have hT' :
        word ∈
          S.completePresentation.presentation.terminalRules.attach.image
            (typedTerminalWord S) := by
      simpa [typedTerminalSample] using hT
    rcases Finset.mem_image.mp hT' with ⟨τ, _hτ, hEq⟩
    rw [← hEq]
    exact typedTerminalWord_positive S τ
  · have hB' :
        word ∈
          S.completePresentation.presentation.binaryRules.attach.image
            (typedBinaryWord S) := by
      simpa [typedBinarySample] using hB
    rcases Finset.mem_image.mp hB' with ⟨τ, _hτ, hEq⟩
    rw [← hEq]
    exact typedBinaryWord_positive S τ
  · have hS' :
        word ∈
          S.completePresentation.presentation.startRules.attach.image
            (typedStartWord S hstart) := by
      simpa [typedStartSample] using hS
    rcases Finset.mem_image.mp hS' with ⟨σ, _hσ, hEq⟩
    rw [← hEq]
    exact typedStartWord_positive S hstart σ

end TypedCharacteristicPositivity


section TypedPresentationSimulation

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

/-- The occurrence anchor attached to a present typed nonterminal. -/
def successfulTypedAnchor
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (X : PresentTypedNonterminal
      S.completePresentation.presentation) :
    Tuple α (G.arity X.node.base) :=
  (S.occurrences.occurrence X).anchor

/-- The exposing context attached to a present typed nonterminal. -/
def successfulTypedExpose
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (X : PresentTypedNonterminal
      S.completePresentation.presentation) :
    NamedSentenceContext α (G.arity X.node.base) :=
  (S.occurrences.occurrence X).expose

/-- Anchor-word membership in the finite typed characteristic sample. -/
theorem successfulTypedAnchor_mem
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hstart : 1 = G.arity G.start)
    (X : PresentTypedNonterminal
      S.completePresentation.presentation) :
    namedFill (G.arity X.node.base)
        (successfulTypedExpose S X)
        (successfulTypedAnchor S X) ∈
      typedCharacteristicSample S hstart := by
  simpa [successfulTypedAnchor, successfulTypedExpose,
    typedAnchorWord] using
      (typedAnchorWord_mem S X hstart)

/-- Terminal unit evidence for a present typed terminal rule. -/
def typedTerminalUnitEvidence
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hstart : 1 = G.arity G.start)
    (τ : S.completePresentation.presentation.terminalRules.attach) :
    SampleUnitEvidence
      (typedCharacteristicSample S hstart)
      obs
      (successfulTypedAnchor S (typedTerminalLHS S τ))
      (castTuple τ.1.wellTyped.symm
        τ.1.baseRule.outputTuple) := by
  let O :=
    S.occurrences.occurrence
      (typedTerminalLHS S τ)
  exact
    { context := O.expose
      type_eq :=
        O.anchor_matches.trans
          (τ.1.cast_outputTuple_matches_lhs obs).symm
      left_mem :=
        successfulTypedAnchor_mem S hstart
          (typedTerminalLHS S τ)
      right_mem :=
        typedTerminalWord_mem S τ hstart }

/-- Parent unit evidence for a present typed binary rule. -/
def typedBinaryUnitEvidence
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hstart : 1 = G.arity G.start)
    (τ : S.completePresentation.presentation.binaryRules.attach) :
    SampleUnitEvidence
      (typedCharacteristicSample S hstart)
      obs
      (successfulTypedAnchor S (typedBinaryLHS S τ))
      (τ.1.baseRule.apply
        (successfulTypedAnchor S (typedBinaryLeft S τ))
        (successfulTypedAnchor S (typedBinaryRight S τ))) := by
  let OP :=
    S.occurrences.occurrence
      (typedBinaryLHS S τ)
  let OL :=
    S.occurrences.occurrence
      (typedBinaryLeft S τ)
  let OR :=
    S.occurrences.occurrence
      (typedBinaryRight S τ)
  have happly :
      tupleType obs
          (τ.1.baseRule.apply OL.anchor OR.anchor) =
        (τ.1.lhs obs).out :=
    τ.1.apply_matches_lhs obs
      OL.anchor_matches
      OR.anchor_matches
  exact
    { context := OP.expose
      type_eq :=
        OP.anchor_matches.trans happly.symm
      left_mem :=
        successfulTypedAnchor_mem S hstart
          (typedBinaryLHS S τ)
      right_mem :=
        typedBinaryWord_mem S τ hstart }

/-- Exact-once binary evidence for a present typed binary rule. -/
def typedBinaryEvidence
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hworking : G.ExactWorkingConditions)
    (hstart : 1 = G.arity G.start)
    (τ : S.completePresentation.presentation.binaryRules.attach) :
    SampleBinaryEvidence
      (typedCharacteristicSample S hstart)
      (successfulTypedExpose S (typedBinaryLHS S τ))
      τ.1.baseRule.body
      (successfulTypedAnchor S (typedBinaryLeft S τ))
      (successfulTypedAnchor S (typedBinaryRight S τ)) := by
  let OP :=
    S.occurrences.occurrence
      (typedBinaryLHS S τ)
  let OL :=
    S.occurrences.occurrence
      (typedBinaryLeft S τ)
  let OR :=
    S.occurrences.occurrence
      (typedBinaryRight S τ)
  let splice :=
    ExactSplicing.exactSplice
      OP.expose
      τ.1.baseRule.body
      (hworking.2 τ.1.baseRule τ.1.inGrammar)
  exact
    { parent_mem :=
        typedBinaryWord_mem S τ hstart
      leftIdentity :=
        splice.leftIdentity OR.anchor
      rightIdentity :=
        fun u => splice.rightIdentity u }

/-- Every typed presentation derivation is simulated from its own typed
anchor.  No base representative or tuple-type determinism is used. -/
theorem presentationDerives_reachable_from_typed_anchor
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    {X : TypedNonterminal G M}
    {x : Tuple α (G.arity X.base)}
    (h : PresentationDerives
      S.completePresentation.presentation X x) :
    SampleLearnerReachable
      (typedCharacteristicSample S hworking.basic.1.symm)
      obs f
      (successfulTypedAnchor S h.presentNode)
      x := by
  induction h with

  | terminal hτ =>
      let τa :
          S.completePresentation.presentation.terminalRules.attach :=
        ⟨τ, hτ⟩
      have hnode :
          (PresentationDerives.terminal hτ).presentNode =
            typedTerminalLHS S τa :=
        PresentTypedNonterminal.eq_of_node_eq rfl
      rw [hnode]
      exact
        SampleLearnerReachable.unit
          (hfan τ.baseRule.lhs)
          (G.arity_pos τ.baseRule.lhs)
          (typedTerminalUnitEvidence
            S hworking.basic.1.symm τa)
          (SampleLearnerReachable.self
            (castTuple τ.wellTyped.symm
              τ.baseRule.outputTuple))

  | binary hτ hx hy ihx ihy =>
      let τa :
          S.completePresentation.presentation.binaryRules.attach :=
        ⟨τ, hτ⟩

      have hleft :
          hx.presentNode =
            typedBinaryLeft S τa :=
        PresentTypedNonterminal.eq_of_node_eq rfl
      have hright :
          hy.presentNode =
            typedBinaryRight S τa :=
        PresentTypedNonterminal.eq_of_node_eq rfl
      have hlhs :
          (PresentationDerives.binary hτ hx hy).presentNode =
            typedBinaryLHS S τa :=
        PresentTypedNonterminal.eq_of_node_eq rfl

      have ihx' := ihx
      rw [hleft] at ihx'

      have ihy' := ihy
      rw [hright] at ihy'

      have hparent :
          SampleLearnerReachable
            (typedCharacteristicSample S hworking.basic.1.symm)
            obs f
            (successfulTypedAnchor S
              (typedBinaryLHS S τa))
            (τ.baseRule.apply
              (successfulTypedAnchor S
                (typedBinaryLeft S τa))
              (successfulTypedAnchor S
                (typedBinaryRight S τa))) :=
        SampleLearnerReachable.unit
          (hfan τ.baseRule.lhs)
          (G.arity_pos τ.baseRule.lhs)
          (typedBinaryUnitEvidence
            S hworking.basic.1.symm τa)
          (SampleLearnerReachable.self _)

      have hchildren :
          SampleLearnerReachable
            (typedCharacteristicSample S hworking.basic.1.symm)
            obs f
            (τ.baseRule.apply
              (successfulTypedAnchor S
                (typedBinaryLeft S τa))
              (successfulTypedAnchor S
                (typedBinaryRight S τa)))
            (τ.baseRule.apply x y) := by
        change
          SampleLearnerReachable
            (typedCharacteristicSample S hworking.basic.1.symm)
            obs f
            (evalTemplateTuple τ.baseRule.body
              (successfulTypedAnchor S
                (typedBinaryLeft S τa))
              (successfulTypedAnchor S
                (typedBinaryRight S τa)))
            (evalTemplateTuple τ.baseRule.body x y)
        exact
          SampleLearnerReachable.binary
            (hfan τ.baseRule.lhs)
            (G.arity_pos τ.baseRule.lhs)
            (typedBinaryEvidence
              S hworking hworking.basic.1.symm τa)
            ihx' ihy'

      rw [hlhs]
      exact SampleLearnerReachable.trans
        hparent hchildren

end TypedPresentationSimulation


section TypedStringSimulation

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

/-- Every word derived by the complete typed presentation is reachable from
the rule-specific start word placed in the concrete typed characteristic
sample. -/
theorem presentationStringDerives_reachable
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    {word : Word α}
    (D :
      PresentationStringDerives
        S.completePresentation.presentation word) :
    word ∈
      ReachableSampleStringLanguage
        (typedCharacteristicSample S hworking.basic.1.symm)
        obs f := by

  let σa :
      S.completePresentation.presentation.startRules.attach :=
    ⟨D.startRule, D.start_mem⟩

  let childPresent :=
    typedStartChild S σa

  have hchildNode :
      D.child_derives.presentNode =
        childPresent :=
    PresentTypedNonterminal.eq_of_node_eq rfl

  have hchild :
      SampleLearnerReachable
        (typedCharacteristicSample S hworking.basic.1.symm)
        obs f
        (successfulTypedAnchor S childPresent)
        D.childTuple := by
    simpa [hchildNode] using
      presentationDerives_reachable_from_typed_anchor
        S hworking hfan D.child_derives

  have hstartArity :
      SampleLearnerReachable
        (typedCharacteristicSample S hworking.basic.1.symm)
        obs f
        (castTuple D.startRule.wellTyped
          (successfulTypedAnchor S childPresent))
        (castTuple D.startRule.wellTyped
          D.childTuple) :=
    SampleLearnerReachable.arityCast
      D.startRule.wellTyped hchild

  have hone :
      SampleLearnerReachable
        (typedCharacteristicSample S hworking.basic.1.symm)
        obs f
        (castTuple D.start_arity.symm
          (castTuple D.startRule.wellTyped
            (successfulTypedAnchor S childPresent)))
        (castTuple D.start_arity.symm
          (castTuple D.startRule.wellTyped
            D.childTuple)) :=
    SampleLearnerReachable.arityCast
      D.start_arity.symm hstartArity

  have hsource :
      singletonTuple
          (typedStartWord S D.start_arity σa) =
        castTuple D.start_arity.symm
          (castTuple D.startRule.wellTyped
            (successfulTypedAnchor S childPresent)) := by
    exact singletonTuple_tupleWordOfArityOne
      D.start_arity
      (castTuple D.startRule.wellTyped
        (successfulTypedAnchor S childPresent))

  have htarget :
      castTuple D.start_arity.symm
          (castTuple D.startRule.wellTyped
            D.childTuple) =
        singletonTuple word :=
    castTuple_symm_eq_singleton_of_singleton_cast_eq
      D.start_arity D.word_eq

  exact
    { startWord :=
        typedStartWord S D.start_arity σa
      start_mem := by
        have hp :
            D.start_arity =
              hworking.basic.1.symm :=
          Subsingleton.elim _ _
        cases hp
        exact typedStartWord_mem
          S σa hworking.basic.1.symm
      reachable := by
        rw [hsource, ← htarget]
        exact hone }

/-- The language of a complete successful typed presentation is contained in
the reachable sample language generated by its concrete typed characteristic
sample. -/
theorem completePresentation_subset_reachable_typedSample
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f) :
    G.StringLanguage ⊆
      ReachableSampleStringLanguage
        (typedCharacteristicSample S hworking.basic.1.symm)
        obs f := by
  intro word hword
  exact presentationStringDerives_reachable
    S hworking hfan
    (S.completePresentation.complete.mem_presentation hword)

/-- Exact reconstruction for a complete successful typed presentation. -/
theorem typedCharacteristicSample_exact_reconstruction
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ReachableSampleStringLanguage
        (typedCharacteristicSample S hworking.basic.1.symm)
        obs f =
      G.StringLanguage := by
  apply Set.Subset.antisymm
  · exact reachableSampleStringLanguage_sound
      G hL
      (typedCharacteristicSample_positive
        S hworking.basic.1.symm)
  · exact completePresentation_subset_reachable_typedSample
      S hworking hfan

end TypedStringSimulation



section SampleReachabilityMonotonicity

variable {α : Type u} {M : Type w}
variable [Monoid M]
variable {S K : Finset (Word α)}
variable {obs : α → M} {f : Nat}

namespace SampleUnitEvidence

/-- Unit evidence remains valid after enlarging the finite sample. -/
def mono
    {d : Nat}
    {x y : Tuple α d}
    (U : SampleUnitEvidence S obs x y)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α))) :
    SampleUnitEvidence K obs x y where
  context := U.context
  type_eq := U.type_eq
  left_mem := hSK U.left_mem
  right_mem := hSK U.right_mem

end SampleUnitEvidence

namespace SampleBinaryEvidence

/-- Binary evidence remains valid after enlarging the finite sample. -/
def mono
    {e dB dC : Nat}
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x : Tuple α dB}
    {y : Tuple α dC}
    (B : SampleBinaryEvidence S parent body x y)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α))) :
    SampleBinaryEvidence K parent body x y where
  parent_mem := hSK B.parent_mem
  leftIdentity := B.leftIdentity
  rightIdentity := B.rightIdentity

end SampleBinaryEvidence

namespace SampleLearnerDerives

/-- Sample learner derivations are monotone under finite-sample extension. -/
def mono
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    {d : Nat}
    {x y : Tuple α d}
    (h : SampleLearnerDerives S obs f x y) :
    SampleLearnerDerives K obs f x y := by
  induction h with
  | self x =>
      exact SampleLearnerDerives.self x
  | unit hd hpos U hyu ih =>
      exact SampleLearnerDerives.unit
        hd hpos (U.mono hSK) ih
  | binary he hpos B hx hy ihx ihy =>
      exact SampleLearnerDerives.binary
        he hpos (B.mono hSK) ihx ihy

end SampleLearnerDerives

namespace SampleLearnerReachable

/-- Reachable learner derivations are monotone under finite-sample extension. -/
def mono
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    {d : Nat}
    {x y : Tuple α d}
    (h : SampleLearnerReachable S obs f x y) :
    SampleLearnerReachable K obs f x y := by
  induction h with
  | self x =>
      exact SampleLearnerReachable.self x
  | step h =>
      exact SampleLearnerReachable.step
        (h.mono hSK)
  | unit hd hpos U hyu ih =>
      exact SampleLearnerReachable.unit
        hd hpos (U.mono hSK) ih
  | binary he hpos B hx hy ihx ihy =>
      exact SampleLearnerReachable.binary
        he hpos (B.mono hSK) ihx ihy
  | trans hxy hyz ihxy ihyz =>
      exact SampleLearnerReachable.trans ihxy ihyz

end SampleLearnerReachable

end SampleReachabilityMonotonicity


section ConcreteTypedRoute

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M]
variable [DecidableEq α] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

/-- The fully concrete typed characteristic sample obtained directly from the
successful trim of `G`. -/
noncomputable def concreteTypedCharacteristicSample
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated) :
    Finset (Word α) :=
  typedCharacteristicSample
    (concreteSuccessfulOccurrenceCompletePresentation
      (obs := obs) hworking hsep)
    hworking.basic.1.symm

/-- The fully concrete typed characteristic sample is positive. -/
theorem concreteTypedCharacteristicSample_positive
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated) :
    (concreteTypedCharacteristicSample
      (obs := obs) hworking hsep : Set (Word α)) ⊆
      G.StringLanguage :=
  typedCharacteristicSample_positive
    (concreteSuccessfulOccurrenceCompletePresentation
      (obs := obs) hworking hsep)
    hworking.basic.1.symm

/-- Exact reconstruction from the concrete typed characteristic sample.

No reducedness, base representative selection, tuple-type determinism, or
canonical parent-output closure is assumed. -/
theorem concreteTypedCharacteristicSample_exact_reconstruction
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ReachableSampleStringLanguage
        (concreteTypedCharacteristicSample
          (obs := obs) hworking hsep)
        obs f =
      G.StringLanguage :=
  typedCharacteristicSample_exact_reconstruction
    (concreteSuccessfulOccurrenceCompletePresentation
      (obs := obs) hworking hsep)
    hworking hfan hL

/-- Every positive finite superset of the concrete typed characteristic sample
also reconstructs the target language exactly. -/
theorem concreteTypedCharacteristicSample_exact_for_positive_superset
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hSK :
      (concreteTypedCharacteristicSample
        (obs := obs) hworking hsep : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKpos :
      (K : Set (Word α)) ⊆
        G.StringLanguage) :
    ReachableSampleStringLanguage K obs f =
      G.StringLanguage := by
  apply Set.Subset.antisymm
  · exact reachableSampleStringLanguage_sound G hL hKpos
  · intro word hword
    have hbase :
        word ∈ ReachableSampleStringLanguage
          (concreteTypedCharacteristicSample
            (obs := obs) hworking hsep)
          obs f := by
      rw [concreteTypedCharacteristicSample_exact_reconstruction
        (obs := obs) hworking hsep hfan hL]
      exact hword
    rcases hbase with
      ⟨startWord, hstartMem, hreach⟩
    exact
      { startWord := startWord
        start_mem := hSK hstartMem
        reachable :=
          SampleLearnerReachable.mono
            hSK hreach }

/-- Eventual prefix-exact reconstruction on every positive text. -/
theorem concreteTypedCharacteristicSample_prefix_exact
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage
            (Ttxt.prefixSample n) obs f =
          G.StringLanguage := by
  intro Ttxt
  obtain ⟨n0, hn0⟩ :=
    TextFor.eventuallyContains_finite_subset
      (concreteTypedCharacteristicSample
        (obs := obs) hworking hsep)
      (concreteTypedCharacteristicSample_positive
        (obs := obs) hworking hsep)
      Ttxt
  refine ⟨n0, ?_⟩
  intro n hn
  exact
    concreteTypedCharacteristicSample_exact_for_positive_superset
      (obs := obs)
      hworking hsep hfan hL
      (hn0 n hn)
      (Ttxt.prefixSample_subset n)

/-- Gold identification for the reachable learner, obtained directly from the
concrete typed characteristic sample. -/
theorem concreteTypedCharacteristicSample_identifies_from_positive_text
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt := by
  intro Ttxt
  exact
    concreteTypedCharacteristicSample_prefix_exact
      (obs := obs)
      hworking hsep hfan hL Ttxt

end ConcreteTypedRoute

end MCFG
