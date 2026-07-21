/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ExactConcreteCanonicalLearnerEquivalence

/-!
# ConcreteCanonicalLearnerIdentification.lean

This file closes the end-to-end positive-data identification theorem for the
corrected finite concrete canonical learner.

`ConcreteTypedCharacteristicSample.lean` previously simulated every typed
presentation derivation in the broad relation `SampleLearnerReachable`.
Here the simulation is rebuilt in the exact-once fragment

```lean
ExactSampleLearnerReachable
```

using the exact-once certificate supplied by `ExactWorkingConditions` for every
binary grammar rule.

The exact reachable semantics is then transferred to the actually enumerated
finite learner by

```lean
correctedConcreteCanonicalLearnerLanguage_eq_exactReachable.
```

The final endpoints establish, directly for

```lean
CorrectedConcreteCanonicalLearnerLanguage
```

and the set-driven learner

```lean
correctedConcreteCanonicalLearner,
```

all of the following:

* exact reconstruction from the concrete typed characteristic sample;
* exact reconstruction from every positive finite superset;
* eventual exactness on every positive text;
* Gold identification in the limit.

The learner definitions depend only on the finite sample, `obs`, and `f`.  The
target grammar occurs only in the correctness theorem.

No reducedness, base representative, tuple-type determinism, supplied canonical
closure, `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section ExactReachabilityMonotonicity

variable {α : Type u} {M : Type w}
variable [Monoid M]
variable {S K : Finset (Word α)}
variable {obs : α → M} {f : Nat}

namespace ExactSampleLearnerReachable

/-- Exact reachable derivations are monotone under finite-sample extension. -/
def mono
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    {d : Nat}
    {x y : Tuple α d}
    (h : ExactSampleLearnerReachable S obs f x y) :
    ExactSampleLearnerReachable K obs f x y := by
  induction h with

  | self x =>
      exact ExactSampleLearnerReachable.self x

  | unit hd hpos U hyu ih =>
      exact ExactSampleLearnerReachable.unit
        hd hpos (U.mono hSK) ih

  | binary he hdB hdC hepos hdBpos hdCpos
      B hexact hx hy ihx ihy =>
      exact ExactSampleLearnerReachable.binary
        he hdB hdC
        hepos hdBpos hdCpos
        (B.mono hSK)
        hexact
        ihx ihy

  | trans hxy hyz ihxy ihyz =>
      exact ExactSampleLearnerReachable.trans
        ihxy ihyz

end ExactSampleLearnerReachable


namespace ExactReachableSampleStringDerives

/-- Exact reachable string derivations are monotone under finite-sample
extension. -/
def mono
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    {word : Word α}
    (D : ExactReachableSampleStringDerives S obs f word) :
    ExactReachableSampleStringDerives K obs f word where

  startWord := D.startWord

  start_mem := hSK D.start_mem

  reachable :=
    D.reachable.mono hSK

end ExactReachableSampleStringDerives


/-- Exact reachable string languages are monotone under finite-sample
extension. -/
theorem exactReachableSampleStringLanguage_mono
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α))) :
    ExactReachableSampleStringLanguage S obs f ⊆
      ExactReachableSampleStringLanguage K obs f := by
  intro word hword
  exact hword.mono hSK

end ExactReachabilityMonotonicity


section ExactTypedPresentationSimulation

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

/-- Every typed presentation derivation is simulated from its own typed anchor
inside the exact-once reachable relation. -/
theorem presentationDerives_exactReachable_from_typed_anchor
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    {X : TypedNonterminal G M}
    {x : Tuple α (G.arity X.base)}
    (h : PresentationDerives
      S.completePresentation.presentation X x) :
    ExactSampleLearnerReachable
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
        ExactSampleLearnerReachable.unit
          (hfan τ.baseRule.lhs)
          (G.arity_pos τ.baseRule.lhs)
          (typedTerminalUnitEvidence
            S hworking.basic.1.symm τa)
          (ExactSampleLearnerReachable.self
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
          ExactSampleLearnerReachable
            (typedCharacteristicSample S hworking.basic.1.symm)
            obs f
            (successfulTypedAnchor S
              (typedBinaryLHS S τa))
            (τ.baseRule.apply
              (successfulTypedAnchor S
                (typedBinaryLeft S τa))
              (successfulTypedAnchor S
                (typedBinaryRight S τa))) :=
        ExactSampleLearnerReachable.unit
          (hfan τ.baseRule.lhs)
          (G.arity_pos τ.baseRule.lhs)
          (typedBinaryUnitEvidence
            S hworking.basic.1.symm τa)
          (ExactSampleLearnerReachable.self _)

      have hchildren :
          ExactSampleLearnerReachable
            (typedCharacteristicSample S hworking.basic.1.symm)
            obs f
            (τ.baseRule.apply
              (successfulTypedAnchor S
                (typedBinaryLeft S τa))
              (successfulTypedAnchor S
                (typedBinaryRight S τa)))
            (τ.baseRule.apply x y) := by
        change
          ExactSampleLearnerReachable
            (typedCharacteristicSample S hworking.basic.1.symm)
            obs f
            (evalTemplateTuple τ.baseRule.body
              (successfulTypedAnchor S
                (typedBinaryLeft S τa))
              (successfulTypedAnchor S
                (typedBinaryRight S τa)))
            (evalTemplateTuple τ.baseRule.body x y)

        exact
          ExactSampleLearnerReachable.binary
            (hfan τ.baseRule.lhs)
            (hfan τ.baseRule.left)
            (hfan τ.baseRule.right)
            (G.arity_pos τ.baseRule.lhs)
            (G.arity_pos τ.baseRule.left)
            (G.arity_pos τ.baseRule.right)
            (typedBinaryEvidence
              S hworking hworking.basic.1.symm τa)
            (hworking.2
              τ.baseRule τ.inGrammar)
            ihx' ihy'

      rw [hlhs]

      exact ExactSampleLearnerReachable.trans
        hparent hchildren

end ExactTypedPresentationSimulation


section ExactTypedStringSimulation

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

/-- Every word derived by the complete typed presentation belongs to exact
reachable semantics over the concrete typed characteristic sample. -/
theorem presentationStringDerives_exactReachable
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    {word : Word α}
    (D :
      PresentationStringDerives
        S.completePresentation.presentation word) :
    word ∈
      ExactReachableSampleStringLanguage
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
      ExactSampleLearnerReachable
        (typedCharacteristicSample S hworking.basic.1.symm)
        obs f
        (successfulTypedAnchor S childPresent)
        D.childTuple := by
    simpa [hchildNode] using
      presentationDerives_exactReachable_from_typed_anchor
        S hworking hfan D.child_derives

  have hstartArity :
      ExactSampleLearnerReachable
        (typedCharacteristicSample S hworking.basic.1.symm)
        obs f
        (castTuple D.startRule.wellTyped
          (successfulTypedAnchor S childPresent))
        (castTuple D.startRule.wellTyped
          D.childTuple) :=
    ExactSampleLearnerReachable.arityCast
      D.startRule.wellTyped hchild

  have hone :
      ExactSampleLearnerReachable
        (typedCharacteristicSample S hworking.basic.1.symm)
        obs f
        (castTuple D.start_arity.symm
          (castTuple D.startRule.wellTyped
            (successfulTypedAnchor S childPresent)))
        (castTuple D.start_arity.symm
          (castTuple D.startRule.wellTyped
            D.childTuple)) :=
    ExactSampleLearnerReachable.arityCast
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

/-- Completeness of exact reachable semantics for a complete successful typed
presentation. -/
theorem completePresentation_subset_exactReachable_typedSample
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f) :
    G.StringLanguage ⊆
      ExactReachableSampleStringLanguage
        (typedCharacteristicSample S hworking.basic.1.symm)
        obs f := by
  intro word hword

  exact presentationStringDerives_exactReachable
    S hworking hfan
    (S.completePresentation.complete.mem_presentation hword)

/-- Exact reachable semantics is sound for every promised positive target. -/
theorem exactReachableSampleStringLanguage_sound
    (K : Finset (Word α))
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage)
    (hK :
      (K : Set (Word α)) ⊆
        G.StringLanguage) :
    ExactReachableSampleStringLanguage K obs f ⊆
      G.StringLanguage := by
  intro word hword

  exact
    hword.toReachableSampleStringDerives.
      sound_for_grammar G hL hK

/-- Exact reconstruction in the exact-once reachable semantics for a complete
successful typed presentation. -/
theorem typedCharacteristicSample_exactReachable_reconstruction
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage) :
    ExactReachableSampleStringLanguage
        (typedCharacteristicSample S hworking.basic.1.symm)
        obs f =
      G.StringLanguage := by
  apply Set.Subset.antisymm

  · exact exactReachableSampleStringLanguage_sound
      G
      (typedCharacteristicSample
        S hworking.basic.1.symm)
      hL
      (typedCharacteristicSample_positive
        S hworking.basic.1.symm)

  · exact
      completePresentation_subset_exactReachable_typedSample
        S hworking hfan

/-- Exact reconstruction for the corrected finite enumerated learner over a
complete successful typed presentation. -/
theorem typedCharacteristicSample_correctedConcrete_reconstruction
    (S : SuccessfulOccurrenceCompletePresentation G obs)
    (hworking : G.ExactWorkingConditions)
    (hfan : G.FanoutAtMost f)
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage) :
    CorrectedConcreteCanonicalLearnerLanguage
        (typedCharacteristicSample S hworking.basic.1.symm)
        obs f =
      G.StringLanguage := by
  rw [
    correctedConcreteCanonicalLearnerLanguage_eq_exactReachable
  ]

  exact
    typedCharacteristicSample_exactReachable_reconstruction
      S hworking hfan hL

end ExactTypedStringSimulation


section ConcreteCorrectedCanonicalRoute

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M]
variable [DecidableEq α] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

/-- Exact reconstruction by the actually enumerated corrected concrete
canonical learner from the fully concrete typed characteristic sample. -/
theorem concreteTypedCharacteristicSample_correctedConcrete_exact
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hfan : G.FanoutAtMost f)
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage) :
    CorrectedConcreteCanonicalLearnerLanguage
        (concreteTypedCharacteristicSample
          (obs := obs) hworking hsep)
        obs f =
      G.StringLanguage := by
  exact
    typedCharacteristicSample_correctedConcrete_reconstruction
      (concreteSuccessfulOccurrenceCompletePresentation
        (obs := obs) hworking hsep)
      hworking hfan hL

/-- The corrected concrete learner reconstructs the target from every positive
finite superset of the concrete typed characteristic sample. -/
theorem concreteTypedCharacteristicSample_correctedConcrete_exact_for_positive_superset
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hfan : G.FanoutAtMost f)
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hSK :
      (concreteTypedCharacteristicSample
        (obs := obs) hworking hsep :
          Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKpos :
      (K : Set (Word α)) ⊆
        G.StringLanguage) :
    CorrectedConcreteCanonicalLearnerLanguage
        K obs f =
      G.StringLanguage := by
  apply Set.Subset.antisymm

  · exact
      correctedConcreteCanonicalLearnerLanguage_sound
        G hL hKpos

  · intro word hword

    have hbase :
        word ∈
          ExactReachableSampleStringLanguage
            (concreteTypedCharacteristicSample
              (obs := obs) hworking hsep)
            obs f := by
      rw [
        ← correctedConcreteCanonicalLearnerLanguage_eq_exactReachable,
        concreteTypedCharacteristicSample_correctedConcrete_exact
          (obs := obs) hworking hsep hfan hL
      ]
      exact hword

    have hlarger :
        word ∈
          ExactReachableSampleStringLanguage
            K obs f :=
      exactReachableSampleStringLanguage_mono
        hSK hbase

    exact hlarger.toCorrectedConcrete

/-- Every positive text eventually yields the target language under the
corrected concrete canonical learner. -/
theorem concreteTypedCharacteristicSample_correctedConcrete_prefix_exact
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hfan : G.FanoutAtMost f)
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        CorrectedConcreteCanonicalLearnerLanguage
            (Ttxt.prefixSample n)
            obs f =
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
    concreteTypedCharacteristicSample_correctedConcrete_exact_for_positive_superset
      (obs := obs)
      hworking hsep hfan hL
      (hn0 n hn)
      (Ttxt.prefixSample_subset n)

/-- Gold identification in the limit by the corrected finite enumerated
canonical learner. -/
theorem correctedConcreteCanonicalLearner_identifies_from_positive_text
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hfan : G.FanoutAtMost f)
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (correctedConcreteCanonicalHypLanguage obs f)
        (correctedConcreteCanonicalLearner
          (α := α))
        Ttxt := by
  intro Ttxt

  exact
    concreteTypedCharacteristicSample_correctedConcrete_prefix_exact
      (obs := obs)
      hworking hsep hfan hL Ttxt

/-- Fully explicit paper-style endpoint.

The characteristic sample is finite and positive, the corrected concrete
learner reconstructs the target exactly from it, and the same learner identifies
the target on every positive text. -/
theorem correctedConcreteCanonicalLearner_paper_main_theorem
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hfan : G.FanoutAtMost f)
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CorrectedConcreteCanonicalLearnerLanguage
          S obs f =
        G.StringLanguage ∧
      ∀ Ttxt : TextFor G.StringLanguage,
        EventuallyCorrectOnText
          (correctedConcreteCanonicalHypLanguage
            obs f)
          (correctedConcreteCanonicalLearner
            (α := α))
          Ttxt := by
  refine
    ⟨concreteTypedCharacteristicSample
        (obs := obs) hworking hsep,
      concreteTypedCharacteristicSample_positive
        (obs := obs) hworking hsep,
      concreteTypedCharacteristicSample_correctedConcrete_exact
        (obs := obs) hworking hsep hfan hL,
      ?_⟩

  exact
    correctedConcreteCanonicalLearner_identifies_from_positive_text
      (obs := obs)
      hworking hsep hfan hL

/-- A conclusion package exposing the concrete sample and every monotone
finite-sample consequence needed for positive-data identification. -/
theorem correctedConcreteCanonicalLearner_conclusion_package
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hfan : G.FanoutAtMost f)
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ G.StringLanguage ∧
      CorrectedConcreteCanonicalLearnerLanguage
          S obs f =
        G.StringLanguage ∧
      (∀ K : Finset (Word α),
        (S : Set (Word α)) ⊆
            (K : Set (Word α)) →
        (K : Set (Word α)) ⊆
            G.StringLanguage →
        CorrectedConcreteCanonicalLearnerLanguage
            K obs f =
          G.StringLanguage) ∧
      (∀ Ttxt : TextFor G.StringLanguage,
        EventuallyCorrectOnText
          (correctedConcreteCanonicalHypLanguage
            obs f)
          (correctedConcreteCanonicalLearner
            (α := α))
          Ttxt) := by
  let S :=
    concreteTypedCharacteristicSample
      (obs := obs) hworking hsep

  refine
    ⟨S,
      concreteTypedCharacteristicSample_positive
        (obs := obs) hworking hsep,
      concreteTypedCharacteristicSample_correctedConcrete_exact
        (obs := obs) hworking hsep hfan hL,
      ?_,
      correctedConcreteCanonicalLearner_identifies_from_positive_text
        (obs := obs)
        hworking hsep hfan hL⟩

  intro K hSK hKpos

  exact
    concreteTypedCharacteristicSample_correctedConcrete_exact_for_positive_superset
      (obs := obs)
      hworking hsep hfan hL
      hSK hKpos

end ConcreteCorrectedCanonicalRoute

end MCFG
