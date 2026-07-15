/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarRepresentation

/-!
# ConcreteCanonicalLearnerWorkingGrammarBoundedRepresentation.lean

The preceding representation theorem produces an actual finite
`WorkingMCFG` for every semantic start-rooted target.  This file turns that
existence statement into a size-indexed finite representation hierarchy.

A bounded representation contains:

* an actual nonterminal type;
* an actual `WorkingMCFG`;
* an explicit list covering every nonterminal;
* the verified `CutCompiledConditions f`;
* exact equality with the represented language;
* a bound on

```text
nonterminal-list length
+ start-rule-list length
+ terminal-rule-list length
+ binary-rule-list length.
```

The size bound at sample-length budget `n` is

```lean
correctedConcreteCompiledGrammarPresentationItemBound n f.
```

The corresponding language class is

```lean
BoundedCutCompiledWorkingGrammarLanguageClass α f n.
```

This file proves:

1. the paper-facing source-rule bound is monotone in sample length;
2. the compiled presentation-item bound is monotone in sample length;
3. the bounded language classes form an increasing hierarchy;
4. every finite sample learner output belongs to the hierarchy at its own
   total sample length;
5. every semantic start-rooted target belongs to some finite level of the
   hierarchy;
6. the witnessing level can be chosen as the total length of one finite
   positive characteristic sample.

Thus the verified positive-learning theorem now yields not merely an actual
finite grammar, but an explicit finite-presentation certificate at a finite
size level.

This remains an item-count hierarchy, not a bit-length hierarchy for words and
templates stored inside each item.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section BoundMonotonicity

/-- The common paper scale is monotone in total sample length. -/
theorem correctedLearnerPaperScale_mono_sampleLength
    {s t f : Nat}
    (hst : s ≤ t) :
    correctedLearnerPaperScale s f ≤
      correctedLearnerPaperScale t f := by
  unfold correctedLearnerPaperScale
  omega

/-- The paper-facing enumeration base is monotone in total sample length. -/
theorem correctedLearnerPaperBase_mono_sampleLength
    {s t f : Nat}
    (hst : s ≤ t) :
    correctedLearnerPaperBase s f ≤
      correctedLearnerPaperBase t f := by
  unfold correctedLearnerPaperBase
  exact
    Nat.mul_le_mul_left
      4
      (correctedLearnerPaperScale_mono_sampleLength
        hst)

/-- The paper-facing quadratic exponent is monotone in total sample length. -/
theorem correctedLearnerPaperExponent_mono_sampleLength
    {s t f : Nat}
    (hst : s ≤ t) :
    correctedLearnerPaperExponent s f ≤
      correctedLearnerPaperExponent t f := by

  let a :=
    correctedLearnerPaperScale s f

  let b :=
    correctedLearnerPaperScale t f

  have hab :
      a ≤ b := by
    dsimp [a, b]
    exact
      correctedLearnerPaperScale_mono_sampleLength
        hst

  unfold correctedLearnerPaperExponent

  exact
    Nat.mul_le_mul
      (Nat.mul_le_mul_left 64 hab)
      hab

/-- The paper-facing source finite-rule bound is monotone in total sample
length. -/
theorem correctedLearnerPaperRuleCountBound_mono_sampleLength
    {s t f : Nat}
    (hst : s ≤ t) :
    correctedLearnerPaperRuleCountBound s f ≤
      correctedLearnerPaperRuleCountBound t f := by

  unfold correctedLearnerPaperRuleCountBound

  exact
    nat_pow_le_pow_mixed
      (correctedLearnerPaperBase_mono_sampleLength
        hst)
      (correctedLearnerPaperBase_gt_one
        t f)
      (correctedLearnerPaperExponent_mono_sampleLength
        hst)

/-- The complete compiled-presentation item bound is monotone in total sample
length. -/
theorem correctedConcreteCompiledGrammarPresentationItemBound_mono_sampleLength
    {s t f : Nat}
    (hst : s ≤ t) :
    correctedConcreteCompiledGrammarPresentationItemBound
        s f ≤
      correctedConcreteCompiledGrammarPresentationItemBound
        t f := by

  unfold
    correctedConcreteCompiledGrammarPresentationItemBound

  apply Nat.pow_le_pow_left

  have hrule :
      correctedLearnerPaperRuleCountBound s f ≤
        correctedLearnerPaperRuleCountBound t f :=
    correctedLearnerPaperRuleCountBound_mono_sampleLength
      hst

  omega

end BoundMonotonicity


section BoundedRepresentation

variable (α : Type u)

/-- A finite working-grammar representation with an explicit nonterminal
enumeration and a verified presentation-item budget. -/
structure BoundedCutCompiledWorkingGrammarRepresentation
    (f n : Nat)
    (L : Set (Word α)) where

  Nonterminal :
    Type w

  grammar :
    WorkingMCFG Nonterminal α

  nonterminals :
    List Nonterminal

  nonterminal_complete :
    ∀ A : Nonterminal,
      A ∈ nonterminals

  conditions :
    grammar.CutCompiledConditions f

  language_eq :
    grammar.StringLanguage = L

  presentationItemCount_le :
    nonterminals.length +
        grammar.startRules.length +
        grammar.terminalRules.length +
        grammar.binaryRules.length ≤
      correctedConcreteCompiledGrammarPresentationItemBound
        n f

/-- Languages possessing a bounded cut-compiled representation at budget
level `n`. -/
def BoundedCutCompiledWorkingGrammarLanguageClass
    (f n : Nat) :
    Set (Set (Word α)) :=
  {L |
    Nonempty
      (BoundedCutCompiledWorkingGrammarRepresentation
        (w := w) α f n L)}

namespace BoundedCutCompiledWorkingGrammarRepresentation

variable {α : Type u}
variable {f n : Nat}
variable {L : Set (Word α)}

/-- Forget the quantitative certificate and retain the unbounded
cut-compiled representation. -/
def forgetBound
    (R :
      BoundedCutCompiledWorkingGrammarRepresentation
        (w := w) α f n L) :
    CutCompiledWorkingGrammarRepresentation
      (w := w) α f L where

  Nonterminal :=
    R.Nonterminal

  grammar :=
    R.grammar

  conditions :=
    R.conditions

  language_eq :=
    R.language_eq

/-- Every bounded representation yields membership in the unbounded
cut-compiled language class. -/
theorem target_mem_unboundedClass
    (R :
      BoundedCutCompiledWorkingGrammarRepresentation
        (w := w) α f n L) :
    L ∈
      CutCompiledWorkingGrammarLanguageClass
        (w := w) α f := by

  exact
    ⟨R.forgetBound⟩

/-- Increase the size budget of a bounded representation. -/
def mono
    {m : Nat}
    (R :
      BoundedCutCompiledWorkingGrammarRepresentation
        (w := w) α f n L)
    (hnm : n ≤ m) :
    BoundedCutCompiledWorkingGrammarRepresentation
      (w := w) α f m L where

  Nonterminal :=
    R.Nonterminal

  grammar :=
    R.grammar

  nonterminals :=
    R.nonterminals

  nonterminal_complete :=
    R.nonterminal_complete

  conditions :=
    R.conditions

  language_eq :=
    R.language_eq

  presentationItemCount_le :=
    R.presentationItemCount_le.trans
      (correctedConcreteCompiledGrammarPresentationItemBound_mono_sampleLength
        hnm)

/-- A bounded representation still exposes the ordinary representation
equality. -/
theorem target_eq_language
    (R :
      BoundedCutCompiledWorkingGrammarRepresentation
        (w := w) α f n L) :
    L = R.grammar.StringLanguage :=
  R.language_eq.symm

/-- Positive fan-out form for a positive fixed fan-out parameter. -/
theorem fanoutAtMost
    (R :
      BoundedCutCompiledWorkingGrammarRepresentation
        (w := w) α f n L)
    (hf : 1 ≤ f) :
    R.grammar.FanoutAtMost f := by

  have hmax :
      max 1 f = f :=
    max_eq_right hf

  rw [← hmax]

  exact R.conditions.2.2.2

end BoundedCutCompiledWorkingGrammarRepresentation

end BoundedRepresentation


section BoundedClassHierarchy

variable {α : Type u}

/-- The size-indexed cut-compiled language classes form an increasing
hierarchy. -/
theorem boundedCutCompiledWorkingGrammarLanguageClass_mono
    {f n m : Nat}
    (hnm : n ≤ m) :
    BoundedCutCompiledWorkingGrammarLanguageClass
        (w := w) α f n ⊆
      BoundedCutCompiledWorkingGrammarLanguageClass
        (w := w) α f m := by

  intro L hL

  rcases hL with ⟨R⟩

  exact
    ⟨R.mono hnm⟩

/-- Every bounded class is contained in the corresponding unbounded
cut-compiled representation class. -/
theorem boundedCutCompiledWorkingGrammarLanguageClass_subset_unbounded
    (f n : Nat) :
    BoundedCutCompiledWorkingGrammarLanguageClass
        (w := w) α f n ⊆
      CutCompiledWorkingGrammarLanguageClass
        (w := w) α f := by

  intro L hL

  rcases hL with ⟨R⟩

  exact
    R.target_mem_unboundedClass

/-- The union of all finite size levels is still contained in the unbounded
representation class. -/
theorem exists_boundedRepresentation_implies_unbounded
    {f : Nat}
    {L : Set (Word α)}
    (hL :
      ∃ n : Nat,
        L ∈
          BoundedCutCompiledWorkingGrammarLanguageClass
            (w := w) α f n) :
    L ∈
      CutCompiledWorkingGrammarLanguageClass
        (w := w) α f := by

  rcases hL with ⟨n, hn⟩

  exact
    boundedCutCompiledWorkingGrammarLanguageClass_subset_unbounded
      (w := w) f n hn

end BoundedClassHierarchy


section LearnerOutputBoundedRepresentation

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]

/-- The concrete learner output on `K`, equipped with its complete finite
nonterminal enumeration and the verified budget at total sample length
`sampleLengthBudget K`. -/
noncomputable def correctedConcreteWorkingGrammarLearner_boundedRepresentation
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    BoundedCutCompiledWorkingGrammarRepresentation
      (w := max u v)
      α f
      (sampleLengthBudget K)
      (CorrectedConcreteCanonicalLearnerLanguage
        K obs f) := by

  let H :=
    correctedConcreteFiniteHypothesis
      K obs f

  let dummy :=
    Classical.choice hα

  exact
    { Nonterminal :=
        CorrectedConcreteCutGrammarNonterminal H

      grammar :=
        H.toCutWorkingMCFG dummy

      nonterminals :=
        H.compiledGrammarNonterminals

      nonterminal_complete :=
        H.mem_compiledGrammarNonterminals

      conditions :=
        H.toCutWorkingMCFG_cutCompiledConditions
          dummy

      language_eq := by
        exact
          correctedConcreteCanonicalFiniteHypothesis_cutWorkingGrammar_eq_corrected
            K obs f dummy

      presentationItemCount_le := by
        change
          H.toCutWorkingMCFGPresentationItemCount
              dummy ≤
            correctedConcreteCompiledGrammarPresentationItemBound
              (sampleLengthBudget K) f

        rw [
          H.toCutWorkingMCFGPresentationItemCount_eq
        ]

        exact
          correctedConcreteFiniteHypothesis_presentationItemCount_le_paperBound
            K obs f }

/-- Every corrected concrete sample language belongs to the bounded hierarchy
at its own total sample length. -/
theorem correctedConcreteCanonicalLearnerLanguage_mem_boundedCutCompiledClass
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    CorrectedConcreteCanonicalLearnerLanguage
        K obs f ∈
      BoundedCutCompiledWorkingGrammarLanguageClass
        (w := max u v)
        α f
        (sampleLengthBudget K) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearner_boundedRepresentation
      hα obs f K⟩

/-- The exact-once reachable sample language has the same bounded
representation, by the verified semantic equivalence. -/
noncomputable def exactReachableSampleStringLanguage_boundedRepresentation
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    BoundedCutCompiledWorkingGrammarRepresentation
      (w := max u v)
      α f
      (sampleLengthBudget K)
      (ExactReachableSampleStringLanguage
        K obs f) := by

  let H :=
    correctedConcreteFiniteHypothesis
      K obs f

  let dummy :=
    Classical.choice hα

  exact
    { Nonterminal :=
        CorrectedConcreteCutGrammarNonterminal H

      grammar :=
        H.toCutWorkingMCFG dummy

      nonterminals :=
        H.compiledGrammarNonterminals

      nonterminal_complete :=
        H.mem_compiledGrammarNonterminals

      conditions :=
        H.toCutWorkingMCFG_cutCompiledConditions
          dummy

      language_eq := by
        exact
          correctedConcreteCanonicalFiniteHypothesis_cutWorkingGrammar_eq_exactReachable
            K obs f dummy

      presentationItemCount_le := by
        change
          H.toCutWorkingMCFGPresentationItemCount
              dummy ≤
            correctedConcreteCompiledGrammarPresentationItemBound
              (sampleLengthBudget K) f

        rw [
          H.toCutWorkingMCFGPresentationItemCount_eq
        ]

        exact
          correctedConcreteFiniteHypothesis_presentationItemCount_le_paperBound
            K obs f }

/-- Membership form for exact-once reachable sample semantics. -/
theorem exactReachableSampleStringLanguage_mem_boundedCutCompiledClass
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    ExactReachableSampleStringLanguage
        K obs f ∈
      BoundedCutCompiledWorkingGrammarLanguageClass
        (w := max u v)
        α f
        (sampleLengthBudget K) := by

  exact
    ⟨exactReachableSampleStringLanguage_boundedRepresentation
      hα obs f K⟩

end LearnerOutputBoundedRepresentation


section BoundedTargetWitness

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]

/-- Quantitative target certificate: one finite positive sample and one bounded
actual working-grammar representation at precisely that sample's total length. -/
structure CorrectedConcreteBoundedWorkingGrammarTargetWitness
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (L : Set (Word α)) where

  sample :
    Finset (Word α)

  sample_positive :
    (sample : Set (Word α)) ⊆ L

  representation :
    BoundedCutCompiledWorkingGrammarRepresentation
      (w := max u v)
      α f
      (sampleLengthBudget sample)
      L

namespace CorrectedConcreteBoundedWorkingGrammarTargetWitness

variable {hα : Nonempty α}
variable {obs : α → M}
variable {f : Nat}
variable {L : Set (Word α)}

/-- A bounded target witness supplies membership at its finite size level. -/
theorem target_mem_boundedClass
    (W :
      CorrectedConcreteBoundedWorkingGrammarTargetWitness
        hα obs f L) :
    L ∈
      BoundedCutCompiledWorkingGrammarLanguageClass
        (w := max u v)
        α f
        (sampleLengthBudget W.sample) := by

  exact ⟨W.representation⟩


end CorrectedConcreteBoundedWorkingGrammarTargetWitness

end BoundedTargetWitness


section CharacteristicSampleToBoundedWitness

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]
variable [DecidableEq α]

/-- A characteristic sample produces a bounded exact grammar representation at
the sample's own total length. -/
noncomputable def correctedConcreteBoundedWorkingGrammarTargetWitness_of_characteristicSample
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (L : Set (Word α))
    (hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L) :
    CorrectedConcreteBoundedWorkingGrammarTargetWitness
      hα obs f L := by

  let R :=
    correctedConcreteWorkingGrammarLearner_boundedRepresentation
      hα obs f S

  have hexact :
      CorrectedConcreteCanonicalLearnerLanguage
          S obs f =
        L := by

    have houtput :=
      hS.2 S
        Set.Subset.rfl
        hS.1

    rw [
      correctedConcreteWorkingGrammarLearner_stringLanguage_eq_corrected
    ] at houtput

    exact houtput

  exact
    { sample :=
        S

      sample_positive :=
        hS.1

      representation :=
        { Nonterminal :=
            R.Nonterminal

          grammar :=
            R.grammar

          nonterminals :=
            R.nonterminals

          nonterminal_complete :=
            R.nonterminal_complete

          conditions :=
            R.conditions

          language_eq :=
            R.language_eq.trans
              hexact

          presentationItemCount_le :=
            R.presentationItemCount_le } }

/-- Existential bounded-class consequence of one characteristic sample. -/
theorem exists_boundedCutCompiledRepresentation_of_characteristicSample
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (L : Set (Word α))
    (hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L) :
    L ∈
      BoundedCutCompiledWorkingGrammarLanguageClass
        (w := max u v)
        α f
        (sampleLengthBudget S) := by

  let W :=
    correctedConcreteBoundedWorkingGrammarTargetWitness_of_characteristicSample
      hα obs f S L hS

  exact
    W.target_mem_boundedClass

end CharacteristicSampleToBoundedWitness


section StartRootedBoundedRepresentation

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Every semantic start-rooted target has a finite positive bounded grammar
certificate. -/
theorem correctedConcreteWorkingGrammarLearner_exists_boundedTargetWitness
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    Nonempty
      (CorrectedConcreteBoundedWorkingGrammarTargetWitness
        hα obs f L) := by

  obtain ⟨S, hS⟩ :=
    correctedConcreteWorkingGrammarLearner_characteristicSample_for_startRootedTargetClass
      (v := w) hα obs f hL

  exact
    ⟨correctedConcreteBoundedWorkingGrammarTargetWitness_of_characteristicSample
      hα obs f S L hS⟩

/-- Every target lies at some finite level of the bounded representation
hierarchy. -/
theorem startRootedTarget_mem_some_boundedCutCompiledClass
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    ∃ n : Nat,
      L ∈
        BoundedCutCompiledWorkingGrammarLanguageClass
          (w := max u v) α f n := by

  rcases
      correctedConcreteWorkingGrammarLearner_exists_boundedTargetWitness
        (v := w) hα obs f hL with
    ⟨W⟩

  exact
    ⟨sampleLengthBudget W.sample,
      W.target_mem_boundedClass⟩

/-- Class-level inclusion into the union of all finite bounded levels. -/
theorem startRootedTargetClass_subset_exists_boundedCutCompiledClass :
    StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f ⊆
      {L : Set (Word α) |
        ∃ n : Nat,
          L ∈
            BoundedCutCompiledWorkingGrammarLanguageClass
              (w := max u v) α f n} := by

  intro L hL

  exact
    startRootedTarget_mem_some_boundedCutCompiledClass
      (v := w) hα obs f hL

/-- Expanded witness form exposing the positive construction sample and its
budget level. -/
theorem correctedConcreteWorkingGrammarLearner_exists_positive_boundedRepresentation
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    ∃ S : Finset (Word α),
      (S : Set (Word α)) ⊆ L ∧
      L ∈
        BoundedCutCompiledWorkingGrammarLanguageClass
          (w := max u v)
          α f
          (sampleLengthBudget S) := by

  rcases
      correctedConcreteWorkingGrammarLearner_exists_boundedTargetWitness
        (v := w) hα obs f hL with
    ⟨W⟩

  exact
    ⟨W.sample,
      W.sample_positive,
      W.target_mem_boundedClass⟩

end StartRootedBoundedRepresentation


section BoundedRepresentationPackages

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Paper-facing bounded-representation hierarchy package. -/
theorem correctedConcreteWorkingGrammarLearner_boundedRepresentation_package :
    (∀ n m : Nat,
      n ≤ m →
      BoundedCutCompiledWorkingGrammarLanguageClass
          (w := max u v) α f n ⊆
        BoundedCutCompiledWorkingGrammarLanguageClass
          (w := max u v) α f m) ∧
      (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f ⊆
        {L : Set (Word α) |
          ∃ n : Nat,
            L ∈
              BoundedCutCompiledWorkingGrammarLanguageClass
                (w := max u v) α f n}) ∧
      (∀ L : Set (Word α),
        L ∈ StartRootedCorrectedConcreteTargetClass
            (v := w) α M obs f →
        ∃ S : Finset (Word α),
          (S : Set (Word α)) ⊆ L ∧
          L ∈
            BoundedCutCompiledWorkingGrammarLanguageClass
              (w := max u v)
              α f
              (sampleLengthBudget S)) := by

  exact
    ⟨fun n m hnm =>
        boundedCutCompiledWorkingGrammarLanguageClass_mono
          (w := max u v) hnm,
      startRootedTargetClass_subset_exists_boundedCutCompiledClass
        (v := w) hα obs f,
      fun L hL =>
        correctedConcreteWorkingGrammarLearner_exists_positive_boundedRepresentation
          (v := w) hα obs f hL⟩

/-- Combined identification and bounded finite-representation endpoint. -/
theorem correctedConcreteWorkingGrammarLearner_identification_boundedRepresentation_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f ⊆
        {L : Set (Word α) |
          ∃ n : Nat,
            L ∈
              BoundedCutCompiledWorkingGrammarLanguageClass
                (w := max u v) α f n}) ∧
      (∀ K : Finset (Word α),
        CorrectedConcreteCanonicalLearnerLanguage
            K obs f ∈
          BoundedCutCompiledWorkingGrammarLanguageClass
            (w := max u v)
            α f
            (sampleLengthBudget K)) := by

  exact
    ⟨correctedConcreteWorkingGrammarLearner_identifies_startRootedTargetClass
        (v := w) hα obs f,
      startRootedTargetClass_subset_exists_boundedCutCompiledClass
        (v := w) hα obs f,
      correctedConcreteCanonicalLearnerLanguage_mem_boundedCutCompiledClass
        hα obs f⟩

end BoundedRepresentationPackages

end MCFG
