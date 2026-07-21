/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerFiniteHypothesisSize

/-!
# ConcreteCanonicalLearnerFiniteObjectIdentification.lean

The preceding files constructed an actual finite dependent rule object and
proved a size bound for it.  This file makes that object the output type of the
learner itself.

A listed derivation now carries membership proofs in the rule lists stored by

```lean
CorrectedConcreteFiniteHypothesis.
```

Thus its semantics genuinely reads the finite object, rather than merely
reusing the finite sample from which the object was constructed.

The main layers are:

```lean
ListedFiniteCorrectedConcreteLearnerDerives
CorrectedConcreteFiniteHypothesis.Language
CorrectedConcreteFiniteHypothesisObject
correctedConcreteFiniteObjectLearner
correctedConcreteFiniteObjectHypLanguage.
```

Completeness of the stored rule lists gives two-way equivalence between listed
derivations and the previously verified finite dependent derivations.
Consequently the finite-object learner has exactly the corrected concrete
canonical learner language.

The file then transfers:

* finite characteristic samples;
* class-level Gold identification;
* selected-stage exactness;
* the explicit rule-count bound

to the learner whose hypotheses are actual finite rule objects.

No target grammar is an input to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section ListedFiniteDerivations

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Derivations using only rule codes explicitly listed in a finite hypothesis
object. -/
inductive ListedFiniteCorrectedConcreteLearnerDerives
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    {d : Nat} → Tuple α d → Tuple α d → Prop where

  | self
      {d : Nat}
      (x : Tuple α d) :
      ListedFiniteCorrectedConcreteLearnerDerives
        K obs f H x x

  | unit
      (U :
        CorrectedConcreteUnitRuleCode
          K obs f)
      (hU :
        U ∈ H.unitRuleCodes)
      {u : Tuple α U.arity}
      (hrest :
        ListedFiniteCorrectedConcreteLearnerDerives
          K obs f H U.target u) :
      ListedFiniteCorrectedConcreteLearnerDerives
        K obs f H U.source u

  | binary
      (B :
        CorrectedConcreteBinaryRuleCode
          K f)
      (hB :
        B ∈ H.binaryRuleCodes)
      {u : Tuple α B.leftArity}
      {v : Tuple α B.rightArity}
      (hleft :
        ListedFiniteCorrectedConcreteLearnerDerives
          K obs f H B.leftSource u)
      (hright :
        ListedFiniteCorrectedConcreteLearnerDerives
          K obs f H B.rightSource v) :
      ListedFiniteCorrectedConcreteLearnerDerives
        K obs f H B.source
          (evalTemplateTuple B.body u v)

  | trans
      {d : Nat}
      {x y z : Tuple α d}
      (hxy :
        ListedFiniteCorrectedConcreteLearnerDerives
          K obs f H x y)
      (hyz :
        ListedFiniteCorrectedConcreteLearnerDerives
          K obs f H y z) :
      ListedFiniteCorrectedConcreteLearnerDerives
        K obs f H x z

namespace ListedFiniteCorrectedConcreteLearnerDerives

variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}
variable {H :
  CorrectedConcreteFiniteHypothesis K obs f}

/-- Forget rule-list membership proofs. -/
theorem toFinite
    {d : Nat}
    {x y : Tuple α d}
    (h :
      ListedFiniteCorrectedConcreteLearnerDerives
        K obs f H x y) :
    FiniteCorrectedConcreteLearnerDerives
      K obs f x y := by
  induction h with

  | self x =>
      exact
        FiniteCorrectedConcreteLearnerDerives.self
          x

  | unit U hU hrest ih =>
      exact
        FiniteCorrectedConcreteLearnerDerives.unit
          U ih

  | binary B hB hleft hright ihleft ihright =>
      exact
        FiniteCorrectedConcreteLearnerDerives.binary
          B ihleft ihright

  | trans hxy hyz ihxy ihyz =>
      exact
        FiniteCorrectedConcreteLearnerDerives.trans
          ihxy ihyz

end ListedFiniteCorrectedConcreteLearnerDerives


namespace FiniteCorrectedConcreteLearnerDerives

variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Every finite dependent derivation can be read using the complete rule lists
stored in any `CorrectedConcreteFiniteHypothesis`. -/
theorem toListed
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    {d : Nat}
    {x y : Tuple α d}
    (h :
      FiniteCorrectedConcreteLearnerDerives
        K obs f x y) :
    ListedFiniteCorrectedConcreteLearnerDerives
      K obs f H x y := by
  induction h with

  | self x =>
      exact
        ListedFiniteCorrectedConcreteLearnerDerives.self
          x

  | unit U hrest ih =>
      exact
        ListedFiniteCorrectedConcreteLearnerDerives.unit
          U
          (H.unitRuleCodes_complete U)
          ih

  | binary B hleft hright ihleft ihright =>
      exact
        ListedFiniteCorrectedConcreteLearnerDerives.binary
          B
          (H.binaryRuleCodes_complete B)
          ihleft ihright

  | trans hxy hyz ihxy ihyz =>
      exact
        ListedFiniteCorrectedConcreteLearnerDerives.trans
          ihxy ihyz

end FiniteCorrectedConcreteLearnerDerives


/-- Tuple-level equivalence between listed-object semantics and the complete
finite dependent relation. -/
theorem listedFiniteCorrectedConcreteLearnerDerives_iff
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    {d : Nat}
    (x y : Tuple α d) :
    ListedFiniteCorrectedConcreteLearnerDerives
        K obs f H x y ↔
      FiniteCorrectedConcreteLearnerDerives
        K obs f x y := by
  constructor
  · exact
      ListedFiniteCorrectedConcreteLearnerDerives.toFinite
  · exact
      FiniteCorrectedConcreteLearnerDerives.toListed H

end ListedFiniteDerivations


section ListedFiniteStringLanguage

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- String derivation whose tuple derivation reads the listed finite rules. -/
structure ListedFiniteCorrectedConcreteStringDerives
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (word : Word α) where

  startWord : Word α

  start_mem :
    startWord ∈ K

  derives :
    ListedFiniteCorrectedConcreteLearnerDerives
      K obs f H
      (singletonTuple startWord)
      (singletonTuple word)

/-- Language read from one actual finite rule object. -/
def CorrectedConcreteFiniteHypothesis.Language
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    Set (Word α) :=
  {word |
    ListedFiniteCorrectedConcreteStringDerives
      K obs f H word}

namespace ListedFiniteCorrectedConcreteStringDerives

variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}
variable {H :
  CorrectedConcreteFiniteHypothesis K obs f}

/-- Forget the listed-rule membership proofs from a string derivation. -/
def toFinite
    {word : Word α}
    (D :
      ListedFiniteCorrectedConcreteStringDerives
        K obs f H word) :
    FiniteCorrectedConcreteStringDerives
      K obs f word where

  startWord :=
    D.startWord

  start_mem :=
    D.start_mem

  derives :=
    D.derives.toFinite

end ListedFiniteCorrectedConcreteStringDerives


namespace FiniteCorrectedConcreteStringDerives

variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Read a finite dependent string derivation through the complete rule lists
of an actual finite hypothesis. -/
def toListed
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    {word : Word α}
    (D :
      FiniteCorrectedConcreteStringDerives
        K obs f word) :
    ListedFiniteCorrectedConcreteStringDerives
      K obs f H word where

  startWord :=
    D.startWord

  start_mem :=
    D.start_mem

  derives :=
    D.derives.toListed H

end FiniteCorrectedConcreteStringDerives


/-- Every listed-object string derivation belongs to the complete finite
dependent language. -/
theorem correctedConcreteFiniteHypothesis_language_subset_finite
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    H.Language ⊆
      FiniteCorrectedConcreteLearnerLanguage
        K obs f := by
  intro word hword
  exact hword.toFinite

/-- Completeness of the stored rule lists gives the reverse inclusion. -/
theorem finiteCorrectedConcreteLearnerLanguage_subset_hypothesis
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    FiniteCorrectedConcreteLearnerLanguage
        K obs f ⊆
      H.Language := by
  intro word hword
  exact hword.toListed H

/-- The language read from any complete finite rule object equals the finite
dependent learner language. -/
theorem CorrectedConcreteFiniteHypothesis.language_eq_finite
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    H.Language =
      FiniteCorrectedConcreteLearnerLanguage
        K obs f := by
  apply Set.Subset.antisymm
  · exact
      correctedConcreteFiniteHypothesis_language_subset_finite
        H
  · exact
      finiteCorrectedConcreteLearnerLanguage_subset_hypothesis
        H

/-- Every complete finite rule object has exactly the corrected concrete
canonical learner language. -/
theorem CorrectedConcreteFiniteHypothesis.language_eq_corrected
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    H.Language =
      CorrectedConcreteCanonicalLearnerLanguage
        K obs f := by
  rw [
    H.language_eq_finite,
    finiteCorrectedConcreteLearnerLanguage_eq
  ]

/-- Every complete finite rule object also has exactly the exact-once reachable
language. -/
theorem CorrectedConcreteFiniteHypothesis.language_eq_exactReachable
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    H.Language =
      ExactReachableSampleStringLanguage
        K obs f := by
  rw [
    H.language_eq_finite,
    finiteCorrectedConcreteLearnerLanguage_eq_exactReachable
  ]

end ListedFiniteStringLanguage


section FixedFiniteObjectHypothesisType

variable (α : Type u)
variable (M : Type v) [Monoid M]
variable (obs : α → M)
variable (f : Nat)

/-- Fixed learner-output type containing the observed finite sample and its
actual complete finite rule object. -/
structure CorrectedConcreteFiniteHypothesisObject where

  sample :
    Finset (Word α)

  rules :
    CorrectedConcreteFiniteHypothesis
      sample obs f

namespace CorrectedConcreteFiniteHypothesisObject

/-- Language read from the stored finite rule object. -/
def Language
    (H :
      CorrectedConcreteFiniteHypothesisObject
        α M obs f) :
    Set (Word α) :=
  H.rules.Language

/-- Number of rules physically stored in the hypothesis. -/
def ruleCount
    (H :
      CorrectedConcreteFiniteHypothesisObject
        α M obs f) :
    Nat :=
  H.rules.ruleCount

end CorrectedConcreteFiniteHypothesisObject

end FixedFiniteObjectHypothesisType


section FiniteObjectLearner

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Learner whose output is the actual finite rule object built from the current
sample. -/
noncomputable def correctedConcreteFiniteObjectLearner
    (obs : α → M)
    (f : Nat) :
    SetDrivenLearner α
      (CorrectedConcreteFiniteHypothesisObject
        α M obs f) :=
  fun K =>
    { sample := K
      rules :=
        correctedConcreteFiniteHypothesis
          K obs f }

/-- Language interpretation for actual finite-object hypotheses. -/
def correctedConcreteFiniteObjectHypLanguage
    (obs : α → M)
    (f : Nat) :
    HypLanguage α
      (CorrectedConcreteFiniteHypothesisObject
        α M obs f) :=
  fun H => H.Language

@[simp] theorem correctedConcreteFiniteObjectLearner_sample
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteFiniteObjectLearner
      obs f K).sample = K :=
  rfl

@[simp] theorem correctedConcreteFiniteObjectLearner_rules
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteFiniteObjectLearner
      obs f K).rules =
        correctedConcreteFiniteHypothesis
          K obs f :=
  rfl

@[simp] theorem correctedConcreteFiniteObjectLearner_ruleCount
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteFiniteObjectLearner
      obs f K).ruleCount =
        (correctedConcreteFiniteHypothesis
          K obs f).ruleCount :=
  rfl

/-- The finite-object learner has exactly the previously verified corrected
concrete language on every sample. -/
theorem correctedConcreteFiniteObjectHypLanguage_apply
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteFiniteObjectHypLanguage
        obs f
        (correctedConcreteFiniteObjectLearner
          obs f K) =
      CorrectedConcreteCanonicalLearnerLanguage
        K obs f := by
  change
    (correctedConcreteFiniteHypothesis
      K obs f).Language =
        CorrectedConcreteCanonicalLearnerLanguage
          K obs f
  exact
    CorrectedConcreteFiniteHypothesis.language_eq_corrected
      (correctedConcreteFiniteHypothesis
        K obs f)

/-- The finite-object learner also has exactly the exact-once reachable
language. -/
theorem correctedConcreteFiniteObjectHypLanguage_eq_exactReachable
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteFiniteObjectHypLanguage
        obs f
        (correctedConcreteFiniteObjectLearner
          obs f K) =
      ExactReachableSampleStringLanguage
        K obs f := by
  change
    (correctedConcreteFiniteHypothesis
      K obs f).Language =
        ExactReachableSampleStringLanguage
          K obs f
  exact
    CorrectedConcreteFiniteHypothesis.language_eq_exactReachable
      (correctedConcreteFiniteHypothesis
        K obs f)

end FiniteObjectLearner


section CharacteristicSampleTransfer

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable [DecidableEq α]

/-- Characteristic-sample statements for the finite-object learner are
equivalent to the earlier corrected-concrete statements. -/
theorem correctedConcreteFiniteObject_characteristicSample_iff
    (obs : α → M)
    (f : Nat)
    (S : Finset (Word α))
    (L : Set (Word α)) :
    CharacteristicSample
        (correctedConcreteFiniteObjectHypLanguage
          obs f)
        (correctedConcreteFiniteObjectLearner
          obs f)
        S L ↔
      CharacteristicSample
        (correctedConcreteCanonicalHypLanguage
          obs f)
        (correctedConcreteCanonicalLearner
          (α := α))
        S L := by
  constructor

  · intro h
    constructor

    · exact h.1

    · intro K hSK hKL

      have hK :=
        h.2 K hSK hKL

      rw [
        correctedConcreteFiniteObjectHypLanguage_apply
      ] at hK

      exact hK

  · intro h
    constructor

    · exact h.1

    · intro K hSK hKL

      have hK :=
        h.2 K hSK hKL

      rw [
        correctedConcreteFiniteObjectHypLanguage_apply
      ]

      exact hK

end CharacteristicSampleTransfer


section StartRootedFiniteObjectClassTheorem

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α] [DecidableEq M]
variable [Monoid M]
variable (obs : α → M)
variable (f : Nat)

/-- Every target in the semantic start-rooted class has a finite
characteristic sample for the learner whose hypotheses are actual finite rule
objects. -/
theorem correctedConcreteFiniteObjectLearner_characteristicSample_for_startRootedTargetClass
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    ∃ S : Finset (Word α),
      CharacteristicSample
        (correctedConcreteFiniteObjectHypLanguage
          obs f)
        (correctedConcreteFiniteObjectLearner
          obs f)
        S L := by

  obtain ⟨S, hS⟩ :=
    correctedConcreteCanonicalLearner_characteristicSample_for_startRootedTargetClass
      (v := w) obs f hL

  exact
    ⟨S,
      (correctedConcreteFiniteObject_characteristicSample_iff
        obs f S L).2 hS⟩

/-- One learner returning actual finite rule objects identifies every language
in the semantic start-rooted target class. -/
theorem correctedConcreteFiniteObjectLearner_identifies_startRootedTargetClass :
    IdentifiesClassFromPositiveData
      (correctedConcreteFiniteObjectHypLanguage
        obs f)
      (correctedConcreteFiniteObjectLearner
        obs f)
      (StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) := by

  intro L hL

  obtain ⟨S, hS⟩ :=
    correctedConcreteFiniteObjectLearner_characteristicSample_for_startRootedTargetClass
      (v := w) obs f hL

  intro T

  exact
    characteristicSample_eventual_correct_on_every_text
      (correctedConcreteFiniteObjectHypLanguage
        obs f)
      (correctedConcreteFiniteObjectLearner
        obs f)
      S hS T

/-- Expanded positive-text form of the finite-object class theorem. -/
theorem correctedConcreteFiniteObjectLearner_identifies_every_startRooted_text :
    ∀ L : Set (Word α),
      L ∈ StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f →
      ∀ T : TextFor L,
        EventuallyCorrectOnText
          (correctedConcreteFiniteObjectHypLanguage
            obs f)
          (correctedConcreteFiniteObjectLearner
            obs f)
          T := by
  intro L hL T
  exact
    correctedConcreteFiniteObjectLearner_identifies_startRootedTargetClass
      (v := w) obs f L hL T

end StartRootedFiniteObjectClassTheorem


section FiniteObjectSizeBounds

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- The learner output on every finite sample satisfies the explicit
paper-facing rule-count estimate. -/
theorem correctedConcreteFiniteObjectLearner_ruleCount_le_explicit_paperPower
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (correctedConcreteFiniteObjectLearner
        obs f K).ruleCount ≤
      (4 * (sampleLengthBudget K + f + 1)) ^
        (64 *
          (sampleLengthBudget K + f + 1) *
          (sampleLengthBudget K + f + 1)) := by

  exact
    correctedConcreteFiniteHypothesis_ruleCount_le_explicit_paperPower
      K obs f

/-- The same size estimate holds at every prefix of every positive text. -/
theorem correctedConcreteFiniteObjectLearner_prefix_ruleCount_le
    {L : Set (Word α)}
    [DecidableEq α]
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat) :
    (correctedConcreteFiniteObjectLearner
        obs f (T.prefixSample n)).ruleCount ≤
      (4 *
        (sampleLengthBudget (T.prefixSample n) +
          f + 1)) ^
        (64 *
          (sampleLengthBudget (T.prefixSample n) +
            f + 1) *
          (sampleLengthBudget (T.prefixSample n) +
            f + 1)) := by

  exact
    correctedConcreteFiniteObjectLearner_ruleCount_le_explicit_paperPower
      obs f (T.prefixSample n)

end FiniteObjectSizeBounds


section SelectedStageFiniteObjectPackage

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α] [DecidableEq M]
variable [Monoid M]
variable (obs : α → M)
variable (f : Nat)

/-- After the selected start-rooted coverage stage, the finite-object learner
has exactly the target language. -/
theorem correctedConcreteFiniteObjectLearner_correct_after_startRootedCoverageStage
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f)
    (T : TextFor L)
    {n : Nat}
    (hn :
      startRootedCorrectedConcreteTargetCoverageStage
          (v := w) obs f hL T ≤ n) :
    correctedConcreteFiniteObjectHypLanguage
        obs f
        (correctedConcreteFiniteObjectLearner
          obs f (T.prefixSample n)) =
      L := by

  rw [
    correctedConcreteFiniteObjectHypLanguage_apply
  ]

  exact
    correctedConcreteCanonicalLearner_correct_after_startRootedCoverageStage
      (v := w) obs f hL T hn

/-- At the selected coverage stage itself, the actual finite-object hypothesis
is already semantically correct. -/
theorem correctedConcreteFiniteObjectLearner_correct_at_startRootedCoverageStage
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f)
    (T : TextFor L) :
    correctedConcreteFiniteObjectHypLanguage
        obs f
        (correctedConcreteFiniteObjectLearner
          obs f
          (T.prefixSample
            (startRootedCorrectedConcreteTargetCoverageStage
              (v := w) obs f hL T))) =
      L := by

  exact
    correctedConcreteFiniteObjectLearner_correct_after_startRootedCoverageStage
      (v := w) obs f hL T
      (Nat.le_refl _)

/-- After the selected stage, every output is both semantically exact and
bounded by the explicit finite-object size expression for that prefix. -/
theorem correctedConcreteFiniteObjectLearner_correct_and_bounded_after_stage
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f)
    (T : TextFor L) :
    ∃ n0 : Nat,
      ∀ n : Nat, n0 ≤ n →
        correctedConcreteFiniteObjectHypLanguage
            obs f
            (correctedConcreteFiniteObjectLearner
              obs f (T.prefixSample n)) =
          L ∧
        (correctedConcreteFiniteObjectLearner
            obs f (T.prefixSample n)).ruleCount ≤
          (4 *
            (sampleLengthBudget (T.prefixSample n) +
              f + 1)) ^
            (64 *
              (sampleLengthBudget (T.prefixSample n) +
                f + 1) *
              (sampleLengthBudget (T.prefixSample n) +
                f + 1)) := by

  refine
    ⟨startRootedCorrectedConcreteTargetCoverageStage
        (v := w) obs f hL T,
      ?_⟩

  intro n hn

  exact
    ⟨correctedConcreteFiniteObjectLearner_correct_after_startRootedCoverageStage
        (v := w) obs f hL T hn,
      correctedConcreteFiniteObjectLearner_prefix_ruleCount_le
        obs f T n⟩

/-- Paper-facing conclusion: one uniform learner outputs actual finite rule
objects, identifies every target in the semantic start-rooted class, and each
output obeys the explicit rule-count bound. -/
theorem correctedConcreteFiniteObjectLearner_class_size_semantic_package :
    IdentifiesClassFromPositiveData
        (correctedConcreteFiniteObjectHypLanguage
          obs f)
        (correctedConcreteFiniteObjectLearner
          obs f)
        (StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f) ∧
      (∀ K : Finset (Word α),
        correctedConcreteFiniteObjectHypLanguage
            obs f
            (correctedConcreteFiniteObjectLearner
              obs f K) =
          CorrectedConcreteCanonicalLearnerLanguage
            K obs f) ∧
      (∀ K : Finset (Word α),
        (correctedConcreteFiniteObjectLearner
            obs f K).ruleCount ≤
          (4 * (sampleLengthBudget K + f + 1)) ^
            (64 *
              (sampleLengthBudget K + f + 1) *
              (sampleLengthBudget K + f + 1))) := by

  exact
    ⟨correctedConcreteFiniteObjectLearner_identifies_startRootedTargetClass
        (v := w) obs f,
      correctedConcreteFiniteObjectHypLanguage_apply
        obs f,
      correctedConcreteFiniteObjectLearner_ruleCount_le_explicit_paperPower
        obs f⟩

end SelectedStageFiniteObjectPackage

end MCFG
