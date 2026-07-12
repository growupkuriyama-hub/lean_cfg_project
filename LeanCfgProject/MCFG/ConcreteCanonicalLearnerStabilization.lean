/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerClassTheorem

/-!
# ConcreteCanonicalLearnerStabilization.lean

The preceding class theorem proves existence of a finite characteristic sample
for every target language in the corrected concrete MCFG class.

This file turns those existential statements into actual target-level
selectors:

```lean
correctedConcreteTargetCharacteristicSample
correctedConcreteTargetCoverageStage
```

The characteristic-sample selector depends only on the target language and its
membership proof in the language class; the hidden grammar witness is not part
of its output type.

For every positive text, the coverage-stage selector chooses a stage after
which the selected finite characteristic sample has appeared.  The file then
proves that:

* every later prefix contains the selected characteristic sample;
* every later corrected-concrete hypothesis language equals the target;
* any two hypotheses after the chosen stage have equal languages;
* the learner is semantically stable from that stage onward.

Thus the Gold-style existential stabilization theorem is exposed through a
concrete, reusable stage function.

No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section TargetCharacteristicSampleSelector

variable {α : Type u}
variable {M : Type w}
variable [Fintype M]
variable [DecidableEq α] [DecidableEq M]
variable [Monoid M]
variable (obs : α → M)
variable (f : Nat)

/-- Choose one finite characteristic sample for a target language in the
corrected concrete target class.

Classical choice is used only after the class theorem has proved existence. -/
noncomputable def correctedConcreteTargetCharacteristicSample
    {L : Set (Word α)}
    (hL :
      L ∈ CorrectedConcreteTargetClass
        (v := v) α M obs f) :
    Finset (Word α) :=
  Classical.choose
    (correctedConcreteCanonicalLearner_characteristicSample_for_targetClass
      (v := v) obs f hL)

/-- The selected target sample is a genuine characteristic sample for the
single corrected concrete learner. -/
theorem correctedConcreteTargetCharacteristicSample_characteristic
    {L : Set (Word α)}
    (hL :
      L ∈ CorrectedConcreteTargetClass
        (v := v) α M obs f) :
    CharacteristicSample
      (correctedConcreteCanonicalHypLanguage
        obs f)
      (correctedConcreteCanonicalLearner
        (α := α))
      (correctedConcreteTargetCharacteristicSample
        (v := v) obs f hL)
      L :=
  Classical.choose_spec
    (correctedConcreteCanonicalLearner_characteristicSample_for_targetClass
      (v := v) obs f hL)

/-- Positivity of the selected target sample. -/
theorem correctedConcreteTargetCharacteristicSample_positive
    {L : Set (Word α)}
    (hL :
      L ∈ CorrectedConcreteTargetClass
        (v := v) α M obs f) :
    (correctedConcreteTargetCharacteristicSample
        (v := v) obs f hL :
      Set (Word α)) ⊆
      L :=
  (correctedConcreteTargetCharacteristicSample_characteristic
    (v := v) obs f hL).1

/-- Every positive finite extension of the selected sample yields the target
language exactly. -/
theorem correctedConcreteTargetCharacteristicSample_exact_for_positive_superset
    {L : Set (Word α)}
    (hL :
      L ∈ CorrectedConcreteTargetClass
        (v := v) α M obs f)
    {K : Finset (Word α)}
    (hSK :
      (correctedConcreteTargetCharacteristicSample
          (v := v) obs f hL :
        Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKpositive :
      (K : Set (Word α)) ⊆ L) :
    correctedConcreteCanonicalHypLanguage
        obs f
        (correctedConcreteCanonicalLearner
          (α := α) K) =
      L :=
  (correctedConcreteTargetCharacteristicSample_characteristic
    (v := v) obs f hL).2
      K hSK hKpositive

/-- Exact reconstruction already holds on the selected characteristic sample
itself. -/
theorem correctedConcreteTargetCharacteristicSample_exact
    {L : Set (Word α)}
    (hL :
      L ∈ CorrectedConcreteTargetClass
        (v := v) α M obs f) :
    correctedConcreteCanonicalHypLanguage
        obs f
        (correctedConcreteCanonicalLearner
          (α := α)
          (correctedConcreteTargetCharacteristicSample
            (v := v) obs f hL)) =
      L := by
  apply
    correctedConcreteTargetCharacteristicSample_exact_for_positive_superset
      (v := v) obs f hL
  · exact Set.Subset.rfl
  · exact
      correctedConcreteTargetCharacteristicSample_positive
        (v := v) obs f hL

end TargetCharacteristicSampleSelector


section CoverageStageSelector

variable {α : Type u}
variable {M : Type w}
variable [Fintype M]
variable [DecidableEq α] [DecidableEq M]
variable [Monoid M]
variable (obs : α → M)
variable (f : Nat)

/-- Choose a text stage after which the selected target characteristic sample
is contained in every prefix sample. -/
noncomputable def correctedConcreteTargetCoverageStage
    {L : Set (Word α)}
    (hL :
      L ∈ CorrectedConcreteTargetClass
        (v := v) α M obs f)
    (T : TextFor L) :
    Nat :=
  Classical.choose
    (TextFor.eventuallyContains_finite_subset
      (correctedConcreteTargetCharacteristicSample
        (v := v) obs f hL)
      (correctedConcreteTargetCharacteristicSample_positive
        (v := v) obs f hL)
      T)

/-- Every prefix after the selected coverage stage contains the selected
characteristic sample. -/
theorem correctedConcreteTargetCharacteristicSample_subset_prefix_after
    {L : Set (Word α)}
    (hL :
      L ∈ CorrectedConcreteTargetClass
        (v := v) α M obs f)
    (T : TextFor L)
    {n : Nat}
    (hn :
      correctedConcreteTargetCoverageStage
          (v := v) obs f hL T ≤ n) :
    (correctedConcreteTargetCharacteristicSample
        (v := v) obs f hL :
      Set (Word α)) ⊆
      (T.prefixSample n : Set (Word α)) := by
  exact
    (Classical.choose_spec
      (TextFor.eventuallyContains_finite_subset
        (correctedConcreteTargetCharacteristicSample
          (v := v) obs f hL)
        (correctedConcreteTargetCharacteristicSample_positive
          (v := v) obs f hL)
        T))
      n hn

/-- Every prefix after the selected coverage stage produces exactly the target
language. -/
theorem correctedConcreteCanonicalLearner_correct_after_coverageStage
    {L : Set (Word α)}
    (hL :
      L ∈ CorrectedConcreteTargetClass
        (v := v) α M obs f)
    (T : TextFor L)
    {n : Nat}
    (hn :
      correctedConcreteTargetCoverageStage
          (v := v) obs f hL T ≤ n) :
    correctedConcreteCanonicalHypLanguage
        obs f
        (correctedConcreteCanonicalLearner
          (α := α) (T.prefixSample n)) =
      L := by
  exact
    correctedConcreteTargetCharacteristicSample_exact_for_positive_superset
      (v := v) obs f hL
      (correctedConcreteTargetCharacteristicSample_subset_prefix_after
        (v := v) obs f hL T hn)
      (T.prefixSample_subset n)

/-- Expanded form using the corrected concrete learner language directly. -/
theorem correctedConcreteCanonicalLearnerLanguage_correct_after_coverageStage
    {L : Set (Word α)}
    (hL :
      L ∈ CorrectedConcreteTargetClass
        (v := v) α M obs f)
    (T : TextFor L)
    {n : Nat}
    (hn :
      correctedConcreteTargetCoverageStage
          (v := v) obs f hL T ≤ n) :
    CorrectedConcreteCanonicalLearnerLanguage
        (T.prefixSample n) obs f =
      L := by
  exact
    correctedConcreteCanonicalLearner_correct_after_coverageStage
      (v := v) obs f hL T hn

/-- At the selected coverage stage itself, the learner is already correct. -/
theorem correctedConcreteCanonicalLearner_correct_at_coverageStage
    {L : Set (Word α)}
    (hL :
      L ∈ CorrectedConcreteTargetClass
        (v := v) α M obs f)
    (T : TextFor L) :
    correctedConcreteCanonicalHypLanguage
        obs f
        (correctedConcreteCanonicalLearner
          (α := α)
          (T.prefixSample
            (correctedConcreteTargetCoverageStage
              (v := v) obs f hL T))) =
      L := by
  exact
    correctedConcreteCanonicalLearner_correct_after_coverageStage
      (v := v) obs f hL T
      (Nat.le_refl _)

/-- Any two learner hypotheses after the selected stage have the same
interpreted language. -/
theorem correctedConcreteCanonicalLearner_eventually_language_constant
    {L : Set (Word α)}
    (hL :
      L ∈ CorrectedConcreteTargetClass
        (v := v) α M obs f)
    (T : TextFor L)
    {m n : Nat}
    (hm :
      correctedConcreteTargetCoverageStage
          (v := v) obs f hL T ≤ m)
    (hn :
      correctedConcreteTargetCoverageStage
          (v := v) obs f hL T ≤ n) :
    correctedConcreteCanonicalHypLanguage
        obs f
        (correctedConcreteCanonicalLearner
          (α := α) (T.prefixSample m)) =
      correctedConcreteCanonicalHypLanguage
        obs f
        (correctedConcreteCanonicalLearner
          (α := α) (T.prefixSample n)) := by
  rw [
    correctedConcreteCanonicalLearner_correct_after_coverageStage
      (v := v) obs f hL T hm,
    correctedConcreteCanonicalLearner_correct_after_coverageStage
      (v := v) obs f hL T hn
  ]

/-- The selected coverage stage is an explicit witness of eventual semantic
stability. -/
theorem correctedConcreteCanonicalLearner_has_stabilizationStage
    {L : Set (Word α)}
    (hL :
      L ∈ CorrectedConcreteTargetClass
        (v := v) α M obs f)
    (T : TextFor L) :
    ∃ n0 : Nat,
      (∀ n : Nat, n0 ≤ n →
        correctedConcreteCanonicalHypLanguage
            obs f
            (correctedConcreteCanonicalLearner
              (α := α) (T.prefixSample n)) =
          L) ∧
      (∀ m n : Nat, n0 ≤ m → n0 ≤ n →
        correctedConcreteCanonicalHypLanguage
            obs f
            (correctedConcreteCanonicalLearner
              (α := α) (T.prefixSample m)) =
          correctedConcreteCanonicalHypLanguage
            obs f
            (correctedConcreteCanonicalLearner
              (α := α) (T.prefixSample n))) := by
  refine
    ⟨correctedConcreteTargetCoverageStage
        (v := v) obs f hL T,
      ?_,
      ?_⟩
  · intro n hn
    exact
      correctedConcreteCanonicalLearner_correct_after_coverageStage
        (v := v) obs f hL T hn
  · intro m n hm hn
    exact
      correctedConcreteCanonicalLearner_eventually_language_constant
        (v := v) obs f hL T hm hn

end CoverageStageSelector


section UniformClassStabilization

variable {α : Type u}
variable {M : Type w}
variable [Fintype M]
variable [DecidableEq α] [DecidableEq M]
variable [Monoid M]
variable (obs : α → M)
variable (f : Nat)

/-- Uniform class-level statement with selected finite samples and selected
stabilization stages.

The selector functions are the same for every target language in the class;
only `L`, its class-membership witness, and the positive text vary. -/
theorem correctedConcreteCanonicalLearner_uniform_selected_stabilization :
    ∀ L : Set (Word α),
      ∀ hL :
        L ∈ CorrectedConcreteTargetClass
          (v := v) α M obs f,
        CharacteristicSample
          (correctedConcreteCanonicalHypLanguage
            obs f)
          (correctedConcreteCanonicalLearner
            (α := α))
          (correctedConcreteTargetCharacteristicSample
            (v := v) obs f hL)
          L ∧
        ∀ T : TextFor L,
          ∀ n : Nat,
            correctedConcreteTargetCoverageStage
                (v := v) obs f hL T ≤ n →
              correctedConcreteCanonicalHypLanguage
                  obs f
                  (correctedConcreteCanonicalLearner
                    (α := α) (T.prefixSample n)) =
                L := by
  intro L hL
  constructor
  · exact
      correctedConcreteTargetCharacteristicSample_characteristic
        (v := v) obs f hL
  · intro T n hn
    exact
      correctedConcreteCanonicalLearner_correct_after_coverageStage
        (v := v) obs f hL T hn

/-- Uniform eventual-constancy form over the whole corrected concrete target
class. -/
theorem correctedConcreteCanonicalLearner_uniform_eventual_language_constancy :
    ∀ L : Set (Word α),
      L ∈ CorrectedConcreteTargetClass
          (v := v) α M obs f →
      ∀ T : TextFor L,
        ∃ n0 : Nat,
          ∀ m n : Nat,
            n0 ≤ m →
            n0 ≤ n →
            correctedConcreteCanonicalHypLanguage
                obs f
                (correctedConcreteCanonicalLearner
                  (α := α) (T.prefixSample m)) =
              correctedConcreteCanonicalHypLanguage
                obs f
                (correctedConcreteCanonicalLearner
                  (α := α) (T.prefixSample n)) := by
  intro L hL T
  refine
    ⟨correctedConcreteTargetCoverageStage
        (v := v) obs f hL T,
      ?_⟩
  intro m n hm hn
  exact
    correctedConcreteCanonicalLearner_eventually_language_constant
      (v := v) obs f hL T hm hn

/-- Paper-style final stabilization package.

For every target in the class it supplies a selected finite characteristic
sample; for every positive text it supplies a selected stage after which all
hypothesis languages are exactly the target and hence pairwise equal. -/
theorem correctedConcreteCanonicalLearner_stabilization_conclusion_package :
    ∀ L : Set (Word α),
      ∀ hL :
        L ∈ CorrectedConcreteTargetClass
          (v := v) α M obs f,
        let S :=
          correctedConcreteTargetCharacteristicSample
            (v := v) obs f hL
        (S : Set (Word α)) ⊆ L ∧
        correctedConcreteCanonicalHypLanguage
            obs f
            (correctedConcreteCanonicalLearner
              (α := α) S) =
          L ∧
        ∀ T : TextFor L,
          let n0 :=
            correctedConcreteTargetCoverageStage
              (v := v) obs f hL T
          (∀ n : Nat, n0 ≤ n →
            correctedConcreteCanonicalHypLanguage
                obs f
                (correctedConcreteCanonicalLearner
                  (α := α) (T.prefixSample n)) =
              L) ∧
          (∀ m n : Nat, n0 ≤ m → n0 ≤ n →
            correctedConcreteCanonicalHypLanguage
                obs f
                (correctedConcreteCanonicalLearner
                  (α := α) (T.prefixSample m)) =
              correctedConcreteCanonicalHypLanguage
                obs f
                (correctedConcreteCanonicalLearner
                  (α := α) (T.prefixSample n))) := by
  intro L hL
  dsimp
  refine
    ⟨correctedConcreteTargetCharacteristicSample_positive
        (v := v) obs f hL,
      correctedConcreteTargetCharacteristicSample_exact
        (v := v) obs f hL,
      ?_⟩
  intro T
  dsimp
  constructor
  · intro n hn
    exact
      correctedConcreteCanonicalLearner_correct_after_coverageStage
        (v := v) obs f hL T hn
  · intro m n hm hn
    exact
      correctedConcreteCanonicalLearner_eventually_language_constant
        (v := v) obs f hL T hm hn

end UniformClassStabilization

end MCFG
