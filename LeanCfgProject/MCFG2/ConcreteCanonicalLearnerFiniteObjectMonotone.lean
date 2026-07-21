/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerFiniteObjectIdentification

/-!
# ConcreteCanonicalLearnerFiniteObjectMonotone.lean

The finite rule-code types depend on the input sample.  Consequently a rule
code over `S` is not literally an element of the rule-code type over a larger
sample `K`.

This file constructs the correct replacement: a semantic simulation of finite
hypothesis objects under sample extension.

For every inclusion

```lean
(S : Set (Word α)) ⊆ (K : Set (Word α)),
```

sample evidence is transported from `S` to `K`.  The finite-enumeration
completeness theorems then select corresponding concrete unit and binary rule
codes over `K`.  These selected rules preserve:

* source and target tuples for unit rules;
* source, left source, right source, and template body for binary rules.

The resulting structure

```lean
CorrectedConcreteFiniteHypothesisSimulation
```

transports listed derivations and listed string derivations between actual
finite hypothesis objects.

The main structural monotonicity theorem is

```lean
correctedConcreteFiniteHypothesis_language_mono.
```

It proves language inclusion by transporting derivation trees through the
finite rule lists, rather than by appealing only to the previously established
semantic equality.

The file also gives monotonicity directly for the learner whose outputs are
actual finite rule objects.

No target grammar occurs in the construction.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section UnitRuleCodeTransport

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {S K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Transport one finite unit-rule code through sample extension.

The underlying proof is:

```text
concrete rule over S
→ sample unit evidence over S
→ sample unit evidence over K
→ completeness of the finite unit-rule enumeration over K.
```
-/
noncomputable def CorrectedConcreteUnitRuleCode.mono
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (U :
      CorrectedConcreteUnitRuleCode
        S obs f) :
    CorrectedConcreteUnitRuleCode
      K obs f :=
  ⟨U.index,
    concreteUnitRuleOfEvidence
      K obs
      (U.rule.evidence.mono hSK)⟩

namespace CorrectedConcreteUnitRuleCode

/-- Arity is unchanged by sample-extension transport. -/
@[simp] theorem mono_arity
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (U :
      CorrectedConcreteUnitRuleCode
        S obs f) :
    (U.mono hSK).arity = U.arity :=
  rfl

/-- Unit-rule source is preserved. -/
theorem mono_source
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (U :
      CorrectedConcreteUnitRuleCode
        S obs f) :
    (U.mono hSK).source =
      U.source := by
  exact
    concreteUnitRuleOfEvidence_source
      K obs
      (U.rule.evidence.mono hSK)

/-- Unit-rule target is preserved. -/
theorem mono_target
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (U :
      CorrectedConcreteUnitRuleCode
        S obs f) :
    (U.mono hSK).target =
      U.target := by
  exact
    concreteUnitRuleOfEvidence_target
      K obs
      (U.rule.evidence.mono hSK)

/-- The transported code is listed in every complete finite hypothesis over
the enlarged sample. -/
theorem mono_mem
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (U :
      CorrectedConcreteUnitRuleCode
        S obs f)
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    U.mono hSK ∈ H.unitRuleCodes :=
  H.unitRuleCodes_complete
    (U.mono hSK)

end CorrectedConcreteUnitRuleCode

end UnitRuleCodeTransport


section BinaryRuleCodeTransport

variable {α : Type u}
variable {S K : Finset (Word α)}
variable {f : Nat}

/-- Transport one corrected finite binary-rule code through sample extension.

Exact-once syntax is retained from the old rule body, while its sample evidence
is transported to the larger sample and re-enumerated there.
-/
noncomputable def CorrectedConcreteBinaryRuleCode.mono
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    CorrectedConcreteBinaryRuleCode
      K f :=
  ⟨B.parentIndex,
    B.leftIndex,
    B.rightIndex,
    correctedConcreteBinaryRuleOfEvidence
      K
      (B.rule.evidence.mono hSK)
      B.rule.witness.body_exactOnce⟩

namespace CorrectedConcreteBinaryRuleCode

/-- Parent arity is unchanged. -/
@[simp] theorem mono_parentArity
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    (B.mono hSK).parentArity =
      B.parentArity :=
  rfl

/-- Left arity is unchanged. -/
@[simp] theorem mono_leftArity
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    (B.mono hSK).leftArity =
      B.leftArity :=
  rfl

/-- Right arity is unchanged. -/
@[simp] theorem mono_rightArity
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    (B.mono hSK).rightArity =
      B.rightArity :=
  rfl

/-- Left source tuple is preserved. -/
theorem mono_leftSource
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    (B.mono hSK).leftSource =
      B.leftSource := by
  exact
    correctedConcreteBinaryRuleOfEvidence_leftSource
      K
      (B.rule.evidence.mono hSK)
      B.rule.witness.body_exactOnce

/-- Right source tuple is preserved. -/
theorem mono_rightSource
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    (B.mono hSK).rightSource =
      B.rightSource := by
  exact
    correctedConcreteBinaryRuleOfEvidence_rightSource
      K
      (B.rule.evidence.mono hSK)
      B.rule.witness.body_exactOnce

/-- Template body is preserved. -/
theorem mono_body
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    (B.mono hSK).body =
      B.body := by
  exact
    correctedConcreteBinaryRuleOfEvidence_body
      K
      (B.rule.evidence.mono hSK)
      B.rule.witness.body_exactOnce

/-- Parent source tuple is preserved. -/
theorem mono_source
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    (B.mono hSK).source =
      B.source := by

  calc
    (B.mono hSK).source =
        evalTemplateTuple B.body
          B.leftSource B.rightSource :=
      correctedConcreteBinaryRuleOfEvidence_source
        K
        (B.rule.evidence.mono hSK)
        B.rule.witness.body_exactOnce
    _ = B.source :=
      B.rule.source_eq_composition.symm

/-- The transported code is listed in every complete finite hypothesis over
the enlarged sample. -/
theorem mono_mem
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (B :
      CorrectedConcreteBinaryRuleCode
        S f)
    (H :
      CorrectedConcreteFiniteHypothesis
        K (fun _ => PUnit.unit) f) :
    B.mono hSK ∈ H.binaryRuleCodes :=
  H.binaryRuleCodes_complete
    (B.mono hSK)

end CorrectedConcreteBinaryRuleCode

end BinaryRuleCodeTransport


section FiniteHypothesisSimulation

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {S K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- A semantic rule simulation between two actual finite hypothesis objects.

The source and target samples may differ.  Every listed source rule is mapped
to a listed target rule preserving the tuples and template used by the
derivation relation. -/
structure CorrectedConcreteFiniteHypothesisSimulation
    (HS :
      CorrectedConcreteFiniteHypothesis
        S obs f)
    (HK :
      CorrectedConcreteFiniteHypothesis
        K obs f) where

  unitMap :
    CorrectedConcreteUnitRuleCode
        S obs f →
      CorrectedConcreteUnitRuleCode
        K obs f

  unitMap_mem :
    ∀ U,
      U ∈ HS.unitRuleCodes →
        unitMap U ∈ HK.unitRuleCodes

  unitMap_source :
    ∀ U,
      (unitMap U).source =
        U.source

  unitMap_target :
    ∀ U,
      (unitMap U).target =
        U.target

  binaryMap :
    CorrectedConcreteBinaryRuleCode
        S f →
      CorrectedConcreteBinaryRuleCode
        K f

  binaryMap_mem :
    ∀ B,
      B ∈ HS.binaryRuleCodes →
        binaryMap B ∈ HK.binaryRuleCodes

  binaryMap_source :
    ∀ B,
      (binaryMap B).source =
        B.source

  binaryMap_leftSource :
    ∀ B,
      (binaryMap B).leftSource =
        B.leftSource

  binaryMap_rightSource :
    ∀ B,
      (binaryMap B).rightSource =
        B.rightSource

  binaryMap_body :
    ∀ B,
      (binaryMap B).body =
        B.body

namespace CorrectedConcreteFiniteHypothesisSimulation

/-- Sample extension produces a semantic simulation between any complete finite
hypothesis objects over the two samples. -/
noncomputable def ofSampleSubset
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (HS :
      CorrectedConcreteFiniteHypothesis
        S obs f)
    (HK :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    CorrectedConcreteFiniteHypothesisSimulation
      HS HK where

  unitMap :=
    fun U => U.mono hSK

  unitMap_mem :=
    fun U hU =>
      HK.unitRuleCodes_complete
        (U.mono hSK)

  unitMap_source :=
    fun U => U.mono_source hSK

  unitMap_target :=
    fun U => U.mono_target hSK

  binaryMap :=
    fun B => B.mono hSK

  binaryMap_mem :=
    fun B hB =>
      HK.binaryRuleCodes_complete
        (B.mono hSK)

  binaryMap_source :=
    fun B => B.mono_source hSK

  binaryMap_leftSource :=
    fun B => B.mono_leftSource hSK

  binaryMap_rightSource :=
    fun B => B.mono_rightSource hSK

  binaryMap_body :=
    fun B => B.mono_body hSK

/-- Transport a listed tuple derivation through a finite-hypothesis
simulation. -/
theorem derives
    {HS :
      CorrectedConcreteFiniteHypothesis
        S obs f}
    {HK :
      CorrectedConcreteFiniteHypothesis
        K obs f}
    (Φ :
      CorrectedConcreteFiniteHypothesisSimulation
        HS HK)
    {d : Nat}
    {x y : Tuple α d}
    (h :
      ListedFiniteCorrectedConcreteLearnerDerives
        S obs f HS x y) :
    ListedFiniteCorrectedConcreteLearnerDerives
      K obs f HK x y := by

  induction h with

  | self x =>
      exact
        ListedFiniteCorrectedConcreteLearnerDerives.self
          x

  | unit U hU hrest ih =>
      let U' :=
        Φ.unitMap U

      have ih' :
          ListedFiniteCorrectedConcreteLearnerDerives
            K obs f HK U'.target _ := by
        rw [Φ.unitMap_target U]
        exact ih

      have hstep :
          ListedFiniteCorrectedConcreteLearnerDerives
            K obs f HK U'.source _ :=
        ListedFiniteCorrectedConcreteLearnerDerives.unit
          U'
          (Φ.unitMap_mem U hU)
          ih'

      rw [Φ.unitMap_source U] at hstep
      exact hstep

  | binary B hB hleft hright ihleft ihright =>
      let B' :=
        Φ.binaryMap B

      have ihleft' :
          ListedFiniteCorrectedConcreteLearnerDerives
            K obs f HK B'.leftSource _ := by
        rw [Φ.binaryMap_leftSource B]
        exact ihleft

      have ihright' :
          ListedFiniteCorrectedConcreteLearnerDerives
            K obs f HK B'.rightSource _ := by
        rw [Φ.binaryMap_rightSource B]
        exact ihright

      have hstep :
          ListedFiniteCorrectedConcreteLearnerDerives
            K obs f HK B'.source
              (evalTemplateTuple B'.body _ _) :=
        ListedFiniteCorrectedConcreteLearnerDerives.binary
          B'
          (Φ.binaryMap_mem B hB)
          ihleft'
          ihright'

      rw [
        Φ.binaryMap_source B,
        Φ.binaryMap_body B
      ] at hstep

      exact hstep

  | trans hxy hyz ihxy ihyz =>
      exact
        ListedFiniteCorrectedConcreteLearnerDerives.trans
          ihxy ihyz

end CorrectedConcreteFiniteHypothesisSimulation

end FiniteHypothesisSimulation


section ListedStringTransport

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {S K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Transport one listed string derivation through sample extension and a
finite-hypothesis simulation. -/
def ListedFiniteCorrectedConcreteStringDerives.mono
    {HS :
      CorrectedConcreteFiniteHypothesis
        S obs f}
    {HK :
      CorrectedConcreteFiniteHypothesis
        K obs f}
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (Φ :
      CorrectedConcreteFiniteHypothesisSimulation
        HS HK)
    {word : Word α}
    (D :
      ListedFiniteCorrectedConcreteStringDerives
        S obs f HS word) :
    ListedFiniteCorrectedConcreteStringDerives
      K obs f HK word where

  startWord :=
    D.startWord

  start_mem :=
    hSK D.start_mem

  derives :=
    Φ.derives D.derives

/-- Structural language monotonicity for actual finite hypothesis objects. -/
theorem correctedConcreteFiniteHypothesis_language_mono
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (HS :
      CorrectedConcreteFiniteHypothesis
        S obs f)
    (HK :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    HS.Language ⊆
      HK.Language := by

  let Φ :
      CorrectedConcreteFiniteHypothesisSimulation
        HS HK :=
    CorrectedConcreteFiniteHypothesisSimulation.ofSampleSubset
      hSK HS HK

  intro word hword

  exact hword.mono hSK Φ

/-- Structural monotonicity specialized to the canonical finite hypothesis
objects output by the learner. -/
theorem correctedConcreteFiniteHypothesis_canonical_language_mono
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α))) :
    (correctedConcreteFiniteHypothesis
        S obs f).Language ⊆
      (correctedConcreteFiniteHypothesis
        K obs f).Language :=
  correctedConcreteFiniteHypothesis_language_mono
    hSK
    (correctedConcreteFiniteHypothesis
      S obs f)
    (correctedConcreteFiniteHypothesis
      K obs f)

end ListedStringTransport


section FiniteObjectLearnerMonotonicity

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- The actual finite-object learner is semantically monotone under finite
sample extension, proved by structural transport of its listed derivations. -/
theorem correctedConcreteFiniteObjectLearner_language_mono
    (obs : α → M)
    (f : Nat)
    {S K : Finset (Word α)}
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α))) :
    correctedConcreteFiniteObjectHypLanguage
        obs f
        (correctedConcreteFiniteObjectLearner
          obs f S) ⊆
      correctedConcreteFiniteObjectHypLanguage
        obs f
        (correctedConcreteFiniteObjectLearner
          obs f K) := by

  change
    (correctedConcreteFiniteHypothesis
        S obs f).Language ⊆
      (correctedConcreteFiniteHypothesis
        K obs f).Language

  exact
    correctedConcreteFiniteHypothesis_canonical_language_mono
      (obs := obs) (f := f) hSK

/-- The finite-object learner is consistent with every observed finite
sample. -/
theorem correctedConcreteFiniteObjectLearner_consistent
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    (K : Set (Word α)) ⊆
      correctedConcreteFiniteObjectHypLanguage
        obs f
        (correctedConcreteFiniteObjectLearner
          obs f K) := by

  rw [
    correctedConcreteFiniteObjectHypLanguage_apply
  ]

  exact
    sample_subset_correctedConcreteCanonicalLearnerLanguage
      K obs f

/-- Structural finite-object monotonicity agrees with the earlier semantic
monotonicity theorem for the corrected concrete learner. -/
theorem correctedConcreteFiniteObjectLearner_monotone_semantic_package
    (obs : α → M)
    (f : Nat) :
    (∀ K : Finset (Word α),
      (K : Set (Word α)) ⊆
        correctedConcreteFiniteObjectHypLanguage
          obs f
          (correctedConcreteFiniteObjectLearner
            obs f K)) ∧
    (∀ S K : Finset (Word α),
      (S : Set (Word α)) ⊆
          (K : Set (Word α)) →
      correctedConcreteFiniteObjectHypLanguage
          obs f
          (correctedConcreteFiniteObjectLearner
            obs f S) ⊆
        correctedConcreteFiniteObjectHypLanguage
          obs f
          (correctedConcreteFiniteObjectLearner
            obs f K)) ∧
    (∀ K : Finset (Word α),
      correctedConcreteFiniteObjectHypLanguage
          obs f
          (correctedConcreteFiniteObjectLearner
            obs f K) =
        CorrectedConcreteCanonicalLearnerLanguage
          K obs f) := by

  exact
    ⟨correctedConcreteFiniteObjectLearner_consistent
        obs f,
      fun S K hSK =>
        correctedConcreteFiniteObjectLearner_language_mono
          obs f hSK,
      correctedConcreteFiniteObjectHypLanguage_apply
        obs f⟩

end FiniteObjectLearnerMonotonicity


section SimulationSemanticPackage

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Paper-facing package exposing the rule-level maps and the resulting
language inclusion for canonical finite objects. -/
theorem correctedConcreteFiniteHypothesis_sampleExtension_package
    (obs : α → M)
    (f : Nat)
    {S K : Finset (Word α)}
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α))) :
    (∃ Φ :
      CorrectedConcreteFiniteHypothesisSimulation
        (correctedConcreteFiniteHypothesis
          S obs f)
        (correctedConcreteFiniteHypothesis
          K obs f),
      (∀ U,
        (Φ.unitMap U).source =
          U.source ∧
        (Φ.unitMap U).target =
          U.target) ∧
      (∀ B,
        (Φ.binaryMap B).source =
            B.source ∧
        (Φ.binaryMap B).leftSource =
            B.leftSource ∧
        (Φ.binaryMap B).rightSource =
            B.rightSource ∧
        (Φ.binaryMap B).body =
            B.body)) ∧
    (correctedConcreteFiniteHypothesis
        S obs f).Language ⊆
      (correctedConcreteFiniteHypothesis
        K obs f).Language := by

  let HS :=
    correctedConcreteFiniteHypothesis
      S obs f

  let HK :=
    correctedConcreteFiniteHypothesis
      K obs f

  let Φ :
      CorrectedConcreteFiniteHypothesisSimulation
        HS HK :=
    CorrectedConcreteFiniteHypothesisSimulation.ofSampleSubset
      hSK HS HK

  refine
    ⟨⟨Φ, ?_, ?_⟩,
      correctedConcreteFiniteHypothesis_language_mono
        hSK HS HK⟩

  · intro U
    exact
      ⟨Φ.unitMap_source U,
        Φ.unitMap_target U⟩

  · intro B
    exact
      ⟨Φ.binaryMap_source B,
        Φ.binaryMap_leftSource B,
        Φ.binaryMap_rightSource B,
        Φ.binaryMap_body B⟩

end SimulationSemanticPackage

end MCFG
