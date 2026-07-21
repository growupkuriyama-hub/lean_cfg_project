/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarBoundedRepresentation

/-!
# ConcreteCanonicalLearnerWorkingGrammarRepresentationRank.lean

The bounded representation hierarchy gives a natural numerical invariant.

This file separates two ranks.

## 1. Bounded representation rank

For a language `L` having some finite cut-compiled representation, define

```lean
boundedCutCompiledWorkingGrammarRepresentationRank.
```

It is the least budget `n` such that

```lean
L ∈ BoundedCutCompiledWorkingGrammarLanguageClass α f n.
```

The rank satisfies:

```lean
L ∈ BoundedClass f n ↔ rank L ≤ n.
```

## 2. Exact learner-output rank

For the fixed actual grammar-valued learner, define

```lean
CorrectedConcreteWorkingGrammarExactOutputAtBudget hα obs f L n
```

to mean that some finite positive sample `K ⊆ L` has total word length at
most `n` and that the actual output grammar on `K` has language exactly `L`.

The least such budget is

```lean
correctedConcreteWorkingGrammarExactOutputRank.
```

For every semantic start-rooted target this rank exists, because a finite
characteristic sample gives an exact output immediately.

The selected characteristic sample supplies the explicit upper bound

```lean
exactOutputRank ≤ sampleLengthBudget selectedCharacteristicSample.
```

Every exact learner output at budget `n` is also a bounded grammar
representation at budget `n`.  Consequently:

```lean
bounded representation rank ≤ exact learner-output rank.
```

These ranks are proof-relative definitions only syntactically: proof
irrelevance shows that the numerical value is independent of the supplied
existence proof.

This is a semantic/sample-length complexity measure.  It is not yet a
computability result for finding the minimum rank.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section GenericBoundedRepresentationRank

variable (α : Type u)

/-- A language has some finite bounded cut-compiled representation. -/
def HasBoundedCutCompiledWorkingGrammarRepresentation
    (f : Nat)
    (L : Set (Word α)) :
    Prop :=
  ∃ n : Nat,
    L ∈
      BoundedCutCompiledWorkingGrammarLanguageClass
        (w := w) α f n

/-- Least finite budget at which a represented language enters the bounded
cut-compiled hierarchy. -/
noncomputable def boundedCutCompiledWorkingGrammarRepresentationRank
    {f : Nat}
    {L : Set (Word α)}
    (hL :
      HasBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) α f L) :
    Nat :=
  Nat.find hL

namespace HasBoundedCutCompiledWorkingGrammarRepresentation

variable {α : Type u}
variable {f : Nat}
variable {L : Set (Word α)}

/-- The least bounded-representation budget really represents the language. -/
theorem rank_mem
    (hL :
      HasBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) α f L) :
    L ∈
      BoundedCutCompiledWorkingGrammarLanguageClass
        (w := w) α f
        (boundedCutCompiledWorkingGrammarRepresentationRank
          (w := w) α hL) := by

  exact
    Nat.find_spec hL

/-- Minimality of the bounded representation rank. -/
theorem rank_le_of_mem
    (hL :
      HasBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) α f L)
    {n : Nat}
    (hn :
      L ∈
        BoundedCutCompiledWorkingGrammarLanguageClass
          (w := w) α f n) :
    boundedCutCompiledWorkingGrammarRepresentationRank
        (w := w) α hL ≤
      n := by

  exact
    Nat.find_min' hL hn

/-- Membership in the bounded hierarchy is exactly being above the least
representation rank. -/
theorem mem_iff_rank_le
    (hL :
      HasBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) α f L)
    (n : Nat) :
    L ∈
        BoundedCutCompiledWorkingGrammarLanguageClass
          (w := w) α f n ↔
      boundedCutCompiledWorkingGrammarRepresentationRank
          (w := w) α hL ≤
        n := by

  constructor

  · intro hn
    exact hL.rank_le_of_mem hn

  · intro hrank

    exact
      boundedCutCompiledWorkingGrammarLanguageClass_mono
        (w := w) hrank
        hL.rank_mem

/-- No budget below the representation rank can represent the language. -/
theorem not_mem_of_lt_rank
    (hL :
      HasBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) α f L)
    {n : Nat}
    (hn :
      n <
        boundedCutCompiledWorkingGrammarRepresentationRank
          (w := w) α hL) :
    L ∉
      BoundedCutCompiledWorkingGrammarLanguageClass
        (w := w) α f n := by

  intro hmem

  have hle :=
    hL.rank_le_of_mem hmem

  omega

/-- Rank zero is equivalent to membership at level zero. -/
theorem rank_eq_zero_iff
    (hL :
      HasBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) α f L) :
    boundedCutCompiledWorkingGrammarRepresentationRank
          (w := w) α hL =
        0 ↔
      L ∈
        BoundedCutCompiledWorkingGrammarLanguageClass
          (w := w) α f 0 := by

  constructor

  · intro hrank

    have hmem :=
      hL.rank_mem

    simpa [hrank] using hmem

  · intro hmem

    have hle :=
      hL.rank_le_of_mem hmem

    omega

/-- The numerical rank is independent of the proof used to establish
representability. -/
theorem rank_proof_irrel
    (h₁ h₂ :
      HasBoundedCutCompiledWorkingGrammarRepresentation
        (w := w) α f L) :
    boundedCutCompiledWorkingGrammarRepresentationRank
        (w := w) α h₁ =
      boundedCutCompiledWorkingGrammarRepresentationRank
        (w := w) α h₂ := by

  have hp :
      h₁ = h₂ :=
    Subsingleton.elim _ _

  subst h₂

  rfl

end HasBoundedCutCompiledWorkingGrammarRepresentation

end GenericBoundedRepresentationRank


section SampleLanguageRepresentationRank

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]

/-- Existence proof used to define the bounded representation rank of one
corrected concrete sample language. -/
theorem correctedConcreteCanonicalLearnerLanguage_hasBoundedRepresentation
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    HasBoundedCutCompiledWorkingGrammarRepresentation
      (w := max u v)
      α f
      (CorrectedConcreteCanonicalLearnerLanguage
        K obs f) := by

  exact
    ⟨sampleLengthBudget K,
      correctedConcreteCanonicalLearnerLanguage_mem_boundedCutCompiledClass
        hα obs f K⟩

/-- Least bounded-presentation budget of one corrected concrete learner
language. -/
noncomputable def correctedConcreteCanonicalLearnerLanguageRepresentationRank
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    Nat :=
  boundedCutCompiledWorkingGrammarRepresentationRank
    (w := max u v)
    α
    (correctedConcreteCanonicalLearnerLanguage_hasBoundedRepresentation
      hα obs f K)

/-- The representation rank of a sample language is at most the total sample
length used to construct it. -/
theorem correctedConcreteCanonicalLearnerLanguageRepresentationRank_le_sampleLength
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteCanonicalLearnerLanguageRepresentationRank
        hα obs f K ≤
      sampleLengthBudget K := by

  unfold
    correctedConcreteCanonicalLearnerLanguageRepresentationRank

  exact
    (correctedConcreteCanonicalLearnerLanguage_hasBoundedRepresentation
      hα obs f K).rank_le_of_mem
        (correctedConcreteCanonicalLearnerLanguage_mem_boundedCutCompiledClass
          hα obs f K)

/-- The sample language belongs to the bounded hierarchy at its least rank. -/
theorem correctedConcreteCanonicalLearnerLanguage_mem_at_representationRank
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    CorrectedConcreteCanonicalLearnerLanguage
        K obs f ∈
      BoundedCutCompiledWorkingGrammarLanguageClass
        (w := max u v)
        α f
        (correctedConcreteCanonicalLearnerLanguageRepresentationRank
          hα obs f K) := by

  exact
    (correctedConcreteCanonicalLearnerLanguage_hasBoundedRepresentation
      hα obs f K).rank_mem

/-- Exact-once reachable sample semantics has some bounded representation. -/
theorem exactReachableSampleStringLanguage_hasBoundedRepresentation
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    HasBoundedCutCompiledWorkingGrammarRepresentation
      (w := max u v)
      α f
      (ExactReachableSampleStringLanguage
        K obs f) := by

  exact
    ⟨sampleLengthBudget K,
      exactReachableSampleStringLanguage_mem_boundedCutCompiledClass
        hα obs f K⟩

/-- Least bounded representation rank of the exact-once reachable sample
language. -/
noncomputable def exactReachableSampleStringLanguageRepresentationRank
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    Nat :=
  boundedCutCompiledWorkingGrammarRepresentationRank
    (w := max u v)
    α
    (exactReachableSampleStringLanguage_hasBoundedRepresentation
      hα obs f K)

/-- Exact-once reachable sample-language rank is also at most total sample
length. -/
theorem exactReachableSampleStringLanguageRepresentationRank_le_sampleLength
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    exactReachableSampleStringLanguageRepresentationRank
        hα obs f K ≤
      sampleLengthBudget K := by

  unfold
    exactReachableSampleStringLanguageRepresentationRank

  exact
    (exactReachableSampleStringLanguage_hasBoundedRepresentation
      hα obs f K).rank_le_of_mem
        (exactReachableSampleStringLanguage_mem_boundedCutCompiledClass
          hα obs f K)

end SampleLanguageRepresentationRank


section ExactOutputBudget

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]

/-- At budget `n`, the actual grammar-valued learner exactly outputs `L` from
some finite positive sample of total length at most `n`. -/
def CorrectedConcreteWorkingGrammarExactOutputAtBudget
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (L : Set (Word α))
    (n : Nat) :
    Prop :=
  ∃ K : Finset (Word α),
    (K : Set (Word α)) ⊆ L ∧
    sampleLengthBudget K ≤ n ∧
    (correctedConcreteWorkingGrammarLearner
      hα obs f K).grammar.StringLanguage =
        L

/-- A language has some finite positive exact-output budget. -/
def HasCorrectedConcreteWorkingGrammarExactOutputBudget
    (hα : Nonempty α)
    (obs : α → M)
    (f : Nat)
    (L : Set (Word α)) :
    Prop :=
  ∃ n : Nat,
    CorrectedConcreteWorkingGrammarExactOutputAtBudget
      hα obs f L n

/-- The exact-output predicate is upward closed in the budget. -/
theorem correctedConcreteWorkingGrammarExactOutputAtBudget_mono
    {hα : Nonempty α}
    {obs : α → M}
    {f : Nat}
    {L : Set (Word α)}
    {n m : Nat}
    (hnm : n ≤ m)
    (h :
      CorrectedConcreteWorkingGrammarExactOutputAtBudget
        hα obs f L n) :
    CorrectedConcreteWorkingGrammarExactOutputAtBudget
      hα obs f L m := by

  rcases h with
    ⟨K, hpositive, hlength, hexact⟩

  exact
    ⟨K,
      hpositive,
      hlength.trans hnm,
      hexact⟩

/-- Least total positive-sample length at which the actual learner outputs the
target language exactly. -/
noncomputable def correctedConcreteWorkingGrammarExactOutputRank
    {hα : Nonempty α}
    {obs : α → M}
    {f : Nat}
    {L : Set (Word α)}
    (hL :
      HasCorrectedConcreteWorkingGrammarExactOutputBudget
        hα obs f L) :
    Nat :=
  Nat.find hL

namespace HasCorrectedConcreteWorkingGrammarExactOutputBudget

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]
variable {hα : Nonempty α}
variable {obs : α → M}
variable {f : Nat}
variable {L : Set (Word α)}

/-- The least exact-output budget is attained by some finite positive sample. -/
theorem rank_spec
    (hL :
      HasCorrectedConcreteWorkingGrammarExactOutputBudget
        hα obs f L) :
    CorrectedConcreteWorkingGrammarExactOutputAtBudget
      hα obs f L
      (correctedConcreteWorkingGrammarExactOutputRank
        hL) := by

  exact
    Nat.find_spec hL

/-- Minimality of the exact-output rank. -/
theorem rank_le_of_exactOutputAtBudget
    (hL :
      HasCorrectedConcreteWorkingGrammarExactOutputBudget
        hα obs f L)
    {n : Nat}
    (hn :
      CorrectedConcreteWorkingGrammarExactOutputAtBudget
        hα obs f L n) :
    correctedConcreteWorkingGrammarExactOutputRank
        hL ≤
      n := by

  exact
    Nat.find_min' hL hn

/-- Exact output at budget `n` is equivalent to being above the exact-output
rank. -/
theorem exactOutputAtBudget_iff_rank_le
    (hL :
      HasCorrectedConcreteWorkingGrammarExactOutputBudget
        hα obs f L)
    (n : Nat) :
    CorrectedConcreteWorkingGrammarExactOutputAtBudget
        hα obs f L n ↔
      correctedConcreteWorkingGrammarExactOutputRank
          hL ≤
        n := by

  constructor

  · intro hn
    exact
      hL.rank_le_of_exactOutputAtBudget
        hn

  · intro hrank

    exact
      correctedConcreteWorkingGrammarExactOutputAtBudget_mono
        hrank
        hL.rank_spec

/-- No smaller budget can produce the target exactly. -/
theorem not_exactOutputAtBudget_of_lt_rank
    (hL :
      HasCorrectedConcreteWorkingGrammarExactOutputBudget
        hα obs f L)
    {n : Nat}
    (hn :
      n <
        correctedConcreteWorkingGrammarExactOutputRank
          hL) :
    ¬
      CorrectedConcreteWorkingGrammarExactOutputAtBudget
        hα obs f L n := by

  intro hexact

  have hle :=
    hL.rank_le_of_exactOutputAtBudget
      hexact

  omega

/-- Proof irrelevance for the exact-output rank. -/
theorem rank_proof_irrel
    (h₁ h₂ :
      HasCorrectedConcreteWorkingGrammarExactOutputBudget
        hα obs f L) :
    correctedConcreteWorkingGrammarExactOutputRank
        h₁ =
      correctedConcreteWorkingGrammarExactOutputRank
        h₂ := by

  have hp :
      h₁ = h₂ :=
    Subsingleton.elim _ _

  subst h₂

  rfl

/-- The rank is witnessed by an actual finite positive sample. -/
theorem exists_sample_at_rank
    (hL :
      HasCorrectedConcreteWorkingGrammarExactOutputBudget
        hα obs f L) :
    ∃ K : Finset (Word α),
      (K : Set (Word α)) ⊆ L ∧
      sampleLengthBudget K ≤
        correctedConcreteWorkingGrammarExactOutputRank
          hL ∧
      (correctedConcreteWorkingGrammarLearner
        hα obs f K).grammar.StringLanguage =
          L := by

  exact hL.rank_spec

end HasCorrectedConcreteWorkingGrammarExactOutputBudget

end ExactOutputBudget


section CharacteristicSampleExactOutputRank

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]
variable [DecidableEq α]

/-- A characteristic sample gives an exact learner output at the budget equal
to its own total length. -/
theorem correctedConcreteWorkingGrammarExactOutputAtBudget_of_characteristicSample
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
    CorrectedConcreteWorkingGrammarExactOutputAtBudget
      hα obs f L
      (sampleLengthBudget S) := by

  exact
    ⟨S,
      hS.1,
      Nat.le_refl _,
      hS.2 S Set.Subset.rfl hS.1⟩

/-- Therefore every characteristic sample establishes existence of a finite
exact-output rank. -/
theorem hasExactOutputBudget_of_characteristicSample
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
    HasCorrectedConcreteWorkingGrammarExactOutputBudget
      hα obs f L := by

  exact
    ⟨sampleLengthBudget S,
      correctedConcreteWorkingGrammarExactOutputAtBudget_of_characteristicSample
        hα obs f S L hS⟩

/-- The least exact-output rank is bounded by the total length of every
characteristic sample. -/
theorem exactOutputRank_le_characteristicSampleLength
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
    correctedConcreteWorkingGrammarExactOutputRank
        (hasExactOutputBudget_of_characteristicSample
          hα obs f S L hS) ≤
      sampleLengthBudget S := by

  exact
    (hasExactOutputBudget_of_characteristicSample
      hα obs f S L hS).rank_le_of_exactOutputAtBudget
        (correctedConcreteWorkingGrammarExactOutputAtBudget_of_characteristicSample
          hα obs f S L hS)

end CharacteristicSampleExactOutputRank


section ExactOutputImpliesBoundedRepresentation

variable {α : Type u}
variable {M : Type v}
variable [Monoid M]

/-- An exact learner output at budget `n` yields a bounded actual grammar
representation at the same budget. -/
theorem boundedRepresentation_of_exactOutputAtBudget
    {hα : Nonempty α}
    {obs : α → M}
    {f : Nat}
    {L : Set (Word α)}
    {n : Nat}
    (h :
      CorrectedConcreteWorkingGrammarExactOutputAtBudget
        hα obs f L n) :
    L ∈
      BoundedCutCompiledWorkingGrammarLanguageClass
        (w := max u v) α f n := by

  rcases h with
    ⟨K, hpositive, hlength, hexact⟩

  let R :=
    correctedConcreteWorkingGrammarLearner_boundedRepresentation
      hα obs f K

  have hRK :
      CorrectedConcreteCanonicalLearnerLanguage
          K obs f ∈
        BoundedCutCompiledWorkingGrammarLanguageClass
          (w := max u v)
          α f
          (sampleLengthBudget K) :=
    correctedConcreteCanonicalLearnerLanguage_mem_boundedCutCompiledClass
      hα obs f K

  have hlanguage :
      CorrectedConcreteCanonicalLearnerLanguage
          K obs f =
        L := by

    rw [
      ← correctedConcreteWorkingGrammarLearner_stringLanguage_eq_corrected
        hα obs f K
    ]

    exact hexact

  rw [hlanguage] at hRK

  exact
    boundedCutCompiledWorkingGrammarLanguageClass_mono
      (w := max u v)
      hlength
      hRK

/-- Every finite exact-output language is boundedly representable. -/
theorem hasBoundedRepresentation_of_hasExactOutputBudget
    {hα : Nonempty α}
    {obs : α → M}
    {f : Nat}
    {L : Set (Word α)}
    (hL :
      HasCorrectedConcreteWorkingGrammarExactOutputBudget
        hα obs f L) :
    HasBoundedCutCompiledWorkingGrammarRepresentation
      (w := max u v) α f L := by

  rcases hL with ⟨n, hn⟩

  exact
    ⟨n,
      boundedRepresentation_of_exactOutputAtBudget
        hn⟩

/-- Bounded representation rank is no larger than exact learner-output rank. -/
theorem boundedRepresentationRank_le_exactOutputRank
    {hα : Nonempty α}
    {obs : α → M}
    {f : Nat}
    {L : Set (Word α)}
    (hL :
      HasCorrectedConcreteWorkingGrammarExactOutputBudget
        hα obs f L) :
    boundedCutCompiledWorkingGrammarRepresentationRank
        (w := max u v)
        α
        (hasBoundedRepresentation_of_hasExactOutputBudget
          hL) ≤
      correctedConcreteWorkingGrammarExactOutputRank
        hL := by

  apply
    (hasBoundedRepresentation_of_hasExactOutputBudget
      hL).rank_le_of_mem

  exact
    boundedRepresentation_of_exactOutputAtBudget
      hL.rank_spec

end ExactOutputImpliesBoundedRepresentation


section StartRootedTargetRanks

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Selected characteristic sample viewed by the actual working-grammar
learner. -/
theorem selectedStartRootedCharacteristicSample_workingGrammar_characteristic
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    CharacteristicSample
      (correctedConcreteWorkingGrammarHypLanguage
        obs f)
      (correctedConcreteWorkingGrammarLearner
        hα obs f)
      (startRootedCorrectedConcreteTargetCharacteristicSample
        (v := w) obs f hL)
      L := by

  apply
    (correctedConcreteWorkingGrammar_characteristicSample_iff
      hα obs f
      (startRootedCorrectedConcreteTargetCharacteristicSample
        (v := w) obs f hL)
      L).2

  exact
    startRootedCorrectedConcreteTargetCharacteristicSample_characteristic
      (v := w) obs f hL

/-- Every semantic start-rooted target has some finite exact-output budget. -/
theorem startRootedTarget_hasExactOutputBudget
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    HasCorrectedConcreteWorkingGrammarExactOutputBudget
      hα obs f L := by

  let S :=
    startRootedCorrectedConcreteTargetCharacteristicSample
      (v := w) obs f hL

  have hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L := by

    exact
      selectedStartRootedCharacteristicSample_workingGrammar_characteristic
        (v := w) hα obs f hL

  exact
    hasExactOutputBudget_of_characteristicSample
      hα obs f S L hS

/-- Canonical exact-output rank of one semantic start-rooted target. -/
noncomputable def startRootedTargetExactOutputRank
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    Nat :=
  correctedConcreteWorkingGrammarExactOutputRank
    (startRootedTarget_hasExactOutputBudget
      (v := w) hα obs f hL)

/-- The target is exactly output at its least canonical budget. -/
theorem startRootedTarget_exactOutputAt_rank
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    CorrectedConcreteWorkingGrammarExactOutputAtBudget
      hα obs f L
      (startRootedTargetExactOutputRank
        (v := w) hα obs f hL) := by

  exact
    (startRootedTarget_hasExactOutputBudget
      (v := w) hα obs f hL).rank_spec

/-- The selected characteristic sample bounds the target's exact-output rank. -/
theorem startRootedTargetExactOutputRank_le_selectedCharacteristicSampleLength
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    startRootedTargetExactOutputRank
        (v := w) hα obs f hL ≤
      sampleLengthBudget
        (startRootedCorrectedConcreteTargetCharacteristicSample
          (v := w) obs f hL) := by

  let S :=
    startRootedCorrectedConcreteTargetCharacteristicSample
      (v := w) obs f hL

  have hS :
      CharacteristicSample
        (correctedConcreteWorkingGrammarHypLanguage
          obs f)
        (correctedConcreteWorkingGrammarLearner
          hα obs f)
        S L :=
    selectedStartRootedCharacteristicSample_workingGrammar_characteristic
      (v := w) hα obs f hL

  unfold
    startRootedTargetExactOutputRank

  exact
    (startRootedTarget_hasExactOutputBudget
      (v := w) hα obs f hL).rank_le_of_exactOutputAtBudget
        (correctedConcreteWorkingGrammarExactOutputAtBudget_of_characteristicSample
          hα obs f S L hS)

/-- Every finite positive exact-output sample gives an upper bound on the
target's exact-output rank. -/
theorem startRootedTargetExactOutputRank_le_sampleLength_of_exactOutput
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f)
    (K : Finset (Word α))
    (hKpositive :
      (K : Set (Word α)) ⊆ L)
    (hKexact :
      (correctedConcreteWorkingGrammarLearner
        hα obs f K).grammar.StringLanguage =
          L) :
    startRootedTargetExactOutputRank
        (v := w) hα obs f hL ≤
      sampleLengthBudget K := by

  unfold
    startRootedTargetExactOutputRank

  apply
    (startRootedTarget_hasExactOutputBudget
      (v := w) hα obs f hL).rank_le_of_exactOutputAtBudget

  exact
    ⟨K,
      hKpositive,
      Nat.le_refl _,
      hKexact⟩

/-- Every target's bounded representation rank is at most its exact-output
rank. -/
theorem startRootedTarget_boundedRepresentationRank_le_exactOutputRank
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f) :
    boundedCutCompiledWorkingGrammarRepresentationRank
        (w := max u v)
        α
        (hasBoundedRepresentation_of_hasExactOutputBudget
          (startRootedTarget_hasExactOutputBudget
            (v := w) hα obs f hL)) ≤
      startRootedTargetExactOutputRank
        (v := w) hα obs f hL := by

  exact
    boundedRepresentationRank_le_exactOutputRank
      (startRootedTarget_hasExactOutputBudget
        (v := w) hα obs f hL)

end StartRootedTargetRanks


section RankPackages

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]
variable [Monoid M]
variable (hα : Nonempty α)
variable (obs : α → M)
variable (f : Nat)

/-- Paper-facing minimal-rank package for every semantic start-rooted target. -/
theorem correctedConcreteWorkingGrammarLearner_targetRank_package :
    ∀ L : Set (Word α),
      ∀ hL :
        L ∈ StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f,
      CorrectedConcreteWorkingGrammarExactOutputAtBudget
        hα obs f L
        (startRootedTargetExactOutputRank
          (v := w) hα obs f hL) ∧
      startRootedTargetExactOutputRank
          (v := w) hα obs f hL ≤
        sampleLengthBudget
          (startRootedCorrectedConcreteTargetCharacteristicSample
            (v := w) obs f hL) := by

  intro L hL

  exact
    ⟨startRootedTarget_exactOutputAt_rank
        (v := w) hα obs f hL,
      startRootedTargetExactOutputRank_le_selectedCharacteristicSampleLength
        (v := w) hα obs f hL⟩

/-- Expanded hierarchy-and-rank endpoint. -/
theorem correctedConcreteWorkingGrammarLearner_representationRank_package :
    (∀ L : Set (Word α),
      L ∈ StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f →
      HasCorrectedConcreteWorkingGrammarExactOutputBudget
        hα obs f L) ∧
    (∀ L : Set (Word α),
      ∀ hL :
        L ∈ StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f,
      CorrectedConcreteWorkingGrammarExactOutputAtBudget
        hα obs f L
        (startRootedTargetExactOutputRank
          (v := w) hα obs f hL)) ∧
    (∀ L : Set (Word α),
      ∀ hL :
        L ∈ StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f,
      boundedCutCompiledWorkingGrammarRepresentationRank
          (w := max u v)
          α
          (hasBoundedRepresentation_of_hasExactOutputBudget
            (startRootedTarget_hasExactOutputBudget
              (v := w) hα obs f hL)) ≤
        startRootedTargetExactOutputRank
          (v := w) hα obs f hL) ∧
    (∀ L : Set (Word α),
      ∀ hL :
        L ∈ StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f,
      startRootedTargetExactOutputRank
          (v := w) hα obs f hL ≤
        sampleLengthBudget
          (startRootedCorrectedConcreteTargetCharacteristicSample
            (v := w) obs f hL)) := by

  exact
    ⟨fun L hL =>
        startRootedTarget_hasExactOutputBudget
          (v := w) hα obs f hL,
      fun L hL =>
        startRootedTarget_exactOutputAt_rank
          (v := w) hα obs f hL,
      fun L hL =>
        startRootedTarget_boundedRepresentationRank_le_exactOutputRank
          (v := w) hα obs f hL,
      fun L hL =>
        startRootedTargetExactOutputRank_le_selectedCharacteristicSampleLength
          (v := w) hα obs f hL⟩

end RankPackages

end MCFG
