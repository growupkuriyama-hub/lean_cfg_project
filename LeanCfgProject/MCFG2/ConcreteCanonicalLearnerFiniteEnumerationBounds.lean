/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.StartRootedConcreteCanonicalLearnerClassTheorem

/-!
# ConcreteCanonicalLearnerFiniteEnumerationBounds.lean

This file gives explicit finite cardinality bounds for the naive enumerators
used by the corrected concrete canonical learner.

The bounds follow the constructions literally:

* fixed-length lists are bounded by powers of the alphabet size;
* bounded words are bounded by a finite geometric sum;
* named contexts are bounded by chunk codes times hole permutations;
* tuple occurrences are bounded by context codes times tuple codes;
* unit rules are bounded by pairs of tuple occurrences;
* exact binary templates are bounded by finite template-word codes;
* corrected binary witnesses are bounded by three occurrence sets times the
  exact-template set;
* rule counts up to fan-out `f` are bounded by finite sums of these quantities.

These are deliberately coarse bounds for the current exhaustive enumerator.
They are not claimed to be polynomial-time bounds.

No target grammar occurs in any enumeration bound.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section GenericFinsetBounds

/-- The cardinality of a finite bi-union is at most the sum of the
cardinalities of its fibers. -/
theorem finset_card_biUnion_le_sum_card
    {ι : Type u}
    {β : Type v}
    (s : Finset ι)
    (t : ι → Finset β) :
    (s.biUnion t).card ≤
      ∑ i in s, (t i).card := by
  classical
  induction s using Finset.induction_on with

  | empty =>
      simp

  | @insert a s ha ih =>
      calc
        ((insert a s).biUnion t).card =
            (t a ∪ s.biUnion t).card := by
          simp [ha]
        _ ≤ (t a).card + (s.biUnion t).card :=
          Finset.card_union_le _ _
        _ ≤ (t a).card +
              ∑ i in s, (t i).card :=
          Nat.add_le_add_left ih _
        _ = ∑ i in insert a s, (t i).card := by
          simp [ha]

end GenericFinsetBounds


section NumericalBounds

/-- Cardinality bound for all words of length at most `bound` over an alphabet
of size `alphabetSize`. -/
def finiteWordEnumerationBound
    (alphabetSize bound : Nat) :
    Nat :=
  ∑ n in Finset.range (bound + 1),
    alphabetSize ^ n

/-- Cardinality bound for well-formed named contexts of arity `d`.

The first factor bounds the `d + 1` chunk words.  The second factor bounds the
length-`d` hole-name list over `Fin d`. -/
def namedContextEnumerationBound
    (alphabetSize bound d : Nat) :
    Nat :=
  (finiteWordEnumerationBound
      alphabetSize bound) ^ (d + 1) *
    d ^ d

/-- Cardinality bound for arity-`d` tuple occurrences. -/
def tupleOccurrenceEnumerationBound
    (alphabetSize bound d : Nat) :
    Nat :=
  namedContextEnumerationBound
      alphabetSize bound d *
    (finiteWordEnumerationBound
      alphabetSize bound) ^ d

/-- Cardinality bound for unit rules of arity `d`. -/
def unitRuleEnumerationBound
    (alphabetSize bound d : Nat) :
    Nat :=
  tupleOccurrenceEnumerationBound
      alphabetSize bound d *
    tupleOccurrenceEnumerationBound
      alphabetSize bound d

/-- Upper bound on the finite template-atom alphabet. -/
def templateAtomEnumerationBound
    (alphabetSize dB dC : Nat) :
    Nat :=
  alphabetSize + dB + dC

/-- Cardinality bound for exact template tuples of output arity `e`. -/
def exactTemplateTupleEnumerationBound
    (alphabetSize bound e dB dC : Nat) :
    Nat :=
  (finiteWordEnumerationBound
      (templateAtomEnumerationBound
        alphabetSize dB dC)
      bound) ^ e

/-- Cardinality bound for corrected exact-once binary witnesses. -/
def correctedBinaryWitnessEnumerationBound
    (alphabetSize bound e dB dC : Nat) :
    Nat :=
  tupleOccurrenceEnumerationBound
      alphabetSize bound e *
    tupleOccurrenceEnumerationBound
      alphabetSize bound dB *
    tupleOccurrenceEnumerationBound
      alphabetSize bound dC *
    exactTemplateTupleEnumerationBound
      alphabetSize bound e dB dC

end NumericalBounds


section FixedLengthListBounds

variable {β : Type u}

/-- Fixed-length list enumeration is bounded by the corresponding power of the
finite alphabet size. -/
theorem card_finiteListsOver_le
    (A : Finset β) :
    ∀ n : Nat,
      (finiteListsOver A n).card ≤
        A.card ^ n := by
  intro n
  induction n with

  | zero =>
      simp [finiteListsOver]

  | succ n ih =>
      classical
      calc
        (finiteListsOver A (n + 1)).card ≤
            (A.product
              (finiteListsOver A n)).card := by
          unfold finiteListsOver
          exact Finset.card_image_le
        _ =
            A.card *
              (finiteListsOver A n).card := by
          simp
        _ ≤
            A.card * (A.card ^ n) :=
          Nat.mul_le_mul_left A.card ih
        _ = A.card ^ (n + 1) := by
          simp [pow_succ, Nat.mul_comm]

end FixedLengthListBounds


section FiniteWordBounds

variable {α : Type u}

/-- Exact-length word enumeration has at most `|A|^n` members. -/
theorem card_finiteWordsOfLength_le
    (A : Finset α)
    (n : Nat) :
    (finiteWordsOfLength A n).card ≤
      A.card ^ n := by
  classical
  calc
    (finiteWordsOfLength A n).card ≤
        (finiteListsOver A n).card := by
      unfold finiteWordsOfLength
      exact Finset.card_image_le
    _ ≤ A.card ^ n :=
      card_finiteListsOver_le A n

/-- Bounded-word enumeration is bounded by the finite geometric sum recorded in
`finiteWordEnumerationBound`. -/
theorem card_finiteWordsUpTo_le
    (A : Finset α)
    (bound : Nat) :
    (finiteWordsUpTo A bound).card ≤
      finiteWordEnumerationBound
        A.card bound := by
  classical
  unfold finiteWordsUpTo
  unfold finiteWordEnumerationBound
  calc
    ((Finset.range (bound + 1)).biUnion
        (fun n => finiteWordsOfLength A n)).card ≤
        ∑ n in Finset.range (bound + 1),
          (finiteWordsOfLength A n).card :=
      finset_card_biUnion_le_sum_card
        (Finset.range (bound + 1))
        (fun n => finiteWordsOfLength A n)
    _ ≤
        ∑ n in Finset.range (bound + 1),
          A.card ^ n := by
      apply Finset.sum_le_sum
      intro n hn
      exact card_finiteWordsOfLength_le A n

/-- The default sample-bounded word set has the corresponding explicit finite
bound. -/
theorem card_sampleBoundedWords_le
    (K : Finset (Word α)) :
    (sampleBoundedWords K).card ≤
      finiteWordEnumerationBound
        (sampleAlphabet K).card
        (sampleLengthBudget K) :=
  card_finiteWordsUpTo_le
    (sampleAlphabet K)
    (sampleLengthBudget K)

end FiniteWordBounds


section ContextBounds

variable {α : Type u}

/-- Raw named-context candidates are bounded by chunk-list codes times
hole-list codes. -/
theorem card_rawNamedContextCandidates_le
    (A : Finset α)
    (bound d : Nat) :
    (rawNamedContextCandidates
        A bound d).card ≤
      namedContextEnumerationBound
        A.card bound d := by
  classical
  let W :=
    finiteWordsUpTo A bound

  have himage :
      (rawNamedContextCandidates
          A bound d).card ≤
        ((finiteListsOver W (d + 1)).product
          (finiteListsOver
            (Finset.univ : Finset (Fin d)) d)).card := by
    unfold rawNamedContextCandidates
    dsimp
    exact Finset.card_image_le

  have hchunks :
      (finiteListsOver W (d + 1)).card ≤
        W.card ^ (d + 1) :=
    card_finiteListsOver_le W (d + 1)

  have hholes :
      (finiteListsOver
        (Finset.univ : Finset (Fin d)) d).card ≤
          d ^ d := by
    simpa using
      card_finiteListsOver_le
        (Finset.univ : Finset (Fin d)) d

  calc
    (rawNamedContextCandidates
        A bound d).card ≤
        ((finiteListsOver W (d + 1)).product
          (finiteListsOver
            (Finset.univ : Finset (Fin d)) d)).card :=
      himage
    _ =
        (finiteListsOver W (d + 1)).card *
          (finiteListsOver
            (Finset.univ : Finset (Fin d)) d).card := by
      simp
    _ ≤
        W.card ^ (d + 1) *
          d ^ d :=
      Nat.mul_le_mul hchunks hholes
    _ ≤
        (finiteWordEnumerationBound
            A.card bound) ^ (d + 1) *
          d ^ d := by
      apply Nat.mul_le_mul_right
      exact Nat.pow_le_pow_left
        (card_finiteWordsUpTo_le A bound)
        (d + 1)
    _ =
        namedContextEnumerationBound
          A.card bound d := by
      rfl

/-- Filtering for well-formed contexts and repackaging with proof fields cannot
increase cardinality. -/
theorem card_namedContextCandidates_le_raw
    (A : Finset α)
    (bound d : Nat) :
    (namedContextCandidates A bound d).card ≤
      (rawNamedContextCandidates A bound d).card := by
  classical
  unfold namedContextCandidates
  dsimp
  calc
    (((rawNamedContextCandidates A bound d).filter
        RawNamedSentenceContext.WellFormed).attach.image
      (fun c =>
        ⟨c.1,
          (Finset.mem_filter.mp c.2).2⟩)).card ≤
        ((rawNamedContextCandidates A bound d).filter
          RawNamedSentenceContext.WellFormed).attach.card :=
      Finset.card_image_le
    _ =
        ((rawNamedContextCandidates A bound d).filter
          RawNamedSentenceContext.WellFormed).card := by
      simp
    _ ≤
        (rawNamedContextCandidates A bound d).card :=
      Finset.card_le_card
        (Finset.filter_subset _ _)

/-- Explicit cardinality bound for well-formed named-context candidates. -/
theorem card_namedContextCandidates_le
    (A : Finset α)
    (bound d : Nat) :
    (namedContextCandidates A bound d).card ≤
      namedContextEnumerationBound
        A.card bound d :=
  (card_namedContextCandidates_le_raw
    A bound d).trans
      (card_rawNamedContextCandidates_le
        A bound d)

end ContextBounds


section TupleOccurrenceBounds

variable {α : Type u}

/-- Tuple-code enumeration is bounded by a power of the component-word set
size. -/
theorem card_finiteTupleCodes_le
    (W : Finset (Word α))
    (d : Nat) :
    (finiteTupleCodes W d).card ≤
      W.card ^ d :=
  card_finiteListsOver_le W d

/-- Before filtering by sample membership, tuple-occurrence candidates are
bounded by context codes times tuple codes. -/
theorem card_tupleOccurrenceCandidatesUpTo_le
    (K : Finset (Word α))
    (d bound : Nat) :
    (tupleOccurrenceCandidatesUpTo
        K d bound).card ≤
      tupleOccurrenceEnumerationBound
        (sampleAlphabet K).card
        bound d := by
  classical
  let A :=
    sampleAlphabet K
  let W :=
    finiteWordsUpTo A bound

  have himage :
      (tupleOccurrenceCandidatesUpTo
          K d bound).card ≤
        ((namedContextCandidates A bound d).product
          (finiteTupleCodes W d)).card := by
    unfold tupleOccurrenceCandidatesUpTo
    dsimp
    exact Finset.card_image_le

  have hcontexts :
      (namedContextCandidates A bound d).card ≤
        namedContextEnumerationBound
          A.card bound d :=
    card_namedContextCandidates_le
      A bound d

  have htuples :
      (finiteTupleCodes W d).card ≤
        (finiteWordEnumerationBound
          A.card bound) ^ d := by
    calc
      (finiteTupleCodes W d).card ≤
          W.card ^ d :=
        card_finiteTupleCodes_le W d
      _ ≤
          (finiteWordEnumerationBound
            A.card bound) ^ d :=
        Nat.pow_le_pow_left
          (card_finiteWordsUpTo_le A bound)
          d

  calc
    (tupleOccurrenceCandidatesUpTo
        K d bound).card ≤
        ((namedContextCandidates A bound d).product
          (finiteTupleCodes W d)).card :=
      himage
    _ =
        (namedContextCandidates A bound d).card *
          (finiteTupleCodes W d).card := by
      simp
    _ ≤
        namedContextEnumerationBound
            A.card bound d *
          (finiteWordEnumerationBound
            A.card bound) ^ d :=
      Nat.mul_le_mul hcontexts htuples
    _ =
        tupleOccurrenceEnumerationBound
          A.card bound d := by
      rfl

/-- Filtering occurrence candidates by membership in the sample cannot
increase cardinality. -/
theorem card_tupleOccurrencesUpTo_le_candidates
    (K : Finset (Word α))
    (d bound : Nat) :
    (tupleOccurrencesUpTo K d bound).card ≤
      (tupleOccurrenceCandidatesUpTo
        K d bound).card := by
  classical
  unfold tupleOccurrencesUpTo
  exact Finset.card_le_card
    (Finset.filter_subset _ _)

/-- Explicit bounded-occurrence cardinality estimate. -/
theorem card_tupleOccurrencesUpTo_le
    (K : Finset (Word α))
    (d bound : Nat) :
    (tupleOccurrencesUpTo K d bound).card ≤
      tupleOccurrenceEnumerationBound
        (sampleAlphabet K).card
        bound d :=
  (card_tupleOccurrencesUpTo_le_candidates
    K d bound).trans
      (card_tupleOccurrenceCandidatesUpTo_le
        K d bound)

/-- Default occurrence cardinality estimate. -/
theorem card_tupleOccurrences_le
    (K : Finset (Word α))
    (d : Nat) :
    (tupleOccurrences K d).card ≤
      tupleOccurrenceEnumerationBound
        (sampleAlphabet K).card
        (sampleLengthBudget K)
        d :=
  card_tupleOccurrencesUpTo_le
    K d (sampleLengthBudget K)

end TupleOccurrenceBounds


section UnitRuleBounds

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Unit-rule filtering cannot exceed the square of the occurrence count. -/
theorem card_concreteUnitRulesUpTo_le_occurrences
    (K : Finset (Word α))
    (obs : α → M)
    (d bound : Nat) :
    (concreteUnitRulesUpTo
        K obs d bound).card ≤
      (tupleOccurrencesUpTo
        K d bound).card *
      (tupleOccurrencesUpTo
        K d bound).card := by
  classical
  unfold concreteUnitRulesUpTo
  dsimp
  calc
    (((tupleOccurrencesUpTo K d bound).product
        (tupleOccurrencesUpTo K d bound)).filter
      (fun p =>
        p.1.context = p.2.context ∧
          tupleType obs p.1.tuple =
            tupleType obs p.2.tuple)).card ≤
        ((tupleOccurrencesUpTo K d bound).product
          (tupleOccurrencesUpTo K d bound)).card :=
      Finset.card_le_card
        (Finset.filter_subset _ _)
    _ =
        (tupleOccurrencesUpTo K d bound).card *
          (tupleOccurrencesUpTo K d bound).card := by
      simp

/-- Explicit bounded unit-rule cardinality estimate. -/
theorem card_concreteUnitRulesUpTo_le
    (K : Finset (Word α))
    (obs : α → M)
    (d bound : Nat) :
    (concreteUnitRulesUpTo
        K obs d bound).card ≤
      unitRuleEnumerationBound
        (sampleAlphabet K).card
        bound d := by
  have hocc :=
    card_tupleOccurrencesUpTo_le
      K d bound
  exact
    (card_concreteUnitRulesUpTo_le_occurrences
      K obs d bound).trans
      (Nat.mul_le_mul hocc hocc)

/-- Default unit-rule cardinality estimate. -/
theorem card_concreteUnitRules_le
    (K : Finset (Word α))
    (obs : α → M)
    (d : Nat) :
    (concreteUnitRules K obs d).card ≤
      unitRuleEnumerationBound
        (sampleAlphabet K).card
        (sampleLengthBudget K)
        d :=
  card_concreteUnitRulesUpTo_le
    K obs d (sampleLengthBudget K)

end UnitRuleBounds


section TemplateBounds

variable {α : Type u}

/-- The finite template-atom alphabet is bounded by terminals plus left and
right variable names. -/
theorem card_finiteTemplateAtoms_le
    (A : Finset α)
    (dB dC : Nat) :
    (finiteTemplateAtoms A dB dC).card ≤
      templateAtomEnumerationBound
        A.card dB dC := by
  classical

  let terminals : Finset (TemplateAtom α dB dC) :=
    A.image (fun a => TemplateAtom.terminal a)

  let leftVariables : Finset (TemplateAtom α dB dC) :=
    (Finset.univ : Finset (Fin dB)).image
      (fun i => TemplateAtom.leftVar i)

  let rightVariables : Finset (TemplateAtom α dB dC) :=
    (Finset.univ : Finset (Fin dC)).image
      (fun j => TemplateAtom.rightVar j)

  have hterminals :
      terminals.card ≤ A.card := by
    exact Finset.card_image_le

  have hleft :
      leftVariables.card ≤ dB := by
    simpa [leftVariables] using
      (Finset.card_image_le :
        ((Finset.univ : Finset (Fin dB)).image
          (fun i =>
            (TemplateAtom.leftVar i :
              TemplateAtom α dB dC))).card ≤
        (Finset.univ : Finset (Fin dB)).card)

  have hright :
      rightVariables.card ≤ dC := by
    simpa [rightVariables] using
      (Finset.card_image_le :
        ((Finset.univ : Finset (Fin dC)).image
          (fun j =>
            (TemplateAtom.rightVar j :
              TemplateAtom α dB dC))).card ≤
        (Finset.univ : Finset (Fin dC)).card)

  have hunion1 :
      (terminals ∪ leftVariables).card ≤
        terminals.card + leftVariables.card :=
    Finset.card_union_le _ _

  have hunion2 :
      (terminals ∪ leftVariables ∪
        rightVariables).card ≤
        (terminals ∪ leftVariables).card +
          rightVariables.card :=
    Finset.card_union_le _ _

  unfold finiteTemplateAtoms
  dsimp
  unfold templateAtomEnumerationBound
  omega

/-- Template-word enumeration has the corresponding explicit bounded-word
estimate over the finite atom alphabet. -/
theorem card_finiteTemplateWordsUpTo_le
    (A : Finset α)
    (dB dC bound : Nat) :
    (finiteTemplateWordsUpTo
        A dB dC bound).card ≤
      finiteWordEnumerationBound
        (templateAtomEnumerationBound
          A.card dB dC)
        bound := by
  calc
    (finiteTemplateWordsUpTo
        A dB dC bound).card ≤
        finiteWordEnumerationBound
          (finiteTemplateAtoms
            A dB dC).card
          bound :=
      card_finiteWordsUpTo_le
        (finiteTemplateAtoms A dB dC)
        bound
    _ ≤
        finiteWordEnumerationBound
          (templateAtomEnumerationBound
            A.card dB dC)
          bound := by
      unfold finiteWordEnumerationBound
      apply Finset.sum_le_sum
      intro n hn
      exact Nat.pow_le_pow_left
        (card_finiteTemplateAtoms_le
          A dB dC)
        n

/-- Template-tuple code enumeration is bounded by a power of the template-word
bound. -/
theorem card_finiteTemplateTupleCodesUpTo_le
    (A : Finset α)
    (e dB dC bound : Nat) :
    (finiteTemplateTupleCodesUpTo
        A e dB dC bound).card ≤
      exactTemplateTupleEnumerationBound
        A.card bound e dB dC := by
  classical
  calc
    (finiteTemplateTupleCodesUpTo
        A e dB dC bound).card ≤
        (finiteListsOver
          (finiteTemplateWordsUpTo
            A dB dC bound)
          e).card := by
      unfold finiteTemplateTupleCodesUpTo
      exact Finset.card_image_le
    _ ≤
        (finiteTemplateWordsUpTo
          A dB dC bound).card ^ e :=
      card_finiteListsOver_le
        (finiteTemplateWordsUpTo
          A dB dC bound)
        e
    _ ≤
        (finiteWordEnumerationBound
          (templateAtomEnumerationBound
            A.card dB dC)
          bound) ^ e :=
      Nat.pow_le_pow_left
        (card_finiteTemplateWordsUpTo_le
          A dB dC bound)
        e
    _ =
        exactTemplateTupleEnumerationBound
          A.card bound e dB dC := by
      rfl

/-- Filtering for exact-once templates and repackaging with proof fields cannot
increase cardinality. -/
theorem card_finiteExactTemplateTupleCodesUpTo_le_tupleCodes
    (A : Finset α)
    (e dB dC bound : Nat) :
    (finiteExactTemplateTupleCodesUpTo
        A e dB dC bound).card ≤
      (finiteTemplateTupleCodesUpTo
        A e dB dC bound).card := by
  classical
  unfold finiteExactTemplateTupleCodesUpTo
  dsimp
  calc
    (((finiteTemplateTupleCodesUpTo
        A e dB dC bound).filter
        (fun C =>
          TemplateTuple.ExactlyOnce C.body)).attach.image
      (fun C =>
        { code := C.1
          exactOnce :=
            (Finset.mem_filter.mp C.2).2 })).card ≤
        ((finiteTemplateTupleCodesUpTo
          A e dB dC bound).filter
          (fun C =>
            TemplateTuple.ExactlyOnce C.body)).attach.card :=
      Finset.card_image_le
    _ =
        ((finiteTemplateTupleCodesUpTo
          A e dB dC bound).filter
          (fun C =>
            TemplateTuple.ExactlyOnce C.body)).card := by
      simp
    _ ≤
        (finiteTemplateTupleCodesUpTo
          A e dB dC bound).card :=
      Finset.card_le_card
        (Finset.filter_subset _ _)

/-- Explicit exact-template cardinality estimate. -/
theorem card_finiteExactTemplateTupleCodesUpTo_le
    (A : Finset α)
    (e dB dC bound : Nat) :
    (finiteExactTemplateTupleCodesUpTo
        A e dB dC bound).card ≤
      exactTemplateTupleEnumerationBound
        A.card bound e dB dC :=
  (card_finiteExactTemplateTupleCodesUpTo_le_tupleCodes
    A e dB dC bound).trans
      (card_finiteTemplateTupleCodesUpTo_le
        A e dB dC bound)

end TemplateBounds


section BinaryWitnessBounds

variable {α : Type u}

/-- Binary-witness candidates are bounded by three occurrence sets and one
exact-template set. -/
theorem card_binaryWitnessCandidatesUpTo_le
    (K : Finset (Word α))
    (e dB dC bound : Nat) :
    (binaryWitnessCandidatesUpTo
        K e dB dC bound).card ≤
      correctedBinaryWitnessEnumerationBound
        (sampleAlphabet K).card
        bound e dB dC := by
  classical

  let parents :=
    (tupleOccurrencesUpTo K e bound).attach

  let lefts :=
    (tupleOccurrencesUpTo K dB bound).attach

  let rights :=
    (tupleOccurrencesUpTo K dC bound).attach

  let templates :=
    finiteExactTemplateTupleCodesUpTo
      (sampleAlphabet K)
      e dB dC bound

  have himage :
      (binaryWitnessCandidatesUpTo
          K e dB dC bound).card ≤
        ((((parents.product lefts).product
          rights).product templates)).card := by
    unfold binaryWitnessCandidatesUpTo
    dsimp
    exact Finset.card_image_le

  have hp :
      parents.card ≤
        tupleOccurrenceEnumerationBound
          (sampleAlphabet K).card
          bound e := by
    simpa [parents] using
      card_tupleOccurrencesUpTo_le
        K e bound

  have hl :
      lefts.card ≤
        tupleOccurrenceEnumerationBound
          (sampleAlphabet K).card
          bound dB := by
    simpa [lefts] using
      card_tupleOccurrencesUpTo_le
        K dB bound

  have hr :
      rights.card ≤
        tupleOccurrenceEnumerationBound
          (sampleAlphabet K).card
          bound dC := by
    simpa [rights] using
      card_tupleOccurrencesUpTo_le
        K dC bound

  have ht :
      templates.card ≤
        exactTemplateTupleEnumerationBound
          (sampleAlphabet K).card
          bound e dB dC := by
    exact
      card_finiteExactTemplateTupleCodesUpTo_le
        (sampleAlphabet K)
        e dB dC bound

  calc
    (binaryWitnessCandidatesUpTo
        K e dB dC bound).card ≤
        ((((parents.product lefts).product
          rights).product templates)).card :=
      himage
    _ =
        parents.card * lefts.card *
          rights.card * templates.card := by
      simp [Nat.mul_assoc]
    _ ≤
        tupleOccurrenceEnumerationBound
              (sampleAlphabet K).card
              bound e *
          tupleOccurrenceEnumerationBound
              (sampleAlphabet K).card
              bound dB *
          tupleOccurrenceEnumerationBound
              (sampleAlphabet K).card
              bound dC *
          exactTemplateTupleEnumerationBound
              (sampleAlphabet K).card
              bound e dB dC :=
      Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul hp hl)
          hr)
        ht
    _ =
        correctedBinaryWitnessEnumerationBound
          (sampleAlphabet K).card
          bound e dB dC := by
      rfl

/-- Filtering by the parent-composition equation cannot increase binary-witness
cardinality. -/
theorem card_concreteBinaryWitnessesUpTo_le_candidates
    (K : Finset (Word α))
    (e dB dC bound : Nat) :
    (concreteBinaryWitnessesUpTo
        K e dB dC bound).card ≤
      (binaryWitnessCandidatesUpTo
        K e dB dC bound).card := by
  classical
  unfold concreteBinaryWitnessesUpTo
  exact Finset.card_le_card
    (Finset.filter_subset _ _)

/-- Explicit bounded binary-witness cardinality estimate. -/
theorem card_concreteBinaryWitnessesUpTo_le
    (K : Finset (Word α))
    (e dB dC bound : Nat) :
    (concreteBinaryWitnessesUpTo
        K e dB dC bound).card ≤
      correctedBinaryWitnessEnumerationBound
        (sampleAlphabet K).card
        bound e dB dC :=
  (card_concreteBinaryWitnessesUpTo_le_candidates
    K e dB dC bound).trans
      (card_binaryWitnessCandidatesUpTo_le
        K e dB dC bound)

/-- Corrected default binary-witness cardinality estimate. -/
theorem card_correctedConcreteBinaryWitnesses_le
    (K : Finset (Word α))
    (e dB dC : Nat) :
    (correctedConcreteBinaryWitnesses
        K e dB dC).card ≤
      correctedBinaryWitnessEnumerationBound
        (sampleAlphabet K).card
        (exactBinaryWitnessBudget K dB dC)
        e dB dC :=
  card_concreteBinaryWitnessesUpTo_le
    K e dB dC
    (exactBinaryWitnessBudget K dB dC)

end BinaryWitnessBounds


section FanoutRuleCountBounds

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Number of enumerated positive-arity unit rules considered up to fan-out
`f`.  The index `k` represents arity `k + 1`. -/
noncomputable def concreteUnitRuleCountUpToFanout
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    Nat :=
  ∑ k in Finset.range f,
    (concreteUnitRules K obs (k + 1)).card

/-- Explicit numerical bound for the total unit-rule count up to fan-out `f`. -/
def concreteUnitRuleCountBound
    (K : Finset (Word α))
    (f : Nat) :
    Nat :=
  ∑ k in Finset.range f,
    unitRuleEnumerationBound
      (sampleAlphabet K).card
      (sampleLengthBudget K)
      (k + 1)

/-- Total number of corrected binary witnesses over all positive arities at
most `f`. -/
noncomputable def correctedBinaryRuleCountUpToFanout
    (K : Finset (Word α))
    (f : Nat) :
    Nat :=
  ∑ e0 in Finset.range f,
    ∑ dB0 in Finset.range f,
      ∑ dC0 in Finset.range f,
        (correctedConcreteBinaryWitnesses
          K (e0 + 1) (dB0 + 1) (dC0 + 1)).card

/-- Explicit numerical bound for the total corrected binary-rule count up to
fan-out `f`. -/
def correctedBinaryRuleCountBound
    (K : Finset (Word α))
    (f : Nat) :
    Nat :=
  ∑ e0 in Finset.range f,
    ∑ dB0 in Finset.range f,
      ∑ dC0 in Finset.range f,
        correctedBinaryWitnessEnumerationBound
          (sampleAlphabet K).card
          (exactBinaryWitnessBudget
            K (dB0 + 1) (dC0 + 1))
          (e0 + 1) (dB0 + 1) (dC0 + 1)

/-- The total enumerated rule count is the sum of unit and corrected binary
rule counts. -/
noncomputable def correctedConcreteRuleCountUpToFanout
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    Nat :=
  concreteUnitRuleCountUpToFanout K obs f +
    correctedBinaryRuleCountUpToFanout K f

/-- Explicit total rule-count bound. -/
def correctedConcreteRuleCountBound
    (K : Finset (Word α))
    (f : Nat) :
    Nat :=
  concreteUnitRuleCountBound K f +
    correctedBinaryRuleCountBound K f

/-- Summed unit-rule cardinality bound up to fan-out `f`. -/
theorem concreteUnitRuleCountUpToFanout_le
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    concreteUnitRuleCountUpToFanout K obs f ≤
      concreteUnitRuleCountBound K f := by
  unfold concreteUnitRuleCountUpToFanout
  unfold concreteUnitRuleCountBound
  apply Finset.sum_le_sum
  intro k hk
  exact card_concreteUnitRules_le
    K obs (k + 1)

/-- Summed corrected binary-rule cardinality bound up to fan-out `f`. -/
theorem correctedBinaryRuleCountUpToFanout_le
    (K : Finset (Word α))
    (f : Nat) :
    correctedBinaryRuleCountUpToFanout K f ≤
      correctedBinaryRuleCountBound K f := by
  unfold correctedBinaryRuleCountUpToFanout
  unfold correctedBinaryRuleCountBound
  apply Finset.sum_le_sum
  intro e0 he0
  apply Finset.sum_le_sum
  intro dB0 hdB0
  apply Finset.sum_le_sum
  intro dC0 hdC0
  exact
    card_correctedConcreteBinaryWitnesses_le
      K (e0 + 1) (dB0 + 1) (dC0 + 1)

/-- Final explicit finite rule-count estimate for the corrected concrete
canonical learner. -/
theorem correctedConcreteRuleCountUpToFanout_le
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    correctedConcreteRuleCountUpToFanout
        K obs f ≤
      correctedConcreteRuleCountBound
        K f := by
  unfold correctedConcreteRuleCountUpToFanout
  unfold correctedConcreteRuleCountBound
  exact Nat.add_le_add
    (concreteUnitRuleCountUpToFanout_le
      K obs f)
    (correctedBinaryRuleCountUpToFanout_le
      K f)

end FanoutRuleCountBounds

end MCFG
