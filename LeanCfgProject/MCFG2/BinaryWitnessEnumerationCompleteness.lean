/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.NamedFillEnumerationBounds

/-!
# BinaryWitnessEnumerationCompleteness.lean

The original default binary-witness enumeration used
`sampleLengthBudget K` as both the occurrence-word bound and the template-word
bound.  That is sufficient for soundness but not for completeness: an
exact-once template contains `dB + dC` variable atoms, and those atoms may
evaluate to empty words.

This file introduces the corrected finite bound

```lean
sampleLengthBudget K + dB + dC
```

and proves completeness for exact-once sample binary evidence.

The proof is concrete:

* count the variable atoms of a template word;
* show that an exact-once body contributes at most `dB + dC` variable atoms to
  each output component;
* show that every terminal atom of a witnessed body occurs in the parent sample
  word and therefore belongs to `sampleAlphabet K`;
* construct a finite code of the actual template tuple;
* construct the parent, left-child, and right-child tuple occurrences from the
  sample binary evidence and its filling identities;
* assemble an actual member of the corrected finite binary-witness set.

The resulting `correctedConcreteBinaryRuleOfEvidence` uses classical choice
only after finite membership existence has been proved.

The theorem is intentionally stated for exact-once bodies.  Arbitrary
`SampleBinaryEvidence` in the broad reachable relation need not carry a
syntactic exact-once certificate.  The concrete paper learner will therefore
use the exact-once reachable fragment constructed from grammar rules.
-/

namespace MCFG

universe u

section CorrectedBinaryBound

variable {α : Type u}

/-- Correct finite bound for both occurrence words and exact-once template
words of a binary witness. -/
def exactBinaryWitnessBudget
    (K : Finset (Word α))
    (dB dC : Nat) :
    Nat :=
  sampleLengthBudget K + dB + dC

theorem sampleLengthBudget_le_exactBinaryWitnessBudget
    (K : Finset (Word α))
    (dB dC : Nat) :
    sampleLengthBudget K ≤
      exactBinaryWitnessBudget K dB dC := by
  unfold exactBinaryWitnessBudget
  omega

end CorrectedBinaryBound


section TemplateVariableCounting

variable {α : Type u}

/-- Number of variable atoms in one template word. -/
def templateVariableCount
    {dB dC : Nat} :
    TemplateWord α dB dC → Nat
  | [] => 0
  | TemplateAtom.terminal _ :: rest =>
      templateVariableCount rest
  | TemplateAtom.leftVar _ :: rest =>
      templateVariableCount rest + 1
  | TemplateAtom.rightVar _ :: rest =>
      templateVariableCount rest + 1

/-- A template word is no longer than its evaluated word plus the number of
variable atoms that may evaluate to empty words. -/
theorem templateWord_length_le_eval_add_variableCount
    {dB dC : Nat}
    (x : Tuple α dB)
    (y : Tuple α dC)
    (word : TemplateWord α dB dC) :
    word.length ≤
      (evalTemplateWord x y word).length +
        templateVariableCount word := by
  induction word with
  | nil =>
      simp [templateVariableCount]
  | cons atom rest ih =>
      cases atom with
      | terminal a =>
          simp [templateVariableCount,
            evalTemplateWord, evalTemplateAtom]
          omega
      | leftVar i =>
          simp [templateVariableCount,
            evalTemplateWord, evalTemplateAtom,
            List.length_append]
          omega
      | rightVar j =>
          simp [templateVariableCount,
            evalTemplateWord, evalTemplateAtom,
            List.length_append]
          omega

/-- Sum of all left-variable counts in one template word. -/
def totalLeftVarCount
    {dB dC : Nat}
    (word : TemplateWord α dB dC) :
    Nat :=
  ∑ i : Fin dB, leftVarCount i word

/-- Sum of all right-variable counts in one template word. -/
def totalRightVarCount
    {dB dC : Nat}
    (word : TemplateWord α dB dC) :
    Nat :=
  ∑ j : Fin dC, rightVarCount j word

/-- A left-variable head contributes exactly one to the total left-variable
count. -/
theorem totalLeftVarCount_leftVar_cons
    {dB dC : Nat}
    (k : Fin dB)
    (rest : TemplateWord α dB dC) :
    totalLeftVarCount
        (TemplateAtom.leftVar k :: rest) =
      totalLeftVarCount rest + 1 := by
  classical
  unfold totalLeftVarCount
  calc
    (∑ i : Fin dB,
        leftVarCount i
          (TemplateAtom.leftVar k :: rest)) =
        ∑ i : Fin dB,
          (leftVarCount i rest +
            if k = i then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hki : k = i
      · simp [leftVarCount, hki]
      · simp [leftVarCount, hki]
    _ =
        (∑ i : Fin dB, leftVarCount i rest) +
          ∑ i : Fin dB, if k = i then 1 else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin dB, leftVarCount i rest) + 1 := by
      simp
    _ = totalLeftVarCount rest + 1 := by
      rfl

/-- A right-variable head contributes exactly one to the total right-variable
count. -/
theorem totalRightVarCount_rightVar_cons
    {dB dC : Nat}
    (k : Fin dC)
    (rest : TemplateWord α dB dC) :
    totalRightVarCount
        (TemplateAtom.rightVar k :: rest) =
      totalRightVarCount rest + 1 := by
  classical
  unfold totalRightVarCount
  calc
    (∑ j : Fin dC,
        rightVarCount j
          (TemplateAtom.rightVar k :: rest)) =
        ∑ j : Fin dC,
          (rightVarCount j rest +
            if k = j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hkj : k = j
      · simp [rightVarCount, hkj]
      · simp [rightVarCount, hkj]
    _ =
        (∑ j : Fin dC, rightVarCount j rest) +
          ∑ j : Fin dC, if k = j then 1 else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ j : Fin dC, rightVarCount j rest) + 1 := by
      simp
    _ = totalRightVarCount rest + 1 := by
      rfl

/-- Variable-atom count is the sum of the existing left and right occurrence
counts. -/
theorem templateVariableCount_eq_totalCounts
    {dB dC : Nat}
    (word : TemplateWord α dB dC) :
    templateVariableCount word =
      totalLeftVarCount word +
        totalRightVarCount word := by
  induction word with
  | nil =>
      simp [templateVariableCount,
        totalLeftVarCount, totalRightVarCount,
        leftVarCount, rightVarCount]
  | cons atom rest ih =>
      cases atom with
      | terminal a =>
          simpa [templateVariableCount,
            totalLeftVarCount, totalRightVarCount,
            leftVarCount, rightVarCount] using ih
      | leftVar k =>
          have hleft :=
            totalLeftVarCount_leftVar_cons
              (α := α) k rest
          have hright :
              totalRightVarCount
                  (TemplateAtom.leftVar k :: rest) =
                totalRightVarCount rest := by
            simp [totalRightVarCount,
              rightVarCount]
          rw [templateVariableCount,
            hleft, hright, ih]
          omega
      | rightVar k =>
          have hleft :
              totalLeftVarCount
                  (TemplateAtom.rightVar k :: rest) =
                totalLeftVarCount rest := by
            simp [totalLeftVarCount,
              leftVarCount]
          have hright :=
            totalRightVarCount_rightVar_cons
              (α := α) k rest
          rw [templateVariableCount,
            hleft, hright, ih]
          omega

end TemplateVariableCounting


section ExactOnceVariableBounds

variable {α : Type u}

/-- In an exact-once template tuple, one selected output component contains a
fixed left variable at most once. -/
theorem leftVarCount_le_one_of_exactOnce
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (hexact : TemplateTuple.ExactlyOnce body)
    (o : Fin e)
    (i : Fin dB) :
    leftVarCount i (body o) ≤ 1 := by
  rcases hexact.2.1 i with
    ⟨selected, hselected, hother⟩
  by_cases h : o = selected
  · subst o
    rw [hselected]
  · rw [hother o h]

/-- Right-variable analogue. -/
theorem rightVarCount_le_one_of_exactOnce
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (hexact : TemplateTuple.ExactlyOnce body)
    (o : Fin e)
    (j : Fin dC) :
    rightVarCount j (body o) ≤ 1 := by
  rcases hexact.2.2 j with
    ⟨selected, hselected, hother⟩
  by_cases h : o = selected
  · subst o
    rw [hselected]
  · rw [hother o h]

/-- At most `dB` left-variable atoms occur in one output component of an
exact-once body. -/
theorem totalLeftVarCount_le_arity_of_exactOnce
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (hexact : TemplateTuple.ExactlyOnce body)
    (o : Fin e) :
    totalLeftVarCount (body o) ≤ dB := by
  unfold totalLeftVarCount
  calc
    (∑ i : Fin dB,
        leftVarCount i (body o)) ≤
        ∑ _i : Fin dB, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      exact leftVarCount_le_one_of_exactOnce
        hexact o i
    _ = dB := by
      simp

/-- At most `dC` right-variable atoms occur in one output component of an
exact-once body. -/
theorem totalRightVarCount_le_arity_of_exactOnce
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (hexact : TemplateTuple.ExactlyOnce body)
    (o : Fin e) :
    totalRightVarCount (body o) ≤ dC := by
  unfold totalRightVarCount
  calc
    (∑ j : Fin dC,
        rightVarCount j (body o)) ≤
        ∑ _j : Fin dC, 1 := by
      apply Finset.sum_le_sum
      intro j hj
      exact rightVarCount_le_one_of_exactOnce
        hexact o j
    _ = dC := by
      simp

/-- One output component of an exact-once body has at most `dB + dC`
variable atoms. -/
theorem templateVariableCount_le_arities_of_exactOnce
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (hexact : TemplateTuple.ExactlyOnce body)
    (o : Fin e) :
    templateVariableCount (body o) ≤
      dB + dC := by
  rw [templateVariableCount_eq_totalCounts]
  exact Nat.add_le_add
    (totalLeftVarCount_le_arity_of_exactOnce
      hexact o)
    (totalRightVarCount_le_arity_of_exactOnce
      hexact o)

/-- Correct componentwise template-length bound. -/
theorem exactOnce_templateWord_length_le
    {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (hexact : TemplateTuple.ExactlyOnce body)
    (x : Tuple α dB)
    (y : Tuple α dC)
    (o : Fin e) :
    (body o).length ≤
      (evalTemplateTuple body x y o).length +
        dB + dC := by
  have hbase :=
    templateWord_length_le_eval_add_variableCount
      x y (body o)
  have hvars :=
    templateVariableCount_le_arities_of_exactOnce
      hexact o
  dsimp [evalTemplateTuple]
  omega

end ExactOnceVariableBounds


section TemplateTerminalVisibility

variable {α : Type u}

/-- Every terminal atom of a template word occurs in its evaluated word. -/
theorem mem_evalTemplateWord_of_terminal_mem
    {dB dC : Nat}
    (x : Tuple α dB)
    (y : Tuple α dC)
    {word : TemplateWord α dB dC}
    {a : α}
    (ha :
      TemplateAtom.terminal a ∈ word) :
    a ∈ evalTemplateWord x y word := by
  induction word with
  | nil =>
      simp at ha
  | cons atom rest ih =>
      rcases List.mem_cons.mp ha with
        hhead | htail
      · cases atom with
        | terminal b =>
            cases hhead
            simp [evalTemplateWord,
              evalTemplateAtom]
        | leftVar i =>
            cases hhead
        | rightVar j =>
            cases hhead
      · cases atom with
        | terminal b =>
            simp [evalTemplateWord,
              evalTemplateAtom, ih htail]
        | leftVar i =>
            simp [evalTemplateWord,
              evalTemplateAtom, ih htail]
        | rightVar j =>
            simp [evalTemplateWord,
              evalTemplateAtom, ih htail]

/-- Every terminal atom of a binary body witnessed in a sample belongs to the
finite sample alphabet. -/
theorem terminal_mem_sampleAlphabet_of_binary_parent_mem
    {K : Finset (Word α)}
    {e dB dC : Nat}
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x : Tuple α dB}
    {y : Tuple α dC}
    (hparent :
      namedFill e parent
        (evalTemplateTuple body x y) ∈ K)
    (o : Fin e)
    {a : α}
    (ha :
      TemplateAtom.terminal a ∈ body o) :
    a ∈ sampleAlphabet K := by
  apply mem_sampleAlphabet_of_mem_word
    K hparent
  apply namedFill_mem_of_mem_component
    parent
    (evalTemplateTuple body x y)
    o
  exact mem_evalTemplateWord_of_terminal_mem
    x y ha

/-- Every atom of a witnessed exact body belongs to the finite atom set used by
the enumerator. -/
theorem templateAtom_mem_finiteTemplateAtoms_of_parent_mem
    {K : Finset (Word α)}
    {e dB dC : Nat}
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x : Tuple α dB}
    {y : Tuple α dC}
    (hparent :
      namedFill e parent
        (evalTemplateTuple body x y) ∈ K)
    (o : Fin e)
    {atom : TemplateAtom α dB dC}
    (hatom : atom ∈ body o) :
    atom ∈ finiteTemplateAtoms
      (sampleAlphabet K) dB dC := by
  cases atom with
  | terminal a =>
      have ha :
          a ∈ sampleAlphabet K :=
        terminal_mem_sampleAlphabet_of_binary_parent_mem
          hparent o hatom
      simp [finiteTemplateAtoms, ha]
  | leftVar i =>
      simp [finiteTemplateAtoms]
  | rightVar j =>
      simp [finiteTemplateAtoms]

end TemplateTerminalVisibility


section ExactTemplateEnumerationCompleteness

variable {α : Type u}

/-- Canonical finite code of an actual template tuple. -/
noncomputable def templateTupleCodeOf
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) :
    FiniteTemplateTupleCode α e dB dC where
  outputs :=
    { entries := List.ofFn body
      length_eq := by simp }

@[simp] theorem templateTupleCodeOf_body
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) :
    (templateTupleCodeOf body).body = body := by
  funext o
  simp [templateTupleCodeOf,
    FiniteTemplateTupleCode.body,
    FiniteListCode.toFunction]

/-- The canonical body code is enumerated whenever every component template
word satisfies the finite atom and length bounds. -/
theorem templateTupleCodeOf_mem
    (A : Finset α)
    {e dB dC bound : Nat}
    (body : TemplateTuple α e dB dC)
    (hlength :
      ∀ o : Fin e,
        (body o).length ≤ bound)
    (hatoms :
      ∀ o : Fin e,
        ∀ atom ∈ body o,
          atom ∈ finiteTemplateAtoms A dB dC) :
    templateTupleCodeOf body ∈
      finiteTemplateTupleCodesUpTo
        A e dB dC bound := by
  classical
  unfold finiteTemplateTupleCodesUpTo
  apply Finset.mem_image.mpr
  refine
    ⟨(templateTupleCodeOf body).outputs,
      ?_, rfl⟩
  apply finiteListsOver_complete
  intro word hword
  change word ∈ List.ofFn body at hword
  rw [List.mem_ofFn] at hword
  rcases hword with ⟨o, rfl⟩
  exact finiteWordsUpTo_complete
    (finiteTemplateAtoms A dB dC)
    bound
    (body o)
    (hlength o)
    (hatoms o)

/-- Canonical exact-once template code. -/
noncomputable def exactTemplateTupleCodeOf
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC)
    (hexact : TemplateTuple.ExactlyOnce body) :
    FiniteExactTemplateTupleCode α e dB dC where
  code := templateTupleCodeOf body
  exactOnce := by
    simpa using hexact

@[simp] theorem exactTemplateTupleCodeOf_body
    {e dB dC : Nat}
    (body : TemplateTuple α e dB dC)
    (hexact : TemplateTuple.ExactlyOnce body) :
    (exactTemplateTupleCodeOf body hexact).body =
      body := by
  exact templateTupleCodeOf_body body

/-- Completeness of the corrected finite exact-template enumeration for one
sample binary witness. -/
theorem exactTemplateTupleCodeOf_mem_for_binaryEvidence
    {K : Finset (Word α)}
    {e dB dC : Nat}
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x : Tuple α dB}
    {y : Tuple α dC}
    (B : SampleBinaryEvidence K parent body x y)
    (hexact : TemplateTuple.ExactlyOnce body) :
    exactTemplateTupleCodeOf body hexact ∈
      finiteExactTemplateTupleCodesUpTo
        (sampleAlphabet K)
        e dB dC
        (exactBinaryWitnessBudget K dB dC) := by
  classical
  have hcode :
      templateTupleCodeOf body ∈
        finiteTemplateTupleCodesUpTo
          (sampleAlphabet K)
          e dB dC
          (exactBinaryWitnessBudget K dB dC) := by
    apply templateTupleCodeOf_mem
    · intro o
      have heval :
          (evalTemplateTuple body x y o).length ≤
            sampleLengthBudget K :=
        (namedFill_component_length_le
          parent
          (evalTemplateTuple body x y)
          o).trans
          (sample_word_length_le_budget
            K B.parent_mem)
      have htemplate :=
        exactOnce_templateWord_length_le
          hexact x y o
      unfold exactBinaryWitnessBudget
      omega
    · intro o atom hatom
      exact
        templateAtom_mem_finiteTemplateAtoms_of_parent_mem
          B.parent_mem o hatom

  unfold finiteExactTemplateTupleCodesUpTo
  let attached :
      { C : FiniteTemplateTupleCode α e dB dC //
        C ∈
          (finiteTemplateTupleCodesUpTo
            (sampleAlphabet K)
            e dB dC
            (exactBinaryWitnessBudget K dB dC)).filter
              (fun C =>
                TemplateTuple.ExactlyOnce C.body) } :=
    ⟨templateTupleCodeOf body,
      Finset.mem_filter.mpr
        ⟨hcode, by simpa using hexact⟩⟩
  apply Finset.mem_image.mpr
  refine ⟨attached, ?_, ?_⟩
  · simp
  · apply FiniteExactTemplateTupleCode.ext
    rfl

end ExactTemplateEnumerationCompleteness


section OccurrenceAtLargerBound

variable {α : Type u}

/-- Every sample occurrence is enumerated at every bound above the total sample
length budget. -/
theorem tupleOccurrenceCandidateOf_mem_of_budget_le
    (K : Finset (Word α))
    {d bound : Nat}
    (c : NamedSentenceContext α d)
    (x : Tuple α d)
    (hfill : namedFill d c x ∈ K)
    (hbudget :
      sampleLengthBudget K ≤ bound) :
    tupleOccurrenceCandidateOf c x ∈
      tupleOccurrencesUpTo K d bound := by
  apply tupleOccurrenceCandidateOf_mem
    K d bound c x
    (wellFormed_holes_length c)
  · intro word hword
    apply finiteWordsUpTo_complete
    · exact
        (namedFill_chunk_length_le
          c x hword).trans
          ((sample_word_length_le_budget
            K hfill).trans hbudget)
    · intro a ha
      exact mem_sampleAlphabet_of_mem_word
        K hfill
        (namedFill_mem_of_mem_chunk
          c x hword ha)
  · intro i
    apply finiteWordsUpTo_complete
    · exact
        (namedFill_component_length_le
          c x i).trans
          ((sample_word_length_le_budget
            K hfill).trans hbudget)
    · intro a ha
      exact mem_sampleAlphabet_of_mem_word
        K hfill
        (namedFill_mem_of_mem_component
          c x i ha)
  · exact hfill

end OccurrenceAtLargerBound


section CorrectedBinaryWitnesses

variable {α : Type u}

/-- Corrected default finite binary-witness enumeration. -/
noncomputable def correctedConcreteBinaryWitnesses
    (K : Finset (Word α))
    (e dB dC : Nat) :
    Finset
      (FiniteBinaryWitnessCandidate
        K e dB dC
          (exactBinaryWitnessBudget K dB dC)) :=
  concreteBinaryWitnessesUpTo
    K e dB dC
    (exactBinaryWitnessBudget K dB dC)

/-- A corrected concrete binary rule is literally a member of the corrected
finite witness set. -/
abbrev CorrectedConcreteBinaryRule
    (K : Finset (Word α))
    (e dB dC : Nat) :=
  (correctedConcreteBinaryWitnesses
    K e dB dC).attach

namespace CorrectedConcreteBinaryRule

def witness
    {K : Finset (Word α)}
    {e dB dC : Nat}
    (R : CorrectedConcreteBinaryRule
      K e dB dC) :
    FiniteBinaryWitnessCandidate
      K e dB dC
        (exactBinaryWitnessBudget K dB dC) :=
  R.1

def source
    {K : Finset (Word α)}
    {e dB dC : Nat}
    (R : CorrectedConcreteBinaryRule
      K e dB dC) :
    Tuple α e :=
  R.witness.parent.1.tuple

def leftSource
    {K : Finset (Word α)}
    {e dB dC : Nat}
    (R : CorrectedConcreteBinaryRule
      K e dB dC) :
    Tuple α dB :=
  R.witness.leftTuple

def rightSource
    {K : Finset (Word α)}
    {e dB dC : Nat}
    (R : CorrectedConcreteBinaryRule
      K e dB dC) :
    Tuple α dC :=
  R.witness.rightTuple

def body
    {K : Finset (Word α)}
    {e dB dC : Nat}
    (R : CorrectedConcreteBinaryRule
      K e dB dC) :
    TemplateTuple α e dB dC :=
  R.witness.body

def parentContext
    {K : Finset (Word α)}
    {e dB dC : Nat}
    (R : CorrectedConcreteBinaryRule
      K e dB dC) :
    NamedSentenceContext α e :=
  R.witness.parentContext

def evidence
    {K : Finset (Word α)}
    {e dB dC : Nat}
    (R : CorrectedConcreteBinaryRule
      K e dB dC) :
    SampleBinaryEvidence K
      R.parentContext R.body
      R.leftSource R.rightSource :=
  sampleBinaryEvidenceOfConcreteWitnessUpTo
    K e dB dC
    (exactBinaryWitnessBudget K dB dC)
    R.1 R.2

theorem source_eq_composition
    {K : Finset (Word α)}
    {e dB dC : Nat}
    (R : CorrectedConcreteBinaryRule
      K e dB dC) :
    R.source =
      evalTemplateTuple R.body
        R.leftSource R.rightSource :=
  concreteBinaryWitness_parent_eq
    K e dB dC
    (exactBinaryWitnessBudget K dB dC)
    R.2

end CorrectedConcreteBinaryRule

end CorrectedBinaryWitnesses


section BinaryRuleOfEvidence

variable {α : Type u}

/-- Every exact-once sample binary evidence is represented by an actual member
of the corrected finite binary-witness set. -/
theorem exists_correctedConcreteBinaryRuleOfEvidence
    (K : Finset (Word α))
    {e dB dC : Nat}
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x : Tuple α dB}
    {y : Tuple α dC}
    (B : SampleBinaryEvidence K parent body x y)
    (hexact : TemplateTuple.ExactlyOnce body) :
    ∃ R :
        FiniteBinaryWitnessCandidate
          K e dB dC
            (exactBinaryWitnessBudget K dB dC),
      R ∈ correctedConcreteBinaryWitnesses
          K e dB dC ∧
        R.parentContext = parent ∧
        R.leftTuple = x ∧
        R.rightTuple = y ∧
        R.body = body := by
  classical
  let bound :=
    exactBinaryWitnessBudget K dB dC

  have hbudget :
      sampleLengthBudget K ≤ bound :=
    sampleLengthBudget_le_exactBinaryWitnessBudget
      K dB dC

  let parentOccurrence :=
    tupleOccurrenceCandidateOf
      parent
      (evalTemplateTuple body x y)

  have hparentOccurrence :
      parentOccurrence ∈
        tupleOccurrencesUpTo K e bound :=
    tupleOccurrenceCandidateOf_mem_of_budget_le
      K parent
      (evalTemplateTuple body x y)
      B.parent_mem hbudget

  have hleftMem :
      namedFill dB B.leftIdentity.ctx x ∈ K := by
    rw [B.leftIdentity.identity x]
    exact B.parent_mem

  let leftOccurrence :=
    tupleOccurrenceCandidateOf
      B.leftIdentity.ctx x

  have hleftOccurrence :
      leftOccurrence ∈
        tupleOccurrencesUpTo K dB bound :=
    tupleOccurrenceCandidateOf_mem_of_budget_le
      K B.leftIdentity.ctx x
      hleftMem hbudget

  have hrightMem :
      namedFill dC
          (B.rightIdentity x).ctx y ∈ K := by
    rw [(B.rightIdentity x).identity y]
    exact B.parent_mem

  let rightOccurrence :=
    tupleOccurrenceCandidateOf
      (B.rightIdentity x).ctx y

  have hrightOccurrence :
      rightOccurrence ∈
        tupleOccurrencesUpTo K dC bound :=
    tupleOccurrenceCandidateOf_mem_of_budget_le
      K (B.rightIdentity x).ctx y
      hrightMem hbudget

  let templateCode :=
    exactTemplateTupleCodeOf body hexact

  have htemplateCode :
      templateCode ∈
        finiteExactTemplateTupleCodesUpTo
          (sampleAlphabet K)
          e dB dC bound := by
    exact exactTemplateTupleCodeOf_mem_for_binaryEvidence
      B hexact

  let R :
      FiniteBinaryWitnessCandidate
        K e dB dC bound :=
    { parent :=
        ⟨parentOccurrence,
          hparentOccurrence⟩
      left :=
        ⟨leftOccurrence,
          hleftOccurrence⟩
      right :=
        ⟨rightOccurrence,
          hrightOccurrence⟩
      template := templateCode }

  have hcandidate :
      R ∈ binaryWitnessCandidatesUpTo
        K e dB dC bound := by
    unfold binaryWitnessCandidatesUpTo
    apply Finset.mem_image.mpr
    refine
      ⟨(((⟨parentOccurrence,
              hparentOccurrence⟩,
            ⟨leftOccurrence,
              hleftOccurrence⟩),
          ⟨rightOccurrence,
            hrightOccurrence⟩),
        templateCode),
        ?_, rfl⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr
          ⟨by simp, by simp⟩,
          by simp⟩,
        htemplateCode⟩

  have hR :
      R ∈ correctedConcreteBinaryWitnesses
        K e dB dC := by
    unfold correctedConcreteBinaryWitnesses
    apply Finset.mem_filter.mpr
    refine ⟨hcandidate, ?_⟩
    simp [R, parentOccurrence,
      FiniteBinaryWitnessCandidate.composedTuple,
      FiniteBinaryWitnessCandidate.body,
      FiniteBinaryWitnessCandidate.leftTuple,
      FiniteBinaryWitnessCandidate.rightTuple,
      templateCode]

  refine ⟨R, hR, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [R, leftOccurrence]
  · simp [R, rightOccurrence]
  · simp [R, templateCode]

/-- Select the corrected finite binary rule after finite membership existence
has been proved. -/
noncomputable def correctedConcreteBinaryRuleOfEvidence
    (K : Finset (Word α))
    {e dB dC : Nat}
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x : Tuple α dB}
    {y : Tuple α dC}
    (B : SampleBinaryEvidence K parent body x y)
    (hexact : TemplateTuple.ExactlyOnce body) :
    CorrectedConcreteBinaryRule K e dB dC := by
  classical
  let hex :=
    exists_correctedConcreteBinaryRuleOfEvidence
      K B hexact
  exact
    ⟨Classical.choose hex,
      (Classical.choose_spec hex).1⟩

theorem correctedConcreteBinaryRuleOfEvidence_parentContext
    (K : Finset (Word α))
    {e dB dC : Nat}
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x : Tuple α dB}
    {y : Tuple α dC}
    (B : SampleBinaryEvidence K parent body x y)
    (hexact : TemplateTuple.ExactlyOnce body) :
    (correctedConcreteBinaryRuleOfEvidence
      K B hexact).parentContext = parent := by
  classical
  exact
    (Classical.choose_spec
      (exists_correctedConcreteBinaryRuleOfEvidence
        K B hexact)).2.1

theorem correctedConcreteBinaryRuleOfEvidence_leftSource
    (K : Finset (Word α))
    {e dB dC : Nat}
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x : Tuple α dB}
    {y : Tuple α dC}
    (B : SampleBinaryEvidence K parent body x y)
    (hexact : TemplateTuple.ExactlyOnce body) :
    (correctedConcreteBinaryRuleOfEvidence
      K B hexact).leftSource = x := by
  classical
  exact
    (Classical.choose_spec
      (exists_correctedConcreteBinaryRuleOfEvidence
        K B hexact)).2.2.1

theorem correctedConcreteBinaryRuleOfEvidence_rightSource
    (K : Finset (Word α))
    {e dB dC : Nat}
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x : Tuple α dB}
    {y : Tuple α dC}
    (B : SampleBinaryEvidence K parent body x y)
    (hexact : TemplateTuple.ExactlyOnce body) :
    (correctedConcreteBinaryRuleOfEvidence
      K B hexact).rightSource = y := by
  classical
  exact
    (Classical.choose_spec
      (exists_correctedConcreteBinaryRuleOfEvidence
        K B hexact)).2.2.2.1

theorem correctedConcreteBinaryRuleOfEvidence_body
    (K : Finset (Word α))
    {e dB dC : Nat}
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x : Tuple α dB}
    {y : Tuple α dC}
    (B : SampleBinaryEvidence K parent body x y)
    (hexact : TemplateTuple.ExactlyOnce body) :
    (correctedConcreteBinaryRuleOfEvidence
      K B hexact).body = body := by
  classical
  exact
    (Classical.choose_spec
      (exists_correctedConcreteBinaryRuleOfEvidence
        K B hexact)).2.2.2.2

/-- The selected corrected binary rule reconstructs the original evidence
source tuple. -/
theorem correctedConcreteBinaryRuleOfEvidence_source
    (K : Finset (Word α))
    {e dB dC : Nat}
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x : Tuple α dB}
    {y : Tuple α dC}
    (B : SampleBinaryEvidence K parent body x y)
    (hexact : TemplateTuple.ExactlyOnce body) :
    (correctedConcreteBinaryRuleOfEvidence
      K B hexact).source =
      evalTemplateTuple body x y := by
  let R :=
    correctedConcreteBinaryRuleOfEvidence
      K B hexact
  calc
    R.source =
        evalTemplateTuple R.body
          R.leftSource R.rightSource :=
      R.source_eq_composition
    _ = evalTemplateTuple body x y := by
      rw [correctedConcreteBinaryRuleOfEvidence_body
            K B hexact,
          correctedConcreteBinaryRuleOfEvidence_leftSource
            K B hexact,
          correctedConcreteBinaryRuleOfEvidence_rightSource
            K B hexact]

end BinaryRuleOfEvidence


/-!
The exact-once binary-rule enumeration is now complete with the corrected
finite bound.

The broad relation `SampleLearnerReachable` still accepts arbitrary
`SampleBinaryEvidence` without a syntactic exact-once field.  Therefore the
next file should not falsely prove equivalence with that broad relation.
Instead it should define the exact-once reachable fragment

```lean
ExactSampleLearnerReachable
```

whose binary constructor carries

```lean
TemplateTuple.ExactlyOnce body
```

and assemble the corrected concrete learner from

```lean
ConcreteUnitRule
CorrectedConcreteBinaryRule.
```

Then both directions between the corrected concrete learner and the exact-once
reachable fragment can be proved by induction.
-/

end MCFG
