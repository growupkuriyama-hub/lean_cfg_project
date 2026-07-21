/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarDescriptionSize

/-!
# ConcreteCanonicalLearnerWorkingGrammarNaturalEncoding.lean

The previous file introduced an abstract natural-number cost for every stored
nonterminal and rule of the actual cut-compiled `WorkingMCFG`.  This file makes
that interface more concrete in two steps.

First, for an arbitrary entry-cost model it constructs the maximum cost of an
entry that is actually stored in the finite presentation.  Hence the uniform
boundedness premise required by the previous description-size theorem is always
available for the finite output itself.

Second, it introduces an explicit natural-number encoding of each of the four
kinds of stored presentation entries.  The code `n` is serialized by the
self-delimiting unary word consisting of `n` one-bits followed by one zero-bit,
so its length is `n + 1`.  If every code used by the output grammar is strictly
below `B`, then every serialized entry has length at most `B`.  Consequently,

```lean
E.unaryDescriptionSize dummy
  ≤ H.compiledGrammarPresentationItemCount * B.
```

The existing structural and paper-facing item-count bounds therefore lift to
fully explicit unary-serialization bounds.

This is a genuine finite encoding layer, but it is not yet the desired compact
binary/bit encoding.  A later file may replace unary code length by a binary
length and then bound the concrete entry codes themselves in terms of the
sample factorization data.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section FiniteListMaximum

/-- Maximum cost of an element of a finite list.  The empty-list maximum is
zero. -/
def listCostMax
    {β : Type u}
    (cost : β → Nat) :
    List β → Nat
  | [] => 0
  | x :: xs =>
      max (cost x) (listCostMax cost xs)

/-- Every element occurring in a list has cost bounded by the recursively
computed list maximum. -/
theorem cost_le_listCostMax_of_mem
    {β : Type u}
    (cost : β → Nat) :
    ∀ (xs : List β) (x : β),
      x ∈ xs →
      cost x ≤ listCostMax cost xs

  | [], x, hx => by
      simp at hx

  | y :: ys, x, hx => by
      simp only [listCostMax]
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact
          (cost_le_listCostMax_of_mem
            cost ys x hx).trans
            (Nat.le_max_right _ _)

end FiniteListMaximum


section MaximumStoredEntryCost

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}
variable
  {H :
    CorrectedConcreteFiniteHypothesis
      K obs f}

namespace CorrectedConcreteCompiledGrammarEntryCost

/-- Maximum encoding cost among all entries actually stored in the compiled
presentation. -/
def maxEntryCost
    (C :
      CorrectedConcreteCompiledGrammarEntryCost H)
    (dummy : α) :
    Nat :=
  max
    (listCostMax
      C.nonterminal
      H.compiledGrammarNonterminals)
    (max
      (listCostMax
        C.startRule
        (H.toCutWorkingMCFG dummy).startRules)
      (max
        (listCostMax
          C.terminalRule
          (H.toCutWorkingMCFG dummy).terminalRules)
        (listCostMax
          C.binaryRule
          (H.toCutWorkingMCFG dummy).binaryRules)))

/-- The maximum cost of the entries actually present automatically satisfies
`BoundedBy`. -/
theorem boundedBy_maxEntryCost
    (C :
      CorrectedConcreteCompiledGrammarEntryCost H)
    (dummy : α) :
    C.BoundedBy dummy (C.maxEntryCost dummy) := by

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro A hA
    exact
      (cost_le_listCostMax_of_mem
        C.nonterminal
        H.compiledGrammarNonterminals
        A hA).trans
        (Nat.le_max_left _ _)

  · intro ρ hρ
    have hcost :
        C.startRule ρ ≤
          listCostMax
            C.startRule
            (H.toCutWorkingMCFG dummy).startRules :=
      cost_le_listCostMax_of_mem
        C.startRule
        (H.toCutWorkingMCFG dummy).startRules
        ρ hρ

    exact
      (hcost.trans
        (Nat.le_max_left _ _)).trans
        (Nat.le_max_right _ _)

  · intro ρ hρ
    have hcost :
        C.terminalRule ρ ≤
          listCostMax
            C.terminalRule
            (H.toCutWorkingMCFG dummy).terminalRules :=
      cost_le_listCostMax_of_mem
        C.terminalRule
        (H.toCutWorkingMCFG dummy).terminalRules
        ρ hρ

    exact
      ((hcost.trans
          (Nat.le_max_left _ _)).trans
          (Nat.le_max_right _ _)).trans
          (Nat.le_max_right _ _)

  · intro ρ hρ
    have hcost :
        C.binaryRule ρ ≤
          listCostMax
            C.binaryRule
            (H.toCutWorkingMCFG dummy).binaryRules :=
      cost_le_listCostMax_of_mem
        C.binaryRule
        (H.toCutWorkingMCFG dummy).binaryRules
        ρ hρ

    exact
      ((hcost.trans
          (Nat.le_max_right _ _)).trans
          (Nat.le_max_right _ _)).trans
          (Nat.le_max_right _ _)

/-- Every finite compiled output has a canonical item-count-times-maximum-cost
bound, without requiring an externally supplied uniform bound. -/
theorem descriptionSize_le_presentationItemCount_mul_maxEntryCost
    (C :
      CorrectedConcreteCompiledGrammarEntryCost H)
    (dummy : α) :
    C.descriptionSize dummy ≤
      H.compiledGrammarPresentationItemCount *
        C.maxEntryCost dummy := by

  exact
    C.descriptionSize_le_presentationItemCount_mul
      dummy
      (C.maxEntryCost dummy)
      (C.boundedBy_maxEntryCost dummy)

/-- Automatic structural description-size bound using the maximum cost of an
entry actually stored in the output presentation. -/
theorem descriptionSize_le_structuralSquare_mul_maxEntryCost
    (C :
      CorrectedConcreteCompiledGrammarEntryCost H)
    (dummy : α) :
    C.descriptionSize dummy ≤
      (K.card + 3 * H.ruleCount + 3) ^ 2 *
        C.maxEntryCost dummy := by

  exact
    C.descriptionSize_le_structuralSquare_mul
      dummy
      (C.maxEntryCost dummy)
      (C.boundedBy_maxEntryCost dummy)

end CorrectedConcreteCompiledGrammarEntryCost

end MaximumStoredEntryCost


section NaturalNumberEncoding

/-- Length of the self-delimiting unary serialization of a natural-number code:
`n` one-bits followed by one zero-bit. -/
def unaryNatCodeLength
    (n : Nat) :
    Nat :=
  n + 1

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Explicit natural-number codes for the four kinds of top-level entries in
one finite compiled grammar presentation. -/
structure CorrectedConcreteCompiledGrammarNaturalEncoding
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) where

  nonterminal :
    CorrectedConcreteCutGrammarNonterminal H → Nat

  startRule :
    StartRule
      (CorrectedConcreteCutGrammarNonterminal H) → Nat

  terminalRule :
    TerminalRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α → Nat

  binaryRule :
    BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H) → Nat

namespace CorrectedConcreteCompiledGrammarNaturalEncoding

variable
  {H :
    CorrectedConcreteFiniteHypothesis
      K obs f}

/-- Convert explicit natural-number entry codes into the abstract entry-cost
model by taking self-delimiting unary code length. -/
def toEntryCost
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H) :
    CorrectedConcreteCompiledGrammarEntryCost H where

  nonterminal := fun A =>
    unaryNatCodeLength (E.nonterminal A)

  startRule := fun ρ =>
    unaryNatCodeLength (E.startRule ρ)

  terminalRule := fun ρ =>
    unaryNatCodeLength (E.terminalRule ρ)

  binaryRule := fun ρ =>
    unaryNatCodeLength (E.binaryRule ρ)

/-- Total length of the unary serialization of all explicit entries in the
compiled presentation. -/
def unaryDescriptionSize
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α) :
    Nat :=
  E.toEntryCost.descriptionSize dummy

/-- Every natural-number code actually used by the compiled presentation is
strictly below `codeBound`. -/
def CodesBelow
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α)
    (codeBound : Nat) :
    Prop :=
  (∀ A ∈ H.compiledGrammarNonterminals,
      E.nonterminal A < codeBound) ∧
    (∀ ρ ∈ (H.toCutWorkingMCFG dummy).startRules,
      E.startRule ρ < codeBound) ∧
    (∀ ρ ∈ (H.toCutWorkingMCFG dummy).terminalRules,
      E.terminalRule ρ < codeBound) ∧
    (∀ ρ ∈ (H.toCutWorkingMCFG dummy).binaryRules,
      E.binaryRule ρ < codeBound)

/-- A strict bound on every used natural-number code gives the uniform unary
code-length bound required by the abstract description-size interface. -/
theorem toEntryCost_boundedBy_of_codesBelow
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α)
    (codeBound : Nat)
    (hE : E.CodesBelow dummy codeBound) :
    E.toEntryCost.BoundedBy dummy codeBound := by

  rcases hE with
    ⟨hN, hS, hT, hB⟩

  refine ⟨?_, ?_, ?_, ?_⟩

  · intro A hA
    simpa [toEntryCost, unaryNatCodeLength] using
      Nat.succ_le_of_lt (hN A hA)

  · intro ρ hρ
    simpa [toEntryCost, unaryNatCodeLength] using
      Nat.succ_le_of_lt (hS ρ hρ)

  · intro ρ hρ
    simpa [toEntryCost, unaryNatCodeLength] using
      Nat.succ_le_of_lt (hT ρ hρ)

  · intro ρ hρ
    simpa [toEntryCost, unaryNatCodeLength] using
      Nat.succ_le_of_lt (hB ρ hρ)

/-- Unary serialization length is bounded by presentation item count times the
size of the finite code space. -/
theorem unaryDescriptionSize_le_presentationItemCount_mul
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α)
    (codeBound : Nat)
    (hE : E.CodesBelow dummy codeBound) :
    E.unaryDescriptionSize dummy ≤
      H.compiledGrammarPresentationItemCount *
        codeBound := by

  unfold unaryDescriptionSize

  exact
    E.toEntryCost.descriptionSize_le_presentationItemCount_mul
      dummy codeBound
      (E.toEntryCost_boundedBy_of_codesBelow
        dummy codeBound hE)

/-- Structural unary-description bound obtained from a finite code-space bound
and the already verified quadratic presentation-size estimate. -/
theorem unaryDescriptionSize_le_structuralSquare_mul
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α)
    (codeBound : Nat)
    (hE : E.CodesBelow dummy codeBound) :
    E.unaryDescriptionSize dummy ≤
      (K.card + 3 * H.ruleCount + 3) ^ 2 *
        codeBound := by

  unfold unaryDescriptionSize

  exact
    E.toEntryCost.descriptionSize_le_structuralSquare_mul
      dummy codeBound
      (E.toEntryCost_boundedBy_of_codesBelow
        dummy codeBound hE)

/-- Maximum unary code length among all entries actually occurring in the
compiled presentation. -/
def maxUnaryEntryCodeLength
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α) :
    Nat :=
  E.toEntryCost.maxEntryCost dummy

/-- Every explicit finite natural-number encoding has an automatic bound using
its maximum used unary code length. -/
theorem unaryDescriptionSize_le_presentationItemCount_mul_maxCodeLength
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α) :
    E.unaryDescriptionSize dummy ≤
      H.compiledGrammarPresentationItemCount *
        E.maxUnaryEntryCodeLength dummy := by

  unfold unaryDescriptionSize
  unfold maxUnaryEntryCodeLength

  exact
    E.toEntryCost.descriptionSize_le_presentationItemCount_mul_maxEntryCost
      dummy

/-- Automatic structural bound for any explicit finite natural-number encoding,
without separately supplying a code-space bound. -/
theorem unaryDescriptionSize_le_structuralSquare_mul_maxCodeLength
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding H)
    (dummy : α) :
    E.unaryDescriptionSize dummy ≤
      (K.card + 3 * H.ruleCount + 3) ^ 2 *
        E.maxUnaryEntryCodeLength dummy := by

  unfold unaryDescriptionSize
  unfold maxUnaryEntryCodeLength

  exact
    E.toEntryCost.descriptionSize_le_structuralSquare_mul_maxEntryCost
      dummy

end CorrectedConcreteCompiledGrammarNaturalEncoding

end NaturalNumberEncoding


section PaperFacingUnaryDescriptionBound

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Paper-facing unary-description bound obtained from a finite natural-number
code-space bound. -/
def correctedConcreteCompiledGrammarUnaryDescriptionBound
    (sampleLength f codeBound : Nat) :
    Nat :=
  correctedConcreteCompiledGrammarPresentationItemBound
      sampleLength f *
    codeBound

/-- The paper-facing presentation-item estimate lifts to any explicit
natural-number encoding whose used codes are strictly below `codeBound`. -/
theorem correctedConcreteFiniteHypothesis_unaryDescriptionSize_le_paperBound
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α)
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding
        (correctedConcreteFiniteHypothesis
          K obs f))
    (codeBound : Nat)
    (hE : E.CodesBelow dummy codeBound) :
    E.unaryDescriptionSize dummy ≤
      correctedConcreteCompiledGrammarUnaryDescriptionBound
        (sampleLengthBudget K) f codeBound := by

  unfold
    CorrectedConcreteCompiledGrammarNaturalEncoding.unaryDescriptionSize

  simpa [
    correctedConcreteCompiledGrammarUnaryDescriptionBound,
    CorrectedConcreteCompiledGrammarNaturalEncoding.toEntryCost
  ] using
    correctedConcreteFiniteHypothesis_descriptionSize_le_paperBound
      K obs f dummy E.toEntryCost codeBound
      (E.toEntryCost_boundedBy_of_codesBelow
        dummy codeBound hE)

/-- Fully expanded unary-description bound for the actual finite learner output,
still parameterized by an upper bound on all used natural-number codes. -/
theorem correctedConcreteFiniteHypothesis_unaryDescriptionSize_le_explicit
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α)
    (E :
      CorrectedConcreteCompiledGrammarNaturalEncoding
        (correctedConcreteFiniteHypothesis
          K obs f))
    (codeBound : Nat)
    (hE : E.CodesBelow dummy codeBound) :
    E.unaryDescriptionSize dummy ≤
      (sampleLengthBudget K +
          3 *
            ((4 *
                (sampleLengthBudget K +
                  f + 1)) ^
              (64 *
                (sampleLengthBudget K +
                  f + 1) *
                (sampleLengthBudget K +
                  f + 1))) +
          4) ^ 2 *
        codeBound := by

  unfold
    CorrectedConcreteCompiledGrammarNaturalEncoding.unaryDescriptionSize

  simpa [
    CorrectedConcreteCompiledGrammarNaturalEncoding.toEntryCost
  ] using
    correctedConcreteFiniteHypothesis_descriptionSize_le_explicit
      K obs f dummy E.toEntryCost codeBound
      (E.toEntryCost_boundedBy_of_codesBelow
        dummy codeBound hE)

end PaperFacingUnaryDescriptionBound

end MCFG
