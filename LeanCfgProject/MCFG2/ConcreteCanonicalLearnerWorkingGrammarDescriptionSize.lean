/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarMindChanges

/-!
# ConcreteCanonicalLearnerWorkingGrammarDescriptionSize.lean

The preceding files count all nonterminal and rule entries in the actual
cut-compiled `WorkingMCFG`.  This file opens the encoded-description-size
layer.

A concrete serialization must assign a natural-number cost to each stored
nonterminal and to each stored start, terminal, and binary rule.  The structure

```lean
CorrectedConcreteCompiledGrammarEntryCost H
```

packages those four cost functions for one finite learner object `H`.
Its total cost on the actual compiled grammar is

```lean
C.descriptionSize dummy.
```

The central lifting theorem says that if every stored entry has cost at most
`c`, then

```lean
C.descriptionSize dummy
  ≤ H.compiledGrammarPresentationItemCount * c.
```

Consequently the previously verified structural and paper-facing item-count
bounds immediately yield encoded-size bounds after any concrete per-entry
encoding bound has been supplied.

This is deliberately an interface theorem.  It does not yet choose a bit
encoding for terminal symbols, words, tuple codes, proof-erased control nodes,
or dependent binary templates.  The next description-size layer can instantiate
the cost functions and prove a sample-length bound for `c`.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section ListCostBound

/-- If every entry of a finite list has cost at most `c`, the total mapped cost
is at most the list length times `c`. -/
theorem list_sum_map_le_length_mul
    {β : Type u}
    (cost : β → Nat)
    (c : Nat) :
    ∀ xs : List β,
      (∀ x ∈ xs, cost x ≤ c) →
      (xs.map cost).sum ≤ xs.length * c

  | [], _ => by
      simp

  | x :: xs, hcost => by
      have hx :
          cost x ≤ c :=
        hcost x (by simp)

      have hxs :
          ∀ y ∈ xs, cost y ≤ c := by
        intro y hy
        exact
          hcost y (by simp [hy])

      have ih :
          (xs.map cost).sum ≤
            xs.length * c :=
        list_sum_map_le_length_mul
          cost c xs hxs

      simpa [Nat.succ_mul, Nat.add_comm] using
        Nat.add_le_add hx ih

end ListCostBound


section CompiledGrammarEntryCosts

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Cost model for the four kinds of top-level objects stored in one actual
cut-compiled grammar presentation.  The values may be bit lengths, symbol
counts, or any other natural-number encoding cost. -/
structure CorrectedConcreteCompiledGrammarEntryCost
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

namespace CorrectedConcreteCompiledGrammarEntryCost

variable
  {H :
    CorrectedConcreteFiniteHypothesis
      K obs f}

/-- Total encoded cost of all explicit nonterminal entries and all three rule
lists in the actual compiled grammar. -/
def descriptionSize
    (C :
      CorrectedConcreteCompiledGrammarEntryCost H)
    (dummy : α) :
    Nat :=
  (H.compiledGrammarNonterminals.map
      C.nonterminal).sum +
    ((H.toCutWorkingMCFG dummy).startRules.map
      C.startRule).sum +
    ((H.toCutWorkingMCFG dummy).terminalRules.map
      C.terminalRule).sum +
    ((H.toCutWorkingMCFG dummy).binaryRules.map
      C.binaryRule).sum

/-- Every actually stored presentation entry has cost at most `c`. -/
def BoundedBy
    (C :
      CorrectedConcreteCompiledGrammarEntryCost H)
    (dummy : α)
    (c : Nat) :
    Prop :=
  (∀ A ∈ H.compiledGrammarNonterminals,
      C.nonterminal A ≤ c) ∧
    (∀ ρ ∈ (H.toCutWorkingMCFG dummy).startRules,
      C.startRule ρ ≤ c) ∧
    (∀ ρ ∈ (H.toCutWorkingMCFG dummy).terminalRules,
      C.terminalRule ρ ≤ c) ∧
    (∀ ρ ∈ (H.toCutWorkingMCFG dummy).binaryRules,
      C.binaryRule ρ ≤ c)

/-- A uniform per-entry cost bound lifts to the complete presentation item
count. -/
theorem descriptionSize_le_presentationItemCount_mul
    (C :
      CorrectedConcreteCompiledGrammarEntryCost H)
    (dummy : α)
    (c : Nat)
    (hC : C.BoundedBy dummy c) :
    C.descriptionSize dummy ≤
      H.compiledGrammarPresentationItemCount * c := by

  rcases hC with
    ⟨hN, hS, hT, hB⟩

  have hn :
      (H.compiledGrammarNonterminals.map
          C.nonterminal).sum ≤
        H.compiledGrammarNonterminals.length * c :=
    list_sum_map_le_length_mul
      C.nonterminal c
      H.compiledGrammarNonterminals hN

  have hs :
      ((H.toCutWorkingMCFG dummy).startRules.map
          C.startRule).sum ≤
        (H.toCutWorkingMCFG dummy).startRules.length * c :=
    list_sum_map_le_length_mul
      C.startRule c
      (H.toCutWorkingMCFG dummy).startRules hS

  have ht :
      ((H.toCutWorkingMCFG dummy).terminalRules.map
          C.terminalRule).sum ≤
        (H.toCutWorkingMCFG dummy).terminalRules.length * c :=
    list_sum_map_le_length_mul
      C.terminalRule c
      (H.toCutWorkingMCFG dummy).terminalRules hT

  have hb :
      ((H.toCutWorkingMCFG dummy).binaryRules.map
          C.binaryRule).sum ≤
        (H.toCutWorkingMCFG dummy).binaryRules.length * c :=
    list_sum_map_le_length_mul
      C.binaryRule c
      (H.toCutWorkingMCFG dummy).binaryRules hB

  unfold descriptionSize

  calc
    (H.compiledGrammarNonterminals.map
          C.nonterminal).sum +
        ((H.toCutWorkingMCFG dummy).startRules.map
          C.startRule).sum +
        ((H.toCutWorkingMCFG dummy).terminalRules.map
          C.terminalRule).sum +
        ((H.toCutWorkingMCFG dummy).binaryRules.map
          C.binaryRule).sum
        ≤
      H.compiledGrammarNonterminals.length * c +
        (H.toCutWorkingMCFG dummy).startRules.length * c +
        (H.toCutWorkingMCFG dummy).terminalRules.length * c +
        (H.toCutWorkingMCFG dummy).binaryRules.length * c := by
          exact
            Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add hn hs)
                ht)
              hb

    _ =
      H.toCutWorkingMCFGPresentationItemCount
          dummy * c := by
        unfold
          CorrectedConcreteFiniteHypothesis.toCutWorkingMCFGPresentationItemCount
        ring

    _ =
      H.compiledGrammarPresentationItemCount * c := by
        rw [
          H.toCutWorkingMCFGPresentationItemCount_eq
            dummy
        ]

/-- Structural encoded-size bound obtained from the quadratic presentation-item
bound. -/
theorem descriptionSize_le_structuralSquare_mul
    (C :
      CorrectedConcreteCompiledGrammarEntryCost H)
    (dummy : α)
    (c : Nat)
    (hC : C.BoundedBy dummy c) :
    C.descriptionSize dummy ≤
      (K.card + 3 * H.ruleCount + 3) ^ 2 * c := by

  exact
    (C.descriptionSize_le_presentationItemCount_mul
      dummy c hC).trans
      (Nat.mul_le_mul_right c
        H.compiledGrammarPresentationItemCount_le_structuralSquare)

end CorrectedConcreteCompiledGrammarEntryCost

end CompiledGrammarEntryCosts


section PaperFacingDescriptionBound

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Paper-facing encoded-description bound obtained by multiplying the verified
presentation-item bound by a uniform per-entry encoding bound. -/
def correctedConcreteCompiledGrammarDescriptionBound
    (sampleLength f entryBound : Nat) :
    Nat :=
  correctedConcreteCompiledGrammarPresentationItemBound
      sampleLength f *
    entryBound

/-- Any concrete entry-cost model with a uniform bound inherits the existing
paper-facing presentation-size estimate. -/
theorem correctedConcreteFiniteHypothesis_descriptionSize_le_paperBound
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α)
    (C :
      CorrectedConcreteCompiledGrammarEntryCost
        (correctedConcreteFiniteHypothesis
          K obs f))
    (entryBound : Nat)
    (hC : C.BoundedBy dummy entryBound) :
    C.descriptionSize dummy ≤
      correctedConcreteCompiledGrammarDescriptionBound
        (sampleLengthBudget K) f entryBound := by

  have hdescription :
      C.descriptionSize dummy ≤
        (correctedConcreteFiniteHypothesis
            K obs f).compiledGrammarPresentationItemCount *
          entryBound :=
    C.descriptionSize_le_presentationItemCount_mul
      dummy entryBound hC

  have hitems :
      (correctedConcreteFiniteHypothesis
          K obs f).compiledGrammarPresentationItemCount ≤
        correctedConcreteCompiledGrammarPresentationItemBound
          (sampleLengthBudget K) f :=
    correctedConcreteFiniteHypothesis_presentationItemCount_le_paperBound
      K obs f

  calc
    C.descriptionSize dummy ≤
        (correctedConcreteFiniteHypothesis
            K obs f).compiledGrammarPresentationItemCount *
          entryBound :=
      hdescription

    _ ≤
        correctedConcreteCompiledGrammarPresentationItemBound
            (sampleLengthBudget K) f *
          entryBound :=
      Nat.mul_le_mul_right entryBound hitems

    _ =
        correctedConcreteCompiledGrammarDescriptionBound
          (sampleLengthBudget K) f entryBound := by
      rfl

/-- Fully expanded encoded-description bound, still parameterized by the
maximum encoded size of one stored presentation entry. -/
theorem correctedConcreteFiniteHypothesis_descriptionSize_le_explicit
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α)
    (C :
      CorrectedConcreteCompiledGrammarEntryCost
        (correctedConcreteFiniteHypothesis
          K obs f))
    (entryBound : Nat)
    (hC : C.BoundedBy dummy entryBound) :
    C.descriptionSize dummy ≤
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
        entryBound := by

  simpa [
    correctedConcreteCompiledGrammarDescriptionBound,
    correctedConcreteCompiledGrammarPresentationItemBound,
    correctedLearnerPaperRuleCountBound,
    correctedLearnerPaperBase,
    correctedLearnerPaperExponent,
    correctedLearnerPaperScale
  ] using
    correctedConcreteFiniteHypothesis_descriptionSize_le_paperBound
      K obs f dummy C entryBound hC

end PaperFacingDescriptionBound

end MCFG
