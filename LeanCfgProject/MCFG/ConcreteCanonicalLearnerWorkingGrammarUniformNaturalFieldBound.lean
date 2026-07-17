/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarNaturalFieldFullyExplicitBound

/-!
# ConcreteCanonicalLearnerWorkingGrammarUniformNaturalFieldBound.lean

The preceding file gives a fully explicit natural-field bound by taking the
maximum of the fully explicit bounds of all stored presentation entries.

This file removes that entry-by-entry maximum.

The only rule-dependent quantity left in a fully explicit binary-rule bound is
the number of framed body tokens.  We therefore define

```lean
H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount dummy
```

as the maximum framed-body-token count among all binary rules actually stored
in the cut-compiled grammar.

Every stored binary rule is then bounded by one uniform quantity built from

* the maximum stored body-token count;
* the complete presentation-item count;
* the augmented terminal-alphabet cardinality; and
* the fixed fan-out bound `max 1 f`.

The uniform binary-rule bound is

```text
max (4 + 2 * maximumBodyTokenCount)
  (max 4
    (max presentationItemCount
      (max 3
        (max maximumBodyTokenCount
          (max terminalAlphabetCard (max 1 f)))))).
```

A top-level binary presentation entry contributes two additional framing fields,
so one uniform presentation-entry bound is obtained by joining

```text
6 + 2 * maximumBodyTokenCount
```

with tags, presentation codes, terminal codes, and the uniform binary-rule
bound.

We prove that every actually stored presentation entry is below this one
uniform entry bound.  Consequently the complete grammar natural serialization
is bounded by

```text
max naturalFieldCount
  (max presentationItemCount uniformEntryBound).
```

This removes

* the maximum over entry-local bounds;
* the maximum over binary-rule-local bounds; and
* every token-local maximum.

The corresponding standard binary width is a valid common width for the whole
natural stream, and the complete logarithmic bit count satisfies the expected
unconditional bound.

After this file the only new structural quantity is the single maximum stored
body-token count.  The next layer can evaluate it separately for the compiler's
three binary-rule families: constant control rules, lifted sample rules, and
saturated cut rules.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section MaximumStoredBinaryRuleBodyTokenCount

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Maximum framed-body-token count among all binary rules actually stored in
the cut-compiled grammar. -/
noncomputable def compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
    (dummy : α) :
    Nat :=
  maximumNaturalFieldValue
    ((H.toCutWorkingMCFG dummy).binaryRules.map
      (fun rho =>
        (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
          bodyTokens.length))

/-- Every stored binary rule's framed-body-token count is below the common
stored-rule maximum. -/
theorem
    compiledBinaryRule_bodyTokenCount_le_storedMaximum
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈ (H.toCutWorkingMCFG dummy).binaryRules) :
    (H.encodeCompiledBinaryRuleNaturalPacket dummy rho).
        bodyTokens.length <=
      H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
        dummy := by

  unfold
    compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount

  apply
    nat_le_maximumNaturalFieldValue_of_mem

  exact
    List.mem_map.mpr
      ⟨rho, hrho, rfl⟩

/-- The expanded arity-plus-template-size body-token count is below the common
stored-rule maximum. -/
theorem
    compiledBinaryRule_arity_add_bodySize_le_storedMaximum
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈ (H.toCutWorkingMCFG dummy).binaryRules) :
    correctedConcreteCutGrammarArity H rho.lhs +
        ((List.ofFn rho.body).map List.length).sum <=
      H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
        dummy := by

  rw [
    ← H.encodeCompiledBinaryRuleNaturalPacket_bodyTokenCount_eq
      dummy rho
  ]

  exact
    H.compiledBinaryRule_bodyTokenCount_le_storedMaximum
      dummy rho hrho

end CorrectedConcreteFiniteHypothesis

end MaximumStoredBinaryRuleBodyTokenCount


section UniformStoredBinaryRuleBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- One natural-value bound valid for every binary rule stored in the compiled
grammar. -/
noncomputable def compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
    (dummy : α) :
    Nat :=
  max
    (4 +
      2 *
        H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
          dummy)
    (max 4
      (max
        H.compiledGrammarPresentationItemCount
        (max 3
          (max
            (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
              dummy)
            (max
              (compiledTerminalAlphabet K dummy).card
              (max 1 f))))))

/-- The encoded natural-field count of every stored binary rule is below the
uniform binary-rule bound. -/
theorem
    compiledBinaryRuleNaturalFieldCount_le_uniformBound_of_mem
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈ (H.toCutWorkingMCFG dummy).binaryRules) :
    (H.encodeCompiledBinaryRuleNaturalList dummy rho).length <=
      H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
        dummy := by

  rw [
    H.encodeCompiledBinaryRuleNaturalList_length
      dummy rho
  ]

  have hbody :
      correctedConcreteCutGrammarArity H rho.lhs +
          ((List.ofFn rho.body).map List.length).sum <=
        H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
          dummy :=
    H.compiledBinaryRule_arity_add_bodySize_le_storedMaximum
      dummy rho hrho

  have hlength :
      4 +
          2 *
            (correctedConcreteCutGrammarArity H rho.lhs +
              ((List.ofFn rho.body).map List.length).sum) <=
        4 +
          2 *
            H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
              dummy :=
    Nat.add_le_add_left
      (Nat.mul_le_mul_left 2 hbody)
      4

  exact
    hlength.trans
      (Nat.le_max_left
        (4 +
          2 *
            H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
              dummy)
        (max 4
          (max
            H.compiledGrammarPresentationItemCount
            (max 3
              (max
                (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                  dummy)
                (max
                  (compiledTerminalAlphabet K dummy).card
                  (max 1 f))))))

/-- The common body-token payload bound of every stored binary rule is below the
uniform binary-rule bound. -/
theorem
    compiledBinaryRuleBodyTokenPayloadBound_le_uniformBound_of_mem
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈ (H.toCutWorkingMCFG dummy).binaryRules) :
    H.compiledBinaryRuleBodyTokenPayloadBound dummy rho <=
      H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
        dummy := by

  unfold
    compiledBinaryRuleBodyTokenPayloadBound
    compiledWorkingGrammarUniformBinaryRuleNaturalValueBound

  apply max_le

  · exact
      (H.compiledBinaryRule_bodyTokenCount_le_storedMaximum
          dummy rho hrho).trans
        ((Nat.le_max_left
            (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
              dummy)
            (max
              (compiledTerminalAlphabet K dummy).card
              (max 1 f))).trans
          ((Nat.le_max_right
              3
              (max
                (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                  dummy)
                (max
                  (compiledTerminalAlphabet K dummy).card
                  (max 1 f)))).trans
            ((Nat.le_max_right
                H.compiledGrammarPresentationItemCount
                (max 3
                  (max
                    (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                      dummy)
                    (max
                      (compiledTerminalAlphabet K dummy).card
                      (max 1 f))))).trans
              ((Nat.le_max_right
                  4
                  (max
                    H.compiledGrammarPresentationItemCount
                    (max 3
                      (max
                        (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                          dummy)
                        (max
                          (compiledTerminalAlphabet K dummy).card
                          (max 1 f)))))).trans
                (Nat.le_max_right
                  (4 +
                    2 *
                      H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                        dummy)
                  (max 4
                    (max
                      H.compiledGrammarPresentationItemCount
                      (max 3
                        (max
                          (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                            dummy)
                          (max
                            (compiledTerminalAlphabet K dummy).card
                            (max 1 f)))))))))

  · apply max_le

    · exact
        (Nat.le_max_left
            (compiledTerminalAlphabet K dummy).card
            (max 1 f)).trans
          ((Nat.le_max_right
              (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                dummy)
              (max
                (compiledTerminalAlphabet K dummy).card
                (max 1 f))).trans
            ((Nat.le_max_right
                3
                (max
                  (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                    dummy)
                  (max
                    (compiledTerminalAlphabet K dummy).card
                    (max 1 f)))).trans
              ((Nat.le_max_right
                  H.compiledGrammarPresentationItemCount
                  (max 3
                    (max
                      (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                        dummy)
                      (max
                        (compiledTerminalAlphabet K dummy).card
                        (max 1 f))))).trans
                ((Nat.le_max_right
                    4
                    (max
                      H.compiledGrammarPresentationItemCount
                      (max 3
                        (max
                          (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                            dummy)
                          (max
                            (compiledTerminalAlphabet K dummy).card
                            (max 1 f)))))).trans
                  (Nat.le_max_right
                    (4 +
                      2 *
                        H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                          dummy)
                    (max 4
                      (max
                        H.compiledGrammarPresentationItemCount
                        (max 3
                          (max
                            (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                              dummy)
                            (max
                              (compiledTerminalAlphabet K dummy).card
                              (max 1 f)))))))))

    · exact
        (Nat.le_max_right
            (compiledTerminalAlphabet K dummy).card
            (max 1 f)).trans
          ((Nat.le_max_right
              (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                dummy)
              (max
                (compiledTerminalAlphabet K dummy).card
                (max 1 f))).trans
            ((Nat.le_max_right
                3
                (max
                  (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                    dummy)
                  (max
                    (compiledTerminalAlphabet K dummy).card
                    (max 1 f)))).trans
              ((Nat.le_max_right
                  H.compiledGrammarPresentationItemCount
                  (max 3
                    (max
                      (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                        dummy)
                      (max
                        (compiledTerminalAlphabet K dummy).card
                        (max 1 f))))).trans
                ((Nat.le_max_right
                    4
                    (max
                      H.compiledGrammarPresentationItemCount
                      (max 3
                        (max
                          (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                            dummy)
                          (max
                            (compiledTerminalAlphabet K dummy).card
                            (max 1 f)))))).trans
                  (Nat.le_max_right
                    (4 +
                      2 *
                        H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                          dummy)
                    (max 4
                      (max
                        H.compiledGrammarPresentationItemCount
                        (max 3
                          (max
                            (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                              dummy)
                            (max
                              (compiledTerminalAlphabet K dummy).card
                              (max 1 f)))))))))

/-- Every stored binary rule's fully explicit local bound is below the one
uniform binary-rule bound. -/
theorem
    compiledBinaryRuleFullyExplicitNaturalValueBound_le_uniform_of_mem
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈ (H.toCutWorkingMCFG dummy).binaryRules) :
    H.compiledBinaryRuleFullyExplicitNaturalValueBound dummy rho <=
      H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
        dummy := by

  unfold
    compiledBinaryRuleFullyExplicitNaturalValueBound

  apply max_le

  · exact
      H.compiledBinaryRuleNaturalFieldCount_le_uniformBound_of_mem
        dummy rho hrho

  · apply max_le

    · exact
        (Nat.le_max_left
            4
            (max
              H.compiledGrammarPresentationItemCount
              (max 3
                (max
                  (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                    dummy)
                  (max
                    (compiledTerminalAlphabet K dummy).card
                    (max 1 f)))))).trans
          (Nat.le_max_right
            (4 +
              2 *
                H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                  dummy)
            (max 4
              (max
                H.compiledGrammarPresentationItemCount
                (max 3
                  (max
                    (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                      dummy)
                    (max
                      (compiledTerminalAlphabet K dummy).card
                      (max 1 f)))))))

    · apply max_le

      · exact
          (Nat.le_max_left
              H.compiledGrammarPresentationItemCount
              (max 3
                (max
                  (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                    dummy)
                  (max
                    (compiledTerminalAlphabet K dummy).card
                    (max 1 f))))).trans
            ((Nat.le_max_right
                4
                (max
                  H.compiledGrammarPresentationItemCount
                  (max 3
                    (max
                      (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                        dummy)
                      (max
                        (compiledTerminalAlphabet K dummy).card
                        (max 1 f)))))).trans
              (Nat.le_max_right
                (4 +
                  2 *
                    H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                      dummy)
                (max 4
                  (max
                    H.compiledGrammarPresentationItemCount
                    (max 3
                      (max
                        (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                          dummy)
                        (max
                          (compiledTerminalAlphabet K dummy).card
                          (max 1 f)))))))

      · apply max_le

        · exact
            (Nat.le_max_left
                3
                (H.compiledBinaryRuleBodyTokenPayloadBound
                  dummy rho)).trans
              ((Nat.le_max_right
                  H.compiledGrammarPresentationItemCount
                  (max 3
                    (max
                      (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                        dummy)
                      (max
                        (compiledTerminalAlphabet K dummy).card
                        (max 1 f))))).trans
                ((Nat.le_max_right
                    4
                    (max
                      H.compiledGrammarPresentationItemCount
                      (max 3
                        (max
                          (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                            dummy)
                          (max
                            (compiledTerminalAlphabet K dummy).card
                            (max 1 f)))))).trans
                  (Nat.le_max_right
                    (4 +
                      2 *
                        H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                          dummy)
                    (max 4
                      (max
                        H.compiledGrammarPresentationItemCount
                        (max 3
                          (max
                            (H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                              dummy)
                            (max
                              (compiledTerminalAlphabet K dummy).card
                              (max 1 f)))))))))

        · exact
            H.compiledBinaryRuleBodyTokenPayloadBound_le_uniformBound_of_mem
              dummy rho hrho

/-- Every stored binary rule's original local natural-value bound is below the
uniform binary-rule bound. -/
theorem
    compiledBinaryRuleNaturalValueBound_le_uniform_of_mem
    (dummy : α)
    (rho : BinaryRule
      (CorrectedConcreteCutGrammarNonterminal H)
      α
      (correctedConcreteCutGrammarArity H))
    (hrho :
      rho ∈ (H.toCutWorkingMCFG dummy).binaryRules) :
    H.compiledBinaryRuleNaturalValueBound dummy rho <=
      H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
        dummy := by

  exact
    (H.compiledBinaryRuleNaturalValueBound_le_fullyExplicit_of_mem
        dummy rho hrho).trans
      (H.compiledBinaryRuleFullyExplicitNaturalValueBound_le_uniform_of_mem
        dummy rho hrho)

end CorrectedConcreteFiniteHypothesis

end UniformStoredBinaryRuleBound


section UniformPresentationEntryBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- One natural-value bound valid for every top-level presentation entry
actually stored in the compiled grammar. -/
noncomputable def compiledWorkingGrammarUniformPresentationEntryNaturalValueBound
    (dummy : α) :
    Nat :=
  max
    (6 +
      2 *
        H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
          dummy)
    (max 3
      (max
        H.compiledGrammarPresentationItemCount
        (max
          (compiledTerminalAlphabet K dummy).card
          (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
            dummy))))

/-- The fully explicit local bound of every actually stored presentation entry
is below the one uniform presentation-entry bound. -/
theorem
    compiledGrammarPresentationEntryFullyExplicitNaturalValueBound_le_uniform_of_mem
    (dummy : α)
    (entry :
      CorrectedConcreteCompiledGrammarPresentationEntry H)
    (hentry :
      entry ∈ H.compiledGrammarPresentationEntries dummy) :
    H.compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
        dummy entry <=
      H.compiledWorkingGrammarUniformPresentationEntryNaturalValueBound
        dummy := by

  cases entry with

  | nonterminal A =>
      unfold
        compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
        compiledWorkingGrammarUniformPresentationEntryNaturalValueBound

      apply max_le

      · omega

      · exact
          (Nat.le_max_left
              H.compiledGrammarPresentationItemCount
              (max
                (compiledTerminalAlphabet K dummy).card
                (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                  dummy))).trans
            ((Nat.le_max_right
                3
                (max
                  H.compiledGrammarPresentationItemCount
                  (max
                    (compiledTerminalAlphabet K dummy).card
                    (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                      dummy)))).trans
              (Nat.le_max_right
                (6 +
                  2 *
                    H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                      dummy)
                (max 3
                  (max
                    H.compiledGrammarPresentationItemCount
                    (max
                      (compiledTerminalAlphabet K dummy).card
                      (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                        dummy))))))

  | startRule rho =>
      unfold
        compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
        compiledWorkingGrammarUniformPresentationEntryNaturalValueBound

      apply max_le

      · omega

      · exact
          (Nat.le_max_left
              H.compiledGrammarPresentationItemCount
              (max
                (compiledTerminalAlphabet K dummy).card
                (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                  dummy))).trans
            ((Nat.le_max_right
                3
                (max
                  H.compiledGrammarPresentationItemCount
                  (max
                    (compiledTerminalAlphabet K dummy).card
                    (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                      dummy)))).trans
              (Nat.le_max_right
                (6 +
                  2 *
                    H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                      dummy)
                (max 3
                  (max
                    H.compiledGrammarPresentationItemCount
                    (max
                      (compiledTerminalAlphabet K dummy).card
                      (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                        dummy))))))

  | terminalRule rho =>
      unfold
        compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
        compiledWorkingGrammarUniformPresentationEntryNaturalValueBound

      apply max_le

      · exact
          (Nat.le_max_left
              3
              (max
                H.compiledGrammarPresentationItemCount
                (max
                  (compiledTerminalAlphabet K dummy).card
                  (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                    dummy)))).trans
            (Nat.le_max_right
              (6 +
                2 *
                  H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                    dummy)
              (max 3
                (max
                  H.compiledGrammarPresentationItemCount
                  (max
                    (compiledTerminalAlphabet K dummy).card
                    (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                      dummy)))))

      · apply max_le

        · exact
            (Nat.le_max_left
                H.compiledGrammarPresentationItemCount
                (max
                  (compiledTerminalAlphabet K dummy).card
                  (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                    dummy))).trans
              ((Nat.le_max_right
                  3
                  (max
                    H.compiledGrammarPresentationItemCount
                    (max
                      (compiledTerminalAlphabet K dummy).card
                      (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                        dummy)))).trans
                (Nat.le_max_right
                  (6 +
                    2 *
                      H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                        dummy)
                  (max 3
                    (max
                      H.compiledGrammarPresentationItemCount
                      (max
                        (compiledTerminalAlphabet K dummy).card
                        (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                          dummy))))))

        · exact
            (Nat.le_max_left
                (compiledTerminalAlphabet K dummy).card
                (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                  dummy)).trans
              ((Nat.le_max_right
                  H.compiledGrammarPresentationItemCount
                  (max
                    (compiledTerminalAlphabet K dummy).card
                    (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                      dummy))).trans
                ((Nat.le_max_right
                    3
                    (max
                      H.compiledGrammarPresentationItemCount
                      (max
                        (compiledTerminalAlphabet K dummy).card
                        (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                          dummy)))).trans
                  (Nat.le_max_right
                    (6 +
                      2 *
                        H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                          dummy)
                    (max 3
                      (max
                        H.compiledGrammarPresentationItemCount
                        (max
                          (compiledTerminalAlphabet K dummy).card
                          (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                            dummy)))))))

  | binaryRule rho =>
      have hrho :
          rho ∈ (H.toCutWorkingMCFG dummy).binaryRules := by

        simpa [
          CorrectedConcreteFiniteHypothesis.compiledGrammarPresentationEntries
        ] using hentry

      unfold
        compiledGrammarPresentationEntryFullyExplicitNaturalValueBound
        compiledWorkingGrammarUniformPresentationEntryNaturalValueBound

      apply max_le

      · have hbody :
            correctedConcreteCutGrammarArity H rho.lhs +
                ((List.ofFn rho.body).map List.length).sum <=
              H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                dummy :=
          H.compiledBinaryRule_arity_add_bodySize_le_storedMaximum
            dummy rho hrho

        rw [
          H.compiledGrammarPresentationEntryNaturalFieldCount_binaryRule
            dummy rho
        ]

        have hcount :
            6 +
                2 *
                  (correctedConcreteCutGrammarArity H rho.lhs +
                    ((List.ofFn rho.body).map List.length).sum) <=
              6 +
                2 *
                  H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                    dummy :=
          Nat.add_le_add_left
            (Nat.mul_le_mul_left 2 hbody)
            6

        exact
          hcount.trans
            (Nat.le_max_left
              (6 +
                2 *
                  H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                    dummy)
              (max 3
                (max
                  H.compiledGrammarPresentationItemCount
                  (max
                    (compiledTerminalAlphabet K dummy).card
                    (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                      dummy)))))

      · apply max_le

        · exact
            (Nat.le_max_left
                3
                (H.compiledBinaryRuleFullyExplicitNaturalValueBound
                  dummy rho)).trans
              ((Nat.le_max_right
                  (H.compiledGrammarPresentationItemCount)
                  (max
                    (compiledTerminalAlphabet K dummy).card
                    (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                      dummy))).trans
                ((Nat.le_max_right
                    3
                    (max
                      H.compiledGrammarPresentationItemCount
                      (max
                        (compiledTerminalAlphabet K dummy).card
                        (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                          dummy)))).trans
                  (Nat.le_max_right
                    (6 +
                      2 *
                        H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                          dummy)
                    (max 3
                      (max
                        H.compiledGrammarPresentationItemCount
                        (max
                          (compiledTerminalAlphabet K dummy).card
                          (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                            dummy)))))))

        · exact
            (H.compiledBinaryRuleFullyExplicitNaturalValueBound_le_uniform_of_mem
                dummy rho hrho).trans
              ((Nat.le_max_right
                  (compiledTerminalAlphabet K dummy).card
                  (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                    dummy)).trans
                ((Nat.le_max_right
                    H.compiledGrammarPresentationItemCount
                    (max
                      (compiledTerminalAlphabet K dummy).card
                      (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                        dummy))).trans
                  ((Nat.le_max_right
                      3
                      (max
                        H.compiledGrammarPresentationItemCount
                        (max
                          (compiledTerminalAlphabet K dummy).card
                          (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                            dummy)))).trans
                    (Nat.le_max_right
                      (6 +
                        2 *
                          H.compiledWorkingGrammarMaximumBinaryRuleBodyTokenCount
                            dummy)
                      (max 3
                        (max
                          H.compiledGrammarPresentationItemCount
                          (max
                            (compiledTerminalAlphabet K dummy).card
                            (H.compiledWorkingGrammarUniformBinaryRuleNaturalValueBound
                              dummy)))))))

/-- The maximum fully explicit entry-local bound is below the one uniform
presentation-entry bound. -/
theorem
    compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound_le_uniform
    (dummy : α) :
    H.compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound
        dummy <=
      H.compiledWorkingGrammarUniformPresentationEntryNaturalValueBound
        dummy := by

  unfold
    compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound
    maximumCompiledGrammarPresentationEntryFullyExplicitNaturalValueBound

  apply
    maximumNaturalFieldValue_le_of_forall_mem

  intro localBound hlocalBound

  rcases List.mem_map.mp hlocalBound with
    ⟨entry, hentry, rfl⟩

  exact
    H.compiledGrammarPresentationEntryFullyExplicitNaturalValueBound_le_uniform_of_mem
      dummy entry hentry

end CorrectedConcreteFiniteHypothesis

end UniformPresentationEntryBound


section CompleteUniformNaturalFieldAndBitBound

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesis

variable
  (H : CorrectedConcreteFiniteHypothesis K obs f)

/-- Complete natural-field bound after eliminating all maxima over entries and
individual binary rules. -/
noncomputable def compiledWorkingGrammarUniformNaturalFieldBound
    (dummy : α) :
    Nat :=
  max
    (H.compiledWorkingGrammarNaturalFieldCount dummy)
    (max
      H.compiledGrammarPresentationItemCount
      (H.compiledWorkingGrammarUniformPresentationEntryNaturalValueBound
        dummy))

/-- The fully explicit entry-maximum-based bound is below the uniform complete
natural-field bound. -/
theorem
    compiledWorkingGrammarFullyExplicitNaturalFieldBound_le_uniform
    (dummy : α) :
    H.compiledWorkingGrammarFullyExplicitNaturalFieldBound dummy <=
      H.compiledWorkingGrammarUniformNaturalFieldBound
        dummy := by

  unfold
    compiledWorkingGrammarFullyExplicitNaturalFieldBound
    compiledWorkingGrammarUniformNaturalFieldBound

  apply max_le

  · exact
      Nat.le_max_left
        (H.compiledWorkingGrammarNaturalFieldCount dummy)
        (max
          H.compiledGrammarPresentationItemCount
          (H.compiledWorkingGrammarUniformPresentationEntryNaturalValueBound
            dummy))

  · apply max_le

    · exact
        (Nat.le_max_left
            H.compiledGrammarPresentationItemCount
            (H.compiledWorkingGrammarUniformPresentationEntryNaturalValueBound
              dummy)).trans
          (Nat.le_max_right
            (H.compiledWorkingGrammarNaturalFieldCount dummy)
            (max
              H.compiledGrammarPresentationItemCount
              (H.compiledWorkingGrammarUniformPresentationEntryNaturalValueBound
                dummy)))

    · exact
        (H.compiledWorkingGrammarMaximumEntryFullyExplicitNaturalValueBound_le_uniform
            dummy).trans
          ((Nat.le_max_right
              H.compiledGrammarPresentationItemCount
              (H.compiledWorkingGrammarUniformPresentationEntryNaturalValueBound
                dummy)).trans
            (Nat.le_max_right
              (H.compiledWorkingGrammarNaturalFieldCount dummy)
              (max
                H.compiledGrammarPresentationItemCount
                (H.compiledWorkingGrammarUniformPresentationEntryNaturalValueBound
                  dummy))))

/-- The original complete natural-field value bound is below the uniform
structural bound. -/
theorem
    compiledWorkingGrammarNaturalFieldValueBound_le_uniform
    (dummy : α) :
    H.compiledWorkingGrammarNaturalFieldValueBound dummy <=
      H.compiledWorkingGrammarUniformNaturalFieldBound
        dummy := by

  exact
    (H.compiledWorkingGrammarNaturalFieldValueBound_le_fullyExplicitBound
        dummy).trans
      (H.compiledWorkingGrammarFullyExplicitNaturalFieldBound_le_uniform
        dummy)

/-- Every natural field of the complete grammar serialization is below the
uniform structural bound. -/
theorem compiledWorkingGrammarNaturalField_le_uniform_of_mem
    (dummy : α)
    {n : Nat}
    (hn :
      n ∈ H.encodeCompiledWorkingGrammarNaturalList dummy) :
    n <=
      H.compiledWorkingGrammarUniformNaturalFieldBound
        dummy := by

  exact
    (H.compiledWorkingGrammarNaturalField_le_valueBound_of_mem
        dummy hn).trans
      (H.compiledWorkingGrammarNaturalFieldValueBound_le_uniform
        dummy)

/-- Standard binary width selected from the uniform structural field bound. -/
noncomputable def compiledWorkingGrammarUniformNaturalFieldBitWidth
    (dummy : α) :
    Nat :=
  binaryNatCodeLength
    (H.compiledWorkingGrammarUniformNaturalFieldBound
      dummy)

/-- The complete natural grammar stream fits the uniform structural width. -/
theorem
    compiledWorkingGrammarNaturalFieldsFitInBits_uniform
    (dummy : α) :
    H.compiledWorkingGrammarNaturalFieldsFitInBits
        dummy
        (H.compiledWorkingGrammarUniformNaturalFieldBitWidth
          dummy) := by

  refine
    ⟨binaryNatCodeLength_pos
        (H.compiledWorkingGrammarUniformNaturalFieldBound
          dummy),
      ?_,
      ?_⟩

  · rw [
      H.encodeCompiledWorkingGrammarNaturalList_length
        dummy
    ]

    exact
      (Nat.le_max_left
          (H.compiledWorkingGrammarNaturalFieldCount dummy)
          (max
            H.compiledGrammarPresentationItemCount
            (H.compiledWorkingGrammarUniformPresentationEntryNaturalValueBound
              dummy))).trans_lt
        (natCode_lt_two_pow_binaryNatCodeLength
          (H.compiledWorkingGrammarUniformNaturalFieldBound
            dummy))

  · intro n hn

    exact
      (H.compiledWorkingGrammarNaturalField_le_uniform_of_mem
          dummy hn).trans_lt
        (natCode_lt_two_pow_binaryNatCodeLength
          (H.compiledWorkingGrammarUniformNaturalFieldBound
            dummy))

/-- The least automatically selected field width is below the uniform
structural width. -/
theorem
    compiledWorkingGrammarAutomaticNaturalFieldBitWidth_le_uniform
    (dummy : α) :
    H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth dummy <=
      H.compiledWorkingGrammarUniformNaturalFieldBitWidth
        dummy := by

  exact
    H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth_le_of_fits
      dummy
      (H.compiledWorkingGrammarNaturalFieldsFitInBits_uniform
        dummy)

/-- Complete unconditional logarithmic bit-size bound after eliminating maxima
over entries and individual binary rules. -/
theorem
    compiledWorkingGrammarLogarithmicBitCount_le_uniform
    (dummy : α) :
    H.compiledWorkingGrammarLogarithmicBitCount dummy <=
      (H.compiledWorkingGrammarNaturalFieldCount dummy + 1) *
        (2 *
            binaryNatCodeLength
              (H.compiledWorkingGrammarUniformNaturalFieldBound
                dummy) +
          1) := by

  exact
    H.compiledWorkingGrammarLogarithmicBitCount_le_of_naturalFieldsFitInBits
      dummy
      (H.compiledWorkingGrammarNaturalFieldsFitInBits_uniform
        dummy)

/-- Compact final endpoint of the uniform natural-field layer. -/
theorem compiledWorkingGrammarUniformNaturalFieldBound_package
    (dummy : α) :
    (H.compiledWorkingGrammarNaturalFieldValueBound dummy <=
      H.compiledWorkingGrammarUniformNaturalFieldBound
        dummy) ∧
      (∀ n ∈
          H.encodeCompiledWorkingGrammarNaturalList dummy,
        n <=
          H.compiledWorkingGrammarUniformNaturalFieldBound
            dummy) ∧
      H.compiledWorkingGrammarNaturalFieldsFitInBits
        dummy
        (H.compiledWorkingGrammarUniformNaturalFieldBitWidth
          dummy) ∧
      (H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth dummy <=
        H.compiledWorkingGrammarUniformNaturalFieldBitWidth
          dummy) ∧
      (H.compiledWorkingGrammarLogarithmicBitCount dummy <=
        (H.compiledWorkingGrammarNaturalFieldCount dummy + 1) *
          (2 *
              binaryNatCodeLength
                (H.compiledWorkingGrammarUniformNaturalFieldBound
                  dummy) +
            1)) := by

  exact
    ⟨H.compiledWorkingGrammarNaturalFieldValueBound_le_uniform
        dummy,
      by
        intro n hn
        exact
          H.compiledWorkingGrammarNaturalField_le_uniform_of_mem
            dummy hn,
      H.compiledWorkingGrammarNaturalFieldsFitInBits_uniform
        dummy,
      H.compiledWorkingGrammarAutomaticNaturalFieldBitWidth_le_uniform
        dummy,
      H.compiledWorkingGrammarLogarithmicBitCount_le_uniform
        dummy⟩

end CorrectedConcreteFiniteHypothesis

end CompleteUniformNaturalFieldAndBitBound

end MCFG
