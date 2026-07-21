/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.Basic

/-!
# ExactOnce.lean

Second clean Lean experiment for the fixed-observation MCFG project.

`Basic.lean` deliberately used a weak `TemplateTuple.Nondeleting` predicate:
every child component occurs at least once.  The paper's working binary
linear nondeleting MCFG rules require more: every child variable occurs
exactly once in the whole output tuple.

This file adds that exact-once layer without changing `Basic.lean`.
The definitions here are conservative: exact working conditions imply the
basic working conditions already established in the first experiment.
-/

namespace MCFG

universe u v

section Counts

variable {α : Type u}

/-- Count occurrences of a left-child variable in a template word. -/
def leftVarCount {dB dC : Nat} (i : Fin dB) :
    TemplateWord α dB dC → Nat
  | [] => 0
  | atom :: rest =>
      match atom with
      | TemplateAtom.terminal _ => leftVarCount i rest
      | TemplateAtom.leftVar j =>
          if j = i then leftVarCount i rest + 1 else leftVarCount i rest
      | TemplateAtom.rightVar _ => leftVarCount i rest

/-- Count occurrences of a right-child variable in a template word. -/
def rightVarCount {dB dC : Nat} (j : Fin dC) :
    TemplateWord α dB dC → Nat
  | [] => 0
  | atom :: rest =>
      match atom with
      | TemplateAtom.terminal _ => rightVarCount j rest
      | TemplateAtom.leftVar _ => rightVarCount j rest
      | TemplateAtom.rightVar k =>
          if k = j then rightVarCount j rest + 1 else rightVarCount j rest

/-- A left-child variable occurs exactly once in the whole template tuple.

The selected output component has count one, and every other output component
has count zero. -/
def LeftOccursExactlyOnce {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) (i : Fin dB) : Prop :=
  ∃ o : Fin e,
    leftVarCount i (body o) = 1 ∧
    ∀ o' : Fin e, o' ≠ o → leftVarCount i (body o') = 0

/-- A right-child variable occurs exactly once in the whole template tuple. -/
def RightOccursExactlyOnce {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) (j : Fin dC) : Prop :=
  ∃ o : Fin e,
    rightVarCount j (body o) = 1 ∧
    ∀ o' : Fin e, o' ≠ o → rightVarCount j (body o') = 0

/-- Exact-once linearity for a binary MCFG template tuple.

This is the paper-side strengthening of the weaker nondeleting predicate in
`Basic.lean`.  The explicit `TemplateTuple.Nondeleting` conjunct is kept so that
the implication back to the first experiment is definitional and CI-stable. -/
def TemplateTuple.ExactlyOnce {e dB dC : Nat}
    (body : TemplateTuple α e dB dC) : Prop :=
  TemplateTuple.Nondeleting body ∧
  (∀ i : Fin dB, LeftOccursExactlyOnce body i) ∧
  (∀ j : Fin dC, RightOccursExactlyOnce body j)

/-- Exact-once templates are nondeleting. -/
theorem TemplateTuple.ExactlyOnce.nondeleting {e dB dC : Nat}
    {body : TemplateTuple α e dB dC}
    (h : TemplateTuple.ExactlyOnce body) :
    TemplateTuple.Nondeleting body :=
  h.1

end Counts


section GrammarExactOnce

variable {N : Type v} {α : Type u}

namespace BinaryRule

/-- Exact-once linearity for a binary rule. -/
def ExactlyOnce {arity : N → Nat} (ρ : BinaryRule N α arity) : Prop :=
  TemplateTuple.ExactlyOnce ρ.body

/-- Exact-once binary rules are nondeleting binary rules. -/
theorem ExactlyOnce.nondeleting {arity : N → Nat}
    {ρ : BinaryRule N α arity}
    (h : ρ.ExactlyOnce) :
    ρ.Nondeleting :=
  TemplateTuple.ExactlyOnce.nondeleting h

end BinaryRule

namespace WorkingMCFG

/-- Every listed binary rule satisfies exact-once linearity. -/
def BinaryRulesExactlyOnce (G : WorkingMCFG N α) : Prop :=
  ∀ ρ : BinaryRule N α G.arity, ρ ∈ G.binaryRules → ρ.ExactlyOnce

/-- The stricter working conditions for the next experimental layer.

This does not replace `BasicWorkingConditions`; it extends it. -/
def ExactWorkingConditions (G : WorkingMCFG N α) : Prop :=
  G.BasicWorkingConditions ∧ G.BinaryRulesExactlyOnce

/-- Exact working conditions imply the basic working conditions from
`Basic.lean`. -/
theorem ExactWorkingConditions.basic
    {G : WorkingMCFG N α}
    (h : G.ExactWorkingConditions) :
    G.BasicWorkingConditions :=
  h.1

/-- Exact working conditions imply all binary rules are nondeleting. -/
theorem ExactWorkingConditions.binaryRulesNondeleting
    {G : WorkingMCFG N α}
    (h : G.ExactWorkingConditions) :
    G.BinaryRulesNondeleting := by
  intro ρ hρ
  exact BinaryRule.ExactlyOnce.nondeleting (h.2 ρ hρ)

/-- Repackage exact working conditions as basic working conditions whose
nondeleting component is justified by exact-once linearity.

This theorem is intentionally modest: it is a stable bridge lemma for later
files, not a full grammar-normal-form theorem. -/
theorem basicWorkingConditions_of_exact
    {G : WorkingMCFG N α}
    (hStart : G.StartArityOne)
    (hStartRules : G.StartRulesWellTyped)
    (hTerminalRules : G.TerminalRulesWellTyped)
    (hExactRules : G.BinaryRulesExactlyOnce) :
    G.BasicWorkingConditions := by
  refine ⟨hStart, hStartRules, hTerminalRules, ?_⟩
  intro ρ hρ
  exact BinaryRule.ExactlyOnce.nondeleting (hExactRules ρ hρ)

end WorkingMCFG

end GrammarExactOnce

end MCFG
