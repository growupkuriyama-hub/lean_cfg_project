/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteOutputTypeRefinementPresentation

/-!
# StartSeparatedOutputTypeRefinementCompleteness.lean

`ConcreteOutputTypeRefinementPresentation.lean` constructs the full finite
output-type presentation and proves completeness under the semantic assumption

```lean
G.StringLanguage ⊆ StartRootedStringLanguage G.
```

That inclusion is false for an arbitrary `WorkingMCFG`, because the current
`DerivesTuple` syntax permits start rules below the root and permits terminal or
binary rules to define the distinguished start nonterminal.

This file replaces the global semantic assumption by a local syntactic
condition.  A grammar is start-separated when:

* no terminal rule has the distinguished start as lhs;
* no binary rule has the distinguished start as lhs;
* no binary rule uses the distinguished start as either child;
* no start rule has the distinguished start as child.

Under this condition, every derivation rooted at a non-start nonterminal is
converted recursively to `StartFreeDerives`, and every derivation rooted at the
start symbol is inverted into exactly one root start rule followed by a
start-free child derivation.

Consequently the full concrete output-type presentation constructed from
`G` and `obs` is complete without assuming the semantic normalization
inclusion separately.
-/

namespace MCFG

universe u v w

section StartSeparationDefinition

variable {N : Type v} {α : Type u}

/-- Local syntactic separation of the distinguished start symbol.

The four conjuncts are precisely the conditions needed to ensure that a start
rule can occur only as the root constructor of a string derivation. -/
def WorkingMCFG.StartSeparated
    (G : WorkingMCFG N α) : Prop :=
  (∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
        ρ.lhs ≠ G.start) ∧
  (∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        ρ.lhs ≠ G.start) ∧
  (∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        ρ.left ≠ G.start ∧ ρ.right ≠ G.start) ∧
  (∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
        ρ.child ≠ G.start)

namespace WorkingMCFG.StartSeparated

variable {G : WorkingMCFG N α}

/-- Terminal rules never define the distinguished start symbol. -/
theorem terminal_lhs_ne_start
    (hsep : G.StartSeparated)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules) :
    ρ.lhs ≠ G.start :=
  hsep.1 ρ hρ

/-- Binary rules never define the distinguished start symbol. -/
theorem binary_lhs_ne_start
    (hsep : G.StartSeparated)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    ρ.lhs ≠ G.start :=
  hsep.2.1 ρ hρ

/-- The left child of a binary rule is never the distinguished start symbol. -/
theorem binary_left_ne_start
    (hsep : G.StartSeparated)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    ρ.left ≠ G.start :=
  (hsep.2.2.1 ρ hρ).1

/-- The right child of a binary rule is never the distinguished start symbol. -/
theorem binary_right_ne_start
    (hsep : G.StartSeparated)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    ρ.right ≠ G.start :=
  (hsep.2.2.1 ρ hρ).2

/-- The child of a start rule is never the distinguished start symbol. -/
theorem start_child_ne_start
    (hsep : G.StartSeparated)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules) :
    ρ.child ≠ G.start :=
  hsep.2.2.2 ρ hρ

end WorkingMCFG.StartSeparated

end StartSeparationDefinition


section StartFreeExtraction

variable {N : Type v} {α : Type u}

namespace DerivesTuple

/-- Recursively erase all possibility of a start step from a derivation whose
root nonterminal is known not to be the distinguished start symbol.

The recursive calls are justified by the start-separation conditions on binary
children.  The `start` constructor is impossible because its conclusion is
definitionally rooted at `G.start`. -/
def toStartFreeOfNeStart
    {G : WorkingMCFG N α}
    (hsep : G.StartSeparated)
    {A : N}
    {x : Tuple α (G.arity A)}
    (h : DerivesTuple G A x)
    (hA : A ≠ G.start) :
    StartFreeDerives G A x :=
  match h with
  | .terminal hρ hwt =>
      StartFreeDerives.terminal hρ hwt

  | .binary hρ hx hy =>
      StartFreeDerives.binary hρ
        (toStartFreeOfNeStart hsep hx
          (hsep.binary_left_ne_start _ hρ))
        (toStartFreeOfNeStart hsep hy
          (hsep.binary_right_ne_start _ hρ))

  | .start _ _ _ =>
      False.elim (hA rfl)
termination_by h

/-- A derivation rooted at the distinguished start symbol is exactly one start
rule followed by a start-free child derivation. -/
theorem start_iff_startRule_startFree
    {G : WorkingMCFG N α}
    (hworking : G.BasicWorkingConditions)
    (hsep : G.StartSeparated)
    {z : Tuple α (G.arity G.start)} :
    DerivesTuple G G.start z ↔
      ∃ ρ : StartRule N,
        ∃ hρ : ρ ∈ G.startRules,
          ∃ childTuple : Tuple α (G.arity ρ.child),
            StartFreeDerives G ρ.child childTuple ∧
              z = castTuple
                (hworking.2.1 ρ hρ)
                childTuple := by
  constructor
  · intro h
    cases h with
    | terminal hρ hwt =>
        exact False.elim
          ((hsep.terminal_lhs_ne_start _ hρ) rfl)

    | binary hρ hx hy =>
        exact False.elim
          ((hsep.binary_lhs_ne_start _ hρ) rfl)

    | start hρ hx hwt =>
        refine ⟨_, hρ, _, ?_, ?_⟩
        · exact hx.toStartFreeOfNeStart hsep
            (hsep.start_child_ne_start _ hρ)
        · have hp : hwt = hworking.2.1 _ hρ :=
            Subsingleton.elim _ _
          cases hp
          rfl

  · rintro ⟨ρ, hρ, childTuple, hchild, rfl⟩
    exact DerivesTuple.start
      hρ
      hchild.toDerivesTuple
      (hworking.2.1 ρ hρ)

end DerivesTuple

end StartFreeExtraction


section StartRootedNormalization

variable {N : Type v} {α : Type u}

/-- Start separation implies the semantic start-rooted normal-form inclusion
left open in `ConcreteOutputTypeRefinementPresentation.lean`. -/
theorem stringLanguage_subset_startRooted_of_startSeparated
    {G : WorkingMCFG N α}
    (hworking : G.BasicWorkingConditions)
    (hsep : G.StartSeparated) :
    G.StringLanguage ⊆ StartRootedStringLanguage G := by
  intro word hword
  rcases hword with ⟨hstart, hderives⟩
  rcases
      (DerivesTuple.start_iff_startRule_startFree
        hworking hsep).mp hderives with
    ⟨ρ, hρ, childTuple, hchild, htuple⟩
  exact
    { startRule := ρ
      start_mem := hρ
      start_wellTyped := hworking.2.1 ρ hρ
      childTuple := childTuple
      child_derives := hchild
      start_arity := hstart
      word_eq := htuple }

/-- Under start separation, the start-rooted normal-form language is exactly
the original string language. -/
theorem startRootedStringLanguage_eq_stringLanguage_of_startSeparated
    {G : WorkingMCFG N α}
    (hworking : G.BasicWorkingConditions)
    (hsep : G.StartSeparated) :
    StartRootedStringLanguage G =
      G.StringLanguage := by
  apply Set.Subset.antisymm
  · exact startRootedStringLanguage_subset_stringLanguage G
  · exact stringLanguage_subset_startRooted_of_startSeparated
      hworking hsep

end StartRootedNormalization


section PresentationGrammarStartSeparation

variable {N : Type v} {α : Type u} {M : Type w}
variable [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- The concrete grammar attached to every output-type presentation is
automatically start-separated because its start symbol is fresh. -/
theorem OutputTypeRefinementPresentation.toWorkingMCFG_startSeparated
    (P : OutputTypeRefinementPresentation G obs) :
    P.toWorkingMCFG.StartSeparated := by
  refine ⟨?_, ?_, ?_, ?_⟩

  · intro ρ hρ
    rcases List.mem_map.mp hρ with ⟨τ, hτ, rfl⟩
    simp [liftPresentationTerminalRule,
      OutputTypeRefinementPresentation.toWorkingMCFG]

  · intro ρ hρ
    rcases List.mem_map.mp hρ with ⟨τ, hτ, rfl⟩
    simp [liftPresentationBinaryRule,
      OutputTypeRefinementPresentation.toWorkingMCFG]

  · intro ρ hρ
    rcases List.mem_map.mp hρ with ⟨τ, hτ, rfl⟩
    constructor <;>
      simp [liftPresentationBinaryRule,
        OutputTypeRefinementPresentation.toWorkingMCFG]

  · intro ρ hρ
    rcases List.mem_map.mp hρ with ⟨σ, hσ, rfl⟩
    simp [liftPresentationStartRule,
      OutputTypeRefinementPresentation.toWorkingMCFG]

end PresentationGrammarStartSeparation


section ConcretePresentationCompleteness

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Start separation discharges the semantic completeness assumption of the
full concrete output-type presentation. -/
def concretePresentationCompleteFor_of_startSeparated
    (hworking : G.BasicWorkingConditions)
    (hsep : G.StartSeparated) :
    PresentationCompleteFor
      (ConcreteOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking) :=
  concretePresentationCompleteFor_of_startRooted
    (obs := obs)
    hworking
    (stringLanguage_subset_startRooted_of_startSeparated
      hworking hsep)

/-- The concrete full output-type presentation generated from `G` and `obs`
has exactly the original language under the local start-separation condition. -/
theorem concretePresentation_stringLanguage_eq_original_of_startSeparated
    (hworking : G.BasicWorkingConditions)
    (hsep : G.StartSeparated) :
    PresentationStringLanguage
        (ConcreteOutputTypeRefinement.presentation
          (G := G) (obs := obs) hworking) =
      G.StringLanguage :=
  (concretePresentationCompleteFor_of_startSeparated
    (obs := obs) hworking hsep).language_eq

/-- Construct a complete finite output-type presentation directly from
`G`, `obs`, finite `N`, finite `M`, basic working conditions, and the local
start-separation condition. -/
noncomputable def concreteCompleteOutputTypePresentation_of_startSeparated
    (hworking : G.BasicWorkingConditions)
    (hsep : G.StartSeparated) :
    CompleteOutputTypePresentation G obs where
  presentation :=
    ConcreteOutputTypeRefinement.presentation
      (G := G) (obs := obs) hworking
  complete :=
    concretePresentationCompleteFor_of_startSeparated
      (obs := obs) hworking hsep

/-- The actual concrete working grammar attached to the full output-type
presentation is language-equivalent to the original grammar under start
separation. -/
theorem concreteWorkingGrammar_stringLanguage_eq_original_of_startSeparated
    (hworking : G.BasicWorkingConditions)
    (hsep : G.StartSeparated) :
    (ConcreteOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking).toWorkingMCFG.StringLanguage =
      G.StringLanguage := by
  calc
    (ConcreteOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking).toWorkingMCFG.StringLanguage =
        PresentationStringLanguage
          (ConcreteOutputTypeRefinement.presentation
            (G := G) (obs := obs) hworking) :=
      presentationStringLanguage_workingGrammar_eq _
    _ = G.StringLanguage :=
      concretePresentation_stringLanguage_eq_original_of_startSeparated
        (obs := obs) hworking hsep

/-- The complete concrete presentation exposes its exact working grammar
language equality through the existing complete-presentation theorem. -/
theorem concreteCompletePresentation_workingGrammar_eq_original_of_startSeparated
    (hworking : G.BasicWorkingConditions)
    (hsep : G.StartSeparated) :
    (concreteCompleteOutputTypePresentation_of_startSeparated
        (G := G) (obs := obs) hworking hsep).
        presentation.toWorkingMCFG.StringLanguage =
      G.StringLanguage :=
  (concreteCompleteOutputTypePresentation_of_startSeparated
    (G := G) (obs := obs) hworking hsep).
    workingGrammar_stringLanguage_eq_original

end ConcretePresentationCompleteness

end MCFG
