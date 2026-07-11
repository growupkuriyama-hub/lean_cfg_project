/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.OutputTypePresentationWorkingGrammar

/-!
# OutputTypePresentationWorkingGrammarEquivalence.lean

This file proves that the concrete `WorkingMCFG` attached to a finite
output-type presentation generates exactly the presentation language.

The proof reverses membership in each of the three mapped rule lists.  A
derivation of a typed grammar nonterminal is converted back to
`PresentationDerives`; a derivation of the fresh start symbol is decomposed
into one lifted typed start rule followed by a presentation derivation.
-/

namespace MCFG

universe u v w

section WorkingGrammarDerivationView

variable {N : Type v} {α : Type u} {M : Type w}
variable [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {P : OutputTypeRefinementPresentation G obs}

/-- Exact inverse view of a derivation in the concrete presentation grammar.

At a typed nonterminal it contains a presentation derivation.  At the fresh
start symbol it contains a present typed start rule, a presentation derivation
of its child, and the exact tuple equation produced by the lifted start step. -/
inductive WorkingGrammarDerivationView
    (P : OutputTypeRefinementPresentation G obs) :
    (A : PresentationGrammarNonterminal G M) →
      Tuple α (P.toWorkingMCFG.arity A) → Prop where
  | typed
      {X : TypedNonterminal G M}
      {x : Tuple α (G.arity X.base)}
      (derives : PresentationDerives P X x) :
      WorkingGrammarDerivationView P
        (PresentationGrammarNonterminal.typed X) x
  | start
      {z : Tuple α (G.arity G.start)}
      (σ : TypedStartRule G M)
      (hσ : P.HasStartRule σ)
      (childTuple : Tuple α (G.arity σ.baseRule.child))
      (childDerives : PresentationDerives P σ.child childTuple)
      (tuple_eq : z = castTuple σ.wellTyped childTuple) :
      WorkingGrammarDerivationView P
        PresentationGrammarNonterminal.start z

namespace WorkingGrammarDerivationView

/-- Reverse a derivation of the concrete presentation grammar by inverting the
three mapped finite rule lists. -/
theorem ofDerives
    {A : PresentationGrammarNonterminal G M}
    {x : Tuple α (P.toWorkingMCFG.arity A)}
    (h : DerivesTuple P.toWorkingMCFG A x) :
    WorkingGrammarDerivationView P A x := by
  induction h with
  | terminal hρ hwt =>
      rcases List.mem_map.mp hρ with ⟨τ, hτ, rfl⟩
      have hτP : P.HasTerminalRule τ := by
        simpa [OutputTypeRefinementPresentation.HasTerminalRule] using hτ
      have hp : hwt = τ.wellTyped := Subsingleton.elim _ _
      cases hp
      exact .typed (PresentationDerives.terminal hτP)

  | binary hρ hx hy ihx ihy =>
      rcases List.mem_map.mp hρ with ⟨τ, hτ, rfl⟩
      have hτP : P.HasBinaryRule τ := by
        simpa [OutputTypeRefinementPresentation.HasBinaryRule] using hτ
      cases ihx with
      | typed hxP =>
          cases ihy with
          | typed hyP =>
              exact .typed
                (PresentationDerives.binary hτP hxP hyP)

  | start hρ hx hwt ihx =>
      rcases List.mem_map.mp hρ with ⟨σ, hσ, rfl⟩
      have hσP : P.HasStartRule σ := by
        simpa [OutputTypeRefinementPresentation.HasStartRule] using hσ
      cases ihx with
      | typed hxP =>
          have hp : hwt = σ.wellTyped := Subsingleton.elim _ _
          cases hp
          exact .start σ hσP _ hxP rfl

end WorkingGrammarDerivationView

end WorkingGrammarDerivationView


section TypedDerivationInverse

variable {N : Type v} {α : Type u} {M : Type w}
variable [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {P : OutputTypeRefinementPresentation G obs}

namespace WorkingGrammarDerives

/-- A concrete-working-grammar derivation whose root is a typed nonterminal
maps back to a derivation in the finite output-type presentation. -/
theorem toPresentationDerives
    {X : TypedNonterminal G M}
    {x : Tuple α (G.arity X.base)}
    (h : DerivesTuple P.toWorkingMCFG
      (PresentationGrammarNonterminal.typed X) x) :
    PresentationDerives P X x := by
  have hv := WorkingGrammarDerivationView.ofDerives h
  cases hv with
  | typed hP => exact hP

end WorkingGrammarDerives

/-- Derivability at every typed nonterminal is exactly presentation
Derivability. -/
theorem workingGrammar_typed_derives_iff
    {X : TypedNonterminal G M}
    {x : Tuple α (G.arity X.base)} :
    DerivesTuple P.toWorkingMCFG
        (PresentationGrammarNonterminal.typed X) x ↔
      PresentationDerives P X x := by
  constructor
  · exact WorkingGrammarDerives.toPresentationDerives
  · exact PresentationDerives.toWorkingMCFG

end TypedDerivationInverse


section FreshStartInverse

variable {N : Type v} {α : Type u} {M : Type w}
variable [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {P : OutputTypeRefinementPresentation G obs}

/-- A derivation of the fresh start symbol consists of exactly one present
lifted typed start rule followed by a presentation derivation of its typed
child. -/
theorem workingGrammar_start_derives_iff
    {z : Tuple α (G.arity G.start)} :
    DerivesTuple P.toWorkingMCFG
        PresentationGrammarNonterminal.start z ↔
      ∃ σ : TypedStartRule G M,
        P.HasStartRule σ ∧
          ∃ childTuple : Tuple α (G.arity σ.baseRule.child),
            PresentationDerives P σ.child childTuple ∧
              z = castTuple σ.wellTyped childTuple := by
  constructor
  · intro h
    have hv := WorkingGrammarDerivationView.ofDerives h
    cases hv with
    | start σ hσ childTuple childDerives tuple_eq =>
        exact ⟨σ, hσ, childTuple, childDerives, tuple_eq⟩
  · rintro ⟨σ, hσ, childTuple, childDerives, rfl⟩
    exact DerivesTuple.start
      (P.liftStartRule_mem hσ)
      childDerives.toWorkingMCFG
      σ.wellTyped

end FreshStartInverse


section LanguageEquivalence

variable {N : Type v} {α : Type u} {M : Type w}
variable [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Every word generated by the concrete presentation grammar is generated by
its finite typed presentation. -/
theorem workingGrammarStringLanguage_subset_presentation
    (P : OutputTypeRefinementPresentation G obs) :
    P.toWorkingMCFG.StringLanguage ⊆
      PresentationStringLanguage P := by
  intro word hword
  rcases hword with ⟨hstart, hderives⟩
  rcases (workingGrammar_start_derives_iff
      (P := P) (z := castTuple hstart (singletonTuple word))).mp hderives with
    ⟨σ, hσ, childTuple, childDerives, tuple_eq⟩
  exact
    { startRule := σ
      start_mem := hσ
      childTuple := childTuple
      child_derives := childDerives
      start_arity := hstart
      word_eq := tuple_eq }

/-- The concrete grammar generated from a finite output-type presentation has
exactly the presentation string language. -/
theorem presentationStringLanguage_workingGrammar_eq
    (P : OutputTypeRefinementPresentation G obs) :
    P.toWorkingMCFG.StringLanguage =
      PresentationStringLanguage P := by
  apply Set.Subset.antisymm
  · exact workingGrammarStringLanguage_subset_presentation P
  · exact presentationStringLanguage_subset_workingGrammar P

/-- Symmetric orientation of the concrete-grammar/presentation-language
identity. -/
theorem presentationStringLanguage_eq_workingGrammar
    (P : OutputTypeRefinementPresentation G obs) :
    PresentationStringLanguage P =
      P.toWorkingMCFG.StringLanguage :=
  (presentationStringLanguage_workingGrammar_eq P).symm

/-- For a complete output-type presentation, the concrete working grammar
produces exactly the original grammar language. -/
theorem CompleteOutputTypePresentation.workingGrammar_stringLanguage_eq_original
    (C : CompleteOutputTypePresentation G obs) :
    C.presentation.toWorkingMCFG.StringLanguage =
      G.StringLanguage := by
  calc
    C.presentation.toWorkingMCFG.StringLanguage =
        PresentationStringLanguage C.presentation :=
      presentationStringLanguage_workingGrammar_eq C.presentation
    _ = G.StringLanguage :=
      C.complete.language_eq

/-- Pointwise membership equivalence for the concrete grammar of a complete
presentation. -/
theorem CompleteOutputTypePresentation.mem_workingGrammar_iff_original
    (C : CompleteOutputTypePresentation G obs)
    {word : Word α} :
    word ∈ C.presentation.toWorkingMCFG.StringLanguage ↔
      word ∈ G.StringLanguage := by
  rw [C.workingGrammar_stringLanguage_eq_original]

end LanguageEquivalence

end MCFG
