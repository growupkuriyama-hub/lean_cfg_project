/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.StartSeparatedOutputTypeRefinementCompleteness

/-!
# ConcreteTrimmedSuccessfulPresentation.lean

This file performs the first concrete trimming step.

Starting from the full finite output-type presentation constructed from `G`
and `obs`, it keeps exactly:

* typed nonterminals admitting an explicit successful exact-once occurrence;
* typed terminal rules whose lhs admits such an occurrence;
* typed binary rules whose lhs and both children admit such occurrences;
* typed start rules whose child admits such an occurrence.

The successful-occurrence predicate is a genuine semantic predicate:

```lean
∃ x c,
  ExactSuccessfulDerivationOccurrence G X.base x c ∧
  X.Matches obs x
```

Because the full typed nonterminal and rule universes are already finite, the
trim is an actual finite `Finset.filter` construction.  Classical decidability
is used only to decide this already stated predicate on a finite set.

The main recursive theorem follows one successful derivation occurrence down a
start-free derivation and reconstructs a derivation using only rules retained
by the trim.  Under exact working conditions and start separation, every word
of the original grammar therefore has a derivation in the concretely trimmed
presentation.

Finally, every present typed nonterminal in the trim carries a proved
successful-occurrence witness, so the previously abstract
`TypedSuccessfulOccurrenceFamily` is constructed from the filter membership
proof itself.

No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section SuccessfulTypedNonterminals

variable {N : Type v} {α : Type u} {M : Type w}
variable [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

namespace TypedNonterminal

/-- A typed nonterminal is successful when one tuple of exactly its stored
output type occurs inside a successful exact-once derivation. -/
def HasSuccessfulOccurrence
    (X : TypedNonterminal G M) : Prop :=
  ∃ (x : Tuple α (G.arity X.base))
    (c : NamedSentenceContext α (G.arity X.base)),
      ExactSuccessfulDerivationOccurrence G X.base x c ∧
        X.Matches obs x

/-- The canonical typed nonterminal of a successfully occurring tuple is
successful. -/
theorem hasSuccessfulOccurrence_of_occurrence
    {A : N}
    {x : Tuple α (G.arity A)}
    {c : NamedSentenceContext α (G.arity A)}
    (O : ExactSuccessfulDerivationOccurrence G A x c) :
    (TypedNonterminal.ofTuple obs A x).HasSuccessfulOccurrence :=
  ⟨x, c, O, TypedNonterminal.matches_ofTuple obs A x⟩

/-- A successful occurrence together with a matching proof establishes
success for an arbitrary typed nonterminal. -/
theorem hasSuccessfulOccurrence_of_matches
    (X : TypedNonterminal G M)
    {x : Tuple α (G.arity X.base)}
    {c : NamedSentenceContext α (G.arity X.base)}
    (O : ExactSuccessfulDerivationOccurrence G X.base x c)
    (hx : X.Matches obs x) :
    X.HasSuccessfulOccurrence :=
  ⟨x, c, O, hx⟩

end TypedNonterminal

end SuccessfulTypedNonterminals


section ConcreteSuccessfulTrim

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

namespace ConcreteSuccessfulOutputTypeRefinement

/-- The finite set of all successful output-typed nonterminals. -/
noncomputable def successfulNonterminals :
    Finset (TypedNonterminal G M) := by
  classical
  exact
    (allTypedNonterminals (G := G) (M := M)).filter
      TypedNonterminal.HasSuccessfulOccurrence

/-- The finite set of typed terminal rules whose typed lhs is successful. -/
noncomputable def successfulTerminalRules
    (hworking : G.BasicWorkingConditions) :
    Finset (TypedTerminalRule G) := by
  classical
  exact
    (ConcreteOutputTypeRefinement.allTypedTerminalRules
      (G := G) hworking).filter
        (fun τ =>
          (τ.lhs obs).HasSuccessfulOccurrence)

/-- The finite set of typed binary rules whose two children and lhs are all
successful. -/
noncomputable def successfulBinaryRules :
    Finset (TypedBinaryRule G M) := by
  classical
  exact
    (ConcreteOutputTypeRefinement.allTypedBinaryRules
      (G := G) (M := M)).filter
        (fun τ =>
          τ.left.HasSuccessfulOccurrence ∧
            τ.right.HasSuccessfulOccurrence ∧
              (τ.lhs obs).HasSuccessfulOccurrence)

/-- The finite set of typed start rules whose typed child is successful. -/
noncomputable def successfulStartRules
    (hworking : G.BasicWorkingConditions) :
    Finset (TypedStartRule G M) := by
  classical
  exact
    (ConcreteOutputTypeRefinement.allTypedStartRules
      (G := G) hworking).filter
        (fun σ =>
          σ.child.HasSuccessfulOccurrence)

/-- The concrete successful trim of the full finite output-type
presentation. -/
noncomputable def presentation
    (hworking : G.BasicWorkingConditions) :
    OutputTypeRefinementPresentation G obs := by
  classical
  exact
    { nonterminals :=
        successfulNonterminals (G := G) (obs := obs)

      terminalRules :=
        successfulTerminalRules (G := G) (obs := obs) hworking

      binaryRules :=
        successfulBinaryRules (G := G) (obs := obs)

      startRules :=
        successfulStartRules (G := G) (obs := obs) hworking

      terminal_lhs_mem := by
        intro τ hτ
        have hs :
            (τ.lhs obs).HasSuccessfulOccurrence :=
          (Finset.mem_filter.mp hτ).2
        apply Finset.mem_filter.mpr
        exact
          ⟨mem_allTypedNonterminals
              (G := G) (M := M) (τ.lhs obs),
            hs⟩

      binary_lhs_mem := by
        intro τ hτ
        have hs :
            (τ.lhs obs).HasSuccessfulOccurrence :=
          (Finset.mem_filter.mp hτ).2.2.2
        apply Finset.mem_filter.mpr
        exact
          ⟨mem_allTypedNonterminals
              (G := G) (M := M) (τ.lhs obs),
            hs⟩

      binary_left_mem := by
        intro τ hτ
        have hs :
            τ.left.HasSuccessfulOccurrence :=
          (Finset.mem_filter.mp hτ).2.1
        apply Finset.mem_filter.mpr
        exact
          ⟨mem_allTypedNonterminals
              (G := G) (M := M) τ.left,
            hs⟩

      binary_right_mem := by
        intro τ hτ
        have hs :
            τ.right.HasSuccessfulOccurrence :=
          (Finset.mem_filter.mp hτ).2.2.1
        apply Finset.mem_filter.mpr
        exact
          ⟨mem_allTypedNonterminals
              (G := G) (M := M) τ.right,
            hs⟩

      start_child_mem := by
        intro σ hσ
        have hs :
            σ.child.HasSuccessfulOccurrence :=
          (Finset.mem_filter.mp hσ).2
        apply Finset.mem_filter.mpr
        exact
          ⟨mem_allTypedNonterminals
              (G := G) (M := M) σ.child,
            hs⟩ }

/-- Membership in the successful nonterminal set is exactly successful
occurrence. -/
theorem hasNonterminal_iff
    (hworking : G.BasicWorkingConditions)
    (X : TypedNonterminal G M) :
    (presentation (G := G) (obs := obs) hworking).HasNonterminal X ↔
      X.HasSuccessfulOccurrence := by
  classical
  simp [presentation, successfulNonterminals,
    OutputTypeRefinementPresentation.HasNonterminal,
    mem_allTypedNonterminals]

/-- A canonical terminal rule is retained whenever its lhs has the supplied
successful occurrence. -/
theorem canonicalTerminalRule_mem
    (hworking : G.ExactWorkingConditions)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    {c :
      NamedSentenceContext α
        (G.arity ρ.lhs)}
    (O :
      ExactSuccessfulDerivationOccurrence G ρ.lhs
        (castTuple
          (hworking.basic.2.2.1 ρ hρ).symm
          ρ.outputTuple)
        c) :
    (presentation (G := G) (obs := obs) hworking.basic).
      HasTerminalRule
        (ConcreteOutputTypeRefinement.canonicalTerminalRule
          hworking.basic ρ hρ) := by
  classical
  let τ :=
    ConcreteOutputTypeRefinement.canonicalTerminalRule
      hworking.basic ρ hρ
  apply Finset.mem_filter.mpr
  refine
    ⟨ConcreteOutputTypeRefinement.canonicalTerminalRule_mem
        hworking.basic ρ hρ,
      ?_⟩
  exact
    TypedNonterminal.hasSuccessfulOccurrence_of_matches
      (τ.lhs obs)
      O
      (τ.cast_outputTuple_matches_lhs obs)

/-- A canonical binary rule is retained whenever the parent occurrence and the
two induced child occurrences are successful. -/
theorem canonicalBinaryRule_mem
    (hworking : G.ExactWorkingConditions)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules)
    {x : Tuple α (G.arity ρ.left)}
    {y : Tuple α (G.arity ρ.right)}
    {parentContext :
      NamedSentenceContext α (G.arity ρ.lhs)}
    (parentOccurrence :
      ExactSuccessfulDerivationOccurrence G ρ.lhs
        (ρ.apply x y) parentContext)
    (leftOccurrence :
      ExactSuccessfulDerivationOccurrence G ρ.left x
        (ExactSplicing.leftContextNSC
          parentContext ρ.body
          (hworking.2 ρ hρ).2.1 y))
    (rightOccurrence :
      ExactSuccessfulDerivationOccurrence G ρ.right y
        (ExactSplicing.rightContextNSC
          parentContext ρ.body
          (hworking.2 ρ hρ).2.2 x)) :
    (presentation (G := G) (obs := obs) hworking.basic).
      HasBinaryRule
        (ConcreteOutputTypeRefinement.canonicalBinaryRule
          ρ hρ (tupleType obs x) (tupleType obs y)) := by
  classical
  let τ :=
    ConcreteOutputTypeRefinement.canonicalBinaryRule
      ρ hρ (tupleType obs x) (tupleType obs y)
  apply Finset.mem_filter.mpr
  refine
    ⟨ConcreteOutputTypeRefinement.canonicalBinaryRule_mem
        ρ hρ (tupleType obs x) (tupleType obs y),
      ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [τ,
      ConcreteOutputTypeRefinement.canonicalBinaryRule,
      TypedBinaryRule.left,
      TypedNonterminal.ofTuple] using
      TypedNonterminal.hasSuccessfulOccurrence_of_occurrence
        (obs := obs) leftOccurrence
  · simpa [τ,
      ConcreteOutputTypeRefinement.canonicalBinaryRule,
      TypedBinaryRule.right,
      TypedNonterminal.ofTuple] using
      TypedNonterminal.hasSuccessfulOccurrence_of_occurrence
        (obs := obs) rightOccurrence
  · exact
      TypedNonterminal.hasSuccessfulOccurrence_of_matches
        (τ.lhs obs)
        parentOccurrence
        (τ.apply_matches_lhs obs rfl rfl)

/-- A canonical start rule is retained whenever its child has the supplied
successful occurrence. -/
theorem canonicalStartRule_mem
    (hworking : G.ExactWorkingConditions)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    {x : Tuple α (G.arity ρ.child)}
    {c : NamedSentenceContext α (G.arity ρ.child)}
    (O :
      ExactSuccessfulDerivationOccurrence G ρ.child x c) :
    (presentation (G := G) (obs := obs) hworking.basic).
      HasStartRule
        (ConcreteOutputTypeRefinement.canonicalStartRule
          hworking.basic ρ hρ (tupleType obs x)) := by
  classical
  let σ :=
    ConcreteOutputTypeRefinement.canonicalStartRule
      hworking.basic ρ hρ (tupleType obs x)
  apply Finset.mem_filter.mpr
  refine
    ⟨ConcreteOutputTypeRefinement.canonicalStartRule_mem
        hworking.basic ρ hρ (tupleType obs x),
      ?_⟩
  simpa [σ,
    ConcreteOutputTypeRefinement.canonicalStartRule,
    TypedStartRule.child,
    TypedNonterminal.ofTuple] using
    TypedNonterminal.hasSuccessfulOccurrence_of_occurrence
      (obs := obs) O

end ConcreteSuccessfulOutputTypeRefinement

end ConcreteSuccessfulTrim


section SuccessfulTrimDerivations

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

namespace StartFreeDerives

/-- A start-free derivation equipped with a successful occurrence at its root
can be reconstructed entirely inside the concrete successful trim. -/
theorem toConcreteSuccessfulPresentation
    (hworking : G.ExactWorkingConditions)
    {A : N}
    {x : Tuple α (G.arity A)}
    (h : StartFreeDerives G A x) :
    ∀ {c : NamedSentenceContext α (G.arity A)},
      ExactSuccessfulDerivationOccurrence G A x c →
        PresentationDerives
          (ConcreteSuccessfulOutputTypeRefinement.presentation
            (G := G) (obs := obs) hworking.basic)
          (TypedNonterminal.ofTuple obs A x)
          x := by
  induction h with

  | terminal hρ hwt =>
      intro c O
      let τ :=
        ConcreteOutputTypeRefinement.canonicalTerminalRule
          hworking.basic ρ hρ
      have hp :
          hwt = hworking.basic.2.2.1 ρ hρ :=
        Subsingleton.elim _ _
      cases hp
      have hmem :
          (ConcreteSuccessfulOutputTypeRefinement.presentation
            (G := G) (obs := obs) hworking.basic).
            HasTerminalRule τ :=
        ConcreteSuccessfulOutputTypeRefinement.canonicalTerminalRule_mem
          (obs := obs) hworking ρ hρ O
      have hnode :
          τ.lhs obs =
            TypedNonterminal.ofTuple obs ρ.lhs
              (castTuple τ.wellTyped.symm
                ρ.outputTuple) :=
        TypedNonterminal.eq_of_matches
          (τ.lhs obs)
          (castTuple τ.wellTyped.symm
            ρ.outputTuple)
          (τ.cast_outputTuple_matches_lhs obs)
      rw [← hnode]
      exact PresentationDerives.terminal hmem

  | binary hρ hx hy ihx ihy =>
      intro parentContext parentOccurrence
      let leftOccurrence :
          ExactSuccessfulDerivationOccurrence G ρ.left x
            (ExactSplicing.leftContextNSC
              parentContext ρ.body
              (hworking.2 ρ hρ).2.1 y) :=
        ExactSuccessfulDerivationOccurrence.throughLeft
          hρ
          (hworking.2 ρ hρ)
          hx.toDerivesTuple
          hy.toDerivesTuple
          parentOccurrence

      let rightOccurrence :
          ExactSuccessfulDerivationOccurrence G ρ.right y
            (ExactSplicing.rightContextNSC
              parentContext ρ.body
              (hworking.2 ρ hρ).2.2 x) :=
        ExactSuccessfulDerivationOccurrence.throughRight
          hρ
          (hworking.2 ρ hρ)
          hx.toDerivesTuple
          hy.toDerivesTuple
          parentOccurrence

      have ihx' :
          PresentationDerives
            (ConcreteSuccessfulOutputTypeRefinement.presentation
              (G := G) (obs := obs) hworking.basic)
            (TypedNonterminal.ofTuple obs ρ.left x)
            x :=
        ihx leftOccurrence

      have ihy' :
          PresentationDerives
            (ConcreteSuccessfulOutputTypeRefinement.presentation
              (G := G) (obs := obs) hworking.basic)
            (TypedNonterminal.ofTuple obs ρ.right y)
            y :=
        ihy rightOccurrence

      let τ :=
        ConcreteOutputTypeRefinement.canonicalBinaryRule
          ρ hρ (tupleType obs x) (tupleType obs y)

      have hmem :
          (ConcreteSuccessfulOutputTypeRefinement.presentation
            (G := G) (obs := obs) hworking.basic).
            HasBinaryRule τ :=
        ConcreteSuccessfulOutputTypeRefinement.canonicalBinaryRule_mem
          (obs := obs) hworking ρ hρ
          parentOccurrence leftOccurrence rightOccurrence

      have ihxτ :
          PresentationDerives
            (ConcreteSuccessfulOutputTypeRefinement.presentation
              (G := G) (obs := obs) hworking.basic)
            τ.left x := by
        simpa [τ,
          ConcreteOutputTypeRefinement.canonicalBinaryRule,
          TypedBinaryRule.left,
          TypedNonterminal.ofTuple] using ihx'

      have ihyτ :
          PresentationDerives
            (ConcreteSuccessfulOutputTypeRefinement.presentation
              (G := G) (obs := obs) hworking.basic)
            τ.right y := by
        simpa [τ,
          ConcreteOutputTypeRefinement.canonicalBinaryRule,
          TypedBinaryRule.right,
          TypedNonterminal.ofTuple] using ihy'

      have hparent :
          τ.lhs obs =
            TypedNonterminal.ofTuple obs ρ.lhs
              (ρ.apply x y) :=
        TypedNonterminal.eq_of_matches
          (τ.lhs obs)
          (ρ.apply x y)
          (τ.apply_matches_lhs obs rfl rfl)

      rw [← hparent]
      exact PresentationDerives.binary hmem ihxτ ihyτ

end StartFreeDerives

end SuccessfulTrimDerivations


section SuccessfulTrimCompleteness

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Every word of a start-separated exact working grammar is generated by the
concrete successful trim. -/
theorem stringLanguage_subset_concreteSuccessfulPresentation
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated) :
    G.StringLanguage ⊆
      PresentationStringLanguage
        (ConcreteSuccessfulOutputTypeRefinement.presentation
          (G := G) (obs := obs) hworking.basic) := by
  intro word hword
  let D : StartRootedStringDerives G word :=
    stringLanguage_subset_startRooted_of_startSeparated
      hworking.basic hsep hword

  have hchildDerives :
      DerivesTuple G D.startRule.child D.childTuple :=
    D.child_derives.toDerivesTuple

  have hstartDerives :
      DerivesTuple G G.start
        (castTuple D.start_wellTyped D.childTuple) :=
    DerivesTuple.start
      D.start_mem
      hchildDerives
      D.start_wellTyped

  let rootOccurrence :
      ExactSuccessfulDerivationOccurrence G G.start
        (castTuple D.start_wellTyped D.childTuple)
        (startIdentityNamedContext G D.start_arity) :=
    ExactSuccessfulDerivationOccurrence.root
      D.start_arity hstartDerives

  let childOccurrence :
      ExactSuccessfulDerivationOccurrence G D.startRule.child
        D.childTuple
        (transportNamedSentenceContext
          D.start_wellTyped.symm
          (startIdentityNamedContext G D.start_arity)) :=
    ExactSuccessfulDerivationOccurrence.throughStart
      D.start_mem
      D.start_wellTyped
      hchildDerives
      rootOccurrence

  have hchild :
      PresentationDerives
        (ConcreteSuccessfulOutputTypeRefinement.presentation
          (G := G) (obs := obs) hworking.basic)
        (TypedNonterminal.ofTuple obs
          D.startRule.child D.childTuple)
        D.childTuple :=
    D.child_derives.toConcreteSuccessfulPresentation
      (obs := obs) hworking childOccurrence

  let σ :=
    ConcreteOutputTypeRefinement.canonicalStartRule
      hworking.basic
      D.startRule
      D.start_mem
      (tupleType obs D.childTuple)

  have hσmem :
      (ConcreteSuccessfulOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking.basic).
        HasStartRule σ :=
    ConcreteSuccessfulOutputTypeRefinement.canonicalStartRule_mem
      (obs := obs) hworking
      D.startRule D.start_mem childOccurrence

  have hchildσ :
      PresentationDerives
        (ConcreteSuccessfulOutputTypeRefinement.presentation
          (G := G) (obs := obs) hworking.basic)
        σ.child D.childTuple := by
    simpa [σ,
      ConcreteOutputTypeRefinement.canonicalStartRule,
      TypedStartRule.child,
      TypedNonterminal.ofTuple] using hchild

  exact
    { startRule := σ
      start_mem := hσmem
      childTuple := D.childTuple
      child_derives := hchildσ
      start_arity := D.start_arity
      word_eq := by
        have hp :
            D.start_wellTyped = σ.wellTyped :=
          Subsingleton.elim _ _
        cases hp
        exact D.word_eq }

/-- The concrete successful trim is complete for the original grammar
language. -/
def concreteSuccessfulPresentationCompleteFor
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated) :
    PresentationCompleteFor
      (ConcreteSuccessfulOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking.basic) where
  complete :=
    stringLanguage_subset_concreteSuccessfulPresentation
      (obs := obs) hworking hsep

/-- The concrete successful trim generates exactly the original language. -/
theorem concreteSuccessfulPresentation_stringLanguage_eq_original
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated) :
    PresentationStringLanguage
        (ConcreteSuccessfulOutputTypeRefinement.presentation
          (G := G) (obs := obs) hworking.basic) =
      G.StringLanguage :=
  (concreteSuccessfulPresentationCompleteFor
    (obs := obs) hworking hsep).language_eq

/-- The concrete successful trim packaged as a complete finite output-type
presentation. -/
noncomputable def concreteSuccessfulCompleteOutputTypePresentation
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated) :
    CompleteOutputTypePresentation G obs where
  presentation :=
    ConcreteSuccessfulOutputTypeRefinement.presentation
      (G := G) (obs := obs) hworking.basic
  complete :=
    concreteSuccessfulPresentationCompleteFor
      (obs := obs) hworking hsep

/-- The actual working grammar generated by the concrete successful trim is
language-equivalent to the original grammar. -/
theorem concreteSuccessfulWorkingGrammar_stringLanguage_eq_original
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated) :
    (ConcreteSuccessfulOutputTypeRefinement.presentation
      (G := G) (obs := obs) hworking.basic).
        toWorkingMCFG.StringLanguage =
      G.StringLanguage := by
  calc
    (ConcreteSuccessfulOutputTypeRefinement.presentation
      (G := G) (obs := obs) hworking.basic).
        toWorkingMCFG.StringLanguage =
        PresentationStringLanguage
          (ConcreteSuccessfulOutputTypeRefinement.presentation
            (G := G) (obs := obs) hworking.basic) :=
      presentationStringLanguage_workingGrammar_eq _
    _ = G.StringLanguage :=
      concreteSuccessfulPresentation_stringLanguage_eq_original
        (obs := obs) hworking hsep

end SuccessfulTrimCompleteness


section SuccessfulOccurrenceExtraction

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M]
variable [DecidableEq α] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Extract the concrete successful occurrence stored by membership in the
successful nonterminal filter.  Classical choice is applied only after the
filter proof has established the required existential. -/
noncomputable def concretePresentTypedSuccessfulOccurrence
    (hworking : G.ExactWorkingConditions)
    (X :
      PresentTypedNonterminal
        (ConcreteSuccessfulOutputTypeRefinement.presentation
          (G := G) (obs := obs) hworking.basic)) :
    PresentTypedSuccessfulOccurrence X := by
  classical
  have hs :
      X.node.HasSuccessfulOccurrence :=
    (ConcreteSuccessfulOutputTypeRefinement.hasNonterminal_iff
      (obs := obs) hworking.basic X.node).mp X.mem
  rcases hs with ⟨x, c, O, hx⟩
  exact
    { anchor := x
      expose := c
      occurrence := O
      anchor_matches := hx }

/-- The successful trim carries a concrete successful occurrence for every
present typed nonterminal; this family is no longer an external assumption. -/
noncomputable def concreteTypedSuccessfulOccurrenceFamily
    (hworking : G.ExactWorkingConditions) :
    TypedSuccessfulOccurrenceFamily
      (ConcreteSuccessfulOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking.basic) where
  occurrence :=
    concretePresentTypedSuccessfulOccurrence
      (obs := obs) hworking

/-- The complete successful presentation together with its automatically
extracted successful-occurrence family. -/
noncomputable def concreteSuccessfulOccurrenceCompletePresentation
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated) :
    SuccessfulOccurrenceCompletePresentation G obs where
  completePresentation :=
    concreteSuccessfulCompleteOutputTypePresentation
      (obs := obs) hworking hsep
  occurrences :=
    concreteTypedSuccessfulOccurrenceFamily
      (obs := obs) hworking

/-- The witness-bearing trimmed presentation is now constructed directly from
`G`, `obs`, exact working conditions, start separation, and finite `N` and
`M`. -/
noncomputable def concreteTrimmedOutputTypePresentation
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated) :
    TrimmedOutputTypePresentation G obs :=
  (concreteSuccessfulOccurrenceCompletePresentation
    (obs := obs) hworking hsep).
      toTrimmedOutputTypePresentation

/-- Every typed nonterminal present in the concrete trim has an explicitly
extracted successful occurrence. -/
theorem concreteTrimmed_anchor_occurrence
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (X :
      PresentTypedNonterminal
        (ConcreteSuccessfulOutputTypeRefinement.presentation
          (G := G) (obs := obs) hworking.basic)) :
    ExactSuccessfulDerivationOccurrence G X.node.base
      ((concreteTrimmedOutputTypePresentation
        (obs := obs) hworking hsep).anchor X)
      ((concreteTrimmedOutputTypePresentation
        (obs := obs) hworking hsep).expose X) :=
  (concreteSuccessfulOccurrenceCompletePresentation
    (obs := obs) hworking hsep).anchor_occurrence X

end SuccessfulOccurrenceExtraction


/-!
Remaining concrete reduction target:

```lean
∀ A : N,
  ∃ X :
    PresentTypedNonterminal
      (ConcreteSuccessfulOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking.basic),
    X.node.base = A
```

This is not true for arbitrary unused base nonterminals.  The next file should
derive it from an explicit reducedness condition saying that every base
nonterminal occurs in some successful derivation.  Once that theorem is proved,
`SuccessfulOccurrenceBaseRepresentativeSelection` can be constructed by
choosing from the proved finite existential, and the existing canonical-rule
closure route can be connected without assuming a representative-selection
record.
-/

end MCFG
