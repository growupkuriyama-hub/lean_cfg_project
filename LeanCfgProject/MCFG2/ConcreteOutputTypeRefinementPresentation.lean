/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.OutputTypePresentationWorkingGrammarEquivalence

/-!
# ConcreteOutputTypeRefinementPresentation.lean

This file constructs the finite full output-type presentation from a grammar
and a finite observation monoid.

All typed nonterminals are enumerated.  All canonical typed terminal rules,
all typed binary rules for all pairs of child output types, and all typed start
rules for all child output types are enumerated as finite sets.

Because the current `DerivesTuple` syntax permits start rules at arbitrary
internal derivation nodes, while `PresentationDerives` intentionally contains
only terminal and binary rules, exact completeness is proved for the precise
start-rooted normal-form language: one start step at the root and no start step
below it.  The final comment records the exact remaining normalization goal for
the unrestricted original language.
-/

namespace MCFG

universe u v w

section TypedNonterminalEnumeration

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M]
variable {G : WorkingMCFG N α}

/-- Output-typed nonterminals are equivalent to the dependent sum of a base
nonterminal and one finite output vector at its arity. -/
def typedNonterminalSigmaEquiv :
    TypedNonterminal G M ≃
      Σ A : N, Fin (G.arity A) → M where
  toFun X := ⟨X.base, X.out⟩
  invFun p := { base := p.1, out := p.2 }
  left_inv X := by cases X; rfl
  right_inv p := by cases p; rfl

/-- The finite set of every output-typed nonterminal of `G`. -/
noncomputable def allTypedNonterminals :
    Finset (TypedNonterminal G M) := by
  classical
  exact
    (Finset.univ : Finset (Σ A : N, Fin (G.arity A) → M)).map
      typedNonterminalSigmaEquiv.symm.toEmbedding

/-- Every output-typed nonterminal occurs in the concrete enumeration. -/
theorem mem_allTypedNonterminals
    (X : TypedNonterminal G M) :
    X ∈ allTypedNonterminals (G := G) (M := M) := by
  classical
  apply Finset.mem_map.mpr
  refine ⟨typedNonterminalSigmaEquiv X, Finset.mem_univ _, ?_⟩
  exact typedNonterminalSigmaEquiv.symm_apply_apply X

end TypedNonterminalEnumeration


section CanonicalTypedRuleEnumeration

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

namespace ConcreteOutputTypeRefinement

/-- Canonical typed terminal rule associated with a listed original terminal
rule. -/
def canonicalTerminalRule
    (hworking : G.BasicWorkingConditions)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules) :
    TypedTerminalRule G where
  baseRule := ρ
  inGrammar := hρ
  wellTyped := hworking.2.2.1 ρ hρ

/-- Canonical typed binary rule associated with one original binary rule and a
pair of child output vectors. -/
def canonicalBinaryRule
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules)
    (leftOut : Fin (G.arity ρ.left) → M)
    (rightOut : Fin (G.arity ρ.right) → M) :
    TypedBinaryRule G M where
  baseRule := ρ
  inGrammar := hρ
  leftOut := leftOut
  rightOut := rightOut

/-- Canonical typed start rule associated with one original start rule and one
child output vector. -/
def canonicalStartRule
    (hworking : G.BasicWorkingConditions)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (childOut : Fin (G.arity ρ.child) → M) :
    TypedStartRule G M where
  baseRule := ρ
  inGrammar := hρ
  wellTyped := hworking.2.1 ρ hρ
  childOut := childOut

/-- Finite enumeration of all canonical typed terminal rules. -/
noncomputable def allTypedTerminalRules
    (hworking : G.BasicWorkingConditions) :
    Finset (TypedTerminalRule G) := by
  classical
  exact G.terminalRules.attach.toFinset.image
    (fun ρ => canonicalTerminalRule hworking ρ.1 ρ.2)

/-- Finite enumeration of every typed binary rule over every pair of finite
child output vectors. -/
noncomputable def allTypedBinaryRules :
    Finset (TypedBinaryRule G M) := by
  classical
  exact G.binaryRules.attach.toFinset.biUnion fun ρ =>
    (Finset.univ : Finset (Fin (G.arity ρ.1.left) → M)).biUnion fun leftOut =>
      (Finset.univ : Finset (Fin (G.arity ρ.1.right) → M)).image fun rightOut =>
        canonicalBinaryRule ρ.1 ρ.2 leftOut rightOut

/-- Finite enumeration of every typed start rule over every finite child output
vector. -/
noncomputable def allTypedStartRules
    (hworking : G.BasicWorkingConditions) :
    Finset (TypedStartRule G M) := by
  classical
  exact G.startRules.attach.toFinset.biUnion fun ρ =>
    (Finset.univ : Finset (Fin (G.arity ρ.1.child) → M)).image fun childOut =>
      canonicalStartRule hworking ρ.1 ρ.2 childOut

/-- Every canonical typed terminal rule occurs in the finite terminal-rule
enumeration. -/
theorem canonicalTerminalRule_mem
    (hworking : G.BasicWorkingConditions)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules) :
    canonicalTerminalRule hworking ρ hρ ∈
      allTypedTerminalRules (G := G) hworking := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨⟨ρ, hρ⟩, ?_, rfl⟩
  simp

/-- Every canonical typed binary rule occurs in the finite binary-rule
enumeration. -/
theorem canonicalBinaryRule_mem
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules)
    (leftOut : Fin (G.arity ρ.left) → M)
    (rightOut : Fin (G.arity ρ.right) → M) :
    canonicalBinaryRule ρ hρ leftOut rightOut ∈
      allTypedBinaryRules (G := G) (M := M) := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨ρ, hρ⟩, ?_, ?_⟩
  · simp
  · apply Finset.mem_biUnion.mpr
    refine ⟨leftOut, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨rightOut, Finset.mem_univ _, rfl⟩

/-- Every canonical typed start rule occurs in the finite start-rule
enumeration. -/
theorem canonicalStartRule_mem
    (hworking : G.BasicWorkingConditions)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (childOut : Fin (G.arity ρ.child) → M) :
    canonicalStartRule hworking ρ hρ childOut ∈
      allTypedStartRules (G := G) hworking := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨ρ, hρ⟩, ?_, ?_⟩
  · simp
  · apply Finset.mem_image.mpr
    exact ⟨childOut, Finset.mem_univ _, rfl⟩

end ConcreteOutputTypeRefinement

end CanonicalTypedRuleEnumeration


section ConcretePresentation

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

namespace ConcreteOutputTypeRefinement

/-- The full finite output-type-refinement presentation generated directly from
`G`, `obs`, and the finite observation monoid. -/
noncomputable def presentation
    (hworking : G.BasicWorkingConditions) :
    OutputTypeRefinementPresentation G obs where
  nonterminals := allTypedNonterminals (G := G) (M := M)
  terminalRules := allTypedTerminalRules (G := G) hworking
  binaryRules := allTypedBinaryRules (G := G) (M := M)
  startRules := allTypedStartRules (G := G) hworking

  terminal_lhs_mem := by
    intro τ hτ
    exact mem_allTypedNonterminals (G := G) (M := M) (τ.lhs obs)

  binary_lhs_mem := by
    intro τ hτ
    exact mem_allTypedNonterminals (G := G) (M := M) (τ.lhs obs)

  binary_left_mem := by
    intro τ hτ
    exact mem_allTypedNonterminals (G := G) (M := M) τ.left

  binary_right_mem := by
    intro τ hτ
    exact mem_allTypedNonterminals (G := G) (M := M) τ.right

  start_child_mem := by
    intro σ hσ
    exact mem_allTypedNonterminals (G := G) (M := M) σ.child

/-- Every output-typed nonterminal is present in the concrete presentation. -/
theorem presentation_hasNonterminal
    (hworking : G.BasicWorkingConditions)
    (X : TypedNonterminal G M) :
    (presentation (G := G) (obs := obs) hworking).HasNonterminal X :=
  mem_allTypedNonterminals X

/-- Every canonical typed terminal rule is present in the concrete
presentation. -/
theorem presentation_hasCanonicalTerminalRule
    (hworking : G.BasicWorkingConditions)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules) :
    (presentation (G := G) (obs := obs) hworking).HasTerminalRule
      (canonicalTerminalRule hworking ρ hρ) :=
  canonicalTerminalRule_mem hworking ρ hρ

/-- Every canonical typed binary rule is present in the concrete
presentation. -/
theorem presentation_hasCanonicalBinaryRule
    (hworking : G.BasicWorkingConditions)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules)
    (leftOut : Fin (G.arity ρ.left) → M)
    (rightOut : Fin (G.arity ρ.right) → M) :
    (presentation (G := G) (obs := obs) hworking).HasBinaryRule
      (canonicalBinaryRule ρ hρ leftOut rightOut) :=
  canonicalBinaryRule_mem ρ hρ leftOut rightOut

/-- Every canonical typed start rule is present in the concrete presentation. -/
theorem presentation_hasCanonicalStartRule
    (hworking : G.BasicWorkingConditions)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (childOut : Fin (G.arity ρ.child) → M) :
    (presentation (G := G) (obs := obs) hworking).HasStartRule
      (canonicalStartRule hworking ρ hρ childOut) :=
  canonicalStartRule_mem hworking ρ hρ childOut

/-- Every typed terminal rule over `G` is present: the enumeration has no
missing terminal decorations. -/
theorem presentation_hasEveryTerminalRule
    (hworking : G.BasicWorkingConditions)
    (τ : TypedTerminalRule G) :
    (presentation (G := G) (obs := obs) hworking).HasTerminalRule τ := by
  have hp :
      hworking.2.2.1 τ.baseRule τ.inGrammar = τ.wellTyped :=
    Subsingleton.elim _ _
  cases τ with
  | mk baseRule inGrammar wellTyped =>
      simp only at hp
      cases hp
      exact presentation_hasCanonicalTerminalRule
        hworking baseRule inGrammar

/-- Every typed binary rule over `G` is present: all child output-vector pairs
are enumerated. -/
theorem presentation_hasEveryBinaryRule
    (hworking : G.BasicWorkingConditions)
    (τ : TypedBinaryRule G M) :
    (presentation (G := G) (obs := obs) hworking).HasBinaryRule τ := by
  simpa [canonicalBinaryRule] using
    presentation_hasCanonicalBinaryRule
      (obs := obs) hworking τ.baseRule τ.inGrammar
        τ.leftOut τ.rightOut

/-- Every typed start rule over `G` is present: all child output vectors are
enumerated. -/
theorem presentation_hasEveryStartRule
    (hworking : G.BasicWorkingConditions)
    (σ : TypedStartRule G M) :
    (presentation (G := G) (obs := obs) hworking).HasStartRule σ := by
  have hp :
      hworking.2.1 σ.baseRule σ.inGrammar = σ.wellTyped :=
    Subsingleton.elim _ _
  cases σ with
  | mk baseRule inGrammar wellTyped childOut =>
      simp only at hp
      cases hp
      exact presentation_hasCanonicalStartRule
        hworking baseRule inGrammar childOut

end ConcreteOutputTypeRefinement

end ConcretePresentation


section StartFreeDerivations

variable {N : Type v} {α : Type u}

/-- Ordinary tuple derivations using terminal and binary rules only.

This is exactly the fragment represented by `PresentationDerives`. -/
inductive StartFreeDerives (G : WorkingMCFG N α) :
    (A : N) → Tuple α (G.arity A) → Prop where
  | terminal
      {ρ : TerminalRule N α}
      (hρ : ρ ∈ G.terminalRules)
      (hwt : G.arity ρ.lhs = 1) :
      StartFreeDerives G ρ.lhs
        (castTuple hwt.symm ρ.outputTuple)
  | binary
      {ρ : BinaryRule N α G.arity}
      (hρ : ρ ∈ G.binaryRules)
      {x : Tuple α (G.arity ρ.left)}
      {y : Tuple α (G.arity ρ.right)}
      (hx : StartFreeDerives G ρ.left x)
      (hy : StartFreeDerives G ρ.right y) :
      StartFreeDerives G ρ.lhs (ρ.apply x y)

namespace StartFreeDerives

/-- Forgetting the start-free certificate gives an ordinary grammar
derivation. -/
theorem toDerivesTuple
    {G : WorkingMCFG N α}
    {A : N}
    {x : Tuple α (G.arity A)}
    (h : StartFreeDerives G A x) :
    DerivesTuple G A x := by
  induction h with
  | terminal hρ hwt =>
      exact DerivesTuple.terminal hρ hwt
  | binary hρ hx hy ihx ihy =>
      exact DerivesTuple.binary hρ ihx ihy

end StartFreeDerives

end StartFreeDerivations


section TypedEqualityLemma

variable {N : Type v} {α : Type u} {M : Type w}
variable [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- A typed nonterminal matching a tuple is the canonical typed nonterminal of
that tuple. -/
theorem TypedNonterminal.eq_of_matches
    (X : TypedNonterminal G M)
    (x : Tuple α (G.arity X.base))
    (h : X.Matches obs x) :
    X = TypedNonterminal.ofTuple obs X.base x := by
  cases X with
  | mk base out =>
      change tupleType obs x = out at h
      cases h
      rfl

end TypedEqualityLemma


section StartFreeCompleteness

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

namespace StartFreeDerives

/-- Every start-free ordinary derivation lifts to the concrete finite
output-type presentation. -/
theorem toConcretePresentation
    (hworking : G.BasicWorkingConditions)
    {A : N}
    {x : Tuple α (G.arity A)}
    (h : StartFreeDerives G A x) :
    PresentationDerives
      (ConcreteOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking)
      (TypedNonterminal.ofTuple obs A x) x := by
  induction h with
  | terminal hρ hwt =>
      let τ := ConcreteOutputTypeRefinement.canonicalTerminalRule
        hworking ρ hρ
      have hmem :
          (ConcreteOutputTypeRefinement.presentation
            (G := G) (obs := obs) hworking).HasTerminalRule τ :=
        ConcreteOutputTypeRefinement.presentation_hasCanonicalTerminalRule
          hworking ρ hρ
      have hp : hwt = τ.wellTyped := Subsingleton.elim _ _
      cases hp
      have hnode :
          τ.lhs obs =
            TypedNonterminal.ofTuple obs ρ.lhs
              (castTuple τ.wellTyped.symm ρ.outputTuple) :=
        TypedNonterminal.eq_of_matches
          (τ.lhs obs)
          (castTuple τ.wellTyped.symm ρ.outputTuple)
          (τ.cast_outputTuple_matches_lhs obs)
      rw [← hnode]
      exact PresentationDerives.terminal hmem

  | binary hρ hx hy ihx ihy =>
      let τ := ConcreteOutputTypeRefinement.canonicalBinaryRule
        ρ hρ (tupleType obs x) (tupleType obs y)
      have hmem :
          (ConcreteOutputTypeRefinement.presentation
            (G := G) (obs := obs) hworking).HasBinaryRule τ :=
        ConcreteOutputTypeRefinement.presentation_hasCanonicalBinaryRule
          hworking ρ hρ (tupleType obs x) (tupleType obs y)
      have ihx' : PresentationDerives
          (ConcreteOutputTypeRefinement.presentation
            (G := G) (obs := obs) hworking)
          τ.left x := by
        simpa [τ, ConcreteOutputTypeRefinement.canonicalBinaryRule,
          TypedBinaryRule.left, TypedNonterminal.ofTuple] using ihx
      have ihy' : PresentationDerives
          (ConcreteOutputTypeRefinement.presentation
            (G := G) (obs := obs) hworking)
          τ.right y := by
        simpa [τ, ConcreteOutputTypeRefinement.canonicalBinaryRule,
          TypedBinaryRule.right, TypedNonterminal.ofTuple] using ihy
      have hparent :
          τ.lhs obs =
            TypedNonterminal.ofTuple obs ρ.lhs (ρ.apply x y) :=
        TypedNonterminal.eq_of_matches
          (τ.lhs obs)
          (ρ.apply x y)
          (τ.apply_matches_lhs obs rfl rfl)
      rw [← hparent]
      exact PresentationDerives.binary hmem ihx' ihy'

end StartFreeDerives

/-- Presentation derivations of the concrete full presentation erase not only
to ordinary derivations but specifically to start-free derivations. -/
theorem PresentationDerives.toStartFreeDerives
    (hworking : G.BasicWorkingConditions)
    {X : TypedNonterminal G M}
    {x : Tuple α (G.arity X.base)}
    (h : PresentationDerives
      (ConcreteOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking) X x) :
    StartFreeDerives G X.base x := by
  induction h with
  | terminal hτ =>
      exact StartFreeDerives.terminal τ.inGrammar τ.wellTyped
  | binary hτ hx hy ihx ihy =>
      exact StartFreeDerives.binary τ.inGrammar ihx ihy

end StartFreeCompleteness


section StartRootedNormalLanguage

variable {N : Type v} {α : Type u}

/-- A string derivation in start-rooted normal form: exactly one start-rule
step at the root and a start-free child derivation below it. -/
structure StartRootedStringDerives
    (G : WorkingMCFG N α)
    (word : Word α) where
  startRule : StartRule N
  start_mem : startRule ∈ G.startRules
  start_wellTyped : G.arity startRule.child = G.arity G.start
  childTuple : Tuple α (G.arity startRule.child)
  child_derives : StartFreeDerives G startRule.child childTuple
  start_arity : 1 = G.arity G.start
  word_eq :
    castTuple start_arity (singletonTuple word) =
      castTuple start_wellTyped childTuple

/-- The start-rooted normal-form language. -/
def StartRootedStringLanguage
    (G : WorkingMCFG N α) : Set (Word α) :=
  { word | StartRootedStringDerives G word }

/-- Every start-rooted normal-form derivation is an ordinary string
derivation. -/
theorem startRootedStringLanguage_subset_stringLanguage
    (G : WorkingMCFG N α) :
    StartRootedStringLanguage G ⊆ G.StringLanguage := by
  intro word D
  refine ⟨D.start_arity, ?_⟩
  rw [D.word_eq]
  exact DerivesTuple.start
    D.start_mem
    D.child_derives.toDerivesTuple
    D.start_wellTyped

end StartRootedNormalLanguage


section ConcretePresentationNormalCompleteness

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Every start-rooted normal-form string derivation is generated by the
concrete full output-type presentation. -/
theorem startRootedStringLanguage_subset_concretePresentation
    (hworking : G.BasicWorkingConditions) :
    StartRootedStringLanguage G ⊆
      PresentationStringLanguage
        (ConcreteOutputTypeRefinement.presentation
          (G := G) (obs := obs) hworking) := by
  intro word D
  let σ := ConcreteOutputTypeRefinement.canonicalStartRule
    hworking D.startRule D.start_mem
      (tupleType obs D.childTuple)
  have hσmem :
      (ConcreteOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking).HasStartRule σ :=
    ConcreteOutputTypeRefinement.presentation_hasCanonicalStartRule
      hworking D.startRule D.start_mem
        (tupleType obs D.childTuple)
  have hchild : PresentationDerives
      (ConcreteOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking)
      σ.child D.childTuple := by
    simpa [σ, ConcreteOutputTypeRefinement.canonicalStartRule,
      TypedStartRule.child, TypedNonterminal.ofTuple] using
      D.child_derives.toConcretePresentation
        (obs := obs) hworking
  have hp : D.start_wellTyped = σ.wellTyped :=
    Subsingleton.elim _ _
  cases hp
  exact
    { startRule := σ
      start_mem := hσmem
      childTuple := D.childTuple
      child_derives := hchild
      start_arity := D.start_arity
      word_eq := D.word_eq }

/-- Every string derivation of the concrete full presentation is start-rooted
and start-free below the root. -/
theorem concretePresentation_subset_startRootedStringLanguage
    (hworking : G.BasicWorkingConditions) :
    PresentationStringLanguage
        (ConcreteOutputTypeRefinement.presentation
          (G := G) (obs := obs) hworking) ⊆
      StartRootedStringLanguage G := by
  intro word D
  exact
    { startRule := D.startRule.baseRule
      start_mem := D.startRule.inGrammar
      start_wellTyped := D.startRule.wellTyped
      childTuple := D.childTuple
      child_derives := D.child_derives.toStartFreeDerives hworking
      start_arity := D.start_arity
      word_eq := D.word_eq }

/-- Exact language characterization of the concrete full output-type
presentation under the current grammar syntax. -/
theorem concretePresentation_stringLanguage_eq_startRooted
    (hworking : G.BasicWorkingConditions) :
    PresentationStringLanguage
        (ConcreteOutputTypeRefinement.presentation
          (G := G) (obs := obs) hworking) =
      StartRootedStringLanguage G := by
  apply Set.Subset.antisymm
  · exact concretePresentation_subset_startRootedStringLanguage hworking
  · exact startRootedStringLanguage_subset_concretePresentation hworking

/-- The actual concrete `WorkingMCFG` generated by the full presentation has
exactly the start-rooted normal-form language. -/
theorem concreteWorkingGrammar_stringLanguage_eq_startRooted
    (hworking : G.BasicWorkingConditions) :
    (ConcreteOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking).toWorkingMCFG.StringLanguage =
      StartRootedStringLanguage G := by
  calc
    (ConcreteOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking).toWorkingMCFG.StringLanguage =
        PresentationStringLanguage
          (ConcreteOutputTypeRefinement.presentation
            (G := G) (obs := obs) hworking) :=
      presentationStringLanguage_workingGrammar_eq _
    _ = StartRootedStringLanguage G :=
      concretePresentation_stringLanguage_eq_startRooted hworking

/-- If the original grammar language is already start-rooted normal, the
concrete full output-type presentation is complete for the original language. -/
def concretePresentationCompleteFor_of_startRooted
    (hworking : G.BasicWorkingConditions)
    (hnormal : G.StringLanguage ⊆ StartRootedStringLanguage G) :
    PresentationCompleteFor
      (ConcreteOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking) where
  complete := by
    intro word hword
    exact startRootedStringLanguage_subset_concretePresentation
      hworking (hnormal hword)

/-- Under start-rooted normalization, the concrete full presentation language
is exactly the original language. -/
theorem concretePresentation_stringLanguage_eq_original_of_startRooted
    (hworking : G.BasicWorkingConditions)
    (hnormal : G.StringLanguage ⊆ StartRootedStringLanguage G) :
    PresentationStringLanguage
        (ConcreteOutputTypeRefinement.presentation
          (G := G) (obs := obs) hworking) =
      G.StringLanguage :=
  (concretePresentationCompleteFor_of_startRooted
    (obs := obs) hworking hnormal).language_eq

/-- Under start-rooted normalization, construct a complete finite
output-type presentation directly from `G` and `obs`. -/
noncomputable def concreteCompleteOutputTypePresentation_of_startRooted
    (hworking : G.BasicWorkingConditions)
    (hnormal : G.StringLanguage ⊆ StartRootedStringLanguage G) :
    CompleteOutputTypePresentation G obs where
  presentation :=
    ConcreteOutputTypeRefinement.presentation
      (G := G) (obs := obs) hworking
  complete :=
    concretePresentationCompleteFor_of_startRooted
      (obs := obs) hworking hnormal

/-- Under start-rooted normalization, the actual concrete working grammar is
language-equivalent to the original grammar. -/
theorem concreteWorkingGrammar_stringLanguage_eq_original_of_startRooted
    (hworking : G.BasicWorkingConditions)
    (hnormal : G.StringLanguage ⊆ StartRootedStringLanguage G) :
    (ConcreteOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking).toWorkingMCFG.StringLanguage =
      G.StringLanguage := by
  calc
    (ConcreteOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking).toWorkingMCFG.StringLanguage =
        StartRootedStringLanguage G :=
      concreteWorkingGrammar_stringLanguage_eq_startRooted hworking
    _ = G.StringLanguage := by
      apply Set.Subset.antisymm
      · exact startRootedStringLanguage_subset_stringLanguage G
      · exact hnormal

end ConcretePresentationNormalCompleteness


/-!
OPEN GOAL required for unconditional `PresentationCompleteFor` under the
current syntax:

```lean
G.StringLanguage ⊆ StartRootedStringLanguage G
```

This statement is not derivable from `BasicWorkingConditions` or
`ExactWorkingConditions` as currently defined: `DerivesTuple.start` may occur
inside a derivation, and terminal or binary rules may also have `G.start` as
their left-hand side.  A start-separation / start-normal-form hypothesis or a
normalization theorem is required before replacing the final
`_of_startRooted` theorems by unconditional ones.
-/

end MCFG
