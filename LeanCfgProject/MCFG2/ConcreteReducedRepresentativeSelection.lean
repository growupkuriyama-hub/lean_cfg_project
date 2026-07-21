/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteTrimmedSuccessfulPresentation

/-!
# ConcreteReducedRepresentativeSelection.lean

The concrete successful trim retains every output-typed nonterminal admitting a
successful exact-once occurrence.  The remaining base-representative layer has
so far been supplied as an external record.

This file constructs those representatives from the ordinary reducedness
ingredients:

* productivity: every base nonterminal derives at least one tuple;
* successful reachability: every base nonterminal has a successful derivation
  spine to the grammar start.

The key new recursive construction is

```lean
ExactSuccessfulDerivationSpine.occurrenceOfDerives
```

which combines an arbitrary derivation at the hole with a successful spine and
produces one coherent `ExactSuccessfulDerivationOccurrence`.  Thus productivity
and successful reachability are equivalent to existence of a successful
occurrence at every base nonterminal.

For a successfully reduced grammar, the canonical typed node of the selected
productive tuple is proved present in the concrete successful trim.  This gives
an actual `SuccessfulOccurrenceBaseRepresentativeSelection`, eliminating that
record as supplied data.

The file also proves all canonical typed-rule membership obligations for this
selection.  Binary left/right endpoint equalities and start-child equality are
definitionally determined by the selected representatives.  The only remaining
canonical-closure obligations are the three parent-output equalities listed at
the end of the file.
-/

namespace MCFG

universe u v w

section SpineOccurrenceEquivalence

variable {N : Type v} {α : Type u}

namespace ExactSuccessfulDerivationSpine

/-- Fill a successful derivation spine with an arbitrary genuinely derived
tuple at its hole.

Unlike `acceptsDerives`, this theorem reconstructs the full inductive
successful-occurrence witness, preserving the exact parent/child derivation
path. -/
def occurrenceOfDerives
    {G : WorkingMCFG N α}
    {A : N}
    {c : NamedSentenceContext α (G.arity A)}
    (S : ExactSuccessfulDerivationSpine G A c) :
    ∀ {x : Tuple α (G.arity A)},
      DerivesTuple G A x →
        ExactSuccessfulDerivationOccurrence G A x c :=
  match S with
  | .root hstart =>
      fun {_x} hx =>
        ExactSuccessfulDerivationOccurrence.root hstart hx

  | .throughStart hρ hwt parentSpine =>
      fun {x} hx =>
        ExactSuccessfulDerivationOccurrence.throughStart
          hρ hwt hx
          (occurrenceOfDerives parentSpine
            (DerivesTuple.start hρ hx hwt))

  | .throughLeft hρ hexact hy parentSpine =>
      fun {x} hx =>
        let parentOccurrence :=
          occurrenceOfDerives parentSpine
            (DerivesTuple.binary hρ hx hy)
        ExactSuccessfulDerivationOccurrence.throughLeft
          hρ hexact hx hy parentOccurrence

  | .throughRight hρ hexact hx parentSpine =>
      fun {y} hy =>
        let parentOccurrence :=
          occurrenceOfDerives parentSpine
            (DerivesTuple.binary hρ hx hy)
        ExactSuccessfulDerivationOccurrence.throughRight
          hρ hexact hx hy parentOccurrence
termination_by S

/-- Successful occurrence is exactly the conjunction of a tuple derivation and
a successful spine carrying the same context. -/
theorem occurrence_iff_derives_and_spine
    {G : WorkingMCFG N α}
    {A : N}
    {x : Tuple α (G.arity A)}
    {c : NamedSentenceContext α (G.arity A)} :
    ExactSuccessfulDerivationOccurrence G A x c ↔
      DerivesTuple G A x ∧
        ExactSuccessfulDerivationSpine G A c := by
  constructor
  · intro O
    exact ⟨O.derives, O.spine⟩
  · rintro ⟨hx, S⟩
    exact S.occurrenceOfDerives hx

end ExactSuccessfulDerivationSpine

end SpineOccurrenceEquivalence


section SuccessfulReducedness

variable {N : Type v} {α : Type u}

/-- Productivity of one base nonterminal. -/
def WorkingMCFG.ProductiveAt
    (G : WorkingMCFG N α)
    (A : N) : Prop :=
  ∃ x : Tuple α (G.arity A),
    DerivesTuple G A x

/-- Successful reachability of one base nonterminal, represented by an exact
derivation spine from that nonterminal occurrence to the start language. -/
def WorkingMCFG.SuccessfullyReachableAt
    (G : WorkingMCFG N α)
    (A : N) : Prop :=
  ∃ c : NamedSentenceContext α (G.arity A),
    ExactSuccessfulDerivationSpine G A c

/-- Reducedness condition used by the concrete successful trim: every base
nonterminal is productive and successfully reachable. -/
def WorkingMCFG.SuccessfullyReduced
    (G : WorkingMCFG N α) : Prop :=
  ∀ A : N,
    G.ProductiveAt A ∧
      G.SuccessfullyReachableAt A

namespace WorkingMCFG.SuccessfullyReduced

variable {G : WorkingMCFG N α}

/-- Select a productive tuple after productivity has been proved. -/
noncomputable def anchor
    (hred : G.SuccessfullyReduced)
    (A : N) :
    Tuple α (G.arity A) :=
  Classical.choose (hred A).1

/-- The selected productive tuple is genuinely derived. -/
theorem anchor_derives
    (hred : G.SuccessfullyReduced)
    (A : N) :
    DerivesTuple G A (hred.anchor A) :=
  Classical.choose_spec (hred A).1

/-- Select a successful exposing spine after successful reachability has been
proved. -/
noncomputable def expose
    (hred : G.SuccessfullyReduced)
    (A : N) :
    NamedSentenceContext α (G.arity A) :=
  Classical.choose (hred A).2

/-- The selected context is an actual successful derivation spine. -/
theorem expose_spine
    (hred : G.SuccessfullyReduced)
    (A : N) :
    ExactSuccessfulDerivationSpine G A
      (hred.expose A) :=
  Classical.choose_spec (hred A).2

/-- Combine the selected productive tuple and selected successful spine into
one coherent successful occurrence. -/
noncomputable def occurrence
    (hred : G.SuccessfullyReduced)
    (A : N) :
    ExactSuccessfulDerivationOccurrence G A
      (hred.anchor A)
      (hred.expose A) :=
  (hred.expose_spine A).occurrenceOfDerives
    (hred.anchor_derives A)

/-- Successful reducedness implies a successful occurrence at every base
nonterminal. -/
theorem exists_occurrence
    (hred : G.SuccessfullyReduced)
    (A : N) :
    ∃ (x : Tuple α (G.arity A))
      (c : NamedSentenceContext α (G.arity A)),
        ExactSuccessfulDerivationOccurrence G A x c :=
  ⟨hred.anchor A, hred.expose A, hred.occurrence A⟩

end WorkingMCFG.SuccessfullyReduced

/-- Productivity plus successful reachability is equivalent to existence of a
successful occurrence at every base nonterminal. -/
theorem successfullyReduced_iff_every_nonterminal_occurs
    {G : WorkingMCFG N α} :
    G.SuccessfullyReduced ↔
      ∀ A : N,
        ∃ (x : Tuple α (G.arity A))
          (c : NamedSentenceContext α (G.arity A)),
            ExactSuccessfulDerivationOccurrence G A x c := by
  constructor
  · intro hred A
    exact hred.exists_occurrence A
  · intro hall A
    rcases hall A with ⟨x, c, O⟩
    exact
      ⟨⟨x, O.derives⟩,
       ⟨c, O.spine⟩⟩

end SuccessfulReducedness


section ConcreteRepresentativeExtraction

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M]
variable [DecidableEq α] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- The canonical typed representative selected for a successfully reduced
base nonterminal. -/
noncomputable def concreteReducedPresentTypedNonterminal
    (hworking : G.ExactWorkingConditions)
    (hred : G.SuccessfullyReduced)
    (A : N) :
    PresentTypedNonterminal
      (ConcreteSuccessfulOutputTypeRefinement.presentation
        (G := G) (obs := obs) hworking.basic) := by
  classical
  refine
    { node :=
        TypedNonterminal.ofTuple obs A
          (hred.anchor A)
      mem := ?_ }
  apply
    (ConcreteSuccessfulOutputTypeRefinement.hasNonterminal_iff
      (obs := obs) hworking.basic _).2
  exact
    TypedNonterminal.hasSuccessfulOccurrence_of_occurrence
      (obs := obs) (hred.occurrence A)

@[simp] theorem concreteReducedPresentTypedNonterminal_base
    (hworking : G.ExactWorkingConditions)
    (hred : G.SuccessfullyReduced)
    (A : N) :
    (concreteReducedPresentTypedNonterminal
      (obs := obs) hworking hred A).node.base = A :=
  rfl

@[simp] theorem concreteReducedPresentTypedNonterminal_out
    (hworking : G.ExactWorkingConditions)
    (hred : G.SuccessfullyReduced)
    (A : N) :
    (concreteReducedPresentTypedNonterminal
      (obs := obs) hworking hred A).node.out =
      tupleType obs (hred.anchor A) :=
  rfl

/-- Every base nonterminal has a present typed representative in the concrete
successful trim. -/
theorem exists_concreteSuccessful_typed_representative
    (hworking : G.ExactWorkingConditions)
    (hred : G.SuccessfullyReduced)
    (A : N) :
    ∃ X :
      PresentTypedNonterminal
        (ConcreteSuccessfulOutputTypeRefinement.presentation
          (G := G) (obs := obs) hworking.basic),
      X.node.base = A :=
  ⟨concreteReducedPresentTypedNonterminal
      (obs := obs) hworking hred A,
    rfl⟩

/-- Construct the formerly external base-representative selection from
successful reducedness. -/
noncomputable def concreteReducedBaseRepresentativeSelection
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced) :
    SuccessfulOccurrenceBaseRepresentativeSelection
      (concreteSuccessfulOccurrenceCompletePresentation
        (G := G) (obs := obs) hworking hsep) := by
  classical
  refine
    { rep := fun A => ?_
      rep_base_eq := fun A => ?_ }
  · simpa
      [concreteSuccessfulOccurrenceCompletePresentation,
       concreteSuccessfulCompleteOutputTypePresentation]
      using
        concreteReducedPresentTypedNonterminal
          (obs := obs) hworking hred A
  · rfl

@[simp] theorem concreteReducedBaseRepresentativeSelection_rep_base
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (A : N) :
    ((concreteReducedBaseRepresentativeSelection
      (obs := obs) hworking hsep hred).rep A).node.base = A :=
  rfl

/-- The concrete reduced representative layer of the witness-bearing trimmed
presentation. -/
noncomputable def concreteReducedTrimmedBaseRepresentatives
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced) :
    TrimmedBaseRepresentatives
      (concreteTrimmedOutputTypePresentation
        (G := G) (obs := obs) hworking hsep) := by
  simpa [concreteTrimmedOutputTypePresentation] using
    (concreteReducedBaseRepresentativeSelection
      (obs := obs) hworking hsep hred).
        toTrimmedBaseRepresentatives

end ConcreteRepresentativeExtraction


section ConcreteCanonicalMembership

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M]
variable [DecidableEq α] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

namespace ConcreteReducedRepresentativeSelection

/-- Shorthand for the concretely constructed successful presentation. -/
noncomputable def successfulPresentation
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated) :
    SuccessfulOccurrenceCompletePresentation G obs :=
  concreteSuccessfulOccurrenceCompletePresentation
    (obs := obs) hworking hsep

/-- Shorthand for the concretely selected base representatives. -/
noncomputable def representatives
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced) :
    SuccessfulOccurrenceBaseRepresentativeSelection
      (successfulPresentation (obs := obs) hworking hsep) :=
  concreteReducedBaseRepresentativeSelection
    (obs := obs) hworking hsep hred

/-- Every canonical terminal rule determined by the concrete representatives
is retained by the successful trim. -/
theorem canonicalTerminalRule_mem
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    (successfulPresentation (obs := obs) hworking hsep).
      completePresentation.presentation.HasTerminalRule
        ((representatives
          (obs := obs) hworking hsep hred).
            canonicalTerminalRule ρ hρ hwt) := by
  let R :=
    representatives (obs := obs) hworking hsep hred
  have hterm :
      DerivesTuple G ρ.lhs
        (castTuple hwt.symm ρ.outputTuple) :=
    DerivesTuple.terminal hρ hwt
  have O :
      ExactSuccessfulDerivationOccurrence G ρ.lhs
        (castTuple hwt.symm ρ.outputTuple)
        (R.expose ρ.lhs) :=
    (R.baseOccurrence ρ.lhs).spine.
      occurrenceOfDerives hterm
  have hmem :=
    ConcreteSuccessfulOutputTypeRefinement.canonicalTerminalRule_mem
      (obs := obs) hworking ρ hρ O
  simpa
    [successfulPresentation,
     representatives,
     concreteSuccessfulOccurrenceCompletePresentation,
     concreteSuccessfulCompleteOutputTypePresentation,
     SuccessfulOccurrenceBaseRepresentativeSelection.canonicalTerminalRule,
     ConcreteOutputTypeRefinement.canonicalTerminalRule]
    using hmem

/-- Every canonical binary rule determined by the concrete representatives is
retained by the successful trim. -/
theorem canonicalBinaryRule_mem
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    (successfulPresentation (obs := obs) hworking hsep).
      completePresentation.presentation.HasBinaryRule
        ((representatives
          (obs := obs) hworking hsep hred).
            canonicalBinaryRule ρ hρ) := by
  let R :=
    representatives (obs := obs) hworking hsep hred
  let leftOccurrence :=
    R.baseOccurrence ρ.left
  let rightOccurrence :=
    R.baseOccurrence ρ.right
  have hparentDerives :
      DerivesTuple G ρ.lhs
        (ρ.apply
          (R.anchor ρ.left)
          (R.anchor ρ.right)) :=
    DerivesTuple.binary hρ
      leftOccurrence.derives
      rightOccurrence.derives
  let parentOccurrence :
      ExactSuccessfulDerivationOccurrence G ρ.lhs
        (ρ.apply
          (R.anchor ρ.left)
          (R.anchor ρ.right))
        (R.expose ρ.lhs) :=
    (R.baseOccurrence ρ.lhs).spine.
      occurrenceOfDerives hparentDerives
  let inducedLeft :
      ExactSuccessfulDerivationOccurrence G ρ.left
        (R.anchor ρ.left)
        (ExactSplicing.leftContextNSC
          (R.expose ρ.lhs)
          ρ.body
          (hworking.2 ρ hρ).2.1
          (R.anchor ρ.right)) :=
    ExactSuccessfulDerivationOccurrence.throughLeft
      hρ
      (hworking.2 ρ hρ)
      leftOccurrence.derives
      rightOccurrence.derives
      parentOccurrence
  let inducedRight :
      ExactSuccessfulDerivationOccurrence G ρ.right
        (R.anchor ρ.right)
        (ExactSplicing.rightContextNSC
          (R.expose ρ.lhs)
          ρ.body
          (hworking.2 ρ hρ).2.2
          (R.anchor ρ.left)) :=
    ExactSuccessfulDerivationOccurrence.throughRight
      hρ
      (hworking.2 ρ hρ)
      leftOccurrence.derives
      rightOccurrence.derives
      parentOccurrence
  have hmem :=
    ConcreteSuccessfulOutputTypeRefinement.canonicalBinaryRule_mem
      (obs := obs) hworking ρ hρ
      parentOccurrence inducedLeft inducedRight
  rw [R.anchor_tupleType ρ.left,
      R.anchor_tupleType ρ.right] at hmem
  simpa
    [successfulPresentation,
     representatives,
     concreteSuccessfulOccurrenceCompletePresentation,
     concreteSuccessfulCompleteOutputTypePresentation,
     SuccessfulOccurrenceBaseRepresentativeSelection.canonicalBinaryRule,
     ConcreteOutputTypeRefinement.canonicalBinaryRule]
    using hmem

/-- Every canonical start rule determined by the concrete representatives is
retained by the successful trim. -/
theorem canonicalStartRule_mem
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    (successfulPresentation (obs := obs) hworking hsep).
      completePresentation.presentation.HasStartRule
        ((representatives
          (obs := obs) hworking hsep hred).
            canonicalStartRule ρ hρ hwt) := by
  let R :=
    representatives (obs := obs) hworking hsep hred
  have hmem :=
    ConcreteSuccessfulOutputTypeRefinement.canonicalStartRule_mem
      (obs := obs) hworking ρ hρ
      (R.baseOccurrence ρ.child)
  rw [R.anchor_tupleType ρ.child] at hmem
  simpa
    [successfulPresentation,
     representatives,
     concreteSuccessfulOccurrenceCompletePresentation,
     concreteSuccessfulCompleteOutputTypePresentation,
     SuccessfulOccurrenceBaseRepresentativeSelection.canonicalStartRule,
     ConcreteOutputTypeRefinement.canonicalStartRule]
    using hmem

/-- The left endpoint of a canonical binary rule is definitionally the selected
left representative. -/
theorem binary_left_rep
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    ((representatives
      (obs := obs) hworking hsep hred).rep ρ.left).node =
      ((representatives
        (obs := obs) hworking hsep hred).
          canonicalBinaryRule ρ hρ).left := by
  rfl

/-- The right endpoint of a canonical binary rule is definitionally the
selected right representative. -/
theorem binary_right_rep
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    ((representatives
      (obs := obs) hworking hsep hred).rep ρ.right).node =
      ((representatives
        (obs := obs) hworking hsep hred).
          canonicalBinaryRule ρ hρ).right := by
  rfl

/-- The child endpoint of a canonical start rule is definitionally the selected
child representative. -/
theorem start_child_rep
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    ((representatives
      (obs := obs) hworking hsep hred).rep ρ.child).node =
      ((representatives
        (obs := obs) hworking hsep hred).
          canonicalStartRule ρ hρ hwt).child := by
  rfl

end ConcreteReducedRepresentativeSelection

end ConcreteCanonicalMembership


/-!
After this file the representative selection, all canonical-rule membership
fields, the binary child equalities, and the start-child equality are concrete.

The existing
`SuccessfulOccurrenceRepresentativeCanonicalRuleClosure` additionally asks for
the following three parent-output equalities:

```lean
∀ (ρ : TerminalRule N α)
  (hρ : ρ ∈ G.terminalRules)
  (hwt : G.arity ρ.lhs = 1),
  (R.rep ρ.lhs).node =
    (R.canonicalTerminalRule ρ hρ hwt).lhs obs

∀ (ρ : BinaryRule N α G.arity)
  (hρ : ρ ∈ G.binaryRules),
  (R.rep ρ.lhs).node =
    (R.canonicalBinaryRule ρ hρ).lhs obs

∀ (ρ : StartRule N)
  (hρ : ρ ∈ G.startRules)
  (hwt : G.arity ρ.child = G.arity G.start),
  (R.rep G.start).node =
    (R.canonicalStartRule ρ hρ hwt).parent
```

These equalities do not follow from ordinary reducedness: one base
nonterminal may derive successfully occurring tuples of several different
observation types.  The next construction must either select a coherent
rule-closed family of typed representatives or replace the one-representative
pre-core by a typed-indexed pre-core.
-/

end MCFG
