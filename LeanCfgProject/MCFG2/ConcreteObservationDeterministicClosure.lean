/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteReducedRepresentativeSelection

/-!
# ConcreteObservationDeterministicClosure.lean

`ConcreteReducedRepresentativeSelection.lean` constructs the successful trim,
one present typed representative for every base nonterminal, all canonical-rule
membership proofs, and all child endpoint equalities.

The only remaining canonical-closure obligations are the parent endpoint
equalities.  They are not consequences of ordinary reducedness: one base
nonterminal may derive successful tuples of several observation types.

This file proves that the remaining obligations follow from the precise
semantic property needed to make one representative per base nonterminal
coherent:

```lean
G.TupleTypeDeterministic obs
```

meaning that any two tuples derivable from the same base nonterminal have the
same componentwise observation type.

Under this property:

* every selected representative equals the canonical typed nonterminal of any
  derivable tuple at its base;
* terminal lhs representatives equal canonical terminal lhs nodes;
* binary lhs representatives equal canonical binary lhs nodes;
* the selected start representative equals every canonical typed start parent.

Hence the complete canonical-rule-closure object is constructed, and the
existing exact-once route yields a concrete finite positive characteristic
sample, exact reconstruction, eventual prefix exactness, and Gold
identification.

No parent endpoint equality is supplied as a record field.
-/

namespace MCFG

universe u v w

section TupleTypeDeterminism

variable {N : Type v} {α : Type u} {M : Type w}
variable [Monoid M]

/-- Every tuple derivable from a fixed base nonterminal has one determined
componentwise observation type. -/
def WorkingMCFG.TupleTypeDeterministic
    (G : WorkingMCFG N α)
    (obs : α → M) : Prop :=
  ∀ (A : N)
    (x y : Tuple α (G.arity A)),
      DerivesTuple G A x →
      DerivesTuple G A y →
        tupleType obs x = tupleType obs y

namespace WorkingMCFG.TupleTypeDeterministic

variable {G : WorkingMCFG N α} {obs : α → M}

/-- Symmetric comparison form. -/
theorem eq_of_derives
    (hdet : G.TupleTypeDeterministic obs)
    {A : N}
    {x y : Tuple α (G.arity A)}
    (hx : DerivesTuple G A x)
    (hy : DerivesTuple G A y) :
    tupleType obs x = tupleType obs y :=
  hdet A x y hx hy

/-- Every derivable tuple has the same observation type as the productive
anchor selected by successful reducedness. -/
theorem eq_reduced_anchor
    (hdet : G.TupleTypeDeterministic obs)
    (hred : G.SuccessfullyReduced)
    {A : N}
    {x : Tuple α (G.arity A)}
    (hx : DerivesTuple G A x) :
    tupleType obs x =
      tupleType obs (hred.anchor A) :=
  hdet A x (hred.anchor A)
    hx (hred.anchor_derives A)

end WorkingMCFG.TupleTypeDeterministic

end TupleTypeDeterminism


section RepresentativeUniqueness

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M]
variable [DecidableEq α] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Under tuple-type determinism, the concrete representative selected for a
base nonterminal is the canonical typed nonterminal of every derivable tuple
at that base. -/
theorem concreteReducedPresentTypedNonterminal_node_eq_of_derives
    (hworking : G.ExactWorkingConditions)
    (hred : G.SuccessfullyReduced)
    (hdet : G.TupleTypeDeterministic obs)
    (A : N)
    {x : Tuple α (G.arity A)}
    (hx : DerivesTuple G A x) :
    (concreteReducedPresentTypedNonterminal
      (obs := obs) hworking hred A).node =
      TypedNonterminal.ofTuple obs A x := by
  apply TypedNonterminal.eq_of_matches
  exact hdet.eq_reduced_anchor hred hx

namespace ConcreteReducedRepresentativeSelection

/-- The concrete base representative equals the canonical typed node of every
derivable tuple at the same base. -/
theorem representative_node_eq_of_derives
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (hdet : G.TupleTypeDeterministic obs)
    (A : N)
    {x : Tuple α (G.arity A)}
    (hx : DerivesTuple G A x) :
    ((representatives
      (obs := obs) hworking hsep hred).rep A).node =
      TypedNonterminal.ofTuple obs A x := by
  simpa
    [representatives,
     concreteReducedBaseRepresentativeSelection]
    using
      concreteReducedPresentTypedNonterminal_node_eq_of_derives
        (obs := obs) hworking hred hdet A hx

end ConcreteReducedRepresentativeSelection

end RepresentativeUniqueness


section ParentEndpointEqualities

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M]
variable [DecidableEq α] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

namespace ConcreteReducedRepresentativeSelection

/-- Tuple-type determinism forces the selected terminal lhs representative to
be the canonical typed terminal lhs. -/
theorem terminal_lhs_rep_of_tupleTypeDeterministic
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (hdet : G.TupleTypeDeterministic obs)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    ((representatives
      (obs := obs) hworking hsep hred).rep ρ.lhs).node =
      ((representatives
        (obs := obs) hworking hsep hred).
          canonicalTerminalRule ρ hρ hwt).lhs obs := by
  let R :=
    representatives (obs := obs) hworking hsep hred
  let τ :=
    R.canonicalTerminalRule ρ hρ hwt
  let x : Tuple α (G.arity ρ.lhs) :=
    castTuple hwt.symm ρ.outputTuple

  have hx : DerivesTuple G ρ.lhs x :=
    DerivesTuple.terminal hρ hwt

  have hrep :
      (R.rep ρ.lhs).node =
        TypedNonterminal.ofTuple obs ρ.lhs x :=
    representative_node_eq_of_derives
      (obs := obs) hworking hsep hred hdet
      ρ.lhs hx

  have hlhs :
      τ.lhs obs =
        TypedNonterminal.ofTuple obs ρ.lhs x := by
    have h :=
      TypedNonterminal.eq_of_matches
        (τ.lhs obs) x
        (τ.cast_outputTuple_matches_lhs obs)
    simpa [τ, x,
      SuccessfulOccurrenceBaseRepresentativeSelection.canonicalTerminalRule]
      using h

  exact hrep.trans hlhs.symm

/-- Tuple-type determinism forces the selected binary lhs representative to be
the canonical typed parent generated from the selected child representatives. -/
theorem binary_lhs_rep_of_tupleTypeDeterministic
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (hdet : G.TupleTypeDeterministic obs)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    ((representatives
      (obs := obs) hworking hsep hred).rep ρ.lhs).node =
      ((representatives
        (obs := obs) hworking hsep hred).
          canonicalBinaryRule ρ hρ).lhs obs := by
  let R :=
    representatives (obs := obs) hworking hsep hred
  let τ :=
    R.canonicalBinaryRule ρ hρ
  let x := R.anchor ρ.left
  let y := R.anchor ρ.right
  let z := ρ.apply x y

  have hx : DerivesTuple G ρ.left x :=
    (R.baseOccurrence ρ.left).derives
  have hy : DerivesTuple G ρ.right y :=
    (R.baseOccurrence ρ.right).derives
  have hz : DerivesTuple G ρ.lhs z :=
    DerivesTuple.binary hρ hx hy

  have hrep :
      (R.rep ρ.lhs).node =
        TypedNonterminal.ofTuple obs ρ.lhs z :=
    representative_node_eq_of_derives
      (obs := obs) hworking hsep hred hdet
      ρ.lhs hz

  have hlhs :
      τ.lhs obs =
        TypedNonterminal.ofTuple obs ρ.lhs z := by
    have hmatch :
        (τ.lhs obs).Matches obs z :=
      τ.apply_matches_lhs obs
        (R.anchor_tupleType ρ.left)
        (R.anchor_tupleType ρ.right)
    have h :=
      TypedNonterminal.eq_of_matches
        (τ.lhs obs) z hmatch
    simpa [τ, z,
      SuccessfulOccurrenceBaseRepresentativeSelection.canonicalBinaryRule]
      using h

  exact hrep.trans hlhs.symm

/-- The parent typed node of a canonical start rule matches the tuple obtained
by transporting the selected child anchor through the start rule. -/
theorem canonicalStartRule_parent_eq_ofTuple
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    ((representatives
      (obs := obs) hworking hsep hred).
        canonicalStartRule ρ hρ hwt).parent =
      TypedNonterminal.ofTuple obs G.start
        (castTuple hwt
          ((representatives
            (obs := obs) hworking hsep hred).anchor ρ.child)) := by
  let R :=
    representatives (obs := obs) hworking hsep hred
  let σ :=
    R.canonicalStartRule ρ hρ hwt
  let x := R.anchor ρ.child
  let z := castTuple hwt x

  have hmatch :
      σ.parent.Matches obs z := by
    change
      tupleType obs (castTuple hwt x) =
        castTuple σ.wellTyped σ.childOut
    rw [tupleType_castTuple_transport]
    have hp : σ.wellTyped = hwt :=
      Subsingleton.elim _ _
    cases hp
    exact congrArg (castTuple hwt)
      (R.anchor_tupleType ρ.child)

  have h :=
    TypedNonterminal.eq_of_matches
      σ.parent z hmatch
  simpa [σ, z,
    SuccessfulOccurrenceBaseRepresentativeSelection.canonicalStartRule,
    TypedStartRule.parent]
    using h

/-- Tuple-type determinism forces the selected grammar-start representative to
be the canonical typed parent of every start rule. -/
theorem start_parent_rep_of_tupleTypeDeterministic
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (hdet : G.TupleTypeDeterministic obs)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    ((representatives
      (obs := obs) hworking hsep hred).rep G.start).node =
      ((representatives
        (obs := obs) hworking hsep hred).
          canonicalStartRule ρ hρ hwt).parent := by
  let R :=
    representatives (obs := obs) hworking hsep hred
  let x := R.anchor ρ.child
  let z := castTuple hwt x

  have hx : DerivesTuple G ρ.child x :=
    (R.baseOccurrence ρ.child).derives
  have hz : DerivesTuple G G.start z :=
    DerivesTuple.start hρ hx hwt

  have hrep :
      (R.rep G.start).node =
        TypedNonterminal.ofTuple obs G.start z :=
    representative_node_eq_of_derives
      (obs := obs) hworking hsep hred hdet
      G.start hz

  have hparent :
      (R.canonicalStartRule ρ hρ hwt).parent =
        TypedNonterminal.ofTuple obs G.start z :=
    canonicalStartRule_parent_eq_ofTuple
      (obs := obs) hworking hsep hred ρ hρ hwt

  exact hrep.trans hparent.symm

end ConcreteReducedRepresentativeSelection

end ParentEndpointEqualities


section ConcreteCanonicalClosure

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M]
variable [DecidableEq α] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

namespace ConcreteReducedRepresentativeSelection

/-- Construct the complete canonical-rule-closure object from successful
reducedness and tuple-type determinism.

The three formerly open parent endpoint fields are proved above; none is
supplied independently. -/
noncomputable def canonicalRuleClosure_of_tupleTypeDeterministic
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (hdet : G.TupleTypeDeterministic obs) :
    SuccessfulOccurrenceRepresentativeCanonicalRuleClosure
      (representatives (obs := obs) hworking hsep hred) where

  terminal_mem := by
    intro ρ hρ hwt
    exact canonicalTerminalRule_mem
      (obs := obs) hworking hsep hred ρ hρ hwt

  terminal_lhs_rep := by
    intro ρ hρ hwt
    exact terminal_lhs_rep_of_tupleTypeDeterministic
      (obs := obs) hworking hsep hred hdet ρ hρ hwt

  binary_mem := by
    intro ρ hρ
    exact canonicalBinaryRule_mem
      (obs := obs) hworking hsep hred ρ hρ

  binary_left_rep := by
    intro ρ hρ
    exact binary_left_rep
      (obs := obs) hworking hsep hred ρ hρ

  binary_right_rep := by
    intro ρ hρ
    exact binary_right_rep
      (obs := obs) hworking hsep hred ρ hρ

  binary_lhs_rep := by
    intro ρ hρ
    exact binary_lhs_rep_of_tupleTypeDeterministic
      (obs := obs) hworking hsep hred hdet ρ hρ

  start_mem := by
    intro ρ hρ hwt
    exact canonicalStartRule_mem
      (obs := obs) hworking hsep hred ρ hρ hwt

  start_child_rep := by
    intro ρ hρ hwt
    exact start_child_rep
      (obs := obs) hworking hsep hred ρ hρ hwt

  start_parent_rep := by
    intro ρ hρ hwt
    exact start_parent_rep_of_tupleTypeDeterministic
      (obs := obs) hworking hsep hred hdet ρ hρ hwt

end ConcreteReducedRepresentativeSelection

/-- The fully concrete canonical-rule-closed pre-core construction.

This removes the externally supplied complete presentation, successful
occurrence family, base representative selection, and canonical closure. -/
noncomputable def concreteObservationDeterministicPreCoreConstruction
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (hdet : G.TupleTypeDeterministic obs) :
    SuccessfulOccurrenceCanonicalRuleClosedPreCoreConstruction G obs where

  presentation :=
    ConcreteReducedRepresentativeSelection.successfulPresentation
      (obs := obs) hworking hsep

  representatives :=
    ConcreteReducedRepresentativeSelection.representatives
      (obs := obs) hworking hsep hred

  canonicalClosure :=
    ConcreteReducedRepresentativeSelection.
      canonicalRuleClosure_of_tupleTypeDeterministic
        (obs := obs) hworking hsep hred hdet

end ConcreteCanonicalClosure


section ConcreteLearningConsequences

variable {N : Type v} {α : Type u} {M : Type w}
variable [Fintype N] [Fintype M]
variable [DecidableEq α] [DecidableEq M] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

/-- The concrete finite characteristic sample generated from `G`, `obs`, exact
working conditions, start separation, successful reducedness, and tuple-type
determinism. -/
noncomputable def concreteObservationDeterministicFiniteSample
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (hdet : G.TupleTypeDeterministic obs) :
    Finset (Word α) :=
  (concreteObservationDeterministicPreCoreConstruction
    (obs := obs) hworking hsep hred hdet).
      finiteSample (f := f) hworking

/-- The concretely generated finite sample is positive. -/
theorem concreteObservationDeterministicFiniteSample_positive
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (hdet : G.TupleTypeDeterministic obs) :
    (concreteObservationDeterministicFiniteSample
      (obs := obs) (f := f)
      hworking hsep hred hdet : Set (Word α)) ⊆
      G.StringLanguage :=
  (concreteObservationDeterministicPreCoreConstruction
    (obs := obs) hworking hsep hred hdet).
      finiteSample_positive (f := f) hworking

/-- Exact reconstruction on every positive finite superset of the concretely
generated sample. -/
theorem concreteObservationDeterministic_exact_for_positive_superset
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (hdet : G.TupleTypeDeterministic obs)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {K : Finset (Word α)}
    (hSK :
      (concreteObservationDeterministicFiniteSample
        (obs := obs) (f := f)
        hworking hsep hred hdet : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    ReachableSampleStringLanguage K obs f =
      G.StringLanguage :=
  (concreteObservationDeterministicPreCoreConstruction
    (obs := obs) hworking hsep hred hdet).
      exact_for_positive_superset
        (f := f) hworking hfan hL hSK hKpos

/-- Eventual exact reconstruction on every positive text. -/
theorem concreteObservationDeterministic_prefix_exact
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (hdet : G.TupleTypeDeterministic obs)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage
            (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (concreteObservationDeterministicPreCoreConstruction
    (obs := obs) hworking hsep hred hdet).
      exact_prefix_reconstruction
        (f := f) hworking hfan hL

/-- Gold identification from the now-concrete presentation, successful trim,
representatives, and canonical rule closure. -/
theorem concreteObservationDeterministic_identifies_from_positive_text
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (hdet : G.TupleTypeDeterministic obs)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (concreteObservationDeterministicPreCoreConstruction
    (obs := obs) hworking hsep hred hdet).
      identifies_from_positive_text
        (f := f) hworking hfan hL

/-- Paper-facing identification conclusion with no supplied presentation,
successful-occurrence family, representative-selection record, output
compatibility, rule realization, or canonical-closure record. -/
theorem concreteObservationDeterministic_paper_main_theorem
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (hdet : G.TupleTypeDeterministic obs)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveIdentificationConclusion G obs :=
  (concreteObservationDeterministicPreCoreConstruction
    (obs := obs) hworking hsep hred hdet).
      exact_working_paper_main_theorem
        (f := f) hworking hfan hL

/-- Full characteristic-sample, prefix-exact, and Gold-identification package
under the concrete tuple-type-deterministic route. -/
theorem concreteObservationDeterministic_paper_conclusion_package
    (hworking : G.ExactWorkingConditions)
    (hsep : G.StartSeparated)
    (hred : G.SuccessfullyReduced)
    (hdet : G.TupleTypeDeterministic obs)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    PaperConstructiveLearningConclusionPackage G obs :=
  (concreteObservationDeterministicPreCoreConstruction
    (obs := obs) hworking hsep hred hdet).
      exact_working_paper_conclusion_package
        (f := f) hworking hfan hL

end ConcreteLearningConsequences

end MCFG
