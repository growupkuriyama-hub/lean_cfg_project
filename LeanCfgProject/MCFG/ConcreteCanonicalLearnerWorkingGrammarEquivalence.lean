/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarConstruction

/-!
# ConcreteCanonicalLearnerWorkingGrammarEquivalence.lean

This file proves the reverse inclusion for the concrete cut-saturated
`WorkingMCFG`.

Every derivation of the constructed grammar has one exact inverse view:

* at `seed`, the derived tuple is the dummy singleton;
* at `control X`, it is obtained from `X.tuple` by a cut-normal finite-object
  derivation;
* at `start`, it is obtained from one observed sample singleton by a cut-normal
  finite-object derivation.

The binary-rule inversion separates the three finite mapped rule families:

1. constant control rules;
2. lifted corrected binary rules;
3. saturated cut rules.

The cut-rule case uses arity transport.  A saturated pair may store its two
tuple codes at propositionally equal, rather than definitionally equal,
arities.  The helper lemmas in this file transport cut-normal derivations
through that equality.

The main language theorem is:

```lean
correctedConcreteFiniteHypothesis_cutWorkingGrammar_language_eq.
```

For every chosen dummy terminal:

```lean
(H.toCutWorkingMCFG dummy).StringLanguage = H.Language.
```

Combining this theorem with the obstruction file gives the exact compilation
domain:

```lean
Nonempty WorkingGrammarRealization ↔
  K = ∅ ∨ Nonempty α.
```

Thus the additional nonempty-alphabet assumption is both sufficient and,
for nonempty samples, necessary.

No target grammar occurs in the construction.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section ArityTransport

variable {α : Type u}

/-- Bundling a tuple after arity transport gives the same dependent tuple code
as bundling the original tuple. -/
theorem FiniteObjectTupleCode.mk_castTuple_symm_eq
    {d e : Nat}
    (h : d = e)
    (x : Tuple α e) :
    FiniteObjectTupleCode.mk
        (castTuple h.symm x) =
      FiniteObjectTupleCode.mk x := by
  cases h
  rfl

/-- Cut-normal derivations transport along an equality of arities. -/
theorem CutNormalizedListedFiniteDerives.castArity
    {M : Type v}
    [Monoid M]
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    {H :
      CorrectedConcreteFiniteHypothesis
        K obs f}
    {d e : Nat}
    (hde : d = e)
    {x y : Tuple α d}
    (D :
      CutNormalizedListedFiniteDerives
        H x y) :
    CutNormalizedListedFiniteDerives
      H
      (castTuple hde x)
      (castTuple hde y) := by
  cases hde
  simpa using D

/-- Listed finite-object derivations transport along an equality of arities. -/
theorem ListedFiniteCorrectedConcreteLearnerDerives.castArity
    {M : Type v}
    [Monoid M]
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    {H :
      CorrectedConcreteFiniteHypothesis
        K obs f}
    {d e : Nat}
    (hde : d = e)
    {x y : Tuple α d}
    (D :
      ListedFiniteCorrectedConcreteLearnerDerives
        K obs f H x y) :
    ListedFiniteCorrectedConcreteLearnerDerives
      K obs f H
      (castTuple hde x)
      (castTuple hde y) := by
  cases hde
  simpa using D

end ArityTransport


section DerivationInverseView

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Exact inverse view of a derivation in the concrete cut-saturated grammar. -/
inductive CorrectedConcreteCutWorkingGrammarDerivationView
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    (A :
      CorrectedConcreteCutGrammarNonterminal H) →
    Tuple α
      ((H.toCutWorkingMCFG dummy).arity A) →
    Prop where

  | seed
      (tuple_eq :
        x =
          correctedConcreteCutSeedTuple
            dummy) :
      CorrectedConcreteCutWorkingGrammarDerivationView
        H dummy
        (.seed :
          CorrectedConcreteCutGrammarNonterminal H)
        x

  | control
      (X : FiniteObjectControlCode H)
      {x : Tuple α X.1.arity}
      (derives :
        CutNormalizedListedFiniteDerives
          H X.1.tuple x) :
      CorrectedConcreteCutWorkingGrammarDerivationView
        H dummy
        (.control X)
        x

  | start
      (sampleWord : K.attach)
      {x : Tuple α 1}
      (derives :
        CutNormalizedListedFiniteDerives
          H
          (singletonTuple sampleWord.1)
          x) :
      CorrectedConcreteCutWorkingGrammarDerivationView
        H dummy
        (.start :
          CorrectedConcreteCutGrammarNonterminal H)
        x

namespace CorrectedConcreteCutWorkingGrammarDerivationView

variable
  {H :
    CorrectedConcreteFiniteHypothesis
      K obs f}
variable
  {dummy : α}

/-- Extract the cut-normal derivation from a view at a specified control node.
Proof irrelevance removes any difference between the two control-membership
proofs. -/
theorem controlNode_derives
    (X : FiniteObjectTupleCode α)
    (hX : H.IsControlCode X)
    {x : Tuple α X.arity}
    (V :
      CorrectedConcreteCutWorkingGrammarDerivationView
        H dummy
        (correctedConcreteControlNode
          H X hX)
        x) :
    CutNormalizedListedFiniteDerives
      H X.tuple x := by
  cases V with
  | control X' D =>
      simpa [
        correctedConcreteControlNode
      ] using D

/-- Extract the exact tuple equation from a seed-node view. -/
theorem seed_tuple_eq
    {x : Tuple α 1}
    (V :
      CorrectedConcreteCutWorkingGrammarDerivationView
        H dummy
        (.seed :
          CorrectedConcreteCutGrammarNonterminal H)
        x) :
    x =
      correctedConcreteCutSeedTuple
        dummy := by
  cases V with
  | seed h =>
      exact h

end CorrectedConcreteCutWorkingGrammarDerivationView

end DerivationInverseView


section DerivationInversion

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}
variable
  {H :
    CorrectedConcreteFiniteHypothesis
      K obs f}
variable
  {dummy : α}

namespace CorrectedConcreteCutWorkingGrammarDerivationView

/-- Reverse every derivation of the concrete cut-saturated grammar. -/
theorem ofDerives
    {A :
      CorrectedConcreteCutGrammarNonterminal H}
    {x :
      Tuple α
        ((H.toCutWorkingMCFG dummy).arity A)}
    (h :
      DerivesTuple
        (H.toCutWorkingMCFG dummy)
        A x) :
    CorrectedConcreteCutWorkingGrammarDerivationView
      H dummy A x := by

  induction h with

  | terminal hρ hwt =>
      change
        ρ ∈
          [correctedConcreteCutSeedRule
            H dummy] at hρ

      simp only [List.mem_singleton] at hρ
      subst ρ

      have hp :
          hwt =
            (rfl :
              (H.toCutWorkingMCFG dummy).arity
                  (correctedConcreteCutSeedRule
                    H dummy).lhs =
                1) :=
        Subsingleton.elim _ _

      cases hp

      exact .seed rfl

  | binary hρ hx hy ihx ihy =>
      change
        ρ ∈
          H.controlCodes.attach.toList.map
              (correctedConcreteCutConstantRule H) ++
            (H.binaryRuleCodes.attach.toList.map
                (correctedConcreteCutLiftedBinaryRule H) ++
              H.cutPairs.attach.toList.map
                (correctedConcreteCutSaturationRule H))
        at hρ

      rw [List.mem_append] at hρ

      rcases hρ with hconstant | hrest

      · rcases List.mem_map.mp hconstant with
          ⟨X, hX, rfl⟩

        rw [
          correctedConcreteCutConstantRule_apply
        ]

        exact
          .control X
            (CutNormalizedListedFiniteDerives.self
              X.1 X.2)

      · rw [List.mem_append] at hrest

        rcases hrest with hlifted | hcut

        · rcases List.mem_map.mp hlifted with
            ⟨B, hB, rfl⟩

          have hleft :
              CutNormalizedListedFiniteDerives
                H B.1.leftSource _ :=
            ihx.controlNode_derives
              B.1.leftSourceCode
              (H.binaryLeftSource_control
                B.1 B.2)

          have hright :
              CutNormalizedListedFiniteDerives
                H B.1.rightSource _ :=
            ihy.controlNode_derives
              B.1.rightSourceCode
              (H.binaryRightSource_control
                B.1 B.2)

          exact
            .control
              ⟨B.1.sourceCode,
                H.binarySource_control
                  B.1 B.2⟩
              (CutNormalizedListedFiniteDerives.binary
                B.1 B.2 hleft hright)

        · rcases List.mem_map.mp hcut with
            ⟨p, hp, rfl⟩

          let harity :
              p.1.1.arity =
                p.1.2.arity :=
            H.cutPairArityEq p

          have hchild :
              CutNormalizedListedFiniteDerives
                H p.1.2.tuple _ :=
            ihx.controlNode_derives
              p.1.2
              (H.cutPair_target_control
                p.2)

          have hchildCast :
              CutNormalizedListedFiniteDerives
                H
                (castTuple
                  harity.symm
                  p.1.2.tuple)
                (castTuple
                  harity.symm
                  _) :=
            hchild.castArity
              harity.symm

          have hmiddleControl :
              H.IsControlCode
                (FiniteObjectTupleCode.mk
                  (castTuple
                    harity.symm
                    p.1.2.tuple)) := by
            rw [
              FiniteObjectTupleCode.mk_castTuple_symm_eq
                harity p.1.2.tuple
            ]
            exact
              H.cutPair_target_control
                p.2

          have hnormalized :
              CutNormalizedListedFiniteDerives
                H p.1.1.tuple
                (castTuple
                  harity.symm
                  _) :=
            CutNormalizedListedFiniteDerives.cut
              (H.cutPair_source_control
                p.2)
              hmiddleControl
              (H.cutPairDerives p)
              hchildCast

          exact
            .control
              ⟨p.1.1,
                H.cutPair_source_control
                  p.2⟩
              hnormalized

  | start hρ hx hwt ihx =>
      change
        ρ ∈
          K.attach.toList.map
            (correctedConcreteCutStartRule H)
        at hρ

      rcases List.mem_map.mp hρ with
        ⟨sampleWord, hsampleWord, rfl⟩

      have hchild :
          CutNormalizedListedFiniteDerives
            H
            (singletonTuple sampleWord.1)
            _ :=
        ihx.controlNode_derives
          (FiniteObjectTupleCode.ofWord
            sampleWord.1)
          (H.word_control
            sampleWord.2)

      have hp :
          hwt =
            (rfl :
              (H.toCutWorkingMCFG dummy).arity
                  (correctedConcreteCutStartRule
                    H sampleWord).child =
                (H.toCutWorkingMCFG dummy).arity
                  (H.toCutWorkingMCFG dummy).start) :=
        Subsingleton.elim _ _

      cases hp

      exact
        .start sampleWord hchild

end CorrectedConcreteCutWorkingGrammarDerivationView

end DerivationInversion


section NodewiseInverseTheorems

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}
variable
  {H :
    CorrectedConcreteFiniteHypothesis
      K obs f}
variable
  {dummy : α}

/-- A derivation at one control nonterminal maps back to a cut-normal
finite-object derivation. -/
theorem cutWorkingGrammar_control_derives_toCutNormalized
    (X : FiniteObjectTupleCode α)
    (hX : H.IsControlCode X)
    {x : Tuple α X.arity}
    (h :
      DerivesTuple
        (H.toCutWorkingMCFG dummy)
        (correctedConcreteControlNode
          H X hX)
        x) :
    CutNormalizedListedFiniteDerives
      H X.tuple x := by
  exact
    (CorrectedConcreteCutWorkingGrammarDerivationView.ofDerives
      h).controlNode_derives X hX

/-- Derivability at every control nonterminal is exactly cut-normal
derivability from its stored control tuple. -/
theorem cutWorkingGrammar_control_derives_iff
    (X : FiniteObjectTupleCode α)
    (hX : H.IsControlCode X)
    {x : Tuple α X.arity} :
    DerivesTuple
        (H.toCutWorkingMCFG dummy)
        (correctedConcreteControlNode
          H X hX)
        x ↔
      CutNormalizedListedFiniteDerives
        H X.tuple x := by
  constructor

  · exact
      cutWorkingGrammar_control_derives_toCutNormalized
        X hX

  · intro D

    have hgrammar :=
      D.toCutWorkingMCFG dummy

    simpa [
      correctedConcreteControlNode
    ] using hgrammar

/-- A derivation of the seed nonterminal produces exactly the dummy singleton
tuple. -/
theorem cutWorkingGrammar_seed_derives_iff
    {x : Tuple α 1} :
    DerivesTuple
        (H.toCutWorkingMCFG dummy)
        (.seed :
          CorrectedConcreteCutGrammarNonterminal H)
        x ↔
      x =
        correctedConcreteCutSeedTuple
          dummy := by
  constructor

  · intro h
    exact
      (CorrectedConcreteCutWorkingGrammarDerivationView.ofDerives
        h).seed_tuple_eq

  · intro hx
    subst x
    exact
      correctedConcreteCutSeed_derives
        H dummy

/-- A derivation at the fresh grammar start is exactly a cut-normal derivation
from one observed sample singleton. -/
theorem cutWorkingGrammar_start_derives_iff
    {x : Tuple α 1} :
    DerivesTuple
        (H.toCutWorkingMCFG dummy)
        (.start :
          CorrectedConcreteCutGrammarNonterminal H)
        x ↔
      ∃ sampleWord : K.attach,
        CutNormalizedListedFiniteDerives
          H
          (singletonTuple sampleWord.1)
          x := by
  constructor

  · intro h

    have V :=
      CorrectedConcreteCutWorkingGrammarDerivationView.ofDerives
        h

    cases V with
    | start sampleWord D =>
        exact ⟨sampleWord, D⟩

  · rintro ⟨sampleWord, D⟩

    have hchild :=
      D.toCutWorkingMCFG dummy

    exact
      DerivesTuple.start
        (H.cutStartRule_mem
          dummy sampleWord)
        hchild
        rfl

end NodewiseInverseTheorems


section ReverseLanguageInclusion

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Every word generated by the concrete cut-saturated grammar belongs to the
listed finite-object language. -/
theorem cutWorkingGrammarStringLanguage_subset_finiteHypothesis
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    (H.toCutWorkingMCFG
        dummy).StringLanguage ⊆
      H.Language := by

  intro word hword

  rcases hword with
    ⟨hstart, hderives⟩

  have hp :
      hstart =
        (rfl :
          1 =
            (H.toCutWorkingMCFG dummy).arity
              (H.toCutWorkingMCFG dummy).start) :=
    Subsingleton.elim _ _

  cases hp

  rcases
      (cutWorkingGrammar_start_derives_iff
        (H := H)
        (dummy := dummy)).mp hderives with
    ⟨sampleWord, hnormalized⟩

  exact
    { startWord :=
        sampleWord.1
      start_mem :=
        sampleWord.2
      derives :=
        hnormalized.toListed }

/-- Exact language equivalence between the concrete working grammar and the
actual listed finite learner object. -/
theorem correctedConcreteFiniteHypothesis_cutWorkingGrammar_language_eq
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    (H.toCutWorkingMCFG
        dummy).StringLanguage =
      H.Language := by
  apply Set.Subset.antisymm

  · exact
      cutWorkingGrammarStringLanguage_subset_finiteHypothesis
        H dummy

  · exact
      correctedConcreteFiniteHypothesis_language_subset_cutWorkingGrammar
        H dummy

/-- Symmetric orientation of the exact compilation theorem. -/
theorem correctedConcreteFiniteHypothesis_language_eq_cutWorkingGrammar
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    H.Language =
      (H.toCutWorkingMCFG
        dummy).StringLanguage :=
  (H.cutWorkingGrammar_language_eq
    dummy).symm

/-- Canonical finite learner object version of the exact compilation theorem. -/
theorem correctedConcreteCanonicalFiniteHypothesis_cutWorkingGrammar_language_eq
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    ((correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG
          dummy).StringLanguage =
      (correctedConcreteFiniteHypothesis
        K obs f).Language :=
  correctedConcreteFiniteHypothesis_cutWorkingGrammar_language_eq
    (correctedConcreteFiniteHypothesis
      K obs f)
    dummy

/-- The compiled working grammar also has exactly the previously verified
corrected concrete canonical learner language. -/
theorem correctedConcreteCanonicalFiniteHypothesis_cutWorkingGrammar_eq_corrected
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    ((correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG
          dummy).StringLanguage =
      CorrectedConcreteCanonicalLearnerLanguage
        K obs f := by
  rw [
    correctedConcreteCanonicalFiniteHypothesis_cutWorkingGrammar_language_eq,
    CorrectedConcreteFiniteHypothesis.language_eq_corrected
  ]

/-- The compiled working grammar also has exactly the exact-once reachable
sample language. -/
theorem correctedConcreteCanonicalFiniteHypothesis_cutWorkingGrammar_eq_exactReachable
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    ((correctedConcreteFiniteHypothesis
        K obs f).toCutWorkingMCFG
          dummy).StringLanguage =
      ExactReachableSampleStringLanguage
        K obs f := by
  rw [
    correctedConcreteCanonicalFiniteHypothesis_cutWorkingGrammar_language_eq,
    CorrectedConcreteFiniteHypothesis.language_eq_exactReachable
  ]

end ReverseLanguageInclusion


section RealizationConstruction

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Realization of one finite learner object by the concrete cut-saturated
working grammar, given a selected dummy terminal. -/
noncomputable def correctedConcreteFiniteHypothesis_cutWorkingGrammarRealization
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (dummy : α) :
    CorrectedConcreteFiniteObjectWorkingGrammarRealization
      K obs f where

  Nonterminal :=
    CorrectedConcreteCutGrammarNonterminal H

  grammar :=
    H.toCutWorkingMCFG dummy

  language_eq :=
    H.cutWorkingGrammar_language_eq
      dummy

/-- A nonempty terminal alphabet is sufficient for realization of every finite
learner object. -/
noncomputable def correctedConcreteFiniteHypothesis_workingGrammarRealization_of_nonempty
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (hα : Nonempty α) :
    CorrectedConcreteFiniteObjectWorkingGrammarRealization
      K obs f :=
  H.cutWorkingGrammarRealization
    (Classical.choice hα)

/-- Canonical finite learner object realization under a nonempty-alphabet
hypothesis. -/
noncomputable def correctedConcreteCanonicalFiniteHypothesis_workingGrammarRealization
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (hα : Nonempty α) :
    CorrectedConcreteFiniteObjectWorkingGrammarRealization
      K obs f :=
  (correctedConcreteFiniteHypothesis
    K obs f).workingGrammarRealization_of_nonempty
      hα

end RealizationConstruction


section ExactCompilationDomain

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- The necessary compilation-domain condition is also sufficient. -/
theorem compilationDomain_implies_workingGrammarRealization
    (hdom :
      FiniteObjectWorkingGrammarCompilationDomain
        K) :
    Nonempty
      (CorrectedConcreteFiniteObjectWorkingGrammarRealization
        K obs f) := by
  classical

  rcases hdom with hK | hα

  · subst K

    exact
      ⟨emptySampleWorkingGrammarRealization
        obs f⟩

  · exact
      ⟨correctedConcreteCanonicalFiniteHypothesis_workingGrammarRealization
        K obs f hα⟩

/-- Exact characterization of when the present lightweight `WorkingMCFG`
syntax can represent the actual finite learner object. -/
theorem workingGrammarRealization_iff_compilationDomain :
    Nonempty
        (CorrectedConcreteFiniteObjectWorkingGrammarRealization
          K obs f) ↔
      FiniteObjectWorkingGrammarCompilationDomain
        K := by
  constructor

  · rintro ⟨R⟩
    exact
      workingGrammarRealization_implies_compilationDomain
        R

  · exact
      compilationDomain_implies_workingGrammarRealization

/-- Expanded form of the exact compilation-domain theorem. -/
theorem workingGrammarRealization_iff_emptySample_or_nonemptyAlphabet :
    Nonempty
        (CorrectedConcreteFiniteObjectWorkingGrammarRealization
          K obs f) ↔
      K = ∅ ∨ Nonempty α :=
  workingGrammarRealization_iff_compilationDomain

end ExactCompilationDomain


section PaperFacingCompilationPackage

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Paper-facing exact compiler package for nonempty terminal alphabets. -/
theorem correctedConcreteFiniteHypothesis_workingGrammar_compilation_package
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (hα : Nonempty α) :
    ∃ N : Type (max u v),
      ∃ G : WorkingMCFG N α,
        G.StringLanguage =
            (correctedConcreteFiniteHypothesis
              K obs f).Language ∧
          G.StringLanguage =
            CorrectedConcreteCanonicalLearnerLanguage
              K obs f ∧
          G.StringLanguage =
            ExactReachableSampleStringLanguage
              K obs f := by

  let H :=
    correctedConcreteFiniteHypothesis
      K obs f

  let dummy :=
    Classical.choice hα

  refine
    ⟨CorrectedConcreteCutGrammarNonterminal H,
      H.toCutWorkingMCFG dummy,
      ?_,
      ?_,
      ?_⟩

  · exact
      H.cutWorkingGrammar_language_eq
        dummy

  · exact
      correctedConcreteCanonicalFiniteHypothesis_cutWorkingGrammar_eq_corrected
        K obs f dummy

  · exact
      correctedConcreteCanonicalFiniteHypothesis_cutWorkingGrammar_eq_exactReachable
        K obs f dummy

/-- Final exact construction-and-obstruction package. -/
theorem correctedConcreteFiniteObject_workingGrammar_exact_domain_package :
    (∀ (K : Finset (Word α))
        (obs : α → M)
        (f : Nat),
      Nonempty α →
      Nonempty
        (CorrectedConcreteFiniteObjectWorkingGrammarRealization
          K obs f)) ∧
    (∀ (K : Finset (Word α))
        (obs : α → M)
        (f : Nat),
      Nonempty
          (CorrectedConcreteFiniteObjectWorkingGrammarRealization
            K obs f) ↔
        K = ∅ ∨ Nonempty α) ∧
    (∀ f : Nat,
      ¬ Nonempty
        (CorrectedConcreteFiniteObjectWorkingGrammarRealization
          emptyAlphabetEpsilonSample
          emptyAlphabetObservation
          f)) := by

  exact
    ⟨fun K obs f hα =>
        ⟨correctedConcreteCanonicalFiniteHypothesis_workingGrammarRealization
          K obs f hα⟩,
      fun K obs f =>
        workingGrammarRealization_iff_emptySample_or_nonemptyAlphabet,
      no_workingGrammarRealization_emptyAlphabet_epsilonSample
        (w := max u v)⟩

end PaperFacingCompilationPackage

end MCFG
