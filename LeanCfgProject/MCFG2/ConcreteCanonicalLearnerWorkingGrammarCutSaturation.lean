/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerWorkingGrammarObstruction

/-!
# ConcreteCanonicalLearnerWorkingGrammarCutSaturation.lean

A direct compilation of the finite learner relation into a `WorkingMCFG`
must handle the explicit transitive-closure constructor.

The key observation is finite-control:

* sample singleton tuples;
* unit-rule sources and targets;
* binary-rule parent and child sources

form a finite set of dependent tuple codes.

If a listed derivation starts outside this finite control set, it can only be
the identity.  Therefore every listed derivation starting at a control tuple
admits a cut-normal form consisting of:

* identity at a control tuple;
* one listed binary composition;
* a cut from one control tuple to another control tuple.

The relation between control tuples may be saturated noncomputably because the
control set is finite.  This file constructs that finite saturation set and
proves the normalization theorem needed by the forthcoming `WorkingMCFG`
compiler.

Main definitions:

```lean
FiniteObjectTupleCode
CorrectedConcreteFiniteHypothesis.controlCodes
CorrectedConcreteFiniteHypothesis.cutPairs
CutNormalizedListedFiniteDerives.
```

Main theorems:

```lean
ListedFiniteCorrectedConcreteLearnerDerives.eq_of_source_not_control
ListedFiniteCorrectedConcreteLearnerDerives.toCutNormalized
CutNormalizedListedFiniteDerives.toListed
listed_derives_iff_cutNormalized_of_control
CorrectedConcreteFiniteHypothesis.cutPairs_finite.
```

No target grammar occurs in the construction.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section TupleCodes

variable (α : Type u)

/-- A tuple bundled together with its arity. -/
abbrev FiniteObjectTupleCode :=
  Σ d : Nat, Tuple α d

namespace FiniteObjectTupleCode

variable {α : Type u}

/-- Bundle one tuple with its arity. -/
def mk
    {d : Nat}
    (x : Tuple α d) :
    FiniteObjectTupleCode α :=
  ⟨d, x⟩

/-- Arity of a bundled tuple. -/
abbrev arity
    (X : FiniteObjectTupleCode α) :
    Nat :=
  X.1

/-- Tuple carried by a bundled tuple code. -/
abbrev tuple
    (X : FiniteObjectTupleCode α) :
    Tuple α X.arity :=
  X.2

/-- The tuple code associated with a sample word. -/
def ofWord
    (word : Word α) :
    FiniteObjectTupleCode α :=
  ⟨1, singletonTuple word⟩

end FiniteObjectTupleCode

end TupleCodes


section RuleTupleCodes

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Source tuple code of a finite unit rule. -/
def CorrectedConcreteUnitRuleCode.sourceCode
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (U :
      CorrectedConcreteUnitRuleCode
        K obs f) :
    FiniteObjectTupleCode α :=
  ⟨U.arity, U.source⟩

/-- Target tuple code of a finite unit rule. -/
def CorrectedConcreteUnitRuleCode.targetCode
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (U :
      CorrectedConcreteUnitRuleCode
        K obs f) :
    FiniteObjectTupleCode α :=
  ⟨U.arity, U.target⟩

/-- Parent source tuple code of a finite binary rule. -/
def CorrectedConcreteBinaryRuleCode.sourceCode
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    FiniteObjectTupleCode α :=
  ⟨B.parentArity, B.source⟩

/-- Left child source tuple code of a finite binary rule. -/
def CorrectedConcreteBinaryRuleCode.leftSourceCode
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    FiniteObjectTupleCode α :=
  ⟨B.leftArity, B.leftSource⟩

/-- Right child source tuple code of a finite binary rule. -/
def CorrectedConcreteBinaryRuleCode.rightSourceCode
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    FiniteObjectTupleCode α :=
  ⟨B.rightArity, B.rightSource⟩

end RuleTupleCodes


section FiniteControlSet

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Finite set of tuple codes that can act as control states in a listed
finite-object derivation. -/
noncomputable def CorrectedConcreteFiniteHypothesis.controlCodes
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    Finset (FiniteObjectTupleCode α) := by
  classical
  exact
    (K.image FiniteObjectTupleCode.ofWord) ∪
      (H.unitRuleCodes.image
        CorrectedConcreteUnitRuleCode.sourceCode) ∪
      (H.unitRuleCodes.image
        CorrectedConcreteUnitRuleCode.targetCode) ∪
      (H.binaryRuleCodes.image
        CorrectedConcreteBinaryRuleCode.sourceCode) ∪
      (H.binaryRuleCodes.image
        CorrectedConcreteBinaryRuleCode.leftSourceCode) ∪
      (H.binaryRuleCodes.image
        CorrectedConcreteBinaryRuleCode.rightSourceCode)

/-- Membership predicate for finite control tuple codes. -/
def CorrectedConcreteFiniteHypothesis.IsControlCode
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (X : FiniteObjectTupleCode α) :
    Prop :=
  X ∈ H.controlCodes

namespace CorrectedConcreteFiniteHypothesis

variable
  (H :
    CorrectedConcreteFiniteHypothesis
      K obs f)

/-- Every observed sample singleton is a control tuple. -/
theorem word_control
    {word : Word α}
    (hword : word ∈ K) :
    H.IsControlCode
      (FiniteObjectTupleCode.ofWord word) := by
  classical
  unfold IsControlCode
  unfold controlCodes
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr
    ⟨word, hword, rfl⟩

/-- Every listed unit-rule source is a control tuple. -/
theorem unitSource_control
    (U :
      CorrectedConcreteUnitRuleCode
        K obs f)
    (hU :
      U ∈ H.unitRuleCodes) :
    H.IsControlCode U.sourceCode := by
  classical
  unfold IsControlCode
  unfold controlCodes
  apply Finset.mem_union_right
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr
    ⟨U, hU, rfl⟩

/-- Every listed unit-rule target is a control tuple. -/
theorem unitTarget_control
    (U :
      CorrectedConcreteUnitRuleCode
        K obs f)
    (hU :
      U ∈ H.unitRuleCodes) :
    H.IsControlCode U.targetCode := by
  classical
  unfold IsControlCode
  unfold controlCodes
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr
    ⟨U, hU, rfl⟩

/-- Every listed binary-rule parent source is a control tuple. -/
theorem binarySource_control
    (B :
      CorrectedConcreteBinaryRuleCode
        K f)
    (hB :
      B ∈ H.binaryRuleCodes) :
    H.IsControlCode B.sourceCode := by
  classical
  unfold IsControlCode
  unfold controlCodes
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr
    ⟨B, hB, rfl⟩

/-- Every listed binary-rule left source is a control tuple. -/
theorem binaryLeftSource_control
    (B :
      CorrectedConcreteBinaryRuleCode
        K f)
    (hB :
      B ∈ H.binaryRuleCodes) :
    H.IsControlCode B.leftSourceCode := by
  classical
  unfold IsControlCode
  unfold controlCodes
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr
    ⟨B, hB, rfl⟩

/-- Every listed binary-rule right source is a control tuple. -/
theorem binaryRightSource_control
    (B :
      CorrectedConcreteBinaryRuleCode
        K f)
    (hB :
      B ∈ H.binaryRuleCodes) :
    H.IsControlCode B.rightSourceCode := by
  classical
  unfold IsControlCode
  unfold controlCodes
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr
    ⟨B, hB, rfl⟩

/-- The set of control tuple codes is finite as a set. -/
theorem controlCodes_finite :
    Set.Finite
      {X : FiniteObjectTupleCode α |
        H.IsControlCode X} := by
  classical
  simpa [IsControlCode] using
    H.controlCodes.finite_toSet

end CorrectedConcreteFiniteHypothesis

end FiniteControlSet


section NoncontrolIdentity

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}
variable
  {H :
    CorrectedConcreteFiniteHypothesis
      K obs f}

namespace ListedFiniteCorrectedConcreteLearnerDerives

/-- A listed derivation whose source is outside the finite control set can only
be the identity. -/
theorem eq_of_source_not_control
    {d : Nat}
    {x y : Tuple α d}
    (h :
      ListedFiniteCorrectedConcreteLearnerDerives
        K obs f H x y)
    (hx :
      ¬ H.IsControlCode
        (FiniteObjectTupleCode.mk x)) :
    y = x := by
  induction h with

  | self x =>
      rfl

  | unit U hU hrest ih =>
      exfalso
      exact hx
        (H.unitSource_control U hU)

  | binary B hB hleft hright ihleft ihright =>
      exfalso
      exact hx
        (H.binarySource_control B hB)

  | trans hxy hyz ihxy ihyz =>
      have hyx :
          y = x :=
        ihxy hx
      subst y
      exact ihyz hx

/-- If a noncontrol source reaches a target, the reverse equality is also
available in the orientation convenient for rewriting. -/
theorem source_eq_of_source_not_control
    {d : Nat}
    {x y : Tuple α d}
    (h :
      ListedFiniteCorrectedConcreteLearnerDerives
        K obs f H x y)
    (hx :
      ¬ H.IsControlCode
        (FiniteObjectTupleCode.mk x)) :
    x = y :=
  (h.eq_of_source_not_control hx).symm

end ListedFiniteCorrectedConcreteLearnerDerives

end NoncontrolIdentity


section CutNormalForm

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}
variable
  (H :
    CorrectedConcreteFiniteHypothesis
      K obs f)

/-- Grammar-friendly normal form for listed finite-object derivations.

The `cut` constructor is restricted to a control target.  Since the control set
is finite, all such cuts can later be saturated into a finite grammar-rule
list. -/
inductive CutNormalizedListedFiniteDerives :
    {d : Nat} → Tuple α d → Tuple α d → Prop where

  | self
      {d : Nat}
      (x : Tuple α d)
      (hx :
        H.IsControlCode
          (FiniteObjectTupleCode.mk x)) :
      CutNormalizedListedFiniteDerives
        x x

  | binary
      (B :
        CorrectedConcreteBinaryRuleCode
          K f)
      (hB :
        B ∈ H.binaryRuleCodes)
      {u : Tuple α B.leftArity}
      {v : Tuple α B.rightArity}
      (hleft :
        CutNormalizedListedFiniteDerives
          B.leftSource u)
      (hright :
        CutNormalizedListedFiniteDerives
          B.rightSource v) :
      CutNormalizedListedFiniteDerives
        B.source
        (evalTemplateTuple B.body u v)

  | cut
      {d : Nat}
      {x y z : Tuple α d}
      (hx :
        H.IsControlCode
          (FiniteObjectTupleCode.mk x))
      (hy :
        H.IsControlCode
          (FiniteObjectTupleCode.mk y))
      (hxy :
        ListedFiniteCorrectedConcreteLearnerDerives
          K obs f H x y)
      (hyz :
        CutNormalizedListedFiniteDerives
          y z) :
      CutNormalizedListedFiniteDerives
        x z

namespace CutNormalizedListedFiniteDerives

variable {H :
  CorrectedConcreteFiniteHypothesis K obs f}

/-- The source of every cut-normal derivation is a finite control tuple. -/
theorem source_control
    {d : Nat}
    {x y : Tuple α d}
    (h :
      CutNormalizedListedFiniteDerives
        H x y) :
    H.IsControlCode
      (FiniteObjectTupleCode.mk x) := by
  induction h with

  | self x hx =>
      exact hx

  | binary B hB hleft hright ihleft ihright =>
      exact
        H.binarySource_control B hB

  | cut hx hy hxy hyz ih =>
      exact hx

/-- Forget the cut-normal presentation and recover the original listed
derivation. -/
theorem toListed
    {d : Nat}
    {x y : Tuple α d}
    (h :
      CutNormalizedListedFiniteDerives
        H x y) :
    ListedFiniteCorrectedConcreteLearnerDerives
      K obs f H x y := by
  induction h with

  | self x hx =>
      exact
        ListedFiniteCorrectedConcreteLearnerDerives.self
          x

  | binary B hB hleft hright ihleft ihright =>
      exact
        ListedFiniteCorrectedConcreteLearnerDerives.binary
          B hB ihleft ihright

  | cut hx hy hxy hyz ih =>
      exact
        ListedFiniteCorrectedConcreteLearnerDerives.trans
          hxy ih

end CutNormalizedListedFiniteDerives

end CutNormalForm


section Normalization

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}
variable
  {H :
    CorrectedConcreteFiniteHypothesis
      K obs f}

namespace ListedFiniteCorrectedConcreteLearnerDerives

/-- Every listed derivation starting at a finite control tuple has a
grammar-friendly cut normal form. -/
theorem toCutNormalized
    {d : Nat}
    {x y : Tuple α d}
    (h :
      ListedFiniteCorrectedConcreteLearnerDerives
        K obs f H x y) :
    H.IsControlCode
        (FiniteObjectTupleCode.mk x) →
      CutNormalizedListedFiniteDerives
        H x y := by
  induction h with

  | self x =>
      intro hx
      exact
        CutNormalizedListedFiniteDerives.self
          x hx

  | unit U hU hrest ih =>
      intro hx

      have hstep :
          ListedFiniteCorrectedConcreteLearnerDerives
            K obs f H U.source U.target :=
        ListedFiniteCorrectedConcreteLearnerDerives.unit
          U hU
          (ListedFiniteCorrectedConcreteLearnerDerives.self
            U.target)

      exact
        CutNormalizedListedFiniteDerives.cut
          (H.unitSource_control U hU)
          (H.unitTarget_control U hU)
          hstep
          (ih (H.unitTarget_control U hU))

  | binary B hB hleft hright ihleft ihright =>
      intro hx

      exact
        CutNormalizedListedFiniteDerives.binary
          B hB
          (ihleft
            (H.binaryLeftSource_control B hB))
          (ihright
            (H.binaryRightSource_control B hB))

  | trans hxy hyz ihxy ihyz =>
      intro hx

      by_cases hy :
        H.IsControlCode
          (FiniteObjectTupleCode.mk y)

      · exact
          CutNormalizedListedFiniteDerives.cut
            hx hy hxy (ihyz hy)

      · have hzy :
            z = y :=
          hyz.eq_of_source_not_control hy
        subst z
        exact ihxy hx

end ListedFiniteCorrectedConcreteLearnerDerives


/-- On a finite control source, the original and cut-normal derivation
relations are equivalent. -/
theorem listed_derives_iff_cutNormalized_of_control
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    {d : Nat}
    {x y : Tuple α d}
    (hx :
      H.IsControlCode
        (FiniteObjectTupleCode.mk x)) :
    ListedFiniteCorrectedConcreteLearnerDerives
        K obs f H x y ↔
      CutNormalizedListedFiniteDerives
        H x y := by
  constructor

  · intro h
    exact h.toCutNormalized hx

  · intro h
    exact h.toListed

end Normalization


section FiniteCutSaturation

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- A pair of control tuple codes is cut-admissible when the arities agree and
the listed finite object derives the target tuple from the source tuple. -/
def CorrectedConcreteFiniteHypothesis.CutAdmissible
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (X Y : FiniteObjectTupleCode α) :
    Prop :=
  ∃ h : X.arity = Y.arity,
    ListedFiniteCorrectedConcreteLearnerDerives
      K obs f H
      X.tuple
      (castTuple h.symm Y.tuple)

/-- Finite saturation of all cut-admissible pairs of control tuples. -/
noncomputable def CorrectedConcreteFiniteHypothesis.cutPairs
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    Finset
      (FiniteObjectTupleCode α ×
        FiniteObjectTupleCode α) := by
  classical
  exact
    (H.controlCodes.product H.controlCodes).filter
      (fun p =>
        H.CutAdmissible p.1 p.2)

namespace CorrectedConcreteFiniteHypothesis

variable
  (H :
    CorrectedConcreteFiniteHypothesis
      K obs f)

/-- Membership in the finite cut saturation exposes source control, target
control, and the reachable cut witness. -/
theorem mem_cutPairs_iff
    {X Y : FiniteObjectTupleCode α} :
    (X, Y) ∈ H.cutPairs ↔
      H.IsControlCode X ∧
      H.IsControlCode Y ∧
      H.CutAdmissible X Y := by
  classical
  simp [
    cutPairs,
    IsControlCode
  ]

/-- Every cut pair has a controlled source. -/
theorem cutPair_source_control
    {X Y : FiniteObjectTupleCode α}
    (hXY :
      (X, Y) ∈ H.cutPairs) :
    H.IsControlCode X :=
  (H.mem_cutPairs_iff.mp hXY).1

/-- Every cut pair has a controlled target. -/
theorem cutPair_target_control
    {X Y : FiniteObjectTupleCode α}
    (hXY :
      (X, Y) ∈ H.cutPairs) :
    H.IsControlCode Y :=
  (H.mem_cutPairs_iff.mp hXY).2.1

/-- Every cut pair carries a listed reachability witness between equal
arities. -/
theorem cutPair_admissible
    {X Y : FiniteObjectTupleCode α}
    (hXY :
      (X, Y) ∈ H.cutPairs) :
    H.CutAdmissible X Y :=
  (H.mem_cutPairs_iff.mp hXY).2.2

/-- The saturated cut relation is finite. -/
theorem cutPairs_finite :
    Set.Finite
      {p :
        FiniteObjectTupleCode α ×
          FiniteObjectTupleCode α |
        p ∈ H.cutPairs} := by
  classical
  simpa using H.cutPairs.finite_toSet

/-- Every admissible pair of controlled tuples occurs in the finite cut
saturation. -/
theorem mem_cutPairs_of_control_admissible
    {X Y : FiniteObjectTupleCode α}
    (hX : H.IsControlCode X)
    (hY : H.IsControlCode Y)
    (hXY : H.CutAdmissible X Y) :
    (X, Y) ∈ H.cutPairs := by
  exact
    H.mem_cutPairs_iff.mpr
      ⟨hX, hY, hXY⟩

end CorrectedConcreteFiniteHypothesis

end FiniteCutSaturation


section SampleStartNormalization

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Every listed string derivation starts at a control tuple and therefore has
a cut-normal tuple derivation. -/
def ListedFiniteCorrectedConcreteStringDerives.toCutNormalized
    {H :
      CorrectedConcreteFiniteHypothesis
        K obs f}
    {word : Word α}
    (D :
      ListedFiniteCorrectedConcreteStringDerives
        K obs f H word) :
    CutNormalizedListedFiniteDerives
      H
      (singletonTuple D.startWord)
      (singletonTuple word) :=
  D.derives.toCutNormalized
    (H.word_control D.start_mem)

/-- String-language membership can be expressed entirely through the finite
cut-normal relation. -/
theorem correctedConcreteFiniteHypothesis_language_iff_cutNormalized
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (word : Word α) :
    word ∈ H.Language ↔
      ∃ startWord : Word α,
        startWord ∈ K ∧
        CutNormalizedListedFiniteDerives
          H
          (singletonTuple startWord)
          (singletonTuple word) := by
  constructor

  · intro hword
    exact
      ⟨hword.startWord,
        hword.start_mem,
        hword.toCutNormalized⟩

  · rintro ⟨startWord, hstart, hderives⟩
    exact
      { startWord := startWord
        start_mem := hstart
        derives := hderives.toListed }

/-- Paper-facing finite-control and normalization package. -/
theorem correctedConcreteFiniteHypothesis_cutSaturation_package
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    Set.Finite
        {X : FiniteObjectTupleCode α |
          H.IsControlCode X} ∧
      Set.Finite
        {p :
          FiniteObjectTupleCode α ×
            FiniteObjectTupleCode α |
          p ∈ H.cutPairs} ∧
      (∀ d : Nat,
        ∀ x y : Tuple α d,
          ¬ H.IsControlCode
              (FiniteObjectTupleCode.mk x) →
          ListedFiniteCorrectedConcreteLearnerDerives
              K obs f H x y →
          y = x) ∧
      (∀ word : Word α,
        word ∈ H.Language ↔
          ∃ startWord : Word α,
            startWord ∈ K ∧
            CutNormalizedListedFiniteDerives
              H
              (singletonTuple startWord)
              (singletonTuple word)) := by
  exact
    ⟨H.controlCodes_finite,
      H.cutPairs_finite,
      fun d x y hx h =>
        h.eq_of_source_not_control hx,
      H.language_iff_cutNormalized⟩

end SampleStartNormalization

end MCFG
