/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerPolynomialExponentBounds

/-!
# ConcreteCanonicalLearnerFiniteHypothesis.lean

The corrected concrete learner has so far been presented through a derivation
relation whose unit and binary constructors receive arities and rules
separately.

This file assembles those rules into actual finite dependent rule-code sets.

For fan-out `f`, a positive arity index is a natural number `d` satisfying

```lean
0 < d ∧ d ≤ f.
```

The two finite rule-code types are:

```lean
CorrectedConcreteUnitRuleCode K obs f
CorrectedConcreteBinaryRuleCode K f.
```

Their complete finite enumerations are:

```lean
finiteCorrectedConcreteUnitRuleCodes
finiteCorrectedConcreteBinaryRuleCodes.
```

They are packaged as the actual finite hypothesis object

```lean
CorrectedConcreteFiniteHypothesis K obs f.
```

A new derivation relation uses the dependent rule codes directly, without
receiving separate arity-bound premises.  The main results prove two-way
equivalence with the previously verified relation:

```lean
FiniteCorrectedConcreteLearnerDerives.toConcrete
CorrectedConcreteCanonicalLearnerDerives.toFinite
finiteCorrectedConcreteLearnerDerives_iff.
```

Consequently the finite-hypothesis string language is exactly the existing
corrected concrete canonical learner language.

The hypothesis is target independent: it depends only on `K`, `obs`, and `f`.

No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section PositiveArityIndices

/-- Finite set of positive arities at most `f`. -/
def positiveArities
    (f : Nat) :
    Finset Nat :=
  (Finset.range (f + 1)).filter
    (fun d => 0 < d)

/-- A positive arity index for fan-out `f`. -/
abbrev PositiveArityIndex
    (f : Nat) :=
  {d : Nat // d ∈ positiveArities f}

namespace PositiveArityIndex

/-- Numerical arity carried by an index. -/
abbrev arity
    {f : Nat}
    (d : PositiveArityIndex f) :
    Nat :=
  d.1

/-- Positivity of every indexed arity. -/
theorem pos
    {f : Nat}
    (d : PositiveArityIndex f) :
    0 < d.arity := by
  have h :=
    (Finset.mem_filter.mp d.2).2
  exact h

/-- Every indexed arity is at most the fan-out bound. -/
theorem le_fanout
    {f : Nat}
    (d : PositiveArityIndex f) :
    d.arity ≤ f := by
  have h :=
    (Finset.mem_filter.mp d.2).1
  simp only [Finset.mem_range] at h
  omega

/-- Construct a positive arity index from the two usual arity premises. -/
def ofBounds
    {d f : Nat}
    (hpos : 0 < d)
    (hdf : d ≤ f) :
    PositiveArityIndex f :=
  ⟨d, by
    apply Finset.mem_filter.mpr
    constructor
    · simp only [Finset.mem_range]
      omega
    · exact hpos⟩

@[simp] theorem arity_ofBounds
    {d f : Nat}
    (hpos : 0 < d)
    (hdf : d ≤ f) :
    (ofBounds hpos hdf).arity = d :=
  rfl

/-- The attached finite set contains every positive arity index. -/
theorem mem_attach
    {f : Nat}
    (d : PositiveArityIndex f) :
    d ∈ (positiveArities f).attach := by
  simp

end PositiveArityIndex

end PositiveArityIndices


section FiniteDependentRuleCodes

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- One unit-rule code, including its positive arity index. -/
abbrev CorrectedConcreteUnitRuleCode
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :=
  Σ d : PositiveArityIndex f,
    ConcreteUnitRule K obs d.arity

namespace CorrectedConcreteUnitRuleCode

abbrev index
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (U :
      CorrectedConcreteUnitRuleCode
        K obs f) :
    PositiveArityIndex f :=
  U.1

abbrev arity
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (U :
      CorrectedConcreteUnitRuleCode
        K obs f) :
    Nat :=
  U.index.arity

abbrev rule
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (U :
      CorrectedConcreteUnitRuleCode
        K obs f) :
    ConcreteUnitRule K obs U.arity :=
  U.2

theorem arity_pos
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (U :
      CorrectedConcreteUnitRuleCode
        K obs f) :
    0 < U.arity :=
  U.index.pos

theorem arity_le
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (U :
      CorrectedConcreteUnitRuleCode
        K obs f) :
    U.arity ≤ f :=
  U.index.le_fanout

def source
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (U :
      CorrectedConcreteUnitRuleCode
        K obs f) :
    Tuple α U.arity :=
  U.rule.source

def target
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (U :
      CorrectedConcreteUnitRuleCode
        K obs f) :
    Tuple α U.arity :=
  U.rule.target

end CorrectedConcreteUnitRuleCode


/-- One corrected binary-rule code, including all three positive arity
indices. -/
abbrev CorrectedConcreteBinaryRuleCode
    (K : Finset (Word α))
    (f : Nat) :=
  Σ e : PositiveArityIndex f,
    Σ dB : PositiveArityIndex f,
      Σ dC : PositiveArityIndex f,
        CorrectedConcreteBinaryRule
          K e.arity dB.arity dC.arity

namespace CorrectedConcreteBinaryRuleCode

abbrev parentIndex
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    PositiveArityIndex f :=
  B.1

abbrev leftIndex
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    PositiveArityIndex f :=
  B.2.1

abbrev rightIndex
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    PositiveArityIndex f :=
  B.2.2.1

abbrev parentArity
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    Nat :=
  B.parentIndex.arity

abbrev leftArity
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    Nat :=
  B.leftIndex.arity

abbrev rightArity
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    Nat :=
  B.rightIndex.arity

abbrev rule
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    CorrectedConcreteBinaryRule
      K B.parentArity
        B.leftArity B.rightArity :=
  B.2.2.2

theorem parentArity_pos
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    0 < B.parentArity :=
  B.parentIndex.pos

theorem leftArity_pos
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    0 < B.leftArity :=
  B.leftIndex.pos

theorem rightArity_pos
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    0 < B.rightArity :=
  B.rightIndex.pos

theorem parentArity_le
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    B.parentArity ≤ f :=
  B.parentIndex.le_fanout

theorem leftArity_le
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    B.leftArity ≤ f :=
  B.leftIndex.le_fanout

theorem rightArity_le
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    B.rightArity ≤ f :=
  B.rightIndex.le_fanout

def source
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    Tuple α B.parentArity :=
  B.rule.source

def leftSource
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    Tuple α B.leftArity :=
  B.rule.leftSource

def rightSource
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    Tuple α B.rightArity :=
  B.rule.rightSource

def body
    {K : Finset (Word α)}
    {f : Nat}
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    TemplateTuple α
      B.parentArity
      B.leftArity
      B.rightArity :=
  B.rule.body

end CorrectedConcreteBinaryRuleCode

end FiniteDependentRuleCodes


section CompleteFiniteRuleEnumerations

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Complete finite enumeration of all corrected unit-rule codes with positive
arity at most `f`. -/
noncomputable def finiteCorrectedConcreteUnitRuleCodes
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    Finset
      (CorrectedConcreteUnitRuleCode
        K obs f) := by
  classical
  exact
    (positiveArities f).attach.sigma
      (fun d =>
        (concreteUnitRules
          K obs d.arity).attach)

/-- Complete finite enumeration of all corrected binary-rule codes whose three
arities are positive and at most `f`. -/
noncomputable def finiteCorrectedConcreteBinaryRuleCodes
    (K : Finset (Word α))
    (f : Nat) :
    Finset
      (CorrectedConcreteBinaryRuleCode
        K f) := by
  classical
  exact
    (positiveArities f).attach.sigma
      (fun e =>
        (positiveArities f).attach.sigma
          (fun dB =>
            (positiveArities f).attach.sigma
              (fun dC =>
                (correctedConcreteBinaryWitnesses
                  K e.arity
                    dB.arity dC.arity).attach)))

/-- Every dependent unit-rule code occurs in the complete finite
enumeration. -/
theorem mem_finiteCorrectedConcreteUnitRuleCodes
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (U :
      CorrectedConcreteUnitRuleCode
        K obs f) :
    U ∈ finiteCorrectedConcreteUnitRuleCodes
      K obs f := by
  classical
  rcases U with ⟨d, U⟩
  simp [
    finiteCorrectedConcreteUnitRuleCodes
  ]

/-- Every dependent binary-rule code occurs in the complete finite
enumeration. -/
theorem mem_finiteCorrectedConcreteBinaryRuleCodes
    (K : Finset (Word α))
    (f : Nat)
    (B :
      CorrectedConcreteBinaryRuleCode
        K f) :
    B ∈ finiteCorrectedConcreteBinaryRuleCodes
      K f := by
  classical
  rcases B with ⟨e, dB, dC, B⟩
  simp [
    finiteCorrectedConcreteBinaryRuleCodes
  ]

/-- Actual finite hypothesis object listed by the corrected concrete learner. -/
structure CorrectedConcreteFiniteHypothesis
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) where

  unitRuleCodes :
    Finset
      (CorrectedConcreteUnitRuleCode
        K obs f)

  binaryRuleCodes :
    Finset
      (CorrectedConcreteBinaryRuleCode
        K f)

  unitRuleCodes_complete :
    ∀ U,
      U ∈ unitRuleCodes

  binaryRuleCodes_complete :
    ∀ B,
      B ∈ binaryRuleCodes

/-- Canonical finite hypothesis consisting of all enumerated corrected rules. -/
noncomputable def correctedConcreteFiniteHypothesis
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    CorrectedConcreteFiniteHypothesis
      K obs f where

  unitRuleCodes :=
    finiteCorrectedConcreteUnitRuleCodes
      K obs f

  binaryRuleCodes :=
    finiteCorrectedConcreteBinaryRuleCodes
      K f

  unitRuleCodes_complete :=
    mem_finiteCorrectedConcreteUnitRuleCodes
      K obs f

  binaryRuleCodes_complete :=
    mem_finiteCorrectedConcreteBinaryRuleCodes
      K f

namespace CorrectedConcreteFiniteHypothesis

/-- Actual number of listed rules in a finite hypothesis object. -/
def ruleCount
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (H :
      CorrectedConcreteFiniteHypothesis
        K obs f) :
    Nat :=
  H.unitRuleCodes.card +
    H.binaryRuleCodes.card

@[simp] theorem canonical_unitRuleCodes
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (correctedConcreteFiniteHypothesis
      K obs f).unitRuleCodes =
        finiteCorrectedConcreteUnitRuleCodes
          K obs f :=
  rfl

@[simp] theorem canonical_binaryRuleCodes
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (correctedConcreteFiniteHypothesis
      K obs f).binaryRuleCodes =
        finiteCorrectedConcreteBinaryRuleCodes
          K f :=
  rfl

end CorrectedConcreteFiniteHypothesis

end CompleteFiniteRuleEnumerations


section CodeConstructors

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Package a previously used corrected unit rule as a dependent finite code. -/
def correctedConcreteUnitRuleCodeOf
    {K : Finset (Word α)}
    {obs : α → M}
    {f d : Nat}
    (hd : d ≤ f)
    (hpos : 0 < d)
    (U : ConcreteUnitRule K obs d) :
    CorrectedConcreteUnitRuleCode
      K obs f :=
  ⟨PositiveArityIndex.ofBounds hpos hd, U⟩

@[simp] theorem correctedConcreteUnitRuleCodeOf_arity
    {K : Finset (Word α)}
    {obs : α → M}
    {f d : Nat}
    (hd : d ≤ f)
    (hpos : 0 < d)
    (U : ConcreteUnitRule K obs d) :
    (correctedConcreteUnitRuleCodeOf
      hd hpos U).arity = d :=
  rfl

@[simp] theorem correctedConcreteUnitRuleCodeOf_rule
    {K : Finset (Word α)}
    {obs : α → M}
    {f d : Nat}
    (hd : d ≤ f)
    (hpos : 0 < d)
    (U : ConcreteUnitRule K obs d) :
    (correctedConcreteUnitRuleCodeOf
      hd hpos U).rule = U :=
  rfl

/-- Package a previously used corrected binary rule as a dependent finite
code. -/
def correctedConcreteBinaryRuleCodeOf
    {K : Finset (Word α)}
    {f e dB dC : Nat}
    (he : e ≤ f)
    (hdB : dB ≤ f)
    (hdC : dC ≤ f)
    (hepos : 0 < e)
    (hdBpos : 0 < dB)
    (hdCpos : 0 < dC)
    (B :
      CorrectedConcreteBinaryRule
        K e dB dC) :
    CorrectedConcreteBinaryRuleCode
      K f :=
  ⟨PositiveArityIndex.ofBounds hepos he,
    PositiveArityIndex.ofBounds hdBpos hdB,
    PositiveArityIndex.ofBounds hdCpos hdC,
    B⟩

@[simp] theorem correctedConcreteBinaryRuleCodeOf_parentArity
    {K : Finset (Word α)}
    {f e dB dC : Nat}
    (he : e ≤ f)
    (hdB : dB ≤ f)
    (hdC : dC ≤ f)
    (hepos : 0 < e)
    (hdBpos : 0 < dB)
    (hdCpos : 0 < dC)
    (B :
      CorrectedConcreteBinaryRule
        K e dB dC) :
    (correctedConcreteBinaryRuleCodeOf
      he hdB hdC
      hepos hdBpos hdCpos B).parentArity =
        e :=
  rfl

@[simp] theorem correctedConcreteBinaryRuleCodeOf_leftArity
    {K : Finset (Word α)}
    {f e dB dC : Nat}
    (he : e ≤ f)
    (hdB : dB ≤ f)
    (hdC : dC ≤ f)
    (hepos : 0 < e)
    (hdBpos : 0 < dB)
    (hdCpos : 0 < dC)
    (B :
      CorrectedConcreteBinaryRule
        K e dB dC) :
    (correctedConcreteBinaryRuleCodeOf
      he hdB hdC
      hepos hdBpos hdCpos B).leftArity =
        dB :=
  rfl

@[simp] theorem correctedConcreteBinaryRuleCodeOf_rightArity
    {K : Finset (Word α)}
    {f e dB dC : Nat}
    (he : e ≤ f)
    (hdB : dB ≤ f)
    (hdC : dC ≤ f)
    (hepos : 0 < e)
    (hdBpos : 0 < dB)
    (hdCpos : 0 < dC)
    (B :
      CorrectedConcreteBinaryRule
        K e dB dC) :
    (correctedConcreteBinaryRuleCodeOf
      he hdB hdC
      hepos hdBpos hdCpos B).rightArity =
        dC :=
  rfl

@[simp] theorem correctedConcreteBinaryRuleCodeOf_rule
    {K : Finset (Word α)}
    {f e dB dC : Nat}
    (he : e ≤ f)
    (hdB : dB ≤ f)
    (hdC : dC ≤ f)
    (hepos : 0 < e)
    (hdBpos : 0 < dB)
    (hdCpos : 0 < dC)
    (B :
      CorrectedConcreteBinaryRule
        K e dB dC) :
    (correctedConcreteBinaryRuleCodeOf
      he hdB hdC
      hepos hdBpos hdCpos B).rule =
        B :=
  rfl

end CodeConstructors


section FiniteHypothesisDerivation

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Derivation relation reading its rules directly from the finite dependent
rule-code types. -/
inductive FiniteCorrectedConcreteLearnerDerives
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    {d : Nat} → Tuple α d → Tuple α d → Prop where

  | self
      {d : Nat}
      (x : Tuple α d) :
      FiniteCorrectedConcreteLearnerDerives
        K obs f x x

  | unit
      (U :
        CorrectedConcreteUnitRuleCode
          K obs f)
      {u : Tuple α U.arity}
      (hrest :
        FiniteCorrectedConcreteLearnerDerives
          K obs f U.target u) :
      FiniteCorrectedConcreteLearnerDerives
        K obs f U.source u

  | binary
      (B :
        CorrectedConcreteBinaryRuleCode
          K f)
      {u : Tuple α B.leftArity}
      {v : Tuple α B.rightArity}
      (hleft :
        FiniteCorrectedConcreteLearnerDerives
          K obs f B.leftSource u)
      (hright :
        FiniteCorrectedConcreteLearnerDerives
          K obs f B.rightSource v) :
      FiniteCorrectedConcreteLearnerDerives
        K obs f B.source
          (evalTemplateTuple B.body u v)

  | trans
      {d : Nat}
      {x y z : Tuple α d}
      (hxy :
        FiniteCorrectedConcreteLearnerDerives
          K obs f x y)
      (hyz :
        FiniteCorrectedConcreteLearnerDerives
          K obs f y z) :
      FiniteCorrectedConcreteLearnerDerives
        K obs f x z

namespace FiniteCorrectedConcreteLearnerDerives

variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Forget dependent rule codes and recover the previously verified corrected
concrete derivation. -/
theorem toConcrete
    {d : Nat}
    {x y : Tuple α d}
    (h :
      FiniteCorrectedConcreteLearnerDerives
        K obs f x y) :
    CorrectedConcreteCanonicalLearnerDerives
      K obs f x y := by
  induction h with

  | self x =>
      exact
        CorrectedConcreteCanonicalLearnerDerives.self
          x

  | unit U hrest ih =>
      exact
        CorrectedConcreteCanonicalLearnerDerives.unit
          U.arity_le
          U.arity_pos
          U.rule
          ih

  | binary B hleft hright ihleft ihright =>
      exact
        CorrectedConcreteCanonicalLearnerDerives.binary
          B.parentArity_le
          B.leftArity_le
          B.rightArity_le
          B.parentArity_pos
          B.leftArity_pos
          B.rightArity_pos
          B.rule
          ihleft ihright

  | trans hxy hyz ihxy ihyz =>
      exact
        CorrectedConcreteCanonicalLearnerDerives.trans
          ihxy ihyz

end FiniteCorrectedConcreteLearnerDerives


namespace CorrectedConcreteCanonicalLearnerDerives

variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Package every corrected concrete derivation into the finite dependent
hypothesis relation. -/
theorem toFinite
    {d : Nat}
    {x y : Tuple α d}
    (h :
      CorrectedConcreteCanonicalLearnerDerives
        K obs f x y) :
    FiniteCorrectedConcreteLearnerDerives
      K obs f x y := by
  induction h with

  | self x =>
      exact
        FiniteCorrectedConcreteLearnerDerives.self
          x

  | unit hd hpos U hrest ih =>
      exact
        FiniteCorrectedConcreteLearnerDerives.unit
          (correctedConcreteUnitRuleCodeOf
            hd hpos U)
          ih

  | binary he hdB hdC hepos hdBpos hdCpos
      B hleft hright ihleft ihright =>
      exact
        FiniteCorrectedConcreteLearnerDerives.binary
          (correctedConcreteBinaryRuleCodeOf
            he hdB hdC
            hepos hdBpos hdCpos B)
          ihleft ihright

  | trans hxy hyz ihxy ihyz =>
      exact
        FiniteCorrectedConcreteLearnerDerives.trans
          ihxy ihyz

end CorrectedConcreteCanonicalLearnerDerives


/-- Tuple-level equivalence between the finite dependent hypothesis and the
previous corrected concrete learner relation. -/
theorem finiteCorrectedConcreteLearnerDerives_iff
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    {d : Nat}
    (x y : Tuple α d) :
    FiniteCorrectedConcreteLearnerDerives
        K obs f x y ↔
      CorrectedConcreteCanonicalLearnerDerives
        K obs f x y := by
  constructor
  · exact
      FiniteCorrectedConcreteLearnerDerives.toConcrete
  · exact
      CorrectedConcreteCanonicalLearnerDerives.toFinite

end FiniteHypothesisDerivation


section FiniteHypothesisStringLanguage

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- String derivation generated by the finite dependent hypothesis. -/
structure FiniteCorrectedConcreteStringDerives
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (word : Word α) where

  startWord : Word α

  start_mem :
    startWord ∈ K

  derives :
    FiniteCorrectedConcreteLearnerDerives
      K obs f
      (singletonTuple startWord)
      (singletonTuple word)

/-- String language of the finite dependent hypothesis object. -/
def FiniteCorrectedConcreteLearnerLanguage
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    Set (Word α) :=
  {word |
    FiniteCorrectedConcreteStringDerives
      K obs f word}

namespace FiniteCorrectedConcreteStringDerives

variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Translate a finite-hypothesis string derivation to the existing corrected
concrete learner. -/
def toConcrete
    {word : Word α}
    (D :
      FiniteCorrectedConcreteStringDerives
        K obs f word) :
    CorrectedConcreteCanonicalStringDerives
      K obs f word where

  startWord :=
    D.startWord

  start_mem :=
    D.start_mem

  derives :=
    D.derives.toConcrete

end FiniteCorrectedConcreteStringDerives


namespace CorrectedConcreteCanonicalStringDerives

variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Translate an existing corrected concrete string derivation to the finite
dependent hypothesis. -/
def toFinite
    {word : Word α}
    (D :
      CorrectedConcreteCanonicalStringDerives
        K obs f word) :
    FiniteCorrectedConcreteStringDerives
      K obs f word where

  startWord :=
    D.startWord

  start_mem :=
    D.start_mem

  derives :=
    D.derives.toFinite

end CorrectedConcreteCanonicalStringDerives


/-- The finite dependent hypothesis language is contained in the previously
verified corrected concrete learner language. -/
theorem finiteCorrectedConcreteLearnerLanguage_subset
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    FiniteCorrectedConcreteLearnerLanguage
        K obs f ⊆
      CorrectedConcreteCanonicalLearnerLanguage
        K obs f := by
  intro word hword
  exact hword.toConcrete

/-- Every derivation of the existing corrected concrete learner is represented
inside the finite dependent hypothesis. -/
theorem correctedConcreteCanonicalLearnerLanguage_subset_finite
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    CorrectedConcreteCanonicalLearnerLanguage
        K obs f ⊆
      FiniteCorrectedConcreteLearnerLanguage
        K obs f := by
  intro word hword
  exact hword.toFinite

/-- Exact equality of the actual finite-hypothesis language and the previously
verified corrected concrete canonical learner language. -/
theorem finiteCorrectedConcreteLearnerLanguage_eq
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    FiniteCorrectedConcreteLearnerLanguage
        K obs f =
      CorrectedConcreteCanonicalLearnerLanguage
        K obs f := by
  apply Set.Subset.antisymm
  · exact
      finiteCorrectedConcreteLearnerLanguage_subset
        K obs f
  · exact
      correctedConcreteCanonicalLearnerLanguage_subset_finite
        K obs f

/-- Therefore the finite dependent hypothesis also agrees exactly with the
exact-once reachable semantics. -/
theorem finiteCorrectedConcreteLearnerLanguage_eq_exactReachable
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    FiniteCorrectedConcreteLearnerLanguage
        K obs f =
      ExactReachableSampleStringLanguage
        K obs f := by
  rw [
    finiteCorrectedConcreteLearnerLanguage_eq,
    correctedConcreteCanonicalLearnerLanguage_eq_exactReachable
  ]

end FiniteHypothesisStringLanguage


section FiniteHypothesisSoundnessAndIdentification

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Soundness of the actual finite hypothesis for every promised positive
target. -/
theorem finiteCorrectedConcreteLearnerLanguage_sound
    {N : Type w}
    (G : WorkingMCFG N α)
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage)
    (hK :
      (K : Set (Word α)) ⊆
        G.StringLanguage) :
    FiniteCorrectedConcreteLearnerLanguage
        K obs f ⊆
      G.StringLanguage := by
  rw [finiteCorrectedConcreteLearnerLanguage_eq]
  exact
    correctedConcreteCanonicalLearnerLanguage_sound
      G hL hK

/-- Exact reconstruction by the actual finite hypothesis on the concrete typed
characteristic sample. -/
theorem concreteTypedCharacteristicSample_finiteHypothesis_exact
    {N : Type w}
    [Fintype N]
    [Fintype M]
    [DecidableEq α]
    [DecidableEq M]
    (G : WorkingMCFG N α)
    (obs : α → M)
    (f : Nat)
    (hworking : G.ExactWorkingConditions)
    (hnormal : G.StartRootedNormal)
    (hfan : G.FanoutAtMost f)
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage) :
    FiniteCorrectedConcreteLearnerLanguage
        (concreteTypedCharacteristicSample_of_startRooted
          (obs := obs) hworking hnormal)
        obs f =
      G.StringLanguage := by
  rw [finiteCorrectedConcreteLearnerLanguage_eq]
  exact
    concreteTypedCharacteristicSample_correctedConcrete_exact_of_startRooted
      (obs := obs)
      hworking hnormal hfan hL

/-- Paper-facing package connecting the actual finite object, its complete rule
lists, and its verified language semantics. -/
theorem correctedConcreteFiniteHypothesis_semantic_package
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (∀ U :
      CorrectedConcreteUnitRuleCode
        K obs f,
      U ∈
        (correctedConcreteFiniteHypothesis
          K obs f).unitRuleCodes) ∧
    (∀ B :
      CorrectedConcreteBinaryRuleCode
        K f,
      B ∈
        (correctedConcreteFiniteHypothesis
          K obs f).binaryRuleCodes) ∧
    FiniteCorrectedConcreteLearnerLanguage
        K obs f =
      CorrectedConcreteCanonicalLearnerLanguage
        K obs f ∧
    FiniteCorrectedConcreteLearnerLanguage
        K obs f =
      ExactReachableSampleStringLanguage
        K obs f := by
  exact
    ⟨(correctedConcreteFiniteHypothesis
        K obs f).unitRuleCodes_complete,
      (correctedConcreteFiniteHypothesis
        K obs f).binaryRuleCodes_complete,
      finiteCorrectedConcreteLearnerLanguage_eq
        K obs f,
      finiteCorrectedConcreteLearnerLanguage_eq_exactReachable
        K obs f⟩

end FiniteHypothesisSoundnessAndIdentification

end MCFG
