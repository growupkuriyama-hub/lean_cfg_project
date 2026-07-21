/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.BinaryWitnesses

/-!
# ConcreteCanonicalLearner.lean

This file assembles the finite unit-rule and binary-witness enumerations into
a target-independent concrete learner.

For a finite sample `K`, observation map `obs`, and fan-out bound `f`, the
learner may use only:

* unit rules belonging to `concreteUnitRules K obs d`, with `0 < d ≤ f`;
* binary rules belonging to
  `concreteBinaryWitnesses K e dB dC`, with all three arities in `1..f`;
* reflexivity and transitive composition.

The generated string language starts from an actual sample word and applies
this concrete derivation relation to singleton tuples.

Every concrete derivation is translated to the previously verified
`SampleLearnerReachable` relation.  Consequently the concrete learner language
is included in `ReachableSampleStringLanguage`, and inherits its soundness for
every positive target satisfying the fixed-observation substitutability
promise.

No target grammar occurs in the learner definition.

The converse inclusion is intentionally not claimed here.  It requires
completeness of the bounded finite enumeration for arbitrary
`SampleUnitEvidence` and `SampleBinaryEvidence`; that is the next construction
target.
-/

namespace MCFG

universe u v w

section FiniteRuleObjects

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- A concrete unit rule is literally an element of the finite unit-rule set. -/
abbrev ConcreteUnitRule
    (K : Finset (Word α))
    (obs : α → M)
    (d : Nat) :=
  (concreteUnitRules K obs d).attach

namespace ConcreteUnitRule

/-- Source tuple of a concrete unit rule. -/
def source
    {K : Finset (Word α)}
    {obs : α → M}
    {d : Nat}
    (U : ConcreteUnitRule K obs d) :
    Tuple α d :=
  U.1.1.tuple

/-- Target tuple of a concrete unit rule. -/
def target
    {K : Finset (Word α)}
    {obs : α → M}
    {d : Nat}
    (U : ConcreteUnitRule K obs d) :
    Tuple α d :=
  U.1.2.tuple

/-- Every concrete unit rule carries valid sample unit evidence. -/
def evidence
    {K : Finset (Word α)}
    {obs : α → M}
    {d : Nat}
    (U : ConcreteUnitRule K obs d) :
    SampleUnitEvidence K obs U.source U.target :=
  sampleUnitEvidenceOfConcreteRule
    K obs d U.1 U.2

end ConcreteUnitRule


/-- A concrete binary rule is literally an element of the finite
binary-witness set. -/
abbrev ConcreteBinaryRule
    (K : Finset (Word α))
    (e dB dC : Nat) :=
  (concreteBinaryWitnesses K e dB dC).attach

namespace ConcreteBinaryRule

/-- Underlying finite binary witness. -/
def witness
    {K : Finset (Word α)}
    {e dB dC : Nat}
    (B : ConcreteBinaryRule K e dB dC) :
    FiniteBinaryWitnessCandidate
      K e dB dC (sampleLengthBudget K) :=
  B.1

/-- Parent source tuple of a concrete binary rule. -/
def source
    {K : Finset (Word α)}
    {e dB dC : Nat}
    (B : ConcreteBinaryRule K e dB dC) :
    Tuple α e :=
  B.witness.parent.1.tuple

/-- Left anchor tuple of a concrete binary rule. -/
def leftSource
    {K : Finset (Word α)}
    {e dB dC : Nat}
    (B : ConcreteBinaryRule K e dB dC) :
    Tuple α dB :=
  B.witness.leftTuple

/-- Right anchor tuple of a concrete binary rule. -/
def rightSource
    {K : Finset (Word α)}
    {e dB dC : Nat}
    (B : ConcreteBinaryRule K e dB dC) :
    Tuple α dC :=
  B.witness.rightTuple

/-- Template body of a concrete binary rule. -/
def body
    {K : Finset (Word α)}
    {e dB dC : Nat}
    (B : ConcreteBinaryRule K e dB dC) :
    TemplateTuple α e dB dC :=
  B.witness.body

/-- Parent named context carried by a concrete binary rule. -/
def parentContext
    {K : Finset (Word α)}
    {e dB dC : Nat}
    (B : ConcreteBinaryRule K e dB dC) :
    NamedSentenceContext α e :=
  B.witness.parentContext

/-- Every concrete binary rule carries valid sample binary evidence. -/
def evidence
    {K : Finset (Word α)}
    {e dB dC : Nat}
    (B : ConcreteBinaryRule K e dB dC) :
    SampleBinaryEvidence K
      B.parentContext
      B.body
      B.leftSource
      B.rightSource :=
  sampleBinaryEvidenceOfConcreteWitness
    K e dB dC B.1 B.2

/-- The parent source is the template composition of the two child sources. -/
theorem source_eq_composition
    {K : Finset (Word α)}
    {e dB dC : Nat}
    (B : ConcreteBinaryRule K e dB dC) :
    B.source =
      evalTemplateTuple B.body
        B.leftSource B.rightSource := by
  exact concreteBinaryWitness_parent_eq
    K e dB dC (sampleLengthBudget K) B.2

end ConcreteBinaryRule

end FiniteRuleObjects


section ConcreteTupleDerivations

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Derivation relation of the concrete canonical learner.

Every nontrivial rule constructor is indexed by membership in an actually
constructed finite rule set. -/
inductive ConcreteCanonicalLearnerDerives
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    {d : Nat} → Tuple α d → Tuple α d → Prop where

  | self
      {d : Nat}
      (x : Tuple α d) :
      ConcreteCanonicalLearnerDerives K obs f x x

  | unit
      {d : Nat}
      {u : Tuple α d}
      (hd : d ≤ f)
      (hpos : 0 < d)
      (U : ConcreteUnitRule K obs d)
      (hrest :
        ConcreteCanonicalLearnerDerives K obs f
          U.target u) :
      ConcreteCanonicalLearnerDerives K obs f
        U.source u

  | binary
      {e dB dC : Nat}
      {u : Tuple α dB}
      {v : Tuple α dC}
      (he : e ≤ f)
      (hdB : dB ≤ f)
      (hdC : dC ≤ f)
      (hepos : 0 < e)
      (hdBpos : 0 < dB)
      (hdCpos : 0 < dC)
      (B : ConcreteBinaryRule K e dB dC)
      (hleft :
        ConcreteCanonicalLearnerDerives K obs f
          B.leftSource u)
      (hright :
        ConcreteCanonicalLearnerDerives K obs f
          B.rightSource v) :
      ConcreteCanonicalLearnerDerives K obs f
        B.source
        (evalTemplateTuple B.body u v)

  | trans
      {d : Nat}
      {x y z : Tuple α d}
      (hxy :
        ConcreteCanonicalLearnerDerives K obs f x y)
      (hyz :
        ConcreteCanonicalLearnerDerives K obs f y z) :
      ConcreteCanonicalLearnerDerives K obs f x z

namespace ConcreteCanonicalLearnerDerives

variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Reflexivity. -/
theorem refl
    {d : Nat}
    (x : Tuple α d) :
    ConcreteCanonicalLearnerDerives K obs f x x :=
  ConcreteCanonicalLearnerDerives.self x

/-- Transitivity. -/
theorem trans'
    {d : Nat}
    {x y z : Tuple α d}
    (hxy :
      ConcreteCanonicalLearnerDerives K obs f x y)
    (hyz :
      ConcreteCanonicalLearnerDerives K obs f y z) :
    ConcreteCanonicalLearnerDerives K obs f x z :=
  ConcreteCanonicalLearnerDerives.trans hxy hyz

/-- Every concrete canonical-learner derivation is a verified reachable
sample-level derivation. -/
theorem toSampleLearnerReachable
    {d : Nat}
    {x y : Tuple α d}
    (h :
      ConcreteCanonicalLearnerDerives K obs f x y) :
    SampleLearnerReachable K obs f x y := by
  induction h with

  | self x =>
      exact SampleLearnerReachable.self x

  | unit hd hpos U hrest ih =>
      exact SampleLearnerReachable.unit
        hd hpos U.evidence ih

  | binary he hdB hdC hepos hdBpos hdCpos B
      hleft hright ihleft ihright =>
      have hbinary :
          SampleLearnerReachable K obs f
            (evalTemplateTuple B.body
              B.leftSource B.rightSource)
            (evalTemplateTuple B.body _ _) :=
        SampleLearnerReachable.binary
          he hepos B.evidence ihleft ihright
      rw [← B.source_eq_composition] at hbinary
      exact hbinary

  | trans hxy hyz ihxy ihyz =>
      exact SampleLearnerReachable.trans ihxy ihyz

/-- Concrete derivations inherit semantic soundness from
`SampleLearnerReachable`. -/
theorem sound_for_grammar
    {N : Type w}
    (G : WorkingMCFG N α)
    {d : Nat}
    {x y : Tuple α d}
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage)
    (hK : PositiveSample G K)
    (h :
      ConcreteCanonicalLearnerDerives K obs f x y) :
    GrammarNamedDistributionalEquivalent
      G obs y x :=
  h.toSampleLearnerReachable.sound_for_grammar
    G hL hK

/-- Concrete derivations preserve observed tuple type for every promised
positive target. -/
theorem tupleType_eq_for_grammar
    {N : Type w}
    (G : WorkingMCFG N α)
    {d : Nat}
    {x y : Tuple α d}
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage)
    (hK : PositiveSample G K)
    (h :
      ConcreteCanonicalLearnerDerives K obs f x y) :
    tupleType obs y = tupleType obs x :=
  h.toSampleLearnerReachable.tupleType_eq_for_grammar
    G hL hK

end ConcreteCanonicalLearnerDerives

end ConcreteTupleDerivations


section ConcreteStringLanguage

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- String derivation of the concrete canonical learner.

The source must be an actual sample word. -/
structure ConcreteCanonicalStringDerives
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (word : Word α) where

  startWord : Word α

  start_mem :
    startWord ∈ K

  derives :
    ConcreteCanonicalLearnerDerives K obs f
      (singletonTuple startWord)
      (singletonTuple word)

/-- Language generated by the concrete canonical learner. -/
def ConcreteCanonicalLearnerLanguage
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    Set (Word α) :=
  { word |
      ConcreteCanonicalStringDerives
        K obs f word }

namespace ConcreteCanonicalStringDerives

variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Every sample word is generated by the concrete learner. -/
def of_sample_word
    {word : Word α}
    (hword : word ∈ K) :
    ConcreteCanonicalStringDerives
      K obs f word :=
  { startWord := word
    start_mem := hword
    derives :=
      ConcreteCanonicalLearnerDerives.self
        (singletonTuple word) }

/-- Translate a concrete string derivation to the existing reachable string
derivation. -/
def toReachableSampleStringDerives
    {word : Word α}
    (D :
      ConcreteCanonicalStringDerives
        K obs f word) :
    ReachableSampleStringDerives
      K obs f word :=
  { startWord := D.startWord
    start_mem := D.start_mem
    reachable :=
      D.derives.toSampleLearnerReachable }

/-- Concrete string derivations are sound for every positive promised target. -/
theorem sound_for_grammar
    {N : Type w}
    (G : WorkingMCFG N α)
    {word : Word α}
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage)
    (hK : PositiveSample G K)
    (D :
      ConcreteCanonicalStringDerives
        K obs f word) :
    word ∈ G.StringLanguage :=
  D.toReachableSampleStringDerives.sound_for_grammar
    G hL hK

end ConcreteCanonicalStringDerives

/-- The concrete learner language is included in the previously verified
reachable sample language. -/
theorem concreteCanonicalLearnerLanguage_subset_reachable
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    ConcreteCanonicalLearnerLanguage K obs f ⊆
      ReachableSampleStringLanguage K obs f := by
  intro word hword
  exact hword.toReachableSampleStringDerives

/-- The finite sample itself is included in the concrete learner language. -/
theorem sample_subset_concreteCanonicalLearnerLanguage
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (K : Set (Word α)) ⊆
      ConcreteCanonicalLearnerLanguage K obs f := by
  intro word hword
  exact
    ConcreteCanonicalStringDerives.of_sample_word
      (obs := obs) (f := f) hword

/-- Soundness of the concrete canonical learner language. -/
theorem concreteCanonicalLearnerLanguage_sound
    {N : Type w}
    (G : WorkingMCFG N α)
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage)
    (hK : PositiveSample G K) :
    ConcreteCanonicalLearnerLanguage K obs f ⊆
      G.StringLanguage := by
  intro word hword
  exact hword.sound_for_grammar G hL hK

end ConcreteStringLanguage


section SetDrivenConcreteLearner

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- The concrete learner hypothesis is its finite input sample.

All rule sets and its language are reconstructed from that finite sample,
`obs`, and `f`; no target grammar is stored in the hypothesis. -/
abbrev ConcreteCanonicalLearnerHyp
    (α : Type u) :=
  Finset (Word α)

/-- Target-independent set-driven concrete learner. -/
def concreteCanonicalLearner :
    SetDrivenLearner α
      (ConcreteCanonicalLearnerHyp α) :=
  fun K => K

/-- Language interpretation of a concrete learner hypothesis. -/
def concreteCanonicalHypLanguage
    (obs : α → M)
    (f : Nat)
    (H : ConcreteCanonicalLearnerHyp α) :
    Set (Word α) :=
  ConcreteCanonicalLearnerLanguage H obs f

@[simp] theorem concreteCanonicalLearner_apply
    (K : Finset (Word α)) :
    concreteCanonicalLearner
      (α := α) K = K :=
  rfl

@[simp] theorem concreteCanonicalHypLanguage_apply
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    concreteCanonicalHypLanguage obs f
        (concreteCanonicalLearner
          (α := α) K) =
      ConcreteCanonicalLearnerLanguage K obs f :=
  rfl

end SetDrivenConcreteLearner


/-!
OPEN GOAL for the next file:

```lean
ReachableSampleStringLanguage K obs f ⊆
  ConcreteCanonicalLearnerLanguage K obs f
```

A direct proof requires finite-enumeration completeness lemmas converting every

```lean
U : SampleUnitEvidence K obs x y
```

into membership of a corresponding element of

```lean
concreteUnitRules K obs d
```

and every

```lean
B : SampleBinaryEvidence K parent body x y
```

used at arities at most `f` into membership of a corresponding element of

```lean
concreteBinaryWitnesses K e dB dC.
```

The current file proves the forward inclusion without hiding that remaining
enumeration theorem in an assumption record.
-/

end MCFG
