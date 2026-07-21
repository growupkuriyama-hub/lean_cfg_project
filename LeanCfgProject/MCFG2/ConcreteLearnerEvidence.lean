/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.LearnerDerivationSoundness

/-!
# ConcreteLearnerEvidence.lean

Tenth clean Lean experiment for the fixed-observation MCFG project.

The previous file proved soundness for an abstract learner-derivation relation
whose unit and binary steps were already justified by target-language evidence.

This file connects finite positive samples to that abstract relation.

The canonical learner is still not fully enumerated here.  Instead, we define
sample-level evidence:

* `SampleUnitEvidence`: two tuples occur in the same sample context and have
  the same observation type;
* `SampleBinaryEvidence`: a sample word witnesses a parent template
  composition, together with the filling-identity witnesses needed for
  substitution.

If `K` is a positive sample for a target grammar `G`, then sample-level evidence
can be converted into target-language evidence.  Therefore sample-level learner
derivations are sound for the target language.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section SampleUnitEvidence

variable {α : Type u} {M : Type v} [Monoid M]

/-- Sample-level evidence for a learner unit rule.

This mirrors the concrete learner's unit-rule guard:
same arity, same componentwise observation type, and one common named context
whose two fillings are both present in the finite sample `K`. -/
structure SampleUnitEvidence
    (K : Finset (Word α))
    {d : Nat} (obs : α → M)
    (x y : Tuple α d) where
  context : NamedSentenceContext α d
  type_eq : tupleType obs x = tupleType obs y
  left_mem : namedFill d context x ∈ K
  right_mem : namedFill d context y ∈ K

namespace SampleUnitEvidence

/-- Convert sample-level unit evidence into target-language unit evidence,
provided the sample is positive for the target grammar. -/
def toNamedUnitEvidence
    {N : Type w}
    {K : Finset (Word α)}
    {d : Nat} {obs : α → M}
    {x y : Tuple α d}
    (G : WorkingMCFG N α)
    (hK : PositiveSample G K)
    (U : SampleUnitEvidence K obs x y) :
    NamedUnitEvidence obs G.StringLanguage x y :=
  { context := U.context,
    type_eq := U.type_eq,
    left_mem := hK (namedFill d U.context x) U.left_mem,
    right_mem := hK (namedFill d U.context y) U.right_mem }

/-- Sample-level unit evidence is semantically sound for a grammar target when
the sample is positive and the grammar language satisfies the promise. -/
theorem sound_for_grammar
    {N : Type w}
    {K : Finset (Word α)}
    (G : WorkingMCFG N α)
    {f d : Nat} {obs : α → M}
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hd : d ≤ f)
    (hpos : 0 < d)
    (hK : PositiveSample G K)
    {x y : Tuple α d}
    (U : SampleUnitEvidence K obs x y) :
    GrammarNamedDistributionalEquivalent G obs x y :=
  (U.toNamedUnitEvidence G hK).sound hL hd hpos

/-- Sample-level unit evidence is symmetric. -/
def symm
    {K : Finset (Word α)}
    {d : Nat} {obs : α → M}
    {x y : Tuple α d}
    (U : SampleUnitEvidence K obs x y) :
    SampleUnitEvidence K obs y x :=
  { context := U.context,
    type_eq := U.type_eq.symm,
    left_mem := U.right_mem,
    right_mem := U.left_mem }

end SampleUnitEvidence

end SampleUnitEvidence


section SampleBinaryEvidence

variable {α : Type u}

/-- Sample-level evidence for a learner binary rule.

`parent_mem` says that the parent filling with the original child tuples is
present in the finite sample.  The two identity fields are the abstract
filling-identity witnesses needed by the soundness proof. -/
structure SampleBinaryEvidence
    (K : Finset (Word α))
    {e dB dC : Nat}
    (parent : NamedSentenceContext α e)
    (body : TemplateTuple α e dB dC)
    (x : Tuple α dB) (y : Tuple α dC) where
  parent_mem : namedFill e parent (evalTemplateTuple body x y) ∈ K
  leftIdentity : LeftFillingIdentity namedFill parent body y
  rightIdentity : ∀ u : Tuple α dB,
    RightFillingIdentity namedFill parent body u

namespace SampleBinaryEvidence

/-- Convert sample-level binary evidence into target-language binary evidence,
provided the sample is positive for the target grammar. -/
def toNamedBinaryEvidence
    {N : Type w} {α : Type u}
    {K : Finset (Word α)}
    {e dB dC : Nat}
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x : Tuple α dB} {y : Tuple α dC}
    (G : WorkingMCFG N α)
    (hK : PositiveSample G K)
    (B : SampleBinaryEvidence K parent body x y) :
    NamedBinaryEvidence G.StringLanguage parent body x y :=
  { parent_mem := hK
      (namedFill e parent (evalTemplateTuple body x y))
      B.parent_mem,
    leftIdentity := B.leftIdentity,
    rightIdentity := B.rightIdentity }

/-- Sample-level binary evidence transports acceptance for a grammar target when
the sample is positive. -/
theorem accepts_for_grammar
    {N : Type w} {α : Type u} {M : Type v} [Monoid M]
    {K : Finset (Word α)}
    (G : WorkingMCFG N α)
    (hK : PositiveSample G K)
    {e dB dC : Nat}
    {obs : α → M}
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x u : Tuple α dB}
    {y v : Tuple α dC}
    (B : SampleBinaryEvidence K parent body x y)
    (hux : GrammarNamedDistributionalEquivalent G obs u x)
    (hvy : GrammarNamedDistributionalEquivalent G obs v y) :
    namedFill e parent (evalTemplateTuple body u v) ∈ G.StringLanguage :=
  (B.toNamedBinaryEvidence G hK).accepts hux hvy

/-- Sample-level binary evidence is semantically sound for a grammar target
under the fixed-observation promise. -/
theorem sound_for_grammar
    {N : Type w} {α : Type u} {M : Type v} [Monoid M]
    {K : Finset (Word α)}
    (G : WorkingMCFG N α)
    {f e dB dC : Nat} {obs : α → M}
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (he : e ≤ f)
    (hpos : 0 < e)
    (hK : PositiveSample G K)
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x u : Tuple α dB}
    {y v : Tuple α dC}
    (B : SampleBinaryEvidence K parent body x y)
    (hux : GrammarNamedDistributionalEquivalent G obs u x)
    (hvy : GrammarNamedDistributionalEquivalent G obs v y) :
    GrammarNamedDistributionalEquivalent G obs
      (evalTemplateTuple body u v)
      (evalTemplateTuple body x y) :=
  (B.toNamedBinaryEvidence G hK).sound hL he hpos hux hvy

end SampleBinaryEvidence

end SampleBinaryEvidence


section SampleLearnerDerivation

variable {α : Type u} {M : Type v} [Monoid M]

/-- Sample-level learner derivations.

This is the sample-evidence version of `AbstractLearnerDerives`.  It is still
abstract relative to the actual finite enumeration of the canonical learner,
but every nontrivial step is now justified by evidence living in the finite
sample `K`. -/
inductive SampleLearnerDerives
    (K : Finset (Word α)) (obs : α → M) (f : Nat) :
    {d : Nat} → Tuple α d → Tuple α d → Prop where
  | self {d : Nat} (x : Tuple α d) :
      SampleLearnerDerives K obs f x x
  | unit {d : Nat} {x y u : Tuple α d}
      (hd : d ≤ f)
      (hpos : 0 < d)
      (U : SampleUnitEvidence K obs x y)
      (hyu : SampleLearnerDerives K obs f y u) :
      SampleLearnerDerives K obs f x u
  | binary {e dB dC : Nat}
      {parent : NamedSentenceContext α e}
      {body : TemplateTuple α e dB dC}
      {x u : Tuple α dB}
      {y v : Tuple α dC}
      (he : e ≤ f)
      (hpos : 0 < e)
      (B : SampleBinaryEvidence K parent body x y)
      (hx : SampleLearnerDerives K obs f x u)
      (hy : SampleLearnerDerives K obs f y v) :
      SampleLearnerDerives K obs f
        (evalTemplateTuple body x y)
        (evalTemplateTuple body u v)

namespace SampleLearnerDerives

variable {K : Finset (Word α)} {obs : α → M} {f : Nat}

/-- Positive samples convert sample-level learner derivations into abstract
target-language learner derivations. -/
theorem toAbstract
    {N : Type w}
    (G : WorkingMCFG N α)
    (hK : PositiveSample G K)
    {d : Nat} {x u : Tuple α d}
    (h : SampleLearnerDerives K obs f x u) :
    AbstractLearnerDerives obs G.StringLanguage f x u := by
  induction h with
  | self x =>
      exact AbstractLearnerDerives.self x
  | unit hd hpos U _ ih =>
      exact AbstractLearnerDerives.unit hd hpos
        (U.toNamedUnitEvidence G hK) ih
  | binary he hpos B _ _ ihx ihy =>
      exact AbstractLearnerDerives.binary he hpos
        (B.toNamedBinaryEvidence G hK) ihx ihy

/-- Soundness of sample-level learner derivations for a grammar target. -/
theorem sound_for_grammar
    {N : Type w}
    (G : WorkingMCFG N α)
    {d : Nat} {x u : Tuple α d}
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hK : PositiveSample G K)
    (h : SampleLearnerDerives K obs f x u) :
    GrammarNamedDistributionalEquivalent G obs u x :=
  grammarAbstractLearnerDerives_sound G hL (h.toAbstract G hK)

/-- A tuple produced by a sample-level learner derivation has the same
componentwise observation type as the source tuple. -/
theorem tupleType_eq_for_grammar
    {N : Type w}
    (G : WorkingMCFG N α)
    {d : Nat} {x u : Tuple α d}
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hK : PositiveSample G K)
    (h : SampleLearnerDerives K obs f x u) :
    tupleType obs u = tupleType obs x :=
  (h.sound_for_grammar G hL hK).1

/-- Accepting named contexts transport from the source tuple to the tuple
produced by a sample-level learner derivation. -/
theorem mem_right_for_grammar
    {N : Type w}
    (G : WorkingMCFG N α)
    {d : Nat} {x u : Tuple α d}
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hK : PositiveSample G K)
    (h : SampleLearnerDerives K obs f x u)
    {c : NamedSentenceContext α d}
    (hc : namedFill d c x ∈ G.StringLanguage) :
    namedFill d c u ∈ G.StringLanguage :=
  grammarAbstractLearnerDerives_mem_right G hL (h.toAbstract G hK) hc

end SampleLearnerDerives

end SampleLearnerDerivation

end MCFG
