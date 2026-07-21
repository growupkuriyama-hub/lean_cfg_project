/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.BinaryWitnessEnumerationCompleteness

/-!
# ExactConcreteCanonicalLearnerEquivalence.lean

The broad relation `SampleLearnerReachable` permits arbitrary
`SampleBinaryEvidence`; it does not remember that the binary template is
exact-once.  Therefore it cannot be definitionally equivalent to the finite
exact-once binary-rule enumeration.

This file introduces the precise intermediate semantics:

```lean
ExactSampleLearnerReachable
```

Its binary constructor carries

```lean
TemplateTuple.ExactlyOnce body
```

and explicit fan-out bounds for the parent and both children.

It also introduces the corrected concrete learner relation using

```lean
ConcreteUnitRule
CorrectedConcreteBinaryRule
```

where the binary-rule enumeration uses the corrected finite template bound

```lean
sampleLengthBudget K + dB + dC.
```

The main results are genuine two-way translations:

```lean
CorrectedConcreteCanonicalLearnerDerives.toExact
ExactSampleLearnerReachable.toCorrectedConcrete
```

and consequently:

```lean
correctedConcreteCanonicalLearnerLanguage_eq_exactReachable
```

Thus the finite enumerated learner and the exact-once reachable semantics have
the same string language.

No target grammar is an input to either learner definition.
-/

namespace MCFG

universe u v w

section ExactReachableRelation

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Exact-once fragment of the reachable sample learner.

Unlike the older broad relation, every binary step records exact-once
linearity of its template. -/
inductive ExactSampleLearnerReachable
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    {d : Nat} → Tuple α d → Tuple α d → Prop where

  | self
      {d : Nat}
      (x : Tuple α d) :
      ExactSampleLearnerReachable K obs f x x

  | unit
      {d : Nat}
      {x y u : Tuple α d}
      (hd : d ≤ f)
      (hpos : 0 < d)
      (U : SampleUnitEvidence K obs x y)
      (hyu :
        ExactSampleLearnerReachable K obs f y u) :
      ExactSampleLearnerReachable K obs f x u

  | binary
      {e dB dC : Nat}
      {parent : NamedSentenceContext α e}
      {body : TemplateTuple α e dB dC}
      {x u : Tuple α dB}
      {y v : Tuple α dC}
      (he : e ≤ f)
      (hdB : dB ≤ f)
      (hdC : dC ≤ f)
      (hepos : 0 < e)
      (hdBpos : 0 < dB)
      (hdCpos : 0 < dC)
      (B : SampleBinaryEvidence K parent body x y)
      (hexact : TemplateTuple.ExactlyOnce body)
      (hx :
        ExactSampleLearnerReachable K obs f x u)
      (hy :
        ExactSampleLearnerReachable K obs f y v) :
      ExactSampleLearnerReachable K obs f
        (evalTemplateTuple body x y)
        (evalTemplateTuple body u v)

  | trans
      {d : Nat}
      {x y z : Tuple α d}
      (hxy :
        ExactSampleLearnerReachable K obs f x y)
      (hyz :
        ExactSampleLearnerReachable K obs f y z) :
      ExactSampleLearnerReachable K obs f x z

namespace ExactSampleLearnerReachable

variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Reflexivity. -/
theorem refl
    {d : Nat}
    (x : Tuple α d) :
    ExactSampleLearnerReachable K obs f x x :=
  ExactSampleLearnerReachable.self x

/-- Transitivity. -/
theorem trans'
    {d : Nat}
    {x y z : Tuple α d}
    (hxy :
      ExactSampleLearnerReachable K obs f x y)
    (hyz :
      ExactSampleLearnerReachable K obs f y z) :
    ExactSampleLearnerReachable K obs f x z :=
  ExactSampleLearnerReachable.trans hxy hyz

/-- Transport an exact reachable derivation across an equality of arities. -/
theorem arityCast
    {d e : Nat}
    (hde : d = e)
    {x y : Tuple α d}
    (h :
      ExactSampleLearnerReachable K obs f x y) :
    ExactSampleLearnerReachable K obs f
      (castTuple hde x)
      (castTuple hde y) := by
  subst e
  simpa using h

/-- Forget the exact-once certificate and obtain the previously verified broad
reachable relation. -/
theorem toSampleLearnerReachable
    {d : Nat}
    {x y : Tuple α d}
    (h :
      ExactSampleLearnerReachable K obs f x y) :
    SampleLearnerReachable K obs f x y := by
  induction h with

  | self x =>
      exact SampleLearnerReachable.self x

  | unit hd hpos U hyu ih =>
      exact SampleLearnerReachable.unit
        hd hpos U ih

  | binary he hdB hdC hepos hdBpos hdCpos
      B hexact hx hy ihx ihy =>
      exact SampleLearnerReachable.binary
        he hepos B ihx ihy

  | trans hxy hyz ihxy ihyz =>
      exact SampleLearnerReachable.trans
        ihxy ihyz

/-- Exact reachable derivations inherit target-language soundness. -/
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
      ExactSampleLearnerReachable K obs f x y) :
    GrammarNamedDistributionalEquivalent
      G obs y x :=
  h.toSampleLearnerReachable.sound_for_grammar
    G hL hK

/-- Exact reachable derivations preserve componentwise observation type. -/
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
      ExactSampleLearnerReachable K obs f x y) :
    tupleType obs y = tupleType obs x :=
  h.toSampleLearnerReachable.
    tupleType_eq_for_grammar G hL hK

end ExactSampleLearnerReachable

end ExactReachableRelation


section CorrectedConcreteRelation

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Concrete canonical learner using the complete unit-rule enumeration and
the corrected exact-once binary-rule enumeration. -/
inductive CorrectedConcreteCanonicalLearnerDerives
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    {d : Nat} → Tuple α d → Tuple α d → Prop where

  | self
      {d : Nat}
      (x : Tuple α d) :
      CorrectedConcreteCanonicalLearnerDerives
        K obs f x x

  | unit
      {d : Nat}
      {u : Tuple α d}
      (hd : d ≤ f)
      (hpos : 0 < d)
      (U : ConcreteUnitRule K obs d)
      (hrest :
        CorrectedConcreteCanonicalLearnerDerives
          K obs f U.target u) :
      CorrectedConcreteCanonicalLearnerDerives
        K obs f U.source u

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
      (B :
        CorrectedConcreteBinaryRule
          K e dB dC)
      (hleft :
        CorrectedConcreteCanonicalLearnerDerives
          K obs f B.leftSource u)
      (hright :
        CorrectedConcreteCanonicalLearnerDerives
          K obs f B.rightSource v) :
      CorrectedConcreteCanonicalLearnerDerives
        K obs f B.source
          (evalTemplateTuple B.body u v)

  | trans
      {d : Nat}
      {x y z : Tuple α d}
      (hxy :
        CorrectedConcreteCanonicalLearnerDerives
          K obs f x y)
      (hyz :
        CorrectedConcreteCanonicalLearnerDerives
          K obs f y z) :
      CorrectedConcreteCanonicalLearnerDerives
        K obs f x z

namespace CorrectedConcreteCanonicalLearnerDerives

variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Reflexivity. -/
theorem refl
    {d : Nat}
    (x : Tuple α d) :
    CorrectedConcreteCanonicalLearnerDerives
      K obs f x x :=
  CorrectedConcreteCanonicalLearnerDerives.self x

/-- Transitivity. -/
theorem trans'
    {d : Nat}
    {x y z : Tuple α d}
    (hxy :
      CorrectedConcreteCanonicalLearnerDerives
        K obs f x y)
    (hyz :
      CorrectedConcreteCanonicalLearnerDerives
        K obs f y z) :
    CorrectedConcreteCanonicalLearnerDerives
      K obs f x z :=
  CorrectedConcreteCanonicalLearnerDerives.trans
    hxy hyz

/-- Every corrected concrete derivation translates to exact reachable
semantics. -/
theorem toExact
    {d : Nat}
    {x y : Tuple α d}
    (h :
      CorrectedConcreteCanonicalLearnerDerives
        K obs f x y) :
    ExactSampleLearnerReachable K obs f x y := by
  induction h with

  | self x =>
      exact ExactSampleLearnerReachable.self x

  | unit hd hpos U hrest ih =>
      exact ExactSampleLearnerReachable.unit
        hd hpos U.evidence ih

  | binary he hdB hdC hepos hdBpos hdCpos
      B hleft hright ihleft ihright =>
      have hbinary :
          ExactSampleLearnerReachable K obs f
            (evalTemplateTuple B.body
              B.leftSource B.rightSource)
            (evalTemplateTuple B.body _ _) :=
        ExactSampleLearnerReachable.binary
          he hdB hdC
          hepos hdBpos hdCpos
          B.evidence
          B.witness.body_exactOnce
          ihleft ihright
      rw [← B.source_eq_composition] at hbinary
      exact hbinary

/-- Corrected concrete derivations inherit broad reachable semantics. -/
theorem toSampleLearnerReachable
    {d : Nat}
    {x y : Tuple α d}
    (h :
      CorrectedConcreteCanonicalLearnerDerives
        K obs f x y) :
    SampleLearnerReachable K obs f x y :=
  h.toExact.toSampleLearnerReachable

/-- Corrected concrete derivations are sound for every promised positive
target. -/
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
      CorrectedConcreteCanonicalLearnerDerives
        K obs f x y) :
    GrammarNamedDistributionalEquivalent
      G obs y x :=
  h.toExact.sound_for_grammar G hL hK

end CorrectedConcreteCanonicalLearnerDerives

end CorrectedConcreteRelation


section ReachableToConcrete

variable {α : Type u}
variable {M : Type v} [Monoid M]

namespace ExactSampleLearnerReachable

variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Translate exact reachable semantics to the corrected finite enumerated
learner.

Unit rules use `concreteUnitRuleOfEvidence`.
Binary rules use `correctedConcreteBinaryRuleOfEvidence`, whose finite
membership was proved in the preceding file. -/
theorem toCorrectedConcrete
    {d : Nat}
    {x y : Tuple α d}
    (h :
      ExactSampleLearnerReachable K obs f x y) :
    CorrectedConcreteCanonicalLearnerDerives
      K obs f x y := by
  induction h with

  | self x =>
      exact
        CorrectedConcreteCanonicalLearnerDerives.self x

  | unit hd hpos U hyu ih =>
      let Q :=
        concreteUnitRuleOfEvidence K obs U

      have hsource :
          Q.source = _ :=
        concreteUnitRuleOfEvidence_source
          K obs U

      have htarget :
          Q.target = _ :=
        concreteUnitRuleOfEvidence_target
          K obs U

      rw [← hsource]
      apply
        CorrectedConcreteCanonicalLearnerDerives.unit
          hd hpos Q
      rw [htarget]
      exact ih

  | binary he hdB hdC hepos hdBpos hdCpos
      B hexact hx hy ihx ihy =>
      let R :=
        correctedConcreteBinaryRuleOfEvidence
          K B hexact

      have hleft :
          CorrectedConcreteCanonicalLearnerDerives
            K obs f R.leftSource _ := by
        rw [correctedConcreteBinaryRuleOfEvidence_leftSource
          K B hexact]
        exact ihx

      have hright :
          CorrectedConcreteCanonicalLearnerDerives
            K obs f R.rightSource _ := by
        rw [correctedConcreteBinaryRuleOfEvidence_rightSource
          K B hexact]
        exact ihy

      have hbinary :
          CorrectedConcreteCanonicalLearnerDerives
            K obs f R.source
              (evalTemplateTuple R.body _ _) :=
        CorrectedConcreteCanonicalLearnerDerives.binary
          he hdB hdC
          hepos hdBpos hdCpos
          R hleft hright

      have hsource :
          R.source =
            evalTemplateTuple _ _ _ :=
        correctedConcreteBinaryRuleOfEvidence_source
          K B hexact

      have hbody :
          R.body = _ :=
        correctedConcreteBinaryRuleOfEvidence_body
          K B hexact

      rw [hsource, hbody] at hbinary
      exact hbinary

  | trans hxy hyz ihxy ihyz =>
      exact
        CorrectedConcreteCanonicalLearnerDerives.trans
          ihxy ihyz

end ExactSampleLearnerReachable

/-- Tuple-level equivalence between corrected finite derivations and exact
reachable semantics. -/
theorem correctedConcreteCanonicalLearnerDerives_iff_exactReachable
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    {d : Nat}
    (x y : Tuple α d) :
    CorrectedConcreteCanonicalLearnerDerives
        K obs f x y ↔
      ExactSampleLearnerReachable K obs f x y := by
  constructor
  · exact
      CorrectedConcreteCanonicalLearnerDerives.toExact
  · exact
      ExactSampleLearnerReachable.toCorrectedConcrete

end ReachableToConcrete


section ExactAndConcreteStringLanguages

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- String derivation using exact reachable tuple semantics. -/
structure ExactReachableSampleStringDerives
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (word : Word α) where

  startWord : Word α

  start_mem :
    startWord ∈ K

  reachable :
    ExactSampleLearnerReachable K obs f
      (singletonTuple startWord)
      (singletonTuple word)

/-- String language generated by exact reachable semantics. -/
def ExactReachableSampleStringLanguage
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    Set (Word α) :=
  { word |
      ExactReachableSampleStringDerives
        K obs f word }

/-- String derivation of the corrected finite enumerated learner. -/
structure CorrectedConcreteCanonicalStringDerives
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (word : Word α) where

  startWord : Word α

  start_mem :
    startWord ∈ K

  derives :
    CorrectedConcreteCanonicalLearnerDerives
      K obs f
      (singletonTuple startWord)
      (singletonTuple word)

/-- Language generated by the corrected concrete canonical learner. -/
def CorrectedConcreteCanonicalLearnerLanguage
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    Set (Word α) :=
  { word |
      CorrectedConcreteCanonicalStringDerives
        K obs f word }

namespace ExactReachableSampleStringDerives

variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Every sample word belongs to the exact reachable language. -/
def of_sample_word
    {word : Word α}
    (hword : word ∈ K) :
    ExactReachableSampleStringDerives
      K obs f word where
  startWord := word
  start_mem := hword
  reachable :=
    ExactSampleLearnerReachable.self
      (singletonTuple word)

/-- Translate exact reachable string derivations to the corrected concrete
learner. -/
def toCorrectedConcrete
    {word : Word α}
    (D :
      ExactReachableSampleStringDerives
        K obs f word) :
    CorrectedConcreteCanonicalStringDerives
      K obs f word where
  startWord := D.startWord
  start_mem := D.start_mem
  derives := D.reachable.toCorrectedConcrete

/-- Forget exactness and obtain the older broad reachable string derivation. -/
def toReachableSampleStringDerives
    {word : Word α}
    (D :
      ExactReachableSampleStringDerives
        K obs f word) :
    ReachableSampleStringDerives
      K obs f word where
  startWord := D.startWord
  start_mem := D.start_mem
  reachable := D.reachable.toSampleLearnerReachable

end ExactReachableSampleStringDerives


namespace CorrectedConcreteCanonicalStringDerives

variable {K : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Every sample word belongs to the corrected concrete language. -/
def of_sample_word
    {word : Word α}
    (hword : word ∈ K) :
    CorrectedConcreteCanonicalStringDerives
      K obs f word where
  startWord := word
  start_mem := hword
  derives :=
    CorrectedConcreteCanonicalLearnerDerives.self
      (singletonTuple word)

/-- Translate corrected concrete string derivations to exact reachable
semantics. -/
def toExact
    {word : Word α}
    (D :
      CorrectedConcreteCanonicalStringDerives
        K obs f word) :
    ExactReachableSampleStringDerives
      K obs f word where
  startWord := D.startWord
  start_mem := D.start_mem
  reachable := D.derives.toExact

/-- Corrected concrete string derivations are sound for every promised positive
target. -/
theorem sound_for_grammar
    {N : Type w}
    (G : WorkingMCFG N α)
    {word : Word α}
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage)
    (hK : PositiveSample G K)
    (D :
      CorrectedConcreteCanonicalStringDerives
        K obs f word) :
    word ∈ G.StringLanguage :=
  D.toExact.toReachableSampleStringDerives.
    sound_for_grammar G hL hK

end CorrectedConcreteCanonicalStringDerives


/-- Corrected finite learner language is contained in exact reachable
semantics. -/
theorem correctedConcreteCanonicalLearnerLanguage_subset_exactReachable
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    CorrectedConcreteCanonicalLearnerLanguage
        K obs f ⊆
      ExactReachableSampleStringLanguage
        K obs f := by
  intro word hword
  exact hword.toExact

/-- Exact reachable semantics is contained in the corrected finite learner
language. -/
theorem exactReachable_subset_correctedConcreteCanonicalLearnerLanguage
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    ExactReachableSampleStringLanguage
        K obs f ⊆
      CorrectedConcreteCanonicalLearnerLanguage
        K obs f := by
  intro word hword
  exact hword.toCorrectedConcrete

/-- The corrected finite enumerated learner and exact reachable semantics
generate exactly the same string language. -/
theorem correctedConcreteCanonicalLearnerLanguage_eq_exactReachable
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    CorrectedConcreteCanonicalLearnerLanguage
        K obs f =
      ExactReachableSampleStringLanguage
        K obs f := by
  apply Set.Subset.antisymm
  · exact
      correctedConcreteCanonicalLearnerLanguage_subset_exactReachable
        K obs f
  · exact
      exactReachable_subset_correctedConcreteCanonicalLearnerLanguage
        K obs f

/-- Exact reachable semantics is contained in the older broad reachable
language. -/
theorem exactReachableSampleStringLanguage_subset_reachable
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    ExactReachableSampleStringLanguage K obs f ⊆
      ReachableSampleStringLanguage K obs f := by
  intro word hword
  exact hword.toReachableSampleStringDerives

/-- The corrected finite learner language is contained in the older broad
reachable language. -/
theorem correctedConcreteCanonicalLearnerLanguage_subset_reachable
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    CorrectedConcreteCanonicalLearnerLanguage
        K obs f ⊆
      ReachableSampleStringLanguage K obs f := by
  rw [correctedConcreteCanonicalLearnerLanguage_eq_exactReachable]
  exact exactReachableSampleStringLanguage_subset_reachable
    K obs f

/-- The finite sample itself is contained in the corrected concrete learner
language. -/
theorem sample_subset_correctedConcreteCanonicalLearnerLanguage
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat) :
    (K : Set (Word α)) ⊆
      CorrectedConcreteCanonicalLearnerLanguage
        K obs f := by
  intro word hword
  exact
    CorrectedConcreteCanonicalStringDerives.of_sample_word
      (obs := obs) (f := f) hword

/-- Soundness of the corrected concrete learner language. -/
theorem correctedConcreteCanonicalLearnerLanguage_sound
    {N : Type w}
    (G : WorkingMCFG N α)
    {K : Finset (Word α)}
    {obs : α → M}
    {f : Nat}
    (hL :
      FixedNamedTupleSubstitutable
        f obs G.StringLanguage)
    (hK : PositiveSample G K) :
    CorrectedConcreteCanonicalLearnerLanguage
        K obs f ⊆
      G.StringLanguage := by
  intro word hword
  exact hword.sound_for_grammar G hL hK

end ExactAndConcreteStringLanguages


section CorrectedSetDrivenLearner

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Target-independent corrected concrete learner. -/
def correctedConcreteCanonicalLearner :
    SetDrivenLearner α (Finset (Word α)) :=
  fun K => K

/-- Language interpretation of the corrected concrete learner hypothesis. -/
def correctedConcreteCanonicalHypLanguage
    (obs : α → M)
    (f : Nat)
    (H : Finset (Word α)) :
    Set (Word α) :=
  CorrectedConcreteCanonicalLearnerLanguage
    H obs f

@[simp] theorem correctedConcreteCanonicalLearner_apply
    (K : Finset (Word α)) :
    correctedConcreteCanonicalLearner
      (α := α) K = K :=
  rfl

@[simp] theorem correctedConcreteCanonicalHypLanguage_apply
    (obs : α → M)
    (f : Nat)
    (K : Finset (Word α)) :
    correctedConcreteCanonicalHypLanguage obs f
        (correctedConcreteCanonicalLearner
          (α := α) K) =
      CorrectedConcreteCanonicalLearnerLanguage
        K obs f :=
  rfl

end CorrectedSetDrivenLearner


/-!
The finite corrected learner is now exactly equivalent to the exact-once
reachable fragment.

The next file should re-run the concrete typed characteristic-sample simulation
with `ExactSampleLearnerReachable` in place of the broad
`SampleLearnerReachable`.  Every binary simulation in
`ConcreteTypedCharacteristicSample.lean` already comes from an exact working
grammar and therefore carries the needed certificate

```lean
hworking.2 τ.baseRule τ.inGrammar :
  τ.baseRule.ExactlyOnce.
```

That will yield exact reconstruction and Gold identification directly for

```lean
CorrectedConcreteCanonicalLearnerLanguage
```

without passing through the broader reachable proxy.
-/

end MCFG
