/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.ConcreteCanonicalLearnerFiniteObjectMonotone

/-!
# ConcreteCanonicalLearnerFiniteObjectDirectedSystem.lean

The finite hypothesis object produced at one sample has a different dependent
type from the object produced at a larger sample.  The preceding file solved
one transport step by constructing a semantic simulation.

This file proves that those simulations form a coherent directed system.

It adds:

```lean
CorrectedConcreteFiniteHypothesisSimulation.refl
CorrectedConcreteFiniteHypothesisSimulation.comp
```

and proves coherence of derivation transport under identity and composition.

For sample inclusions

```lean
S ⊆ K ⊆ T,
```

the directly reconstructed rule over `T` need not be definitionally equal to
the rule obtained by reconstructing first over `K` and then over `T`.
Nevertheless, both rules preserve exactly the same:

* unit source and target;
* binary source, child sources, and template body.

The file records those pointwise semantic coherence theorems.

For every positive text it then defines:

```lean
correctedConcreteTextFiniteHypothesis
correctedConcreteTextSimulation.
```

These form a directed system indexed by prefix length.  Direct and iterated
transport of listed derivations are propositionally coherent.

Finally, after the selected characteristic-sample coverage stage, every
simulation in this directed system is language exact: its source and target
finite-object languages are both the target language.

No target grammar is used in the rule transport itself.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w

section RuleTransportCoherence

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {S K T : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

/-- Two-step and direct unit-rule transport have the same source tuple. -/
theorem CorrectedConcreteUnitRuleCode.mono_trans_source
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKT :
      (K : Set (Word α)) ⊆
        (T : Set (Word α)))
    (U :
      CorrectedConcreteUnitRuleCode
        S obs f) :
    ((U.mono hSK).mono hKT).source =
      (U.mono (hSK.trans hKT)).source := by
  calc
    ((U.mono hSK).mono hKT).source =
        (U.mono hSK).source :=
      (U.mono hSK).mono_source hKT
    _ = U.source :=
      U.mono_source hSK
    _ =
        (U.mono (hSK.trans hKT)).source :=
      (U.mono_source (hSK.trans hKT)).symm

/-- Two-step and direct unit-rule transport have the same target tuple. -/
theorem CorrectedConcreteUnitRuleCode.mono_trans_target
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKT :
      (K : Set (Word α)) ⊆
        (T : Set (Word α)))
    (U :
      CorrectedConcreteUnitRuleCode
        S obs f) :
    ((U.mono hSK).mono hKT).target =
      (U.mono (hSK.trans hKT)).target := by
  calc
    ((U.mono hSK).mono hKT).target =
        (U.mono hSK).target :=
      (U.mono hSK).mono_target hKT
    _ = U.target :=
      U.mono_target hSK
    _ =
        (U.mono (hSK.trans hKT)).target :=
      (U.mono_target (hSK.trans hKT)).symm

/-- Identity unit-rule transport preserves the source tuple. -/
theorem CorrectedConcreteUnitRuleCode.mono_refl_source
    (U :
      CorrectedConcreteUnitRuleCode
        S obs f) :
    (U.mono
      (Set.Subset.rfl :
        (S : Set (Word α)) ⊆
          (S : Set (Word α)))).source =
      U.source :=
  U.mono_source Set.Subset.rfl

/-- Identity unit-rule transport preserves the target tuple. -/
theorem CorrectedConcreteUnitRuleCode.mono_refl_target
    (U :
      CorrectedConcreteUnitRuleCode
        S obs f) :
    (U.mono
      (Set.Subset.rfl :
        (S : Set (Word α)) ⊆
          (S : Set (Word α)))).target =
      U.target :=
  U.mono_target Set.Subset.rfl


/-- Two-step and direct binary-rule transport have the same parent source. -/
theorem CorrectedConcreteBinaryRuleCode.mono_trans_source
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKT :
      (K : Set (Word α)) ⊆
        (T : Set (Word α)))
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    ((B.mono hSK).mono hKT).source =
      (B.mono (hSK.trans hKT)).source := by
  calc
    ((B.mono hSK).mono hKT).source =
        (B.mono hSK).source :=
      (B.mono hSK).mono_source hKT
    _ = B.source :=
      B.mono_source hSK
    _ =
        (B.mono (hSK.trans hKT)).source :=
      (B.mono_source (hSK.trans hKT)).symm

/-- Two-step and direct binary-rule transport have the same left source. -/
theorem CorrectedConcreteBinaryRuleCode.mono_trans_leftSource
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKT :
      (K : Set (Word α)) ⊆
        (T : Set (Word α)))
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    ((B.mono hSK).mono hKT).leftSource =
      (B.mono (hSK.trans hKT)).leftSource := by
  calc
    ((B.mono hSK).mono hKT).leftSource =
        (B.mono hSK).leftSource :=
      (B.mono hSK).mono_leftSource hKT
    _ = B.leftSource :=
      B.mono_leftSource hSK
    _ =
        (B.mono (hSK.trans hKT)).leftSource :=
      (B.mono_leftSource (hSK.trans hKT)).symm

/-- Two-step and direct binary-rule transport have the same right source. -/
theorem CorrectedConcreteBinaryRuleCode.mono_trans_rightSource
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKT :
      (K : Set (Word α)) ⊆
        (T : Set (Word α)))
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    ((B.mono hSK).mono hKT).rightSource =
      (B.mono (hSK.trans hKT)).rightSource := by
  calc
    ((B.mono hSK).mono hKT).rightSource =
        (B.mono hSK).rightSource :=
      (B.mono hSK).mono_rightSource hKT
    _ = B.rightSource :=
      B.mono_rightSource hSK
    _ =
        (B.mono (hSK.trans hKT)).rightSource :=
      (B.mono_rightSource (hSK.trans hKT)).symm

/-- Two-step and direct binary-rule transport have the same template body. -/
theorem CorrectedConcreteBinaryRuleCode.mono_trans_body
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKT :
      (K : Set (Word α)) ⊆
        (T : Set (Word α)))
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    ((B.mono hSK).mono hKT).body =
      (B.mono (hSK.trans hKT)).body := by
  calc
    ((B.mono hSK).mono hKT).body =
        (B.mono hSK).body :=
      (B.mono hSK).mono_body hKT
    _ = B.body :=
      B.mono_body hSK
    _ =
        (B.mono (hSK.trans hKT)).body :=
      (B.mono_body (hSK.trans hKT)).symm

/-- Identity binary-rule transport preserves the parent source. -/
theorem CorrectedConcreteBinaryRuleCode.mono_refl_source
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    (B.mono
      (Set.Subset.rfl :
        (S : Set (Word α)) ⊆
          (S : Set (Word α)))).source =
      B.source :=
  B.mono_source Set.Subset.rfl

/-- Identity binary-rule transport preserves the left source. -/
theorem CorrectedConcreteBinaryRuleCode.mono_refl_leftSource
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    (B.mono
      (Set.Subset.rfl :
        (S : Set (Word α)) ⊆
          (S : Set (Word α)))).leftSource =
      B.leftSource :=
  B.mono_leftSource Set.Subset.rfl

/-- Identity binary-rule transport preserves the right source. -/
theorem CorrectedConcreteBinaryRuleCode.mono_refl_rightSource
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    (B.mono
      (Set.Subset.rfl :
        (S : Set (Word α)) ⊆
          (S : Set (Word α)))).rightSource =
      B.rightSource :=
  B.mono_rightSource Set.Subset.rfl

/-- Identity binary-rule transport preserves the template body. -/
theorem CorrectedConcreteBinaryRuleCode.mono_refl_body
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    (B.mono
      (Set.Subset.rfl :
        (S : Set (Word α)) ⊆
          (S : Set (Word α)))).body =
      B.body :=
  B.mono_body Set.Subset.rfl

end RuleTransportCoherence


section SimulationIdentityAndComposition

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {S K T : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesisSimulation

/-- Identity semantic simulation of one finite hypothesis object. -/
def refl
    (H :
      CorrectedConcreteFiniteHypothesis
        S obs f) :
    CorrectedConcreteFiniteHypothesisSimulation
      H H where

  unitMap :=
    fun U => U

  unitMap_mem :=
    fun U hU => hU

  unitMap_source :=
    fun U => rfl

  unitMap_target :=
    fun U => rfl

  binaryMap :=
    fun B => B

  binaryMap_mem :=
    fun B hB => hB

  binaryMap_source :=
    fun B => rfl

  binaryMap_leftSource :=
    fun B => rfl

  binaryMap_rightSource :=
    fun B => rfl

  binaryMap_body :=
    fun B => rfl

/-- Composition of finite-hypothesis simulations. -/
def comp
    {HS :
      CorrectedConcreteFiniteHypothesis
        S obs f}
    {HK :
      CorrectedConcreteFiniteHypothesis
        K obs f}
    {HT :
      CorrectedConcreteFiniteHypothesis
        T obs f}
    (Φ :
      CorrectedConcreteFiniteHypothesisSimulation
        HS HK)
    (Ψ :
      CorrectedConcreteFiniteHypothesisSimulation
        HK HT) :
    CorrectedConcreteFiniteHypothesisSimulation
      HS HT where

  unitMap :=
    fun U =>
      Ψ.unitMap (Φ.unitMap U)

  unitMap_mem :=
    fun U hU =>
      Ψ.unitMap_mem
        (Φ.unitMap U)
        (Φ.unitMap_mem U hU)

  unitMap_source :=
    fun U => by
      calc
        (Ψ.unitMap (Φ.unitMap U)).source =
            (Φ.unitMap U).source :=
          Ψ.unitMap_source (Φ.unitMap U)
        _ = U.source :=
          Φ.unitMap_source U

  unitMap_target :=
    fun U => by
      calc
        (Ψ.unitMap (Φ.unitMap U)).target =
            (Φ.unitMap U).target :=
          Ψ.unitMap_target (Φ.unitMap U)
        _ = U.target :=
          Φ.unitMap_target U

  binaryMap :=
    fun B =>
      Ψ.binaryMap (Φ.binaryMap B)

  binaryMap_mem :=
    fun B hB =>
      Ψ.binaryMap_mem
        (Φ.binaryMap B)
        (Φ.binaryMap_mem B hB)

  binaryMap_source :=
    fun B => by
      calc
        (Ψ.binaryMap (Φ.binaryMap B)).source =
            (Φ.binaryMap B).source :=
          Ψ.binaryMap_source (Φ.binaryMap B)
        _ = B.source :=
          Φ.binaryMap_source B

  binaryMap_leftSource :=
    fun B => by
      calc
        (Ψ.binaryMap (Φ.binaryMap B)).leftSource =
            (Φ.binaryMap B).leftSource :=
          Ψ.binaryMap_leftSource (Φ.binaryMap B)
        _ = B.leftSource :=
          Φ.binaryMap_leftSource B

  binaryMap_rightSource :=
    fun B => by
      calc
        (Ψ.binaryMap (Φ.binaryMap B)).rightSource =
            (Φ.binaryMap B).rightSource :=
          Ψ.binaryMap_rightSource (Φ.binaryMap B)
        _ = B.rightSource :=
          Φ.binaryMap_rightSource B

  binaryMap_body :=
    fun B => by
      calc
        (Ψ.binaryMap (Φ.binaryMap B)).body =
            (Φ.binaryMap B).body :=
          Ψ.binaryMap_body (Φ.binaryMap B)
        _ = B.body :=
          Φ.binaryMap_body B

/-- Identity simulation does not change the proposition proved by a listed
derivation. -/
theorem derives_refl
    (H :
      CorrectedConcreteFiniteHypothesis
        S obs f)
    {d : Nat}
    {x y : Tuple α d}
    (h :
      ListedFiniteCorrectedConcreteLearnerDerives
        S obs f H x y) :
    (refl H).derives h = h := by
  exact Subsingleton.elim _ _

/-- Transport by a composite simulation is propositionally coherent with
successive transport. -/
theorem derives_comp
    {HS :
      CorrectedConcreteFiniteHypothesis
        S obs f}
    {HK :
      CorrectedConcreteFiniteHypothesis
        K obs f}
    {HT :
      CorrectedConcreteFiniteHypothesis
        T obs f}
    (Φ :
      CorrectedConcreteFiniteHypothesisSimulation
        HS HK)
    (Ψ :
      CorrectedConcreteFiniteHypothesisSimulation
        HK HT)
    {d : Nat}
    {x y : Tuple α d}
    (h :
      ListedFiniteCorrectedConcreteLearnerDerives
        S obs f HS x y) :
    (comp Φ Ψ).derives h =
      Ψ.derives (Φ.derives h) := by
  exact Subsingleton.elim _ _

/-- Any two simulations with the same endpoints induce propositionally equal
transport proofs. -/
theorem derives_proof_irrel
    {HS :
      CorrectedConcreteFiniteHypothesis
        S obs f}
    {HK :
      CorrectedConcreteFiniteHypothesis
        K obs f}
    (Φ Ψ :
      CorrectedConcreteFiniteHypothesisSimulation
        HS HK)
    {d : Nat}
    {x y : Tuple α d}
    (h :
      ListedFiniteCorrectedConcreteLearnerDerives
        S obs f HS x y) :
    Φ.derives h =
      Ψ.derives h := by
  exact Subsingleton.elim _ _

/-- A simulation induces inclusion of the listed finite-object languages once
start words of the source sample remain present in the target sample. -/
theorem language_subset
    {HS :
      CorrectedConcreteFiniteHypothesis
        S obs f}
    {HK :
      CorrectedConcreteFiniteHypothesis
        K obs f}
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (Φ :
      CorrectedConcreteFiniteHypothesisSimulation
        HS HK) :
    HS.Language ⊆
      HK.Language := by
  intro word hword
  exact hword.mono hSK Φ

/-- Language inclusion induced by composite simulations is the transitive
composite of the two component inclusions. -/
theorem language_subset_comp
    {HS :
      CorrectedConcreteFiniteHypothesis
        S obs f}
    {HK :
      CorrectedConcreteFiniteHypothesis
        K obs f}
    {HT :
      CorrectedConcreteFiniteHypothesis
        T obs f}
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKT :
      (K : Set (Word α)) ⊆
        (T : Set (Word α)))
    (Φ :
      CorrectedConcreteFiniteHypothesisSimulation
        HS HK)
    (Ψ :
      CorrectedConcreteFiniteHypothesisSimulation
        HK HT) :
    HS.Language ⊆
      HT.Language :=
  (Φ.language_subset hSK).trans
    (Ψ.language_subset hKT)

end CorrectedConcreteFiniteHypothesisSimulation

end SimulationIdentityAndComposition


section SampleSubsetSimulationCoherence

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable {S K T : Finset (Word α)}
variable {obs : α → M}
variable {f : Nat}

namespace CorrectedConcreteFiniteHypothesisSimulation

/-- Direct and two-step sample-extension simulations have semantically
coherent unit-rule maps. -/
theorem ofSampleSubset_comp_unit_coherent
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKT :
      (K : Set (Word α)) ⊆
        (T : Set (Word α)))
    (HS :
      CorrectedConcreteFiniteHypothesis
        S obs f)
    (HK :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (HT :
      CorrectedConcreteFiniteHypothesis
        T obs f)
    (U :
      CorrectedConcreteUnitRuleCode
        S obs f) :
    let direct :=
      ofSampleSubset
        (hSK.trans hKT) HS HT
    let sequential :=
      comp
        (ofSampleSubset hSK HS HK)
        (ofSampleSubset hKT HK HT)
    (sequential.unitMap U).source =
        (direct.unitMap U).source ∧
      (sequential.unitMap U).target =
        (direct.unitMap U).target := by
  dsimp [ofSampleSubset, comp]
  exact
    ⟨U.mono_trans_source hSK hKT,
      U.mono_trans_target hSK hKT⟩

/-- Direct and two-step sample-extension simulations have semantically
coherent binary-rule maps. -/
theorem ofSampleSubset_comp_binary_coherent
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKT :
      (K : Set (Word α)) ⊆
        (T : Set (Word α)))
    (HS :
      CorrectedConcreteFiniteHypothesis
        S obs f)
    (HK :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (HT :
      CorrectedConcreteFiniteHypothesis
        T obs f)
    (B :
      CorrectedConcreteBinaryRuleCode
        S f) :
    let direct :=
      ofSampleSubset
        (hSK.trans hKT) HS HT
    let sequential :=
      comp
        (ofSampleSubset hSK HS HK)
        (ofSampleSubset hKT HK HT)
    (sequential.binaryMap B).source =
        (direct.binaryMap B).source ∧
      (sequential.binaryMap B).leftSource =
        (direct.binaryMap B).leftSource ∧
      (sequential.binaryMap B).rightSource =
        (direct.binaryMap B).rightSource ∧
      (sequential.binaryMap B).body =
        (direct.binaryMap B).body := by
  dsimp [ofSampleSubset, comp]
  exact
    ⟨B.mono_trans_source hSK hKT,
      B.mono_trans_leftSource hSK hKT,
      B.mono_trans_rightSource hSK hKT,
      B.mono_trans_body hSK hKT⟩

/-- Direct and two-step sample-extension transport of a listed derivation are
propositionally equal. -/
theorem ofSampleSubset_comp_derives_coherent
    (hSK :
      (S : Set (Word α)) ⊆
        (K : Set (Word α)))
    (hKT :
      (K : Set (Word α)) ⊆
        (T : Set (Word α)))
    (HS :
      CorrectedConcreteFiniteHypothesis
        S obs f)
    (HK :
      CorrectedConcreteFiniteHypothesis
        K obs f)
    (HT :
      CorrectedConcreteFiniteHypothesis
        T obs f)
    {d : Nat}
    {x y : Tuple α d}
    (h :
      ListedFiniteCorrectedConcreteLearnerDerives
        S obs f HS x y) :
    (ofSampleSubset
      (hSK.trans hKT) HS HT).derives h =
      (ofSampleSubset hKT HK HT).derives
        ((ofSampleSubset hSK HS HK).derives h) := by
  exact Subsingleton.elim _ _

end CorrectedConcreteFiniteHypothesisSimulation

end SampleSubsetSimulationCoherence


section TextPrefixDirectedSystem

variable {α : Type u}
variable {M : Type v} [Monoid M]
variable [DecidableEq α]

/-- Canonical finite hypothesis at one text prefix. -/
noncomputable def correctedConcreteTextFiniteHypothesis
    {L : Set (Word α)}
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat) :
    CorrectedConcreteFiniteHypothesis
      (T.prefixSample n) obs f :=
  correctedConcreteFiniteHypothesis
    (T.prefixSample n) obs f

/-- Canonical finite-hypothesis simulation along a monotone text-prefix
inclusion. -/
noncomputable def correctedConcreteTextSimulation
    {L : Set (Word α)}
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    {m n : Nat}
    (hmn : m ≤ n) :
    CorrectedConcreteFiniteHypothesisSimulation
      (correctedConcreteTextFiniteHypothesis
        obs f T m)
      (correctedConcreteTextFiniteHypothesis
        obs f T n) :=
  CorrectedConcreteFiniteHypothesisSimulation.ofSampleSubset
    (T.prefixSample_mono hmn)
    (correctedConcreteTextFiniteHypothesis
      obs f T m)
    (correctedConcreteTextFiniteHypothesis
      obs f T n)

/-- Structural transport of a listed derivation from an earlier text prefix to
a later prefix. -/
theorem correctedConcreteTextSimulation_derives
    {L : Set (Word α)}
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    {m n : Nat}
    (hmn : m ≤ n)
    {d : Nat}
    {x y : Tuple α d}
    (h :
      ListedFiniteCorrectedConcreteLearnerDerives
        (T.prefixSample m) obs f
        (correctedConcreteTextFiniteHypothesis
          obs f T m)
        x y) :
    ListedFiniteCorrectedConcreteLearnerDerives
      (T.prefixSample n) obs f
      (correctedConcreteTextFiniteHypothesis
        obs f T n)
      x y :=
  (correctedConcreteTextSimulation
    obs f T hmn).derives h

/-- The actual finite-object languages along a text form a monotone chain. -/
theorem correctedConcreteTextFiniteHypothesis_language_mono
    {L : Set (Word α)}
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    {m n : Nat}
    (hmn : m ≤ n) :
    (correctedConcreteTextFiniteHypothesis
        obs f T m).Language ⊆
      (correctedConcreteTextFiniteHypothesis
        obs f T n).Language := by
  exact
    (correctedConcreteTextSimulation
      obs f T hmn).language_subset
        (T.prefixSample_mono hmn)

/-- Identity transport at one prefix is propositionally the identity on listed
derivations. -/
theorem correctedConcreteTextSimulation_refl
    {L : Set (Word α)}
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    (n : Nat)
    {d : Nat}
    {x y : Tuple α d}
    (h :
      ListedFiniteCorrectedConcreteLearnerDerives
        (T.prefixSample n) obs f
        (correctedConcreteTextFiniteHypothesis
          obs f T n)
        x y) :
    (correctedConcreteTextSimulation
      obs f T (Nat.le_refl n)).derives h =
      h := by
  exact Subsingleton.elim _ _

/-- Direct transport from prefix `m` to prefix `p` agrees propositionally with
transport through an intermediate prefix `n`. -/
theorem correctedConcreteTextSimulation_trans
    {L : Set (Word α)}
    (obs : α → M)
    (f : Nat)
    (T : TextFor L)
    {m n p : Nat}
    (hmn : m ≤ n)
    (hnp : n ≤ p)
    {d : Nat}
    {x y : Tuple α d}
    (h :
      ListedFiniteCorrectedConcreteLearnerDerives
        (T.prefixSample m) obs f
        (correctedConcreteTextFiniteHypothesis
          obs f T m)
        x y) :
    (correctedConcreteTextSimulation
      obs f T (hmn.trans hnp)).derives h =
      (correctedConcreteTextSimulation
        obs f T hnp).derives
        ((correctedConcreteTextSimulation
          obs f T hmn).derives h) := by
  exact Subsingleton.elim _ _

/-- Text-prefix finite hypotheses, simulations, monotone languages, identity
coherence, and composition coherence form one reusable directed-system
package. -/
theorem correctedConcreteTextFiniteHypothesis_directedSystem_package
    {L : Set (Word α)}
    (obs : α → M)
    (f : Nat)
    (T : TextFor L) :
    (∀ m n : Nat, m ≤ n →
      Nonempty
        (CorrectedConcreteFiniteHypothesisSimulation
          (correctedConcreteTextFiniteHypothesis
            obs f T m)
          (correctedConcreteTextFiniteHypothesis
            obs f T n))) ∧
    (∀ m n : Nat, m ≤ n →
      (correctedConcreteTextFiniteHypothesis
          obs f T m).Language ⊆
        (correctedConcreteTextFiniteHypothesis
          obs f T n).Language) ∧
    (∀ n : Nat,
      ∀ d : Nat,
        ∀ x y : Tuple α d,
          ∀ h :
            ListedFiniteCorrectedConcreteLearnerDerives
              (T.prefixSample n) obs f
              (correctedConcreteTextFiniteHypothesis
                obs f T n)
              x y,
            (correctedConcreteTextSimulation
              obs f T (Nat.le_refl n)).derives h =
              h) ∧
    (∀ m n p : Nat,
      ∀ hmn : m ≤ n,
        ∀ hnp : n ≤ p,
          ∀ d : Nat,
            ∀ x y : Tuple α d,
              ∀ h :
                ListedFiniteCorrectedConcreteLearnerDerives
                  (T.prefixSample m) obs f
                  (correctedConcreteTextFiniteHypothesis
                    obs f T m)
                  x y,
                (correctedConcreteTextSimulation
                  obs f T (hmn.trans hnp)).derives h =
                  (correctedConcreteTextSimulation
                    obs f T hnp).derives
                    ((correctedConcreteTextSimulation
                      obs f T hmn).derives h)) := by
  refine ⟨?_, ?_, ?_, ?_⟩

  · intro m n hmn
    exact
      ⟨correctedConcreteTextSimulation
        obs f T hmn⟩

  · intro m n hmn
    exact
      correctedConcreteTextFiniteHypothesis_language_mono
        obs f T hmn

  · intro n d x y h
    exact
      correctedConcreteTextSimulation_refl
        obs f T n h

  · intro m n p hmn hnp d x y h
    exact
      correctedConcreteTextSimulation_trans
        obs f T hmn hnp h

end TextPrefixDirectedSystem


section EventuallyExactDirectedSystem

variable {α : Type u}
variable {M : Type v}
variable [Fintype M]
variable [DecidableEq α] [DecidableEq M]
variable [Monoid M]
variable (obs : α → M)
variable (f : Nat)

/-- After the selected coverage stage, every canonical simulation between text
prefix hypotheses has source and target language equal to the target. -/
theorem correctedConcreteTextSimulation_eventually_languageExact
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f)
    (T : TextFor L) :
    ∃ n0 : Nat,
      ∀ m n : Nat,
        n0 ≤ m →
        m ≤ n →
        let Hm :=
          correctedConcreteTextFiniteHypothesis
            obs f T m
        let Hn :=
          correctedConcreteTextFiniteHypothesis
            obs f T n
        Nonempty
            (CorrectedConcreteFiniteHypothesisSimulation
              Hm Hn) ∧
          Hm.Language = L ∧
          Hn.Language = L ∧
          Hm.Language = Hn.Language := by

  refine
    ⟨startRootedCorrectedConcreteTargetCoverageStage
        (v := w) obs f hL T,
      ?_⟩

  intro m n hm hmn
  dsimp

  have hn :
      startRootedCorrectedConcreteTargetCoverageStage
          (v := w) obs f hL T ≤ n :=
    hm.trans hmn

  have hmExact :
      (correctedConcreteTextFiniteHypothesis
          obs f T m).Language = L := by
    change
      correctedConcreteFiniteObjectHypLanguage
          obs f
          (correctedConcreteFiniteObjectLearner
            obs f (T.prefixSample m)) =
        L
    exact
      correctedConcreteFiniteObjectLearner_correct_after_startRootedCoverageStage
        (v := w) obs f hL T hm

  have hnExact :
      (correctedConcreteTextFiniteHypothesis
          obs f T n).Language = L := by
    change
      correctedConcreteFiniteObjectHypLanguage
          obs f
          (correctedConcreteFiniteObjectLearner
            obs f (T.prefixSample n)) =
        L
    exact
      correctedConcreteFiniteObjectLearner_correct_after_startRootedCoverageStage
        (v := w) obs f hL T hn

  exact
    ⟨⟨correctedConcreteTextSimulation
        obs f T hmn⟩,
      hmExact,
      hnExact,
      hmExact.trans hnExact.symm⟩

/-- After the selected stage, every structural prefix simulation is a
language-equivalence witness between two actual finite rule objects. -/
theorem correctedConcreteTextFiniteHypothesis_eventually_constant_directedSystem
    {L : Set (Word α)}
    (hL :
      L ∈ StartRootedCorrectedConcreteTargetClass
        (v := w) α M obs f)
    (T : TextFor L) :
    ∃ n0 : Nat,
      (∀ n : Nat, n0 ≤ n →
        (correctedConcreteTextFiniteHypothesis
            obs f T n).Language =
          L) ∧
      (∀ m n : Nat, n0 ≤ m → m ≤ n →
        Nonempty
          (CorrectedConcreteFiniteHypothesisSimulation
            (correctedConcreteTextFiniteHypothesis
              obs f T m)
            (correctedConcreteTextFiniteHypothesis
              obs f T n)) ∧
        (correctedConcreteTextFiniteHypothesis
            obs f T m).Language =
          (correctedConcreteTextFiniteHypothesis
            obs f T n).Language) := by

  let n0 :=
    startRootedCorrectedConcreteTargetCoverageStage
      (v := w) obs f hL T

  refine ⟨n0, ?_, ?_⟩

  · intro n hn
    change
      correctedConcreteFiniteObjectHypLanguage
          obs f
          (correctedConcreteFiniteObjectLearner
            obs f (T.prefixSample n)) =
        L
    exact
      correctedConcreteFiniteObjectLearner_correct_after_startRootedCoverageStage
        (v := w) obs f hL T hn

  · intro m n hm hmn

    have hn :
        n0 ≤ n :=
      hm.trans hmn

    have hmExact :
        (correctedConcreteTextFiniteHypothesis
            obs f T m).Language = L := by
      change
        correctedConcreteFiniteObjectHypLanguage
            obs f
            (correctedConcreteFiniteObjectLearner
              obs f (T.prefixSample m)) =
          L
      exact
        correctedConcreteFiniteObjectLearner_correct_after_startRootedCoverageStage
          (v := w) obs f hL T hm

    have hnExact :
        (correctedConcreteTextFiniteHypothesis
            obs f T n).Language = L := by
      change
        correctedConcreteFiniteObjectHypLanguage
            obs f
            (correctedConcreteFiniteObjectLearner
              obs f (T.prefixSample n)) =
          L
      exact
        correctedConcreteFiniteObjectLearner_correct_after_startRootedCoverageStage
          (v := w) obs f hL T hn

    exact
      ⟨⟨correctedConcreteTextSimulation
          obs f T hmn⟩,
        hmExact.trans hnExact.symm⟩

/-- Paper-facing conclusion package: text prefixes form a coherent directed
system of finite rule objects, and the system becomes semantically constant
after the selected characteristic-sample stage. -/
theorem correctedConcreteFiniteObject_directedStabilization_package :
    ∀ L : Set (Word α),
      L ∈ StartRootedCorrectedConcreteTargetClass
          (v := w) α M obs f →
      ∀ T : TextFor L,
        (∀ m n : Nat, m ≤ n →
          Nonempty
            (CorrectedConcreteFiniteHypothesisSimulation
              (correctedConcreteTextFiniteHypothesis
                obs f T m)
              (correctedConcreteTextFiniteHypothesis
                obs f T n))) ∧
        (∀ m n : Nat, m ≤ n →
          (correctedConcreteTextFiniteHypothesis
              obs f T m).Language ⊆
            (correctedConcreteTextFiniteHypothesis
              obs f T n).Language) ∧
        (∃ n0 : Nat,
          (∀ n : Nat, n0 ≤ n →
            (correctedConcreteTextFiniteHypothesis
                obs f T n).Language =
              L) ∧
          (∀ m n : Nat, n0 ≤ m → m ≤ n →
            Nonempty
              (CorrectedConcreteFiniteHypothesisSimulation
                (correctedConcreteTextFiniteHypothesis
                  obs f T m)
                (correctedConcreteTextFiniteHypothesis
                  obs f T n)) ∧
            (correctedConcreteTextFiniteHypothesis
                obs f T m).Language =
              (correctedConcreteTextFiniteHypothesis
                obs f T n).Language)) := by

  intro L hL T

  exact
    ⟨fun m n hmn =>
        ⟨correctedConcreteTextSimulation
          obs f T hmn⟩,
      fun m n hmn =>
        correctedConcreteTextFiniteHypothesis_language_mono
          obs f T hmn,
      correctedConcreteTextFiniteHypothesis_eventually_constant_directedSystem
        (v := w) obs f hL T⟩

end EventuallyExactDirectedSystem

end MCFG
