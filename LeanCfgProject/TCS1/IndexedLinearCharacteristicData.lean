import LeanCfgProject.TCS1.IndexedLinearNormalizationTheorem
import LeanCfgProject.TCS1.LinearCharacteristicSourceBounds

/-!
# TCS #1: characteristic data for arbitrary finite indexed linear CFGs

This module closes the remaining Section 8 composition gap.

Starting from an arbitrary finite indexed CFG whose right-hand sides are
linear, the verified raw preprocessing and specialized linear-spine
normalization produce a concrete separated-start terminal/binary grammar.
The existing linear witness theorem can therefore be instantiated directly.
No already-preprocessed hypothesis remains.

For a fixed finite monoid homomorphism H, fixed-H substitutability of the
original source language yields

* an internally constructed finite characteristic sample;
* exact reconstruction of the original source language;
* an explicit source-polynomial bound on the encoded sample size; and
* conservative Gold identification from positive data.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w z

section IndexedLinearCharacteristicData

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable {M : Type z} [Monoid M] [Fintype M]

variable [Fintype N] [Fintype α] [Fintype P]

/-- Canonical linear sample after the full arbitrary-CFG normalization chain. -/
noncomputable def indexedLinearCanonicalSample
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) :
    Finset (Word α) :=
  concreteLinearCanonicalSample
    H
    (LinearConstructedTerminalRule
      (G.linearPreparedGrammar hlinear))
    (LinearConstructedBinaryRule
      (G.linearPreparedGrammar hlinear))
    (linearConstructedStartRule
      (G.linearPreparedGrammar hlinear) S)
    (G.linearKeepEmpty hlinear S)

/--
Exact normalization transports fixed-H substitutability from the original
linear CFG language to the concrete linear-spine presentation.
-/
theorem indexedLinear_fixedHSubstitutable_normalized
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N)
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules S)) :
    FixedHSubstitutable H
      (UntypedStartLanguage
        (LinearConstructedTerminalRule
          (G.linearPreparedGrammar hlinear))
        (LinearConstructedBinaryRule
          (G.linearPreparedGrammar hlinear))
        (linearConstructedStartRule
          (G.linearPreparedGrammar hlinear) S)
        (G.linearKeepEmpty hlinear S)) := by
  rw [indexedLinear_normalization_language_eq
    G hlinear S]
  exact hsub

/--
Source-only polynomial envelope for arbitrary linear targets.

The inner cubic is the explicit preprocessing-size envelope; the outer
characteristic envelope is the verified short-witness bound.
-/
def indexedLinearCharacteristicEnvelope
    (m sourceScale : Nat) : Nat :=
  linearSourceCharacteristicEnvelope
    m (linearPreparedEncodingEnvelope sourceScale)

/--
Characteristic-data theorem for an arbitrary finite indexed linear CFG.

For fixed H, the right-hand side is a polynomial in the original source
encoding scale.
-/
set_option maxHeartbeats 1000000 in
theorem indexedLinear_characteristic_package
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N)
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules S)) :
    BatchLanguage H
        (indexedLinearCanonicalSample
          H G hlinear S)
      =
    LeastClosedLanguage G.toMixedRules S
    ∧
    (∑ word ∈
      indexedLinearCanonicalSample
        H G hlinear S,
      (word.length + 1))
      ≤
    indexedLinearCharacteristicEnvelope
      (Fintype.card M)
      G.linearNormalizationSourceScale := by
  let Gp := G.linearPreparedGrammar hlinear
  have hshape :
      UntypedLinearSpineShape
        (LinearConstructedTerminalRule Gp)
        (LinearConstructedBinaryRule Gp)
        (LinearConstructedWrapper Gp) := by
    exact
      linearConstructed_untypedLinearSpineShape Gp
  have hsubNorm :
      FixedHSubstitutable H
        (UntypedStartLanguage
          (LinearConstructedTerminalRule Gp)
          (LinearConstructedBinaryRule Gp)
          (linearConstructedStartRule Gp S)
          (G.linearKeepEmpty hlinear S)) := by
    simpa [Gp] using
      indexedLinear_fixedHSubstitutable_normalized
        H G hlinear S hsub
  have hpack :=
    concreteLinear_characteristic_package_of_untyped_shape
      H
      (LinearConstructedTerminalRule Gp)
      (LinearConstructedBinaryRule Gp)
      (linearConstructedStartRule Gp S)
      (G.linearKeepEmpty hlinear S)
      (LinearConstructedWrapper Gp)
      hshape hsubNorm
  constructor
  · calc
      BatchLanguage H
          (indexedLinearCanonicalSample
            H G hlinear S)
        =
      UntypedStartLanguage
          (LinearConstructedTerminalRule Gp)
          (LinearConstructedBinaryRule Gp)
          (linearConstructedStartRule Gp S)
          (G.linearKeepEmpty hlinear S) := by
            simpa [indexedLinearCanonicalSample, Gp]
              using hpack.1
      _ =
      LeastClosedLanguage G.toMixedRules S := by
        simpa [Gp] using
          indexedLinear_normalization_language_eq
            G hlinear S
  · have hsample :
        (∑ word ∈
          indexedLinearCanonicalSample
            H G hlinear S,
          (word.length + 1))
          ≤
        linearCharacteristicEnvelope
          (Fintype.card M)
          (Fintype.card (LinearConstructedState Gp))
          (@Fintype.card
            (UntypedTerminalRuleIndex
              (LinearConstructedTerminalRule Gp))
            (Fintype.ofFinite _))
          (@Fintype.card
            (UntypedBinaryRuleIndex
              (LinearConstructedBinaryRule Gp))
            (Fintype.ofFinite _)) := by
      simpa [indexedLinearCanonicalSample, Gp]
        using hpack.2
    have hpreparedEnvelope :
        linearCharacteristicEnvelope
          (Fintype.card M)
          (Fintype.card (LinearConstructedState Gp))
          (@Fintype.card
            (UntypedTerminalRuleIndex
              (LinearConstructedTerminalRule Gp))
            (Fintype.ofFinite _))
          (@Fintype.card
            (UntypedBinaryRuleIndex
              (LinearConstructedBinaryRule Gp))
            (Fintype.ofFinite _))
          ≤
        linearSourceCharacteristicEnvelope
          (Fintype.card M) Gp.encodingScale := by
      exact
        preparedLinear_characteristicEnvelope_le_sourceScale
          (M := M) Gp
    have hscale :
        Gp.encodingScale ≤
          linearPreparedEncodingEnvelope
            G.linearNormalizationSourceScale := by
      exact
        indexedLinear_preparedEncodingScale_le
          G hlinear
    have hmono :
        linearSourceCharacteristicEnvelope
            (Fintype.card M) Gp.encodingScale
          ≤
        linearSourceCharacteristicEnvelope
            (Fintype.card M)
            (linearPreparedEncodingEnvelope
              G.linearNormalizationSourceScale) :=
      linearSourceCharacteristicEnvelope_mono hscale
    exact
      le_trans hsample
        (le_trans hpreparedEnvelope
          (by
            simpa [indexedLinearCharacteristicEnvelope]
              using hmono))

/-- Exact-reconstruction projection of the arbitrary linear characteristic theorem. -/
theorem indexedLinear_characteristic_language_eq
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N)
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules S)) :
    BatchLanguage H
        (indexedLinearCanonicalSample
          H G hlinear S)
      =
    LeastClosedLanguage G.toMixedRules S :=
  (indexedLinear_characteristic_package
    H G hlinear S hsub).1

/-- Source-polynomial sample-size projection. -/
theorem indexedLinear_characteristic_sample_size_le
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N)
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules S)) :
    (∑ word ∈
      indexedLinearCanonicalSample
        H G hlinear S,
      (word.length + 1))
      ≤
    indexedLinearCharacteristicEnvelope
      (Fintype.card M)
      G.linearNormalizationSourceScale :=
  (indexedLinear_characteristic_package
    H G hlinear S hsub).2

/--
Concrete conservative Gold identification for an arbitrary finite indexed
linear target.
-/
theorem indexedLinear_conservativeGold_identification
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N)
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules S))
    (datum : Nat → Word α)
    (hpositive :
      ∀ n,
        datum n ∈ LeastClosedLanguage G.toMixedRules S)
    (hcoverage :
      ∀ word,
        word ∈ LeastClosedLanguage G.toMixedRules S →
        ∃ n,
          word ∈ concreteAccumulatedSample datum n) :
    ∃ n₀,
      (BatchLanguage H
          (concreteConservativeHypothesis H datum n₀)
          =
        LeastClosedLanguage G.toMixedRules S
        ∧
        ∀ j,
          concreteConservativeHypothesis H datum (n₀ + j) =
            concreteConservativeHypothesis H datum n₀)
      ∨
      (∃ n,
        n₀ ≤ n ∧
        concreteConservativeHypothesis H datum (n + 1) ≠
          concreteConservativeHypothesis H datum n ∧
        BatchLanguage H
          (concreteConservativeHypothesis H datum (n + 1))
          =
        LeastClosedLanguage G.toMixedRules S
        ∧
        ∀ j,
          concreteConservativeHypothesis H datum ((n + 1) + j) =
            concreteConservativeHypothesis H datum (n + 1)) := by
  have hchar :=
    (indexedLinear_characteristic_package
      H G hlinear S hsub).1
  exact
    concreteConservative_gold_identification_explicit
      H
      (LeastClosedLanguage G.toMixedRules S)
      (indexedLinearCanonicalSample
        H G hlinear S)
      hchar hsub
      datum hpositive hcoverage

end IndexedLinearCharacteristicData

end TCS1
end LeanCfgProject
