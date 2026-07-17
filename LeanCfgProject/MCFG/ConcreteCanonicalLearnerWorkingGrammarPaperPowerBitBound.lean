/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarPaperBitEnvelope

/-!
# ConcreteCanonicalLearnerWorkingGrammarPaperPowerBitBound.lean

The preceding file compresses the complete checked logarithmic description size
into the paper-facing quadratic envelope

```lean
correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope sampleLength f.
```

This file absorbs that remaining polynomial envelope into one larger power of
the already established paper base.

Write

```text
B(s,f) = correctedLearnerPaperBase s f,
Q(s,f) = correctedLearnerPaperExponent s f,
R(s,f) = B(s,f) ^ Q(s,f).
```

The existing corrected-learner rule-count estimate is exactly `R(s,f)`.

The proof proceeds through the following deliberately coarse hierarchy.

```text
paper body bound       ≤ B^2 ≤ R,
presentation bound     ≤ R^3,
description scale D    ≤ 3 * R^3,
natural-field envelope ≤ 31 * R^6,
checked bit envelope   ≤ 3072 * R^12 ≤ R^13.
```

The last absorption uses the very large verified lower bound

```text
3072 ≤ R(s,f),
```

which follows already from `4^6 ≤ B^Q`.

Therefore the complete checked logarithmic bit serialization is bounded by

```text
R(s,f)^13
  =
B(s,f) ^ (Q(s,f) * 13).
```

We define

```lean
correctedConcreteCompiledGrammarPaperPowerExponent
correctedConcreteCompiledGrammarPaperPowerBitBound
```

and prove the final canonical endpoint

```lean
correctedConcreteFiniteHypothesis_logarithmicBitCount_le_paperPower.
```

Expanded, the right-hand side is

```text
(4 * (sampleLengthBudget K + f + 1)) ^
  ((64 *
      (sampleLengthBudget K + f + 1) *
      (sampleLengthBudget K + f + 1)) * 13).
```

Thus the actual complete, checked, prefix-free logarithmic serialization has a
single-power description-size estimate using the same linear base and the same
quadratic exponent scale as the learner's rule-count theorem.

No target grammar is supplied to the learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v

section ElementaryBinaryLengthBound

/-- Every natural number is strictly below two raised to one more than itself. -/
theorem nat_lt_two_pow_self_add_one :
    ∀ n : Nat,
      n < 2 ^ (n + 1)

  | 0 => by
      norm_num

  | n + 1 => by
      have ih :
          n < 2 ^ (n + 1) :=
        nat_lt_two_pow_self_add_one n

      have hle :
          n + 1 <= 2 ^ (n + 1) :=
        Nat.succ_le_of_lt ih

      have hpositive :
          0 < 2 ^ (n + 1) := by
        positivity

      calc
        n + 1 <=
            2 ^ (n + 1) :=
          hle
        _ <
            2 ^ (n + 1) +
              2 ^ (n + 1) := by
          omega
        _ =
            2 ^ ((n + 1) + 1) := by
          simp [
            pow_succ,
            Nat.mul_two
          ]

/-- A natural number's standard binary payload length is at most one more than
the number itself. -/
theorem binaryNatCodeLength_le_self_add_one
    (n : Nat) :
    binaryNatCodeLength n <= n + 1 := by

  exact
    binaryNatCodeLength_le_of_pos_of_lt_two_pow
      (by omega)
      (nat_lt_two_pow_self_add_one n)

end ElementaryBinaryLengthBound


section PaperPowerBasicBounds

/-- The paper scale is always positive. -/
theorem correctedLearnerPaperScale_pos
    (sampleLength f : Nat) :
    1 <= correctedLearnerPaperScale
      sampleLength f := by

  unfold correctedLearnerPaperScale

  omega

/-- The paper base is at least four. -/
theorem four_le_correctedLearnerPaperBase
    (sampleLength f : Nat) :
    4 <= correctedLearnerPaperBase
      sampleLength f := by

  unfold
    correctedLearnerPaperBase

  have hscale :
      1 <= correctedLearnerPaperScale
        sampleLength f :=
    correctedLearnerPaperScale_pos
      sampleLength f

  omega

/-- The quadratic paper exponent is already at least sixty-four. -/
theorem sixtyFour_le_correctedLearnerPaperExponent
    (sampleLength f : Nat) :
    64 <= correctedLearnerPaperExponent
      sampleLength f := by

  have hscale :
      1 <= correctedLearnerPaperScale
        sampleLength f :=
    correctedLearnerPaperScale_pos
      sampleLength f

  have hsquare :
      1 <=
        correctedLearnerPaperScale sampleLength f *
          correctedLearnerPaperScale sampleLength f :=
    Nat.mul_le_mul hscale hscale

  unfold correctedLearnerPaperExponent

  have hmul :=
    Nat.mul_le_mul_left
      64
      hsquare

  simpa [Nat.mul_assoc] using hmul

/-- Any fixed power whose exponent is below the paper exponent is below the
paper rule-count power. -/
theorem correctedLearnerPaperBase_pow_le_ruleCountBound
    (sampleLength f k : Nat)
    (hk :
      k <= correctedLearnerPaperExponent
        sampleLength f) :
    correctedLearnerPaperBase sampleLength f ^ k <=
      correctedLearnerPaperRuleCountBound
        sampleLength f := by

  unfold
    correctedLearnerPaperRuleCountBound

  exact
    Nat.pow_le_pow_of_le
      (correctedLearnerPaperBase_gt_one
        sampleLength f)
      hk

/-- The paper base itself is below the rule-count power. -/
theorem correctedLearnerPaperBase_le_ruleCountBound
    (sampleLength f : Nat) :
    correctedLearnerPaperBase sampleLength f <=
      correctedLearnerPaperRuleCountBound
        sampleLength f := by

  have hexponent :
      1 <=
        correctedLearnerPaperExponent
          sampleLength f := by

    have h64 :=
      sixtyFour_le_correctedLearnerPaperExponent
        sampleLength f

    omega

  simpa using
    correctedLearnerPaperBase_pow_le_ruleCountBound
      sampleLength f 1 hexponent

/-- The square of the paper base is below the rule-count power. -/
theorem correctedLearnerPaperBase_sq_le_ruleCountBound
    (sampleLength f : Nat) :
    correctedLearnerPaperBase sampleLength f ^ 2 <=
      correctedLearnerPaperRuleCountBound
        sampleLength f := by

  apply
    correctedLearnerPaperBase_pow_le_ruleCountBound

  have h64 :=
    sixtyFour_le_correctedLearnerPaperExponent
      sampleLength f

  omega

/-- The sixth power of the paper base is below the rule-count power. -/
theorem correctedLearnerPaperBase_pow_six_le_ruleCountBound
    (sampleLength f : Nat) :
    correctedLearnerPaperBase sampleLength f ^ 6 <=
      correctedLearnerPaperRuleCountBound
        sampleLength f := by

  apply
    correctedLearnerPaperBase_pow_le_ruleCountBound

  have h64 :=
    sixtyFour_le_correctedLearnerPaperExponent
      sampleLength f

  omega

/-- The paper rule-count power is already at least `3072`. -/
theorem threeThousandSeventyTwo_le_correctedLearnerPaperRuleCountBound
    (sampleLength f : Nat) :
    3072 <=
      correctedLearnerPaperRuleCountBound
        sampleLength f := by

  have hbase :
      4 <=
        correctedLearnerPaperBase
          sampleLength f :=
    four_le_correctedLearnerPaperBase
      sampleLength f

  have hfourPow :
      4 ^ 6 <=
        correctedLearnerPaperBase sampleLength f ^ 6 :=
    Nat.pow_le_pow_left
      hbase
      6

  have htoRule :
      correctedLearnerPaperBase sampleLength f ^ 6 <=
        correctedLearnerPaperRuleCountBound
          sampleLength f :=
    correctedLearnerPaperBase_pow_six_le_ruleCountBound
      sampleLength f

  have hconstant :
      3072 <= 4 ^ 6 := by
    norm_num

  exact
    hconstant.trans
      (hfourPow.trans htoRule)

/-- The paper rule-count power is greater than one. -/
theorem correctedLearnerPaperRuleCountBound_gt_one
    (sampleLength f : Nat) :
    1 <
      correctedLearnerPaperRuleCountBound
        sampleLength f := by

  have hlarge :=
    threeThousandSeventyTwo_le_correctedLearnerPaperRuleCountBound
      sampleLength f

  omega

end PaperPowerBasicBounds


section PaperBodyAndPresentationPowerBounds

/-- The paper body-token expression is below the square of the paper base. -/
theorem correctedConcreteCompiledGrammarPaperBodyBound_le_base_sq
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarPaperBodyBound
        sampleLength f <=
      correctedLearnerPaperBase sampleLength f ^ 2 := by

  let scale :=
    correctedLearnerPaperScale
      sampleLength f

  let fanout :=
    max 1 f

  have hscale :
      1 <= scale := by
    simpa [scale] using
      correctedLearnerPaperScale_pos
        sampleLength f

  have hsample :
      sampleLength <= scale := by
    dsimp [
      scale,
      correctedLearnerPaperScale
    ]

    omega

  have hfanout :
      fanout <= scale := by
    dsimp [
      fanout,
      scale,
      correctedLearnerPaperScale
    ]

    apply max_le
    · omega
    · omega

  have hinner :
      sampleLength + 2 * fanout <=
        3 * scale := by
    omega

  have hfirst :
      2 * fanout <= 2 * scale :=
    Nat.mul_le_mul_left
      2
      hfanout

  have hproduct :
      fanout *
          (sampleLength + 2 * fanout) <=
        scale * (3 * scale) :=
    Nat.mul_le_mul
      hfanout
      hinner

  have hscaleSelf :
      scale <= scale * scale := by

    calc
      scale =
          scale * 1 := by
        simp
      _ <=
          scale * scale :=
        Nat.mul_le_mul_left
          scale
          hscale

  have htwoScale :
      2 * scale <=
        2 * (scale * scale) :=
    Nat.mul_le_mul_left
      2
      hscaleSelf

  have hcoarse :
      2 * scale +
          scale * (3 * scale) <=
        16 * (scale * scale) := by

    have hrewrite :
        scale * (3 * scale) =
          3 * (scale * scale) := by
      ring

    rw [hrewrite]

    omega

  calc
    correctedConcreteCompiledGrammarPaperBodyBound
          sampleLength f =
        2 * fanout +
          fanout *
            (sampleLength + 2 * fanout) := by
      rfl
    _ <=
        2 * scale +
          scale * (3 * scale) :=
      Nat.add_le_add
        hfirst
        hproduct
    _ <=
        16 * (scale * scale) :=
      hcoarse
    _ =
        correctedLearnerPaperBase
            sampleLength f ^ 2 := by
      unfold
        correctedLearnerPaperBase

      dsimp [scale]

      ring

/-- The paper body-token expression is below the paper rule-count power. -/
theorem correctedConcreteCompiledGrammarPaperBodyBound_le_ruleCountBound
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarPaperBodyBound
        sampleLength f <=
      correctedLearnerPaperRuleCountBound
        sampleLength f := by

  exact
    (correctedConcreteCompiledGrammarPaperBodyBound_le_base_sq
        sampleLength f).trans
      (correctedLearnerPaperBase_sq_le_ruleCountBound
        sampleLength f)

/-- The additive non-presentation part of the paper description scale is below
the square of the paper base. -/
theorem
    correctedConcreteCompiledGrammarPaperSmallTerms_le_base_sq
    (sampleLength f : Nat) :
    sampleLength + f + 10 <=
      correctedLearnerPaperBase sampleLength f ^ 2 := by

  let scale :=
    correctedLearnerPaperScale
      sampleLength f

  have hscale :
      1 <= scale := by
    simpa [scale] using
      correctedLearnerPaperScale_pos
        sampleLength f

  have hscaleSelf :
      scale <= scale * scale := by

    calc
      scale =
          scale * 1 := by
        simp
      _ <=
          scale * scale :=
        Nat.mul_le_mul_left
          scale
          hscale

  have honeSquare :
      1 <= scale * scale :=
    hscale.trans hscaleSelf

  have hnine :
      9 <= 9 * (scale * scale) := by

    have h :=
      Nat.mul_le_mul_left
        9
        honeSquare

    simpa using h

  have hcoarse :
      scale + 9 <=
        16 * (scale * scale) := by
    omega

  calc
    sampleLength + f + 10 =
        scale + 9 := by
      dsimp [
        scale,
        correctedLearnerPaperScale
      ]

      omega
    _ <=
        16 * (scale * scale) :=
      hcoarse
    _ =
        correctedLearnerPaperBase
            sampleLength f ^ 2 := by
      unfold
        correctedLearnerPaperBase

      dsimp [scale]

      ring

/-- The additive non-presentation part of the paper description scale is below
the paper rule-count power. -/
theorem
    correctedConcreteCompiledGrammarPaperSmallTerms_le_ruleCountBound
    (sampleLength f : Nat) :
    sampleLength + f + 10 <=
      correctedLearnerPaperRuleCountBound
        sampleLength f := by

  exact
    (correctedConcreteCompiledGrammarPaperSmallTerms_le_base_sq
        sampleLength f).trans
      (correctedLearnerPaperBase_sq_le_ruleCountBound
        sampleLength f)

/-- The paper-facing complete presentation-item bound is below the cube of the
paper rule-count power. -/
theorem
    correctedConcreteCompiledGrammarPresentationItemBound_le_ruleCountCube
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarPresentationItemBound
        sampleLength f <=
      correctedLearnerPaperRuleCountBound
          sampleLength f ^ 3 := by

  let ruleBound :=
    correctedLearnerPaperRuleCountBound
      sampleLength f

  have hsampleBase :
      sampleLength + 4 <=
        correctedLearnerPaperBase
          sampleLength f := by

    unfold
      correctedLearnerPaperBase
      correctedLearnerPaperScale

    omega

  have hsampleRule :
      sampleLength + 4 <=
        ruleBound :=
    hsampleBase.trans
      (by
        simpa [ruleBound] using
          correctedLearnerPaperBase_le_ruleCountBound
            sampleLength f)

  have hinside :
      sampleLength +
          3 * ruleBound +
          4 <=
        4 * ruleBound := by
    omega

  have hsquare :
      (sampleLength +
          3 * ruleBound +
          4) ^ 2 <=
        (4 * ruleBound) ^ 2 :=
    Nat.pow_le_pow_left
      hinside
      2

  have hsixteen :
      16 <= ruleBound := by

    have hlarge :
        3072 <= ruleBound := by
      simpa [ruleBound] using
        threeThousandSeventyTwo_le_correctedLearnerPaperRuleCountBound
          sampleLength f

    omega

  have habsorb :
      16 * ruleBound ^ 2 <=
        ruleBound * ruleBound ^ 2 :=
    Nat.mul_le_mul_right
      (ruleBound ^ 2)
      hsixteen

  calc
    correctedConcreteCompiledGrammarPresentationItemBound
          sampleLength f =
        (sampleLength +
            3 * ruleBound +
            4) ^ 2 := by
      rfl
    _ <=
        (4 * ruleBound) ^ 2 :=
      hsquare
    _ =
        16 * ruleBound ^ 2 := by
      ring
    _ <=
        ruleBound * ruleBound ^ 2 :=
      habsorb
    _ =
        ruleBound ^ 3 := by
      ring

end PaperBodyAndPresentationPowerBounds


section DescriptionAndNaturalFieldPowerBounds

/-- The complete paper description scale is below three cubes of the paper
rule-count power. -/
theorem
    correctedConcreteCompiledGrammarPaperDescriptionScale_le_three_ruleCubes
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarPaperDescriptionScale
        sampleLength f <=
      3 *
        (correctedLearnerPaperRuleCountBound
          sampleLength f ^ 3) := by

  let ruleBound :=
    correctedLearnerPaperRuleCountBound
      sampleLength f

  have hpresentation :
      correctedConcreteCompiledGrammarPresentationItemBound
          sampleLength f <=
        ruleBound ^ 3 := by

    simpa [ruleBound] using
      correctedConcreteCompiledGrammarPresentationItemBound_le_ruleCountCube
        sampleLength f

  have hbody :
      correctedConcreteCompiledGrammarPaperBodyBound
          sampleLength f <=
        ruleBound := by

    simpa [ruleBound] using
      correctedConcreteCompiledGrammarPaperBodyBound_le_ruleCountBound
        sampleLength f

  have hsmall :
      sampleLength + f + 10 <=
        ruleBound := by

    simpa [ruleBound] using
      correctedConcreteCompiledGrammarPaperSmallTerms_le_ruleCountBound
        sampleLength f

  have hruleCube :
      ruleBound <= ruleBound ^ 3 := by

    have hrule :
        1 < ruleBound := by
      simpa [ruleBound] using
        correctedLearnerPaperRuleCountBound_gt_one
          sampleLength f

    have hpow :=
      Nat.pow_le_pow_of_le
        hrule
        (show 1 <= 3 by omega)

    simpa using hpow

  unfold
    correctedConcreteCompiledGrammarPaperDescriptionScale

  omega

/-- The paper natural-field envelope is below `31 * R^6`. -/
theorem
    correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope_le_thirtyOne_rulePowSix
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
        sampleLength f <=
      31 *
        (correctedLearnerPaperRuleCountBound
          sampleLength f ^ 6) := by

  let ruleBound :=
    correctedLearnerPaperRuleCountBound
      sampleLength f

  let ruleCube :=
    ruleBound ^ 3

  let descriptionScale :=
    correctedConcreteCompiledGrammarPaperDescriptionScale
      sampleLength f

  have hdescription :
      descriptionScale <=
        3 * ruleCube := by

    simpa [
      descriptionScale,
      ruleCube,
      ruleBound
    ] using
      correctedConcreteCompiledGrammarPaperDescriptionScale_le_three_ruleCubes
        sampleLength f

  have hfactor :
      1 + 3 * descriptionScale <=
        1 + 9 * ruleCube := by
    omega

  have hproduct :
      descriptionScale *
          (1 + 3 * descriptionScale) <=
        (3 * ruleCube) *
          (1 + 9 * ruleCube) :=
    Nat.mul_le_mul
      hdescription
      hfactor

  have hruleOne :
      1 <= ruleBound := by

    have hlarge :
        3072 <= ruleBound := by
      simpa [ruleBound] using
        threeThousandSeventyTwo_le_correctedLearnerPaperRuleCountBound
          sampleLength f

    omega

  have hcubeOne :
      1 <= ruleCube := by

    dsimp [ruleCube]

    simpa using
      Nat.pow_le_pow_left
        hruleOne
        3

  have hcubeSelf :
      ruleCube <=
        ruleCube * ruleCube := by

    calc
      ruleCube =
          ruleCube * 1 := by
        simp
      _ <=
          ruleCube * ruleCube :=
        Nat.mul_le_mul_left
          ruleCube
          hcubeOne

  have hcubeSquareOne :
      1 <= ruleCube * ruleCube :=
    hcubeOne.trans hcubeSelf

  have hcoarse :
      1 +
          (3 * ruleCube) *
            (1 + 9 * ruleCube) <=
        31 * (ruleCube * ruleCube) := by

    have hrewrite :
        (3 * ruleCube) *
            (1 + 9 * ruleCube) =
          3 * ruleCube +
            27 * (ruleCube * ruleCube) := by
      ring

    rw [hrewrite]

    have hthree :
        3 * ruleCube <=
          3 * (ruleCube * ruleCube) :=
      Nat.mul_le_mul_left
        3
        hcubeSelf

    omega

  calc
    correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
          sampleLength f =
        1 +
          descriptionScale *
            (1 + 3 * descriptionScale) := by
      rfl
    _ <=
        1 +
          (3 * ruleCube) *
            (1 + 9 * ruleCube) :=
      Nat.add_le_add_left
        hproduct
        1
    _ <=
        31 * (ruleCube * ruleCube) :=
      hcoarse
    _ =
        31 * ruleBound ^ 6 := by
      dsimp [
        ruleCube
      ]

      ring

end DescriptionAndNaturalFieldPowerBounds


section FinalPaperPowerBitBound

/-- Exponent of the final single-power checked bit bound. -/
def correctedConcreteCompiledGrammarPaperPowerExponent
    (sampleLength f : Nat) :
    Nat :=
  correctedLearnerPaperExponent
      sampleLength f *
    13

/-- Final single-power checked logarithmic description-size bound. -/
def correctedConcreteCompiledGrammarPaperPowerBitBound
    (sampleLength f : Nat) :
    Nat :=
  correctedLearnerPaperBase
      sampleLength f ^
    correctedConcreteCompiledGrammarPaperPowerExponent
      sampleLength f

/-- The paper logarithmic bit envelope is below `3072 * R^12`. -/
theorem
    correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope_le_threeThousandSeventyTwo_rulePowTwelve
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope
        sampleLength f <=
      3072 *
        (correctedLearnerPaperRuleCountBound
          sampleLength f ^ 12) := by

  let ruleBound :=
    correctedLearnerPaperRuleCountBound
      sampleLength f

  let envelope :=
    correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope
      sampleLength f

  have henvelope :
      envelope <=
        31 * ruleBound ^ 6 := by

    simpa [
      envelope,
      ruleBound
    ] using
      correctedConcreteCompiledGrammarPaperNaturalFieldEnvelope_le_thirtyOne_rulePowSix
        sampleLength f

  have hruleOne :
      1 <= ruleBound := by

    have hlarge :
        3072 <= ruleBound := by
      simpa [ruleBound] using
        threeThousandSeventyTwo_le_correctedLearnerPaperRuleCountBound
          sampleLength f

    omega

  have hrulePowSixOne :
      1 <= ruleBound ^ 6 := by

    simpa using
      Nat.pow_le_pow_left
        hruleOne
        6

  have henvelopeAdd :
      envelope + 1 <=
        32 * ruleBound ^ 6 := by
    omega

  have hcode :
      binaryNatCodeLength envelope <=
        envelope + 1 :=
    binaryNatCodeLength_le_self_add_one
      envelope

  have hcodeFactor :
      2 * binaryNatCodeLength envelope + 1 <=
        3 * (envelope + 1) := by
    omega

  have hfirstProduct :
      (envelope + 1) *
          (2 * binaryNatCodeLength envelope + 1) <=
        (envelope + 1) *
          (3 * (envelope + 1)) :=
    Nat.mul_le_mul_left
      (envelope + 1)
      hcodeFactor

  have hsquare :
      (envelope + 1) ^ 2 <=
        (32 * ruleBound ^ 6) ^ 2 :=
    Nat.pow_le_pow_left
      henvelopeAdd
      2

  have hthreeSquare :
      3 * (envelope + 1) ^ 2 <=
        3 * (32 * ruleBound ^ 6) ^ 2 :=
    Nat.mul_le_mul_left
      3
      hsquare

  calc
    correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope
          sampleLength f =
        (envelope + 1) *
          (2 *
              binaryNatCodeLength envelope +
            1) := by
      rfl
    _ <=
        (envelope + 1) *
          (3 * (envelope + 1)) :=
      hfirstProduct
    _ =
        3 * (envelope + 1) ^ 2 := by
      ring
    _ <=
        3 * (32 * ruleBound ^ 6) ^ 2 :=
      hthreeSquare
    _ =
        3072 * ruleBound ^ 12 := by
      ring

/-- The polynomial paper bit envelope is below the thirteenth power of the
paper rule-count power. -/
theorem
    correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope_le_rulePowThirteen
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope
        sampleLength f <=
      correctedLearnerPaperRuleCountBound
          sampleLength f ^ 13 := by

  let ruleBound :=
    correctedLearnerPaperRuleCountBound
      sampleLength f

  have hbit :
      correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope
          sampleLength f <=
        3072 * ruleBound ^ 12 := by

    simpa [ruleBound] using
      correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope_le_threeThousandSeventyTwo_rulePowTwelve
        sampleLength f

  have hconstant :
      3072 <= ruleBound := by

    simpa [ruleBound] using
      threeThousandSeventyTwo_le_correctedLearnerPaperRuleCountBound
        sampleLength f

  have habsorb :
      3072 * ruleBound ^ 12 <=
        ruleBound * ruleBound ^ 12 :=
    Nat.mul_le_mul_right
      (ruleBound ^ 12)
      hconstant

  exact
    hbit.trans
      (habsorb.trans
        (by
          ring))

/-- The thirteenth rule-count power is exactly the final paper-base power with
exponent multiplied by thirteen. -/
theorem
    correctedLearnerPaperRuleCountBound_pow_thirteen_eq_powerBitBound
    (sampleLength f : Nat) :
    correctedLearnerPaperRuleCountBound
        sampleLength f ^ 13 =
      correctedConcreteCompiledGrammarPaperPowerBitBound
        sampleLength f := by

  unfold
    correctedLearnerPaperRuleCountBound
    correctedConcreteCompiledGrammarPaperPowerBitBound
    correctedConcreteCompiledGrammarPaperPowerExponent

  symm

  exact
    Nat.pow_mul
      (correctedLearnerPaperBase sampleLength f)
      (correctedLearnerPaperExponent sampleLength f)
      13

/-- The paper logarithmic bit envelope is below one larger power of the same
paper base. -/
theorem
    correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope_le_powerBitBound
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope
        sampleLength f <=
      correctedConcreteCompiledGrammarPaperPowerBitBound
        sampleLength f := by

  exact
    (correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope_le_rulePowThirteen
        sampleLength f).trans_eq
      (correctedLearnerPaperRuleCountBound_pow_thirteen_eq_powerBitBound
        sampleLength f)

/-- Expanded form of the final single-power checked bit bound. -/
theorem correctedConcreteCompiledGrammarPaperPowerBitBound_eq_expanded
    (sampleLength f : Nat) :
    correctedConcreteCompiledGrammarPaperPowerBitBound
        sampleLength f =
      (4 * (sampleLength + f + 1)) ^
        ((64 *
            (sampleLength + f + 1) *
            (sampleLength + f + 1)) *
          13) := by

  rfl

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Final single-power checked logarithmic description-size theorem for the
actual canonical cut-compiled grammar. -/
theorem
    correctedConcreteFiniteHypothesis_logarithmicBitCount_le_paperPower
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    (correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarLogarithmicBitCount dummy <=
      correctedConcreteCompiledGrammarPaperPowerBitBound
        (sampleLengthBudget K) f := by

  exact
    (correctedConcreteFiniteHypothesis_logarithmicBitCount_le_paperEnvelope
        K obs f dummy).trans
      (correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope_le_powerBitBound
        (sampleLengthBudget K) f)

/-- Fully expanded final checked logarithmic description-size theorem. -/
theorem
    correctedConcreteFiniteHypothesis_logarithmicBitCount_le_explicit_paperPower
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    (correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarLogarithmicBitCount dummy <=
      (4 * (sampleLengthBudget K + f + 1)) ^
        ((64 *
            (sampleLengthBudget K + f + 1) *
            (sampleLengthBudget K + f + 1)) *
          13) := by

  exact
    correctedConcreteFiniteHypothesis_logarithmicBitCount_le_paperPower
      K obs f dummy

/-- Compact final single-power description-size package. -/
theorem
    correctedConcreteFiniteHypothesis_paperPowerBitBound_package
    (K : Finset (Word α))
    (obs : α → M)
    (f : Nat)
    (dummy : α) :
    ((correctedConcreteFiniteHypothesis K obs f).
        compiledWorkingGrammarLogarithmicBitCount dummy <=
      correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope
        (sampleLengthBudget K) f) ∧
      (correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope
          (sampleLengthBudget K) f <=
        correctedLearnerPaperRuleCountBound
            (sampleLengthBudget K) f ^ 13) ∧
      (correctedLearnerPaperRuleCountBound
          (sampleLengthBudget K) f ^ 13 =
        correctedConcreteCompiledGrammarPaperPowerBitBound
          (sampleLengthBudget K) f) ∧
      ((correctedConcreteFiniteHypothesis K obs f).
          compiledWorkingGrammarLogarithmicBitCount dummy <=
        correctedConcreteCompiledGrammarPaperPowerBitBound
          (sampleLengthBudget K) f) := by

  exact
    ⟨correctedConcreteFiniteHypothesis_logarithmicBitCount_le_paperEnvelope
        K obs f dummy,
      correctedConcreteCompiledGrammarPaperLogarithmicBitEnvelope_le_rulePowThirteen
        (sampleLengthBudget K) f,
      correctedLearnerPaperRuleCountBound_pow_thirteen_eq_powerBitBound
        (sampleLengthBudget K) f,
      correctedConcreteFiniteHypothesis_logarithmicBitCount_le_paperPower
        K obs f dummy⟩

end FinalPaperPowerBitBound

end MCFG
