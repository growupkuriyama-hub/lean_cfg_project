import LeanCfgProject.TCS1.UntypedUsefulTrim
import LeanCfgProject.TCS1.CanonicalWitnessCounting
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# TCS #1: size of the final untyped useful-state trim

The productive/reachable trim is represented by a subtype of the incoming
non-start state space.  Its actual terminal and binary rule relations are
therefore bounded by the ambient finite spaces X x Sigma and X x X x X.

This coarse bound is intentionally representation-independent.  If both the
incoming non-start state count and alphabet size are bounded by g, then the
entire reduced terminal/binary presentation has size at most

  g + g^2 + g^3.

That is sufficient to transport the already verified polynomial bound for the
specialized linear normalization through the manuscript's final trimming
step.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section UntypedUsefulTrimSize

variable {N : Type u}
variable {α : Type v}

/-- Encoded-size proxy for the useful-state terminal/binary presentation. -/
def untypedUsefulGrammarSize
    [Fintype N] [Fintype α]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) : Nat :=
  Fintype.card
      (UntypedUsefulState
        terminalRule binaryRule startRule)
    +
  @Fintype.card
      (UntypedTerminalRuleIndex
        (untypedUsefulTerminalRule
          terminalRule binaryRule startRule))
      (Fintype.ofFinite _)
    +
  @Fintype.card
      (UntypedBinaryRuleIndex
        (untypedUsefulBinaryRule
          terminalRule binaryRule startRule))
      (Fintype.ofFinite _)

/-- Useful terminal rules are bounded by useful states times alphabet size. -/
theorem untypedUsefulTerminalRuleIndex_card_le_ambient
    [Fintype N] [Fintype α]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :
    @Fintype.card
        (UntypedTerminalRuleIndex
          (untypedUsefulTerminalRule
            terminalRule binaryRule startRule))
        (Fintype.ofFinite _)
      ≤
    Fintype.card
        (UntypedUsefulState
          terminalRule binaryRule startRule)
      *
    Fintype.card α := by
  letI :
      Fintype
        (UntypedTerminalRuleIndex
          (untypedUsefulTerminalRule
            terminalRule binaryRule startRule)) :=
    Fintype.ofFinite _
  calc
    Fintype.card
        (UntypedTerminalRuleIndex
          (untypedUsefulTerminalRule
            terminalRule binaryRule startRule))
        ≤
      Fintype.card
        (UntypedUsefulState
            terminalRule binaryRule startRule
          × α) :=
      Fintype.card_subtype_le _
    _ =
      Fintype.card
          (UntypedUsefulState
            terminalRule binaryRule startRule)
        * Fintype.card α := by
      simp

/-- Useful binary rules are bounded by the cube of useful-state count. -/
theorem untypedUsefulBinaryRuleIndex_card_le_ambient
    [Fintype N] [Fintype α]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :
    @Fintype.card
        (UntypedBinaryRuleIndex
          (untypedUsefulBinaryRule
            terminalRule binaryRule startRule))
        (Fintype.ofFinite _)
      ≤
    Fintype.card
        (UntypedUsefulState
          terminalRule binaryRule startRule)
      *
      (Fintype.card
          (UntypedUsefulState
            terminalRule binaryRule startRule)
        *
       Fintype.card
          (UntypedUsefulState
            terminalRule binaryRule startRule)) := by
  letI :
      Fintype
        (UntypedBinaryRuleIndex
          (untypedUsefulBinaryRule
            terminalRule binaryRule startRule)) :=
    Fintype.ofFinite _
  calc
    Fintype.card
        (UntypedBinaryRuleIndex
          (untypedUsefulBinaryRule
            terminalRule binaryRule startRule))
        ≤
      Fintype.card
        (UntypedUsefulState
            terminalRule binaryRule startRule
          ×
         (UntypedUsefulState
            terminalRule binaryRule startRule
          ×
          UntypedUsefulState
            terminalRule binaryRule startRule)) :=
      Fintype.card_subtype_le _
    _ =
      Fintype.card
          (UntypedUsefulState
            terminalRule binaryRule startRule)
        *
        (Fintype.card
            (UntypedUsefulState
              terminalRule binaryRule startRule)
          *
         Fintype.card
            (UntypedUsefulState
              terminalRule binaryRule startRule)) := by
      simp

/-- Uniform cubic envelope for the final reduced presentation. -/
def untypedUsefulGrammarSizeEnvelope
    (g : Nat) : Nat :=
  g + g ^ 2 + g ^ 3

/--
If incoming state count and alphabet size are both at most g, final trimming
produces a reduced grammar whose state-plus-rule size is at most
g + g^2 + g^3.
-/
theorem untypedUsefulGrammarSize_le_envelope
    [Fintype N] [Fintype α]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (g : Nat)
    (hN : Fintype.card N ≤ g)
    (hα : Fintype.card α ≤ g) :
    untypedUsefulGrammarSize
        terminalRule binaryRule startRule
      ≤
    untypedUsefulGrammarSizeEnvelope g := by
  have hU :
      Fintype.card
          (UntypedUsefulState
            terminalRule binaryRule startRule)
        ≤ g :=
    le_trans
      (untypedUsefulState_card_le
        terminalRule binaryRule startRule)
      hN
  have ht0 :=
    untypedUsefulTerminalRuleIndex_card_le_ambient
      terminalRule binaryRule startRule
  have ht :
      @Fintype.card
          (UntypedTerminalRuleIndex
            (untypedUsefulTerminalRule
              terminalRule binaryRule startRule))
          (Fintype.ofFinite _)
        ≤
      g ^ 2 := by
    have hmul :
        Fintype.card
            (UntypedUsefulState
              terminalRule binaryRule startRule)
          * Fintype.card α
        ≤
        g * g :=
      Nat.mul_le_mul hU hα
    exact le_trans ht0
      (by simpa [pow_two] using hmul)
  have hb0 :=
    untypedUsefulBinaryRuleIndex_card_le_ambient
      terminalRule binaryRule startRule
  have hpair :
      Fintype.card
          (UntypedUsefulState
            terminalRule binaryRule startRule)
        *
        Fintype.card
          (UntypedUsefulState
            terminalRule binaryRule startRule)
      ≤
      g * g :=
    Nat.mul_le_mul hU hU
  have htriple :
      Fintype.card
          (UntypedUsefulState
            terminalRule binaryRule startRule)
        *
        (Fintype.card
            (UntypedUsefulState
              terminalRule binaryRule startRule)
          *
         Fintype.card
            (UntypedUsefulState
              terminalRule binaryRule startRule))
      ≤
      g * (g * g) :=
    Nat.mul_le_mul hU hpair
  have hb :
      @Fintype.card
          (UntypedBinaryRuleIndex
            (untypedUsefulBinaryRule
              terminalRule binaryRule startRule))
          (Fintype.ofFinite _)
        ≤
      g ^ 3 := by
    exact le_trans hb0
      (by
        simpa [pow_succ, pow_two, Nat.mul_assoc]
          using htriple)
  unfold untypedUsefulGrammarSize
  unfold untypedUsefulGrammarSizeEnvelope
  omega

end UntypedUsefulTrimSize

end TCS1
end LeanCfgProject
