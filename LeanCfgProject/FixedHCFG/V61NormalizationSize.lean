import LeanCfgProject.FixedHCFG.V61BinarizationThickness

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
Polynomial-size bookkeeping for Appendix A of TCS revision v61.

The semantic preservation and thickness arguments are already handled in the
preceding v61 files.  Here we isolate the elementary counting facts used by
the manuscript: terminal isolation/binarization create only linearly many
intermediate nonterminals, epsilon elimination creates at most three variants
per binary rule, and unit-closure copying is quadratic in the number of
nonterminals and non-unit productions.
-/

/--
A fresh start symbol, original symbols, terminal wrappers, and binarization
chain symbols fit in `4*n` whenever each of the latter three families has size
at most `n` and the input size is nonzero.
-/
theorem v61_intermediate_card_le_four_mul
    (sourceCard wrapperCard chainCard n : Nat)
    (hSource : sourceCard ≤ n)
    (hWrapper : wrapperCard ≤ n)
    (hChain : chainCard ≤ n)
    (hn : 1 ≤ n) :
    1 + sourceCard + wrapperCard + chainCard ≤ 4 * n := by
  omega

/--
Because every binary production creates at most the three variants `BC`, `B`,
and `C`, epsilon elimination preserves linear rule size.
-/
theorem v61_epsilon_variant_linear_bound
    (terminalCount unitCount binaryCount n c : Nat)
    (hPre : terminalCount + unitCount + binaryCount ≤ c * n) :
    terminalCount + unitCount + 3 * binaryCount ≤ 3 * c * n := by
  have hLocal :
      terminalCount + unitCount + 3 * binaryCount ≤
        3 * (terminalCount + unitCount + binaryCount) := by
    omega
  have hScaled := Nat.mul_le_mul_left 3 hPre
  calc
    terminalCount + unitCount + 3 * binaryCount ≤
        3 * (terminalCount + unitCount + binaryCount) := hLocal
    _ ≤ 3 * (c * n) := hScaled
    _ = 3 * c * n := by ring

/--
Unit closure copies at most one non-unit production for every pair consisting
of a source nonterminal and a reachable non-unit production.
-/
theorem v61_unit_copy_quadratic_bound
    (nonterminalCount nonunitCount n cN cP : Nat)
    (hN : nonterminalCount ≤ cN * n)
    (hP : nonunitCount ≤ cP * n) :
    nonterminalCount * nonunitCount ≤
      (cN * cP) * n * n := by
  calc
    nonterminalCount * nonunitCount ≤
        (cN * n) * (cP * n) := Nat.mul_le_mul hN hP
    _ = (cN * cP) * n * n := by ring

/--
After unit copying and trimming, symbols plus rules remain quadratic.  Trimming
can only decrease the two counts.
-/
theorem v61_final_size_quadratic_bound
    (finalSymbols finalRules nonterminalCount nonunitCount n cN cP : Nat)
    (hn : 1 ≤ n)
    (hFinalSymbols : finalSymbols ≤ nonterminalCount)
    (hFinalRules : finalRules ≤ nonterminalCount * nonunitCount)
    (hN : nonterminalCount ≤ cN * n)
    (hP : nonunitCount ≤ cP * n) :
    finalSymbols + finalRules ≤
      (cN + cN * cP) * n * n := by
  have hNquad : nonterminalCount ≤ cN * n * n := by
    calc
      nonterminalCount ≤ cN * n := hN
      _ = (cN * n) * 1 := by simp
      _ ≤ (cN * n) * n := Nat.mul_le_mul_left (cN * n) hn
  have hCopy :=
    v61_unit_copy_quadratic_bound
      nonterminalCount nonunitCount n cN cP hN hP
  calc
    finalSymbols + finalRules ≤
        nonterminalCount + nonterminalCount * nonunitCount :=
      Nat.add_le_add hFinalSymbols hFinalRules
    _ ≤ cN * n * n + (cN * cP) * n * n :=
      Nat.add_le_add hNquad hCopy
    _ = (cN + cN * cP) * n * n := by ring

/--
Concrete `c_N = 4` version of the v61 thickness envelope.  The remaining
structural obligation is only to exhibit the three linearly bounded families
of intermediate nonterminals and the block-expansion certificate.
-/
theorem v61_explicit_four_post_unit_thickness
    {N0 : Type v} {NB : Type w} {Sigma : Type u}
    [Fintype NB]
    {epsilon : V61EpsilonRules NB}
    {terminal : V60TerminalRules NB Sigma}
    {unit : V61UnitRules NB}
    {binary : V60BinaryRules NB}
    (shortLen : N0 → Nat)
    (tauR n sourceCard wrapperCard chainCard : Nat)
    (hn : 1 ≤ n)
    (hShort : ∀ A : N0, shortLen A ≤ tauR)
    (hExpansion : V61BinarizationExpansionCertificate
      epsilon terminal unit binary shortLen n)
    (hCardDecomp :
      Fintype.card NB ≤ 1 + sourceCard + wrapperCard + chainCard)
    (hSource : sourceCard ≤ n)
    (hWrapper : wrapperCard ≤ n)
    (hChain : chainCard ≤ n) :
    V60BaseThicknessBound
      (V61UnitFreeTerminal terminal
        (V61EpsElimUnit epsilon terminal unit binary))
      (V61UnitFreeBinary
        (V61EpsElimUnit epsilon terminal unit binary) binary)
      (1 + 4 * n * n * (tauR + 1)) := by
  have hCardAux :
      1 + sourceCard + wrapperCard + chainCard ≤ 4 * n :=
    v61_intermediate_card_le_four_mul
      sourceCard wrapperCard chainCard n hSource hWrapper hChain hn
  have hCard : Fintype.card NB ≤ 4 * n := le_trans hCardDecomp hCardAux
  exact v61_binarization_to_post_unit_polynomial_thickness
    shortLen tauR n 4 hShort hExpansion hCard

end FixedHCFG
end LeanCfgProject
