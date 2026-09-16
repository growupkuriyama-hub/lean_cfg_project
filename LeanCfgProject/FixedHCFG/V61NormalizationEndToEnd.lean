import LeanCfgProject.FixedHCFG.V61RawGrammarSize

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
End-point wrappers for the quantitative part of Appendix A in TCS revision
v61.  The purpose of this file is not to define the concrete normalization
algorithm yet, but to assemble the already verified semantic and counting
lemmas so that the remaining construction obligations are exposed explicitly.
-/

/--
From a raw source grammar, a structured contiguous-block certificate and the
linear decomposition of intermediate nonterminals imply the manuscript's
post-unit SSBNF-core thickness envelope directly in terms of the raw input
symbol size.
-/
theorem v61_raw_to_post_unit_thickness
    {N0 : Type v} {NB : Type w} {Sigma : Type u}
    [Fintype N0] [Fintype NB]
    (G : V61RawGrammar N0 Sigma)
    {epsilon : V61EpsilonRules NB}
    {terminal : V60TerminalRules NB Sigma}
    {unit : V61UnitRules NB}
    {binary : V60BinaryRules NB}
    (embed : N0 → NB)
    (sourceTree : ∀ A : N0,
      V61NullableDerivationTree epsilon terminal unit binary (embed A))
    (shortLen : N0 → Nat)
    (tauR : Nat)
    (hSource : ∀ A : N0,
      (V61NullableDerivationTree.yield (sourceTree A)).length = shortLen A)
    (hShort : ∀ A : N0, shortLen A ≤ tauR)
    (hCoverage : V61BinarizationBlockCoverage
      epsilon terminal unit binary embed sourceTree
        (V61RawGrammar.symbolSize G))
    (hCardDecomp :
      Fintype.card NB ≤
        1 + Fintype.card N0 +
          V61RawGrammar.wrapperCount G.productions +
          V61RawGrammar.chainCount G.productions) :
    V60BaseThicknessBound
      (V61UnitFreeTerminal terminal
        (V61EpsElimUnit epsilon terminal unit binary))
      (V61UnitFreeBinary
        (V61EpsElimUnit epsilon terminal unit binary) binary)
      (1 + 4 * V61RawGrammar.symbolSize G *
        V61RawGrammar.symbolSize G * (tauR + 1)) := by
  have hExpansion : V61BinarizationExpansionCertificate
      epsilon terminal unit binary shortLen
        (V61RawGrammar.symbolSize G) :=
    v61_block_coverage_to_expansion_certificate
      embed sourceTree shortLen (V61RawGrammar.symbolSize G)
      hSource hCoverage
  exact v61_explicit_four_post_unit_thickness
    shortLen tauR (V61RawGrammar.symbolSize G)
    (Fintype.card N0)
    (V61RawGrammar.wrapperCount G.productions)
    (V61RawGrammar.chainCount G.productions)
    (V61RawGrammar.one_le_symbolSize G)
    hShort hExpansion hCardDecomp
    (V61RawGrammar.card_le_symbolSize G)
    (V61RawGrammar.wrapperCount_le_symbolSize G)
    (V61RawGrammar.chainCount_le_symbolSize G)

/--
Raw-grammar wrapper for the quadratic final-size bookkeeping.  The hypotheses
`hIntermediate`, `hClassify`, `hFinalSymbols` and `hFinalRules` are precisely
the finite counting obligations that the concrete terminal-isolation,
binarization, epsilon-elimination, unit-closure and trimming construction must
supply.
-/
theorem v61_raw_final_size_quadratic
    {N0 : Type v} {Sigma : Type u}
    [Fintype N0]
    (G : V61RawGrammar N0 Sigma)
    (terminalCount unitCount binaryCount : Nat)
    (intermediateNT finalSymbols finalRules : Nat)
    (hIntermediate :
      intermediateNT ≤
        1 + Fintype.card N0 +
          V61RawGrammar.wrapperCount G.productions +
          V61RawGrammar.chainCount G.productions)
    (hClassify : terminalCount + unitCount + binaryCount ≤
      G.productions.length +
        V61RawGrammar.wrapperCount G.productions +
        V61RawGrammar.chainCount G.productions)
    (hFinalSymbols : finalSymbols ≤ intermediateNT)
    (hFinalRules :
      finalRules ≤
        intermediateNT * (terminalCount + unitCount + 3 * binaryCount)) :
    finalSymbols + finalRules ≤
      40 * V61RawGrammar.symbolSize G *
        V61RawGrammar.symbolSize G := by
  have hN : intermediateNT ≤ 4 * V61RawGrammar.symbolSize G :=
    le_trans hIntermediate
      (V61RawGrammar.intermediate_family_count_le_four_size G)
  have hP : terminalCount + unitCount + 3 * binaryCount ≤
      9 * V61RawGrammar.symbolSize G :=
    V61RawGrammar.post_epsilon_rule_count_le_nine_size
      G terminalCount unitCount binaryCount hClassify
  exact V61RawGrammar.final_size_le_forty_square
    G finalSymbols finalRules intermediateNT
    (terminalCount + unitCount + 3 * binaryCount)
    hFinalSymbols hFinalRules hN hP

end FixedHCFG
end LeanCfgProject
