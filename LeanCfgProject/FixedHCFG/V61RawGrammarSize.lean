import LeanCfgProject.FixedHCFG.V61BinarizationBlocks

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
A small v61-specific finite CFG presentation for the size bookkeeping in
Appendix A.  This is intentionally only the syntactic input layer: semantic
normalization remains in the preceding files.  The chosen `symbolSize` is a
reasonable symbol-count measure (nonterminals, productions, and right-hand-side
symbols, plus one start-symbol unit); the manuscript's bit encoding is assumed
only polynomially equivalent to such a measure.
-/

/-- One production of an arbitrary source CFG. -/
structure V61RawProduction (N : Type v) (Sigma : Type u) where
  lhs : N
  rhs : List (V61SourceAtom N Sigma)

/-- A finite source CFG presented by a finite list of productions. -/
structure V61RawGrammar (N : Type v) (Sigma : Type u) where
  start : N
  productions : List (V61RawProduction N Sigma)

/-- Number of terminal occurrences in one source right-hand side. -/
def v61TerminalOccurrences
    {N : Type v} {Sigma : Type u} :
    List (V61SourceAtom N Sigma) → Nat
  | [] => 0
  | V61SourceAtom.nonterminal _ :: rest => v61TerminalOccurrences rest
  | V61SourceAtom.terminal _ :: rest => 1 + v61TerminalOccurrences rest

/-- Terminal occurrences never exceed the number of right-hand-side symbols. -/
theorem v61_terminal_occurrences_le_length
    {N : Type v} {Sigma : Type u}
    (rhs : List (V61SourceAtom N Sigma)) :
    v61TerminalOccurrences rhs ≤ rhs.length := by
  induction rhs with
  | nil => simp [v61TerminalOccurrences]
  | cons a rest ih =>
      cases a with
      | nonterminal A =>
          simp [v61TerminalOccurrences, ih]
      | terminal a =>
          simp [v61TerminalOccurrences, ih]

/-- Number of fresh binary-chain symbols needed by a right-associated binarization. -/
def v61BinarizationChainCount (rhsLength : Nat) : Nat := rhsLength - 2

/-- A production never needs more chain symbols than symbols in its right-hand side. -/
theorem v61_binarization_chain_count_le (m : Nat) :
    v61BinarizationChainCount m ≤ m := by
  exact Nat.sub_le m 2

namespace V61RawGrammar

variable {N : Type v} {Sigma : Type u}

/-- Total number of right-hand-side symbol occurrences. -/
def rhsSymbolCount : List (V61RawProduction N Sigma) → Nat
  | [] => 0
  | p :: rest => p.rhs.length + rhsSymbolCount rest

/-- Total number of terminal-wrapper symbols needed by terminal isolation. -/
def wrapperCount : List (V61RawProduction N Sigma) → Nat
  | [] => 0
  | p :: rest => v61TerminalOccurrences p.rhs + wrapperCount rest

/-- Total number of fresh binary-chain symbols for right-associated binarization. -/
def chainCount : List (V61RawProduction N Sigma) → Nat
  | [] => 0
  | p :: rest => v61BinarizationChainCount p.rhs.length + chainCount rest

/-- Terminal isolation introduces at most one wrapper per source RHS symbol. -/
theorem wrapperCount_le_rhsSymbolCount
    (ps : List (V61RawProduction N Sigma)) :
    wrapperCount ps ≤ rhsSymbolCount ps := by
  induction ps with
  | nil => simp [wrapperCount, rhsSymbolCount]
  | cons p rest ih =>
      have hp := v61_terminal_occurrences_le_length p.rhs
      simp only [wrapperCount, rhsSymbolCount]
      exact Nat.add_le_add hp ih

/-- Binarization introduces at most one chain symbol per source RHS symbol. -/
theorem chainCount_le_rhsSymbolCount
    (ps : List (V61RawProduction N Sigma)) :
    chainCount ps ≤ rhsSymbolCount ps := by
  induction ps with
  | nil => simp [chainCount, rhsSymbolCount]
  | cons p rest ih =>
      have hp := v61_binarization_chain_count_le p.rhs.length
      simp only [chainCount, rhsSymbolCount]
      exact Nat.add_le_add hp ih

/-- Every individual RHS length is bounded by the total RHS-symbol count. -/
theorem rhs_length_le_rhsSymbolCount_of_mem
    {p : V61RawProduction N Sigma}
    {ps : List (V61RawProduction N Sigma)}
    (hp : p ∈ ps) :
    p.rhs.length ≤ rhsSymbolCount ps := by
  induction ps with
  | nil => simp at hp
  | cons q rest ih =>
      simp only [List.mem_cons] at hp
      simp only [rhsSymbolCount]
      rcases hp with rfl | hp
      · exact Nat.le_add_right _ _
      · exact le_trans (ih hp) (Nat.le_add_left _ _)

/--
A concrete symbol-count input size.  The leading `1` pays for the start symbol
and ensures a nonzero size, which is convenient for the polynomial envelopes.
-/
def symbolSize [Fintype N] (G : V61RawGrammar N Sigma) : Nat :=
  1 + Fintype.card N + G.productions.length + rhsSymbolCount G.productions

/-- The source nonterminal count is bounded by the chosen input size. -/
theorem card_le_symbolSize [Fintype N] (G : V61RawGrammar N Sigma) :
    Fintype.card N ≤ symbolSize G := by
  unfold symbolSize
  omega

/-- The number of source productions is bounded by the chosen input size. -/
theorem productions_length_le_symbolSize [Fintype N]
    (G : V61RawGrammar N Sigma) :
    G.productions.length ≤ symbolSize G := by
  unfold symbolSize
  omega

/-- The total source RHS-symbol count is bounded by the chosen input size. -/
theorem rhsSymbolCount_le_symbolSize [Fintype N]
    (G : V61RawGrammar N Sigma) :
    rhsSymbolCount G.productions ≤ symbolSize G := by
  unfold symbolSize
  omega

/-- The terminal-wrapper family is linearly bounded by the input size. -/
theorem wrapperCount_le_symbolSize [Fintype N]
    (G : V61RawGrammar N Sigma) :
    wrapperCount G.productions ≤ symbolSize G := by
  exact le_trans (wrapperCount_le_rhsSymbolCount G.productions)
    (rhsSymbolCount_le_symbolSize G)

/-- The binarization-chain family is linearly bounded by the input size. -/
theorem chainCount_le_symbolSize [Fintype N]
    (G : V61RawGrammar N Sigma) :
    chainCount G.productions ≤ symbolSize G := by
  exact le_trans (chainCount_le_rhsSymbolCount G.productions)
    (rhsSymbolCount_le_symbolSize G)

/-- Every source production has RHS length at most the input size. -/
theorem rhs_length_le_symbolSize_of_mem [Fintype N]
    (G : V61RawGrammar N Sigma)
    {p : V61RawProduction N Sigma}
    (hp : p ∈ G.productions) :
    p.rhs.length ≤ symbolSize G := by
  exact le_trans (rhs_length_le_rhsSymbolCount_of_mem hp)
    (rhsSymbolCount_le_symbolSize G)

/-- The chosen source size is always positive. -/
theorem one_le_symbolSize [Fintype N] (G : V61RawGrammar N Sigma) :
    1 ≤ symbolSize G := by
  unfold symbolSize
  omega

/--
Explicit `4n` intermediate-nonterminal envelope: fresh start + original
nonterminals + terminal wrappers + binary-chain symbols.
-/
theorem intermediate_family_count_le_four_size [Fintype N]
    (G : V61RawGrammar N Sigma) :
    1 + Fintype.card N + wrapperCount G.productions +
        chainCount G.productions ≤
      4 * symbolSize G := by
  exact v61_intermediate_card_le_four_mul
    (Fintype.card N) (wrapperCount G.productions)
    (chainCount G.productions) (symbolSize G)
    (card_le_symbolSize G) (wrapperCount_le_symbolSize G)
    (chainCount_le_symbolSize G) (one_le_symbolSize G)

/--
Before epsilon elimination, transformed source rules plus wrapper rules plus
chain rules are bounded by `3n` under this coarse but convenient accounting.
-/
theorem pre_epsilon_rule_count_le_three_size [Fintype N]
    (G : V61RawGrammar N Sigma) :
    G.productions.length + wrapperCount G.productions +
        chainCount G.productions ≤
      3 * symbolSize G := by
  have hP := productions_length_le_symbolSize G
  have hW := wrapperCount_le_symbolSize G
  have hC := chainCount_le_symbolSize G
  omega

/--
Consequently, the standard at-most-three nullable-child variants give a `9n`
post-epsilon rule envelope.
-/
theorem post_epsilon_rule_count_le_nine_size [Fintype N]
    (G : V61RawGrammar N Sigma)
    (terminalCount unitCount binaryCount : Nat)
    (hClassify : terminalCount + unitCount + binaryCount ≤
      G.productions.length + wrapperCount G.productions +
        chainCount G.productions) :
    terminalCount + unitCount + 3 * binaryCount ≤
      9 * symbolSize G := by
  have hPre : terminalCount + unitCount + binaryCount ≤
      3 * symbolSize G :=
    le_trans hClassify (pre_epsilon_rule_count_le_three_size G)
  have h := v61_epsilon_variant_linear_bound
    terminalCount unitCount binaryCount (symbolSize G) 3 hPre
  simpa [Nat.mul_assoc] using h

/--
With the explicit `4n` nonterminal and `9n` non-unit-rule envelopes, unit
closure plus trimming has a coarse explicit `40 n^2` final-size bound.
-/
theorem final_size_le_forty_square [Fintype N]
    (G : V61RawGrammar N Sigma)
    (finalSymbols finalRules intermediateNT nonunitCount : Nat)
    (hFinalSymbols : finalSymbols ≤ intermediateNT)
    (hFinalRules : finalRules ≤ intermediateNT * nonunitCount)
    (hN : intermediateNT ≤ 4 * symbolSize G)
    (hP : nonunitCount ≤ 9 * symbolSize G) :
    finalSymbols + finalRules ≤
      40 * symbolSize G * symbolSize G := by
  have h := v61_final_size_quadratic_bound
    finalSymbols finalRules intermediateNT nonunitCount
    (symbolSize G) 4 9 (one_le_symbolSize G)
    hFinalSymbols hFinalRules hN hP
  norm_num at h ⊢
  exact h

end V61RawGrammar

end FixedHCFG
end LeanCfgProject
