import LeanCfgProject.FixedHCFG.V61RightBinarization

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
Carrier coverage for the concrete terminal-isolation/right-binarization stage
of Appendix A in TCS revision v61.

The quantitative normalization proof already knows how to turn structured
block coverage into the intermediate thickness bound.  This file reduces that
coverage obligation to the standard four families of intermediate symbols:

* the fresh start symbol;
* embedded source nonterminals;
* terminal-isolation wrappers; and
* proper right-binarization suffix nodes of length at least two.

The final family is count-compatible with `rhs.length - 2`: the full right-hand
side is rooted at the embedded source lhs, while only proper suffixes of length
at least two require fresh chain symbols.
-/

/--
A proof-relevant classification of an intermediate nonterminal produced by the
standard normalization front end.
-/
inductive V61RawIntermediateCarrier
    {N0 : Type v} {NB : Type w} {Sigma : Type u}
    (G : V61RawGrammar N0 Sigma)
    (freshStart : NB)
    (embed : N0 → NB)
    (leaf : V61SourceAtom N0 Sigma → NB)
    (node : V61RawProduction N0 Sigma →
      List (V61SourceAtom N0 Sigma) → NB) :
    NB → Type (max u (max v w)) where
  | fresh :
      V61RawIntermediateCarrier G freshStart embed leaf node freshStart
  | source (A : N0) :
      V61RawIntermediateCarrier G freshStart embed leaf node (embed A)
  | wrapper (a : Sigma) :
      V61RawIntermediateCarrier G freshStart embed leaf node
        (leaf (V61SourceAtom.terminal a))
  | chain
      (p : V61RawProduction N0 Sigma)
      (suffix : List (V61SourceAtom N0 Sigma))
      (hp : p ∈ G.productions)
      (hTwo : 2 ≤ suffix.length)
      (hProper : suffix.length < p.rhs.length) :
      V61RawIntermediateCarrier G freshStart embed leaf node
        (node p suffix)

namespace V61RawIntermediateCarrier

variable {N0 : Type v} {NB : Type w} {Sigma : Type u}
variable {epsilon : V61EpsilonRules NB}
variable {terminal : V60TerminalRules NB Sigma}
variable {unit : V61UnitRules NB}
variable {binary : V60BinaryRules NB}
variable {embed : N0 → NB}
variable {sourceTree : ∀ A : N0,
  V61NullableDerivationTree epsilon terminal unit binary (embed A)}

/--
The standard carrier classification plus the usual terminal-wrapper and
right-chain rules imply structured block coverage at raw input size `n`.
-/
theorem blockCoverage
    [Fintype N0]
    (G : V61RawGrammar N0 Sigma)
    (freshStart : NB)
    (leaf : V61SourceAtom N0 Sigma → NB)
    (node : V61RawProduction N0 Sigma →
      List (V61SourceAtom N0 Sigma) → NB)
    (hFresh : unit freshStart (embed G.start))
    (hNonterminal : ∀ A : N0,
      leaf (V61SourceAtom.nonterminal A) = embed A)
    (hTerminal : ∀ a : Sigma,
      terminal (leaf (V61SourceAtom.terminal a)) a)
    (hPair : ∀ (p : V61RawProduction N0 Sigma)
        (a b : V61SourceAtom N0 Sigma),
      binary (node p [a, b]) (leaf a) (leaf b))
    (hLong : ∀ (p : V61RawProduction N0 Sigma)
        (a b c : V61SourceAtom N0 Sigma)
        (rest : List (V61SourceAtom N0 Sigma)),
      binary (node p (a :: b :: c :: rest))
        (leaf a) (node p (b :: c :: rest)))
    (hCarrier : ∀ A : NB,
      V61RawIntermediateCarrier G freshStart embed leaf node A) :
    V61BinarizationBlockCoverage
      epsilon terminal unit binary embed sourceTree
        (V61RawGrammar.symbolSize G) := by
  intro A
  cases hCarrier A with
  | fresh =>
      refine ⟨[V61SourceAtom.nonterminal G.start], ?_, ?_⟩
      · exact .stepUnit hFresh (.source G.start)
      · simpa using V61RawGrammar.one_le_symbolSize G
  | source A0 =>
      refine ⟨[V61SourceAtom.nonterminal A0], .source A0, ?_⟩
      simpa using V61RawGrammar.one_le_symbolSize G
  | wrapper a =>
      refine ⟨[V61SourceAtom.terminal a], ?_, ?_⟩
      · exact V61RightBinarization.atom_leaf_block
          leaf hNonterminal hTerminal (V61SourceAtom.terminal a)
      · simpa using V61RawGrammar.one_le_symbolSize G
  | chain p suffix hp hTwo hProper =>
      refine ⟨suffix, ?_, ?_⟩
      · exact V61RightBinarization.right_suffix_block_of_isolated_atoms
          (node := node p) leaf hNonterminal hTerminal
          (hPair p) (hLong p) suffix hTwo
      · exact le_trans (Nat.le_of_lt hProper)
          (V61RawGrammar.rhs_length_le_symbolSize_of_mem G hp)

/--
Carrier coverage removes the abstract `V61BinarizationBlockCoverage`
hypothesis from the raw-to-post-unit thickness theorem.  The remaining
front-end obligations are now exactly the concrete symbol classification,
normalization rules, and the already separate finite-cardinality decomposition.
-/
theorem toPostUnitThickness
    [Fintype N0] [Fintype NB]
    (G : V61RawGrammar N0 Sigma)
    (freshStart : NB)
    (leaf : V61SourceAtom N0 Sigma → NB)
    (node : V61RawProduction N0 Sigma →
      List (V61SourceAtom N0 Sigma) → NB)
    (shortLen : N0 → Nat)
    (tauR : Nat)
    (hSource : ∀ A : N0,
      (V61NullableDerivationTree.yield (sourceTree A)).length = shortLen A)
    (hShort : ∀ A : N0, shortLen A ≤ tauR)
    (hFresh : unit freshStart (embed G.start))
    (hNonterminal : ∀ A : N0,
      leaf (V61SourceAtom.nonterminal A) = embed A)
    (hTerminal : ∀ a : Sigma,
      terminal (leaf (V61SourceAtom.terminal a)) a)
    (hPair : ∀ (p : V61RawProduction N0 Sigma)
        (a b : V61SourceAtom N0 Sigma),
      binary (node p [a, b]) (leaf a) (leaf b))
    (hLong : ∀ (p : V61RawProduction N0 Sigma)
        (a b c : V61SourceAtom N0 Sigma)
        (rest : List (V61SourceAtom N0 Sigma)),
      binary (node p (a :: b :: c :: rest))
        (leaf a) (node p (b :: c :: rest)))
    (hCarrier : ∀ A : NB,
      V61RawIntermediateCarrier G freshStart embed leaf node A)
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
  apply v61_raw_to_post_unit_thickness
    G embed sourceTree shortLen tauR hSource hShort
  · exact blockCoverage G freshStart leaf node hFresh hNonterminal hTerminal
      hPair hLong hCarrier
  · exact hCardDecomp

end V61RawIntermediateCarrier

end FixedHCFG
end LeanCfgProject
