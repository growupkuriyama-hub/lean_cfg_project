import LeanCfgProject.FixedHCFG.V61PostUnitBridge

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
The quantitative core of the first paragraph of Appendix A in TCS revision
v61: terminal isolation and binarization create symbols that expand a block of
an original right-hand side.  If that block contains at most `n` original
symbols and every original nonterminal has a terminal witness of length at
most `tauR`, then the block has a terminal witness of length at most
`n * (tauR + 1)`; terminal atoms cost one.

The file deliberately packages the remaining grammar-construction obligation
as `V61BinarizationExpansionCertificate`.  Instantiating that certificate with
the concrete terminal-isolation/binarization construction will finish the
nonstandard quantitative step of Proposition 7.4 without changing the later
epsilon/unit proofs.
-/

/-- One symbol of an original CFG right-hand side. -/
inductive V61SourceAtom (N : Type v) (Sigma : Type u) where
  | nonterminal (A : N)
  | terminal (a : Sigma)

/-- Length contribution of a source atom after choosing short terminal yields. -/
def v61SourceAtomCost
    {N : Type v} {Sigma : Type u}
    (shortLen : N → Nat) : V61SourceAtom N Sigma → Nat
  | .nonterminal A => shortLen A
  | .terminal _ => 1

/-- Terminals and productive source nonterminals both cost at most `tauR + 1`. -/
theorem v61_source_atom_cost_le
    {N : Type v} {Sigma : Type u}
    (shortLen : N → Nat) (tauR : Nat)
    (hShort : ∀ A : N, shortLen A ≤ tauR)
    (a : V61SourceAtom N Sigma) :
    v61SourceAtomCost shortLen a ≤ tauR + 1 := by
  cases a with
  | nonterminal A =>
      exact le_trans (hShort A) (Nat.le_succ tauR)
  | terminal a =>
      omega

/-- Cost of a contiguous source block after short witnesses are substituted. -/
def v61SourceBlockCost
    {N : Type v} {Sigma : Type u}
    (shortLen : N → Nat) (atoms : List (V61SourceAtom N Sigma)) : Nat :=
  atoms.foldr (fun a total => v61SourceAtomCost shortLen a + total) 0

/-- A source block of length `m` costs at most `m * (tauR + 1)`. -/
theorem v61_source_block_cost_le_length_mul
    {N : Type v} {Sigma : Type u}
    (shortLen : N → Nat) (tauR : Nat)
    (hShort : ∀ A : N, shortLen A ≤ tauR)
    (atoms : List (V61SourceAtom N Sigma)) :
    v61SourceBlockCost shortLen atoms ≤ atoms.length * (tauR + 1) := by
  induction atoms with
  | nil =>
      simp [v61SourceBlockCost]
  | cons a rest ih =>
      have ha := v61_source_atom_cost_le shortLen tauR hShort a
      change v61SourceAtomCost shortLen a + v61SourceBlockCost shortLen rest ≤
        Nat.succ rest.length * (tauR + 1)
      calc
        v61SourceAtomCost shortLen a + v61SourceBlockCost shortLen rest ≤
            (tauR + 1) + rest.length * (tauR + 1) :=
          Nat.add_le_add ha ih
        _ = Nat.succ rest.length * (tauR + 1) := by
          simp [Nat.succ_mul, Nat.add_comm]

/-- The manuscript's `O(n)` block-length hypothesis gives the desired bound. -/
theorem v61_source_block_cost_le
    {N : Type v} {Sigma : Type u}
    (shortLen : N → Nat) (tauR n : Nat)
    (hShort : ∀ A : N, shortLen A ≤ tauR)
    (atoms : List (V61SourceAtom N Sigma))
    (hLen : atoms.length ≤ n) :
    v61SourceBlockCost shortLen atoms ≤ n * (tauR + 1) := by
  exact le_trans
    (v61_source_block_cost_le_length_mul shortLen tauR hShort atoms)
    (Nat.mul_le_mul_right (tauR + 1) hLen)

/--
Proof-relevant interface for the concrete terminal-isolation/binarization
construction.  Each intermediate nonterminal `A` comes with a source block of
length at most `n` and a same-root derivation whose frontier length is exactly
the cost of that block.
-/
def V61BinarizationExpansionCertificate
    {N0 : Type v} {NB : Type w} {Sigma : Type u}
    (epsilon : V61EpsilonRules NB)
    (terminal : V60TerminalRules NB Sigma)
    (unit : V61UnitRules NB)
    (binary : V60BinaryRules NB)
    (shortLen : N0 → Nat)
    (n : Nat) : Prop :=
  ∀ A : NB,
    ∃ (atoms : List (V61SourceAtom N0 Sigma))
      (t : V61NullableDerivationTree epsilon terminal unit binary A),
      atoms.length ≤ n ∧
        (V61NullableDerivationTree.yield t).length =
          v61SourceBlockCost shortLen atoms

/--
A block-expansion certificate immediately yields the intermediate thickness
bound `tau_B ≤ n * (tau_R + 1)` used in Appendix A.
-/
theorem v61_binarization_expansion_thickness
    {N0 : Type v} {NB : Type w} {Sigma : Type u}
    {epsilon : V61EpsilonRules NB}
    {terminal : V60TerminalRules NB Sigma}
    {unit : V61UnitRules NB}
    {binary : V60BinaryRules NB}
    (shortLen : N0 → Nat)
    (tauR n : Nat)
    (hShort : ∀ A : N0, shortLen A ≤ tauR)
    (hExpansion : V61BinarizationExpansionCertificate
      epsilon terminal unit binary shortLen n) :
    V61NullableThicknessBound epsilon terminal unit binary
      (n * (tauR + 1)) := by
  intro A t
  obtain ⟨atoms, witness, hLen, hYield⟩ := hExpansion A
  refine ⟨witness, ?_⟩
  rw [hYield]
  exact v61_source_block_cost_le shortLen tauR n hShort atoms hLen

/--
Compose the first-paragraph binarization estimate with the already verified
nullable-path, epsilon-elimination and unit-elimination pipeline.  Only the
linear bound on the number of intermediate nonterminals remains as a separate
size certificate.
-/
theorem v61_binarization_to_post_unit_polynomial_thickness
    {N0 : Type v} {NB : Type w} {Sigma : Type u}
    [Fintype NB]
    {epsilon : V61EpsilonRules NB}
    {terminal : V60TerminalRules NB Sigma}
    {unit : V61UnitRules NB}
    {binary : V60BinaryRules NB}
    (shortLen : N0 → Nat)
    (tauR n cN : Nat)
    (hShort : ∀ A : N0, shortLen A ≤ tauR)
    (hExpansion : V61BinarizationExpansionCertificate
      epsilon terminal unit binary shortLen n)
    (hCard : Fintype.card NB ≤ cN * n) :
    V60BaseThicknessBound
      (V61UnitFreeTerminal terminal
        (V61EpsElimUnit epsilon terminal unit binary))
      (V61UnitFreeBinary
        (V61EpsElimUnit epsilon terminal unit binary) binary)
      (1 + cN * n * n * (tauR + 1)) := by
  have hThickness :
      V61NullableThicknessBound epsilon terminal unit binary
        (n * (tauR + 1)) :=
    v61_binarization_expansion_thickness shortLen tauR n hShort hExpansion
  simpa using
    (v61_post_unit_polynomial_base_thickness
      (epsilon := epsilon) (terminal := terminal) (unit := unit)
      (binary := binary)
      (tau := n * (tauR + 1)) (n := n) (tauR := tauR)
      (cN := cN) (cTau := 1)
      hThickness hCard (by simp))

end FixedHCFG
end LeanCfgProject
