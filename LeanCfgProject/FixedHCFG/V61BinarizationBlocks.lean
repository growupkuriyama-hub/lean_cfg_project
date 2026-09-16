import LeanCfgProject.FixedHCFG.V61NormalizationSize

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
Structured contiguous-block witnesses for the terminal-isolation/binarization
stage of Appendix A in TCS revision v61.

`V61BinarizationExpansionCertificate` records only the resulting source block
and its witness length.  The type below is stronger: its constructors explain
how that block is assembled by epsilon, terminal, unit and binary productions,
with binary composition represented by list concatenation.  Thus the
"contiguous block of an original right-hand side" argument can be discharged
by constructing these derivations for the concrete binarization chains.
-/

/-- Source-block cost is additive under concatenation. -/
theorem v61_source_block_cost_append
    {N : Type v} {Sigma : Type u}
    (shortLen : N → Nat)
    (xs ys : List (V61SourceAtom N Sigma)) :
    v61SourceBlockCost shortLen (xs ++ ys) =
      v61SourceBlockCost shortLen xs + v61SourceBlockCost shortLen ys := by
  induction xs with
  | nil =>
      simp [v61SourceBlockCost]
  | cons a rest ih =>
      simp [v61SourceBlockCost, ih, Nat.add_assoc]

/--
A derivation annotated by the contiguous source block represented at its root.
Original nonterminals use a supplied same-root witness; terminal wrappers
represent one terminal atom; binary rules concatenate adjacent blocks.
-/
inductive V61BlockDerivation
    {N0 : Type v} {NB : Type w} {Sigma : Type u}
    (epsilon : V61EpsilonRules NB)
    (terminal : V60TerminalRules NB Sigma)
    (unit : V61UnitRules NB)
    (binary : V60BinaryRules NB)
    (embed : N0 → NB)
    (sourceTree : ∀ A : N0,
      V61NullableDerivationTree epsilon terminal unit binary (embed A)) :
    NB → List (V61SourceAtom N0 Sigma) → Type (max u (max v w)) where
  | source (A : N0) :
      V61BlockDerivation epsilon terminal unit binary embed sourceTree
        (embed A) [V61SourceAtom.nonterminal A]
  | eps (A : NB) (hrule : epsilon A) :
      V61BlockDerivation epsilon terminal unit binary embed sourceTree A []
  | term (A : NB) (a : Sigma) (hrule : terminal A a) :
      V61BlockDerivation epsilon terminal unit binary embed sourceTree
        A [V61SourceAtom.terminal a]
  | stepUnit {A B : NB} {atoms : List (V61SourceAtom N0 Sigma)}
      (hrule : unit A B)
      (sub : V61BlockDerivation epsilon terminal unit binary embed sourceTree
        B atoms) :
      V61BlockDerivation epsilon terminal unit binary embed sourceTree A atoms
  | combine {A B C : NB}
      {leftAtoms rightAtoms : List (V61SourceAtom N0 Sigma)}
      (hrule : binary A B C)
      (left : V61BlockDerivation epsilon terminal unit binary embed sourceTree
        B leftAtoms)
      (right : V61BlockDerivation epsilon terminal unit binary embed sourceTree
        C rightAtoms) :
      V61BlockDerivation epsilon terminal unit binary embed sourceTree
        A (leftAtoms ++ rightAtoms)

namespace V61BlockDerivation

variable {N0 : Type v} {NB : Type w} {Sigma : Type u}
variable {epsilon : V61EpsilonRules NB}
variable {terminal : V60TerminalRules NB Sigma}
variable {unit : V61UnitRules NB}
variable {binary : V60BinaryRules NB}
variable {embed : N0 → NB}
variable {sourceTree : ∀ A : N0,
  V61NullableDerivationTree epsilon terminal unit binary (embed A)}

/-- Forget the source-block annotation and recover an ordinary v61 tree. -/
def toTree {A : NB} {atoms : List (V61SourceAtom N0 Sigma)} :
    V61BlockDerivation epsilon terminal unit binary embed sourceTree A atoms →
      V61NullableDerivationTree epsilon terminal unit binary A
  | .source A => sourceTree A
  | .eps A hrule => .epsilon A hrule
  | .term A a hrule => .terminal A a hrule
  | .stepUnit hrule sub => .unit _ _ hrule (toTree sub)
  | .combine hrule left right =>
      .binary _ _ _ hrule (toTree left) (toTree right)

/--
The ordinary frontier of an annotated block derivation has exactly the cost of
its source block once the source nonterminal witnesses realize `shortLen`.
-/
theorem toTree_yield_length
    (shortLen : N0 → Nat)
    (hSource : ∀ A : N0,
      (V61NullableDerivationTree.yield (sourceTree A)).length = shortLen A)
    {A : NB} {atoms : List (V61SourceAtom N0 Sigma)}
    (d : V61BlockDerivation epsilon terminal unit binary embed sourceTree
      A atoms) :
    (V61NullableDerivationTree.yield (toTree d)).length =
      v61SourceBlockCost shortLen atoms := by
  induction d with
  | source A =>
      simpa [toTree, v61SourceBlockCost, v61SourceAtomCost] using hSource A
  | eps A hrule =>
      simp [toTree, V61NullableDerivationTree.yield, v61SourceBlockCost]
  | term A a hrule =>
      simp [toTree, V61NullableDerivationTree.yield,
        v61SourceBlockCost, v61SourceAtomCost]
  | stepUnit hrule sub ih =>
      simpa [toTree, V61NullableDerivationTree.yield] using ih
  | combine hrule left right ihLeft ihRight =>
      simp [toTree, V61NullableDerivationTree.yield, List.length_append,
        ihLeft, ihRight, v61_source_block_cost_append]

end V61BlockDerivation

/--
Coverage obligation for the concrete binarized grammar: every intermediate
nonterminal represents some contiguous source block of length at most `n`.
-/
def V61BinarizationBlockCoverage
    {N0 : Type v} {NB : Type w} {Sigma : Type u}
    (epsilon : V61EpsilonRules NB)
    (terminal : V60TerminalRules NB Sigma)
    (unit : V61UnitRules NB)
    (binary : V60BinaryRules NB)
    (embed : N0 → NB)
    (sourceTree : ∀ A : N0,
      V61NullableDerivationTree epsilon terminal unit binary (embed A))
    (n : Nat) : Prop :=
  ∀ A : NB,
    ∃ (atoms : List (V61SourceAtom N0 Sigma))
      (d : V61BlockDerivation epsilon terminal unit binary embed sourceTree
        A atoms),
      atoms.length ≤ n

/-- Structured block coverage implies the earlier numerical expansion certificate. -/
theorem v61_block_coverage_to_expansion_certificate
    {N0 : Type v} {NB : Type w} {Sigma : Type u}
    {epsilon : V61EpsilonRules NB}
    {terminal : V60TerminalRules NB Sigma}
    {unit : V61UnitRules NB}
    {binary : V60BinaryRules NB}
    (embed : N0 → NB)
    (sourceTree : ∀ A : N0,
      V61NullableDerivationTree epsilon terminal unit binary (embed A))
    (shortLen : N0 → Nat)
    (n : Nat)
    (hSource : ∀ A : N0,
      (V61NullableDerivationTree.yield (sourceTree A)).length = shortLen A)
    (hCoverage : V61BinarizationBlockCoverage
      epsilon terminal unit binary embed sourceTree n) :
    V61BinarizationExpansionCertificate
      epsilon terminal unit binary shortLen n := by
  intro A
  obtain ⟨atoms, d, hLen⟩ := hCoverage A
  refine ⟨atoms, V61BlockDerivation.toTree d, hLen, ?_⟩
  exact V61BlockDerivation.toTree_yield_length shortLen hSource d

/-- Structured block coverage yields the Appendix A intermediate thickness bound. -/
theorem v61_block_coverage_thickness
    {N0 : Type v} {NB : Type w} {Sigma : Type u}
    {epsilon : V61EpsilonRules NB}
    {terminal : V60TerminalRules NB Sigma}
    {unit : V61UnitRules NB}
    {binary : V60BinaryRules NB}
    (embed : N0 → NB)
    (sourceTree : ∀ A : N0,
      V61NullableDerivationTree epsilon terminal unit binary (embed A))
    (shortLen : N0 → Nat)
    (tauR n : Nat)
    (hSource : ∀ A : N0,
      (V61NullableDerivationTree.yield (sourceTree A)).length = shortLen A)
    (hShort : ∀ A : N0, shortLen A ≤ tauR)
    (hCoverage : V61BinarizationBlockCoverage
      epsilon terminal unit binary embed sourceTree n) :
    V61NullableThicknessBound epsilon terminal unit binary
      (n * (tauR + 1)) := by
  apply v61_binarization_expansion_thickness shortLen tauR n hShort
  exact v61_block_coverage_to_expansion_certificate
    embed sourceTree shortLen n hSource hCoverage

end FixedHCFG
end LeanCfgProject
