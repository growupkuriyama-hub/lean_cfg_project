import LeanCfgProject.MCFG.FI_v2_1_CanonicalRuleListCountingGold

/-!
# FI v2.1 Lean experiment: canonical enumeration-bound interface

This fifty-ninth layer introduces a conservative bound interface for the
canonical learner grammar package.

The previous layers expose exact rule-list counts for the finite refined rule
lists carried by a canonical package.  This file does not prove any polynomial
or asymptotic estimate.  Instead, it records the shape of an enumeration-bound
certificate: external natural-number bounds may be supplied for refined rule
counts, ordinary rule counts, output-type counts, and local type-choice counts,
and the package records that the actual listed finite data are below those
bounds.

The point is to prepare a stable target for later complexity statements without
committing to the concrete `List.bind` enumeration implementation yet.
-/

namespace FIv21

universe u v w

noncomputable section

section CanonicalEnumerationBoundInterface

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- External enumeration bounds for the finite data carried by a canonical
learner grammar package.

The bounds are intentionally plain natural numbers.  Later files can instantiate
these fields by closed-form expressions in the size of the base grammar, the
fan-out, and the finite observation monoid. -/
structure CanonicalEnumerationBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  terminalBound : Nat
  binaryBound : Nat
  startBound : Nat
  totalBound : Nat
  ordinaryBound : Nat
  outputTypeBound : Nat → Nat
  binaryTypeChoiceBound : (ρ : BinaryRule N α G.arity) → Nat
  startTypeChoiceBound : (ρ : StartRule N) → Nat
  terminalCount_le : P.refinedTerminalRuleCount ≤ terminalBound
  binaryCount_le : P.refinedBinaryRuleCount ≤ binaryBound
  startCount_le : P.refinedStartRuleCount ≤ startBound
  totalCount_le : P.refinedRuleCount ≤ totalBound
  ordinaryCount_le : P.ordinaryRuleCount ≤ ordinaryBound
  outputTypeCount_le : ∀ d : Nat,
    P.planOutputTypeCount d ≤ outputTypeBound d
  binaryTypeChoiceCount_le : ∀ ρ : BinaryRule N α G.arity,
    P.planBinaryTypeChoiceCount ρ ≤ binaryTypeChoiceBound ρ
  startTypeChoiceCount_le : ∀ ρ : StartRule N,
    P.planStartTypeChoiceCount ρ ≤ startTypeChoiceBound ρ

namespace CanonicalEnumerationBounds

/-- The tautological bound certificate obtained by taking every bound to be the
actual count.  This is useful as a safe default before sharper estimates are
proved. -/
def exactForPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) :
    CanonicalEnumerationBounds P :=
  { terminalBound := P.refinedTerminalRuleCount
    binaryBound := P.refinedBinaryRuleCount
    startBound := P.refinedStartRuleCount
    totalBound := P.refinedRuleCount
    ordinaryBound := P.ordinaryRuleCount
    outputTypeBound := fun d => P.planOutputTypeCount d
    binaryTypeChoiceBound := fun ρ => P.planBinaryTypeChoiceCount ρ
    startTypeChoiceBound := fun ρ => P.planStartTypeChoiceCount ρ
    terminalCount_le := le_rfl
    binaryCount_le := le_rfl
    startCount_le := le_rfl
    totalCount_le := le_rfl
    ordinaryCount_le := le_rfl
    outputTypeCount_le := by
      intro d
      exact le_rfl
    binaryTypeChoiceCount_le := by
      intro ρ
      exact le_rfl
    startTypeChoiceCount_le := by
      intro ρ
      exact le_rfl }

/-- The terminal refined-rule count is below the supplied terminal bound. -/
theorem refinedTerminalRuleCount_le
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (B : CanonicalEnumerationBounds P) :
    P.refinedTerminalRuleCount ≤ B.terminalBound := by
  exact B.terminalCount_le

/-- The binary refined-rule count is below the supplied binary bound. -/
theorem refinedBinaryRuleCount_le
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (B : CanonicalEnumerationBounds P) :
    P.refinedBinaryRuleCount ≤ B.binaryBound := by
  exact B.binaryCount_le

/-- The start refined-rule count is below the supplied start bound. -/
theorem refinedStartRuleCount_le
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (B : CanonicalEnumerationBounds P) :
    P.refinedStartRuleCount ≤ B.startBound := by
  exact B.startCount_le

/-- The total refined-rule count is below the supplied total bound. -/
theorem refinedRuleCount_le
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (B : CanonicalEnumerationBounds P) :
    P.refinedRuleCount ≤ B.totalBound := by
  exact B.totalCount_le

/-- The ordinary base-rule count is below the supplied ordinary bound. -/
theorem ordinaryRuleCount_le
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (B : CanonicalEnumerationBounds P) :
    P.ordinaryRuleCount ≤ B.ordinaryBound := by
  exact B.ordinaryCount_le

/-- The output-type count at arity `d` is below the supplied arity-wise bound. -/
theorem outputTypeCount_le_bound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (B : CanonicalEnumerationBounds P) (d : Nat) :
    P.planOutputTypeCount d ≤ B.outputTypeBound d := by
  exact B.outputTypeCount_le d

/-- The binary type-choice count for an ordinary binary rule is below the
supplied local bound. -/
theorem binaryTypeChoiceCount_le_bound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (B : CanonicalEnumerationBounds P)
    (ρ : BinaryRule N α G.arity) :
    P.planBinaryTypeChoiceCount ρ ≤ B.binaryTypeChoiceBound ρ := by
  exact B.binaryTypeChoiceCount_le ρ

/-- The start type-choice count for an ordinary start rule is below the supplied
local bound. -/
theorem startTypeChoiceCount_le_bound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (B : CanonicalEnumerationBounds P)
    (ρ : StartRule N) :
    P.planStartTypeChoiceCount ρ ≤ B.startTypeChoiceBound ρ := by
  exact B.startTypeChoiceCount_le ρ

end CanonicalEnumerationBounds

end CanonicalEnumerationBoundInterface

end

end FIv21
