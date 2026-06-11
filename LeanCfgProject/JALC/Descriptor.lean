import LeanCfgProject.JALC.TwoSidedContext

namespace LeanCfgProject
namespace JALC

universe u v

/-
Finite descriptor layer for the JALC algebra experiment.

This file introduces a lightweight finite descriptor for typed CFG
presentations.  The point is not to formalize every grammar-theoretic
detail at once, but to provide a finite Lean object corresponding to the
paper's descriptor-level construction.
-/


/-- A terminal production observed through a finite two-sided context.

Intuitively, this records that a typed nonterminal may produce one
terminal symbol under an observed surrounding context.
-/
structure TerminalRule (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) where
  lhs : TypedNonterminal N Obs
  terminal : Sigma
  ctx : ObservedContext Obs
deriving DecidableEq, Fintype


/-- A nullary production, used for epsilon-like or zero-yield components.

This is deliberately abstract: the paper-facing descriptor only needs a
finite support of such zero-ary observations.
-/
structure NullaryRule (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) where
  lhs : TypedNonterminal N Obs
  ctx : ObservedContext Obs
deriving DecidableEq, Fintype


/-- A binary production in the typed descriptor.

The parent and both children are typed nonterminals.  The additional
observed context is a finite record of the surrounding h-information used
by the frame-transport equation.
-/
structure BinaryRule (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) where
  parent : TypedNonterminal N Obs
  leftChild : TypedNonterminal N Obs
  rightChild : TypedNonterminal N Obs
  ctx : ObservedContext Obs
deriving DecidableEq, Fintype


/-- The finite rule universe associated with a fixed finite observer and
finite nonterminal/alphabet sets. -/
structure DescriptorUniverse (N : Type u) (Sigma : Type v)
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N] [Fintype Sigma] [DecidableEq Sigma] where
  terminalUniverse : Finset (TerminalRule N Obs)
  nullaryUniverse : Finset (NullaryRule N Obs)
  binaryUniverse : Finset (BinaryRule N Obs)


/-- The canonical full finite universe of terminal rules. -/
def allTerminalRules (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N] [Fintype Sigma] [DecidableEq Sigma] :
    Finset (TerminalRule N Obs) :=
  Finset.univ


/-- The canonical full finite universe of nullary rules. -/
def allNullaryRules (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N] :
    Finset (NullaryRule N Obs) :=
  Finset.univ


/-- The canonical full finite universe of binary rules. -/
def allBinaryRules (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N] :
    Finset (BinaryRule N Obs) :=
  Finset.univ


/-- The canonical full descriptor universe. -/
def fullDescriptorUniverse (N : Type u) (Sigma : Type v)
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N] [Fintype Sigma] [DecidableEq Sigma] :
    DescriptorUniverse N Sigma Obs :=
  {
    terminalUniverse := allTerminalRules N Obs
    nullaryUniverse := allNullaryRules N Obs
    binaryUniverse := allBinaryRules N Obs
  }


/-- A finite descriptor consists of a start typed nonterminal and finite
supports of terminal, nullary, and binary observed rules. -/
structure FiniteDescriptor (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N] [Fintype Sigma] [DecidableEq Sigma] where
  start : TypedNonterminal N Obs
  terminalRules : Finset (TerminalRule N Obs)
  nullaryRules : Finset (NullaryRule N Obs)
  binaryRules : Finset (BinaryRule N Obs)


/-- The total number of explicitly stored rules in a descriptor. -/
def FiniteDescriptor.ruleCount (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N] [Fintype Sigma] [DecidableEq Sigma]
    (D : FiniteDescriptor N Obs) : Nat :=
  D.terminalRules.card + D.nullaryRules.card + D.binaryRules.card


/-- The empty descriptor with a chosen start state. -/
def emptyDescriptor (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N] [Fintype Sigma] [DecidableEq Sigma]
    (s : TypedNonterminal N Obs) : FiniteDescriptor N Obs :=
  {
    start := s
    terminalRules := ∅
    nullaryRules := ∅
    binaryRules := ∅
  }


/-- The empty descriptor stores zero rules. -/
theorem emptyDescriptor_ruleCount_zero (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N] [Fintype Sigma] [DecidableEq Sigma]
    (s : TypedNonterminal N Obs) :
    (emptyDescriptor N Obs s).ruleCount N Obs = 0 := by
  unfold emptyDescriptor FiniteDescriptor.ruleCount
  simp


/-- Every terminal rule belongs to the full finite universe. -/
theorem terminalRule_mem_fullUniverse (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N] [Fintype Sigma] [DecidableEq Sigma]
    (r : TerminalRule N Obs) :
    r ∈ allTerminalRules N Obs := by
  unfold allTerminalRules
  simp


/-- Every nullary rule belongs to the full finite universe. -/
theorem nullaryRule_mem_fullUniverse (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N]
    (r : NullaryRule N Obs) :
    r ∈ allNullaryRules N Obs := by
  unfold allNullaryRules
  simp


/-- Every binary rule belongs to the full finite universe. -/
theorem binaryRule_mem_fullUniverse (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N]
    (r : BinaryRule N Obs) :
    r ∈ allBinaryRules N Obs := by
  unfold allBinaryRules
  simp


/-- Paper-facing statement: the descriptor rule universe is finite. -/
def descriptorUniverseFinite (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N] [Fintype Sigma] [DecidableEq Sigma] :
    DescriptorUniverse N Sigma Obs :=
  fullDescriptorUniverse N Sigma Obs


end JALC
end LeanCfgProject