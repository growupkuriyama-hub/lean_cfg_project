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
deriving DecidableEq


/-- Equivalence between terminal rules and a finite product carrier. -/
def terminalRuleEquiv (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) :
    TerminalRule N Obs ≃
      TypedNonterminal N Obs × Sigma × ObservedContext Obs where
  toFun := fun r => (r.lhs, r.terminal, r.ctx)
  invFun := fun p =>
    {
      lhs := p.1
      terminal := p.2.1
      ctx := p.2.2
    }
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro p
    rcases p with ⟨lhs, terminal, ctx⟩
    rfl


/-- Terminal rules form a finite type when nonterminals and terminals are finite. -/
noncomputable instance terminalRuleFintype (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) [Fintype N] [Fintype Sigma] :
    Fintype (TerminalRule N Obs) := by
  letI : Fintype (TypedNonterminal N Obs) := typedNonterminalFintype N Obs
  letI : Fintype (ObservedContext Obs) := observedContextFintype Obs
  exact Fintype.ofEquiv
    (TypedNonterminal N Obs × Sigma × ObservedContext Obs)
    (terminalRuleEquiv N Obs).symm


/-- A nullary production, used for epsilon-like or zero-yield components.

This is deliberately lightweight: the paper-facing descriptor only needs
a finite support of such zero-ary observations.
-/
structure NullaryRule (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) where
  lhs : TypedNonterminal N Obs
  ctx : ObservedContext Obs
deriving DecidableEq


/-- Equivalence between nullary rules and a finite product carrier. -/
def nullaryRuleEquiv (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) :
    NullaryRule N Obs ≃
      TypedNonterminal N Obs × ObservedContext Obs where
  toFun := fun r => (r.lhs, r.ctx)
  invFun := fun p =>
    {
      lhs := p.1
      ctx := p.2
    }
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro p
    rcases p with ⟨lhs, ctx⟩
    rfl


/-- Nullary rules form a finite type when nonterminals are finite. -/
noncomputable instance nullaryRuleFintype (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) [Fintype N] :
    Fintype (NullaryRule N Obs) := by
  letI : Fintype (TypedNonterminal N Obs) := typedNonterminalFintype N Obs
  letI : Fintype (ObservedContext Obs) := observedContextFintype Obs
  exact Fintype.ofEquiv
    (TypedNonterminal N Obs × ObservedContext Obs)
    (nullaryRuleEquiv N Obs).symm


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
deriving DecidableEq


/-- Equivalence between binary rules and a finite product carrier. -/
def binaryRuleEquiv (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) :
    BinaryRule N Obs ≃
      TypedNonterminal N Obs ×
        TypedNonterminal N Obs ×
          TypedNonterminal N Obs ×
            ObservedContext Obs where
  toFun := fun r => (r.parent, r.leftChild, r.rightChild, r.ctx)
  invFun := fun p =>
    {
      parent := p.1
      leftChild := p.2.1
      rightChild := p.2.2.1
      ctx := p.2.2.2
    }
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro p
    rcases p with ⟨parent, leftChild, rightChild, ctx⟩
    rfl


/-- Binary rules form a finite type when nonterminals are finite. -/
noncomputable instance binaryRuleFintype (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) [Fintype N] :
    Fintype (BinaryRule N Obs) := by
  letI : Fintype (TypedNonterminal N Obs) := typedNonterminalFintype N Obs
  letI : Fintype (ObservedContext Obs) := observedContextFintype Obs
  exact Fintype.ofEquiv
    (TypedNonterminal N Obs ×
      TypedNonterminal N Obs ×
        TypedNonterminal N Obs ×
          ObservedContext Obs)
    (binaryRuleEquiv N Obs).symm


/-- The finite rule universe associated with a fixed finite observer and
finite nonterminal/alphabet sets. -/
structure DescriptorUniverse (N : Type u) (Sigma : Type v)
    (Obs : FixedFiniteMonoidHom Sigma) where
  terminalUniverse : Finset (TerminalRule N Obs)
  nullaryUniverse : Finset (NullaryRule N Obs)
  binaryUniverse : Finset (BinaryRule N Obs)


/-- The canonical full finite universe of terminal rules. -/
noncomputable def allTerminalRules (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) [Fintype N] [Fintype Sigma] :
    Finset (TerminalRule N Obs) := by
  letI : Fintype (TerminalRule N Obs) := terminalRuleFintype N Obs
  exact Finset.univ


/-- The canonical full finite universe of nullary rules. -/
noncomputable def allNullaryRules (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) [Fintype N] :
    Finset (NullaryRule N Obs) := by
  letI : Fintype (NullaryRule N Obs) := nullaryRuleFintype N Obs
  exact Finset.univ


/-- The canonical full finite universe of binary rules. -/
noncomputable def allBinaryRules (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) [Fintype N] :
    Finset (BinaryRule N Obs) := by
  letI : Fintype (BinaryRule N Obs) := binaryRuleFintype N Obs
  exact Finset.univ


/-- The canonical full descriptor universe. -/
noncomputable def fullDescriptorUniverse (N : Type u) (Sigma : Type v)
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [Fintype Sigma] :
    DescriptorUniverse N Sigma Obs :=
  {
    terminalUniverse := allTerminalRules N Obs
    nullaryUniverse := allNullaryRules N Obs
    binaryUniverse := allBinaryRules N Obs
  }


/-- A finite descriptor consists of a start typed nonterminal and finite
supports of terminal, nullary, and binary observed rules. -/
structure FiniteDescriptor (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) where
  start : TypedNonterminal N Obs
  terminalRules : Finset (TerminalRule N Obs)
  nullaryRules : Finset (NullaryRule N Obs)
  binaryRules : Finset (BinaryRule N Obs)


/-- The total number of explicitly stored rules in a descriptor. -/
def FiniteDescriptor.ruleCount {N : Type u} {Sigma : Type v}
    {Obs : FixedFiniteMonoidHom Sigma}
    (D : FiniteDescriptor N Obs) : Nat :=
  D.terminalRules.card + D.nullaryRules.card + D.binaryRules.card


/-- The empty descriptor with a chosen start state. -/
def emptyDescriptor (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
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
    (s : TypedNonterminal N Obs) :
    (emptyDescriptor N Obs s).ruleCount = 0 := by
  unfold emptyDescriptor FiniteDescriptor.ruleCount
  simp


/-- Paper-facing statement: the descriptor rule universe is finite. -/
noncomputable def descriptorUniverseFinite (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [Fintype Sigma] :
    DescriptorUniverse N Sigma Obs :=
  fullDescriptorUniverse N Sigma Obs

end JALC
end LeanCfgProject