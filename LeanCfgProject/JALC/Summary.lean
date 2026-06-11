import LeanCfgProject.JALC.Basic
import LeanCfgProject.JALC.TwoSidedContext
import LeanCfgProject.JALC.Descriptor
import LeanCfgProject.JALC.ResidualConcept

namespace LeanCfgProject
namespace JALC

universe u v

/-
Paper-facing summary module for the JALC algebra experiment.

The intended CI target is:

  lake build LeanCfgProject.JALC.Summary

This module imports the checked Lean files corresponding to the finite
typed architecture used in the JALC paper.
-/


/-- Summary item 1: the finite monoid observer interface is available. -/
def SummaryObserverInterface (Sigma : Type u) :=
  FixedFiniteMonoidHom Sigma


/-- Summary item 2: two-sided h-types are available. -/
def SummaryTwoSidedType {Sigma : Type u}
    (Obs : FixedFiniteMonoidHom Sigma) :=
  TwoSidedType Obs


/-- Summary item 3: observed two-sided contexts are available. -/
def SummaryObservedContext {Sigma : Type u}
    (Obs : FixedFiniteMonoidHom Sigma) :=
  ObservedContext Obs


/-- Summary item 4: typed nonterminals are available. -/
def SummaryTypedNonterminal (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) :=
  TypedNonterminal N Obs


/-- Summary item 5: finite descriptors are available. -/
def SummaryFiniteDescriptor (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N] [Fintype Sigma] [DecidableEq Sigma] :=
  FiniteDescriptor N Obs


/-- Summary item 6: residual concepts are available. -/
def SummaryResidualConcept (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N]
    (R : Incidence N Obs) [DecidableRel R] :=
  ResidualConcept N Obs R


/-- The paper-facing finite typed-state universe. -/
def SummaryTypedStateUniverse (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N] :
    Finset (TypedState N Obs) :=
  allTypedStates N Obs


/-- The paper-facing finite observed-context universe. -/
def SummaryContextUniverse {Sigma : Type u}
    (Obs : FixedFiniteMonoidHom Sigma) :
    Finset (ContextState Obs) :=
  allContextStates Obs


/-- The paper-facing full descriptor universe. -/
def SummaryDescriptorUniverse (N : Type u) (Sigma : Type v)
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N] [Fintype Sigma] [DecidableEq Sigma] :
    DescriptorUniverse N Sigma Obs :=
  fullDescriptorUniverse N Sigma Obs


/--
A compact paper-facing statement:

For finite nonterminals and a finite alphabet, the descriptor universe
used by the JALC construction is a finite Lean object.
-/
def checked_finite_descriptor_universe (N : Type u) (Sigma : Type v)
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N] [Fintype Sigma] [DecidableEq Sigma] :
    DescriptorUniverse N Sigma Obs :=
  fullDescriptorUniverse N Sigma Obs


/--
A compact paper-facing statement:

The residual/concept layer is represented by finite extents and finite
intents over typed states and observed contexts.
-/
def checked_residual_concept_layer (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N]
    (R : Incidence N Obs) [DecidableRel R] :=
  ResidualConcept N Obs R


end JALC
end LeanCfgProject