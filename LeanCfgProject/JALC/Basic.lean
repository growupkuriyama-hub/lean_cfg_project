import Std

namespace LeanCfgProject
namespace JALC

universe u v

/-
Basic finite-observer infrastructure for the JALC algebra experiment.

This file sets up the finite monoid observer and the two-sided typed
state space used by the paper.
-/


/-- A fixed finite monoid observer on words over `Sigma`.

The monoid structure is kept explicit so that the development remains
lightweight and paper-facing.
-/
structure FixedFiniteMonoidHom (Sigma : Type u) where
  M : Type v
  instFintype : Fintype M
  instDecEq : DecidableEq M
  one : M
  mul : M → M → M
  h : List Sigma → M
  mul_assoc : ∀ a b c : M, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : M, mul one a = a
  mul_one : ∀ a : M, mul a one = a

attribute [instance] FixedFiniteMonoidHom.instFintype
attribute [instance] FixedFiniteMonoidHom.instDecEq


/-- The value of a word under the fixed observer. -/
def obsValue {Sigma : Type u} (Obs : FixedFiniteMonoidHom Sigma)
    (w : List Sigma) : Obs.M :=
  Obs.h w


/-- A two-sided type: left boundary, middle yield value, and right boundary. -/
structure TwoSidedType {Sigma : Type u} (Obs : FixedFiniteMonoidHom Sigma) where
  left : Obs.M
  mid : Obs.M
  right : Obs.M
deriving DecidableEq, Fintype


/-- A typed nonterminal: a nonterminal together with its two-sided type. -/
structure TypedNonterminal (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) where
  nt : N
  ty : TwoSidedType Obs
deriving DecidableEq, Fintype


/-- The untyped boundary pair surrounding a generated yield. -/
structure BoundaryPair {Sigma : Type u} (Obs : FixedFiniteMonoidHom Sigma) where
  left : Obs.M
  right : Obs.M
deriving DecidableEq, Fintype


/-- Convert a two-sided type to its external boundary pair. -/
def TwoSidedType.boundary {Sigma : Type u}
    {Obs : FixedFiniteMonoidHom Sigma}
    (t : TwoSidedType Obs) : BoundaryPair Obs :=
  { left := t.left, right := t.right }


/-- Transport the middle component by multiplying on the left and right.

This is the basic algebraic operation behind the frame-transport equations
used later in the paper.
-/
def transportMid {Sigma : Type u}
    {Obs : FixedFiniteMonoidHom Sigma}
    (l r : Obs.M) (m : Obs.M) : Obs.M :=
  Obs.mul l (Obs.mul m r)


/-- Transport a two-sided type by changing the external boundary. -/
def transportType {Sigma : Type u}
    {Obs : FixedFiniteMonoidHom Sigma}
    (l r : Obs.M) (t : TwoSidedType Obs) : TwoSidedType Obs :=
  {
    left := l
    mid := transportMid l r t.mid
    right := r
  }


/-- The middle component is unchanged under transport by the two units. -/
theorem transportMid_one_one {Sigma : Type u}
    {Obs : FixedFiniteMonoidHom Sigma}
    (m : Obs.M) :
    transportMid Obs.one Obs.one m = m := by
  unfold transportMid
  rw [Obs.one_mul, Obs.one_mul]


/-- Transporting a type by unit boundaries preserves its middle component. -/
theorem transportType_one_one_mid {Sigma : Type u}
    {Obs : FixedFiniteMonoidHom Sigma}
    (t : TwoSidedType Obs) :
    (transportType Obs.one Obs.one t).mid = t.mid := by
  unfold transportType
  exact transportMid_one_one t.mid


/-- The finite universe of all two-sided types. -/
def allTwoSidedTypes {Sigma : Type u}
    (Obs : FixedFiniteMonoidHom Sigma) : Finset (TwoSidedType Obs) :=
  Finset.univ


/-- The finite universe of typed nonterminals. -/
def allTypedNonterminals (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) [Fintype N] [DecidableEq N] :
    Finset (TypedNonterminal N Obs) :=
  Finset.univ


end JALC
end LeanCfgProject