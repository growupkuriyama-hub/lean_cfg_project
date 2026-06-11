import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

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
deriving DecidableEq


/-- Equivalence between two-sided types and triples of monoid values. -/
def twoSidedTypeEquiv {Sigma : Type u}
    (Obs : FixedFiniteMonoidHom Sigma) :
    TwoSidedType Obs ≃ Obs.M × Obs.M × Obs.M where
  toFun := fun t => (t.left, t.mid, t.right)
  invFun := fun p =>
    {
      left := p.1
      mid := p.2.1
      right := p.2.2
    }
  left_inv := by
    intro t
    cases t
    rfl
  right_inv := by
    intro p
    rcases p with ⟨l, m, r⟩
    rfl


/-- The two-sided type space is finite because the observer monoid is finite. -/
noncomputable instance twoSidedTypeFintype {Sigma : Type u}
    (Obs : FixedFiniteMonoidHom Sigma) :
    Fintype (TwoSidedType Obs) :=
  Fintype.ofEquiv (Obs.M × Obs.M × Obs.M) (twoSidedTypeEquiv Obs).symm


/-- A typed nonterminal: a nonterminal together with its two-sided type. -/
structure TypedNonterminal (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) where
  nt : N
  ty : TwoSidedType Obs
deriving DecidableEq


/-- Equivalence between typed nonterminals and pairs of a nonterminal and a type. -/
def typedNonterminalEquiv (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) :
    TypedNonterminal N Obs ≃ N × TwoSidedType Obs where
  toFun := fun q => (q.nt, q.ty)
  invFun := fun p =>
    {
      nt := p.1
      ty := p.2
    }
  left_inv := by
    intro q
    cases q
    rfl
  right_inv := by
    intro p
    rcases p with ⟨nt, ty⟩
    rfl


/-- Typed nonterminals are finite when the nonterminal set is finite. -/
noncomputable instance typedNonterminalFintype (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) [Fintype N] :
    Fintype (TypedNonterminal N Obs) :=
  Fintype.ofEquiv (N × TwoSidedType Obs)
    (typedNonterminalEquiv N Obs).symm


/-- The untyped boundary pair surrounding a generated yield. -/
structure BoundaryPair {Sigma : Type u} (Obs : FixedFiniteMonoidHom Sigma) where
  left : Obs.M
  right : Obs.M
deriving DecidableEq


/-- Equivalence between boundary pairs and pairs of monoid values. -/
def boundaryPairEquiv {Sigma : Type u}
    (Obs : FixedFiniteMonoidHom Sigma) :
    BoundaryPair Obs ≃ Obs.M × Obs.M where
  toFun := fun b => (b.left, b.right)
  invFun := fun p =>
    {
      left := p.1
      right := p.2
    }
  left_inv := by
    intro b
    cases b
    rfl
  right_inv := by
    intro p
    rcases p with ⟨l, r⟩
    rfl


/-- Boundary pairs are finite because the observer monoid is finite. -/
noncomputable instance boundaryPairFintype {Sigma : Type u}
    (Obs : FixedFiniteMonoidHom Sigma) :
    Fintype (BoundaryPair Obs) :=
  Fintype.ofEquiv (Obs.M × Obs.M) (boundaryPairEquiv Obs).symm


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
  rw [Obs.mul_one, Obs.one_mul]


/-- Transporting a type by unit boundaries preserves its middle component. -/
theorem transportType_one_one_mid {Sigma : Type u}
    {Obs : FixedFiniteMonoidHom Sigma}
    (t : TwoSidedType Obs) :
    (transportType Obs.one Obs.one t).mid = t.mid := by
  unfold transportType
  exact transportMid_one_one t.mid


/-- The finite universe of all two-sided types. -/
noncomputable def allTwoSidedTypes {Sigma : Type u}
    (Obs : FixedFiniteMonoidHom Sigma) : Finset (TwoSidedType Obs) :=
  Finset.univ


/-- The finite universe of typed nonterminals. -/
noncomputable def allTypedNonterminals (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) [Fintype N] [DecidableEq N] :
    Finset (TypedNonterminal N Obs) :=
  Finset.univ

end JALC
end LeanCfgProject