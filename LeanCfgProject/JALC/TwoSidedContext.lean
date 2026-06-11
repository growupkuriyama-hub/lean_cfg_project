import LeanCfgProject.JALC.Basic

namespace LeanCfgProject
namespace JALC

universe u

/-
Observed two-sided contexts for the JALC algebra experiment.

At this stage we do not formalize raw string contexts. Instead, we
formalize the finite h-observed contexts: the left and right monoid
values surrounding a yield. This is the finite object used by the
paper's descriptor-level construction.
-/


/-- An h-observed two-sided context.

The pair `(left, right)` represents the h-values of the material on the
left and right of a generated yield.
-/
structure ObservedContext {Sigma : Type u}
    (Obs : FixedFiniteMonoidHom Sigma) where
  left : Obs.M
  right : Obs.M
deriving DecidableEq


/-- Equivalence between observed contexts and pairs of monoid values. -/
def observedContextEquiv {Sigma : Type u}
    (Obs : FixedFiniteMonoidHom Sigma) :
    ObservedContext Obs ≃ Obs.M × Obs.M where
  toFun := fun c => (c.left, c.right)
  invFun := fun p =>
    {
      left := p.1
      right := p.2
    }
  left_inv := by
    intro c
    cases c
    rfl
  right_inv := by
    intro p
    rcases p with ⟨l, r⟩
    rfl


/-- Observed contexts are finite because the observer monoid is finite. -/
noncomputable instance observedContextFintype {Sigma : Type u}
    (Obs : FixedFiniteMonoidHom Sigma) :
    Fintype (ObservedContext Obs) := by
  letI : Fintype Obs.M := Obs.instFintype
  exact Fintype.ofEquiv (Obs.M × Obs.M)
    (observedContextEquiv Obs).symm


/-- The empty observed context. -/
def emptyContext {Sigma : Type u}
    (Obs : FixedFiniteMonoidHom Sigma) : ObservedContext Obs :=
  {
    left := Obs.one
    right := Obs.one
  }


/-- Apply an observed two-sided context to a middle h-value. -/
def applyContext {Sigma : Type u}
    {Obs : FixedFiniteMonoidHom Sigma}
    (c : ObservedContext Obs) (m : Obs.M) : Obs.M :=
  Obs.mul c.left (Obs.mul m c.right)


/-- The empty observed context acts trivially. -/
theorem apply_emptyContext {Sigma : Type u}
    {Obs : FixedFiniteMonoidHom Sigma}
    (m : Obs.M) :
    applyContext (emptyContext Obs) m = m := by
  unfold applyContext emptyContext
  rw [Obs.mul_one, Obs.one_mul]


/-- Convert an observed context and a middle value into a two-sided type. -/
def contextType {Sigma : Type u}
    {Obs : FixedFiniteMonoidHom Sigma}
    (c : ObservedContext Obs) (m : Obs.M) : TwoSidedType Obs :=
  {
    left := c.left
    mid := m
    right := c.right
  }


/-- The total h-value observed through a two-sided type. -/
def totalValue {Sigma : Type u}
    {Obs : FixedFiniteMonoidHom Sigma}
    (t : TwoSidedType Obs) : Obs.M :=
  Obs.mul t.left (Obs.mul t.mid t.right)


/-- The total value of a context type is obtained by applying the context. -/
theorem totalValue_contextType {Sigma : Type u}
    {Obs : FixedFiniteMonoidHom Sigma}
    (c : ObservedContext Obs) (m : Obs.M) :
    totalValue (contextType c m) = applyContext c m := by
  rfl


/-- Compose an outer observed context with an inner observed context.

If the inner context sends `m` to `l * m * r`, and the outer context then
surrounds the result by `L` and `R`, the composed context is
`(L * l, r * R)`.
-/
def composeContext {Sigma : Type u}
    {Obs : FixedFiniteMonoidHom Sigma}
    (outer inner : ObservedContext Obs) : ObservedContext Obs :=
  {
    left := Obs.mul outer.left inner.left
    right := Obs.mul inner.right outer.right
  }


/-- Applying a composed context is the same as applying the inner context
and then the outer context. -/
theorem apply_composeContext {Sigma : Type u}
    {Obs : FixedFiniteMonoidHom Sigma}
    (outer inner : ObservedContext Obs) (m : Obs.M) :
    applyContext (composeContext outer inner) m =
      applyContext outer (applyContext inner m) := by
  unfold applyContext composeContext
  change
    Obs.mul (Obs.mul outer.left inner.left)
        (Obs.mul m (Obs.mul inner.right outer.right)) =
      Obs.mul outer.left
        (Obs.mul (Obs.mul inner.left (Obs.mul m inner.right)) outer.right)
  calc
    Obs.mul (Obs.mul outer.left inner.left)
        (Obs.mul m (Obs.mul inner.right outer.right))
        =
      Obs.mul outer.left
        (Obs.mul inner.left (Obs.mul m (Obs.mul inner.right outer.right))) := by
          rw [Obs.mul_assoc]
    _ =
      Obs.mul outer.left
        (Obs.mul inner.left (Obs.mul (Obs.mul m inner.right) outer.right)) := by
          rw [← Obs.mul_assoc m inner.right outer.right]
    _ =
      Obs.mul outer.left
        (Obs.mul (Obs.mul inner.left (Obs.mul m inner.right)) outer.right) := by
          rw [← Obs.mul_assoc inner.left (Obs.mul m inner.right) outer.right]


/-- The empty context is a left identity for context composition. -/
theorem empty_composeContext {Sigma : Type u}
    {Obs : FixedFiniteMonoidHom Sigma}
    (c : ObservedContext Obs) :
    composeContext (emptyContext Obs) c = c := by
  cases c with
  | mk l r =>
    unfold composeContext emptyContext
    apply ObservedContext.ext
    · exact Obs.one_mul l
    · exact Obs.mul_one r


/-- The empty context is a right identity for context composition. -/
theorem compose_emptyContext {Sigma : Type u}
    {Obs : FixedFiniteMonoidHom Sigma}
    (c : ObservedContext Obs) :
    composeContext c (emptyContext Obs) = c := by
  cases c with
  | mk l r =>
    unfold composeContext emptyContext
    apply ObservedContext.ext
    · exact Obs.mul_one l
    · exact Obs.one_mul r


/-- Paper-facing finite universe of observed contexts. -/
noncomputable def allObservedContexts {Sigma : Type u}
    (Obs : FixedFiniteMonoidHom Sigma) : Finset (ObservedContext Obs) := by
  letI : Fintype Obs.M := Obs.instFintype
  letI : Fintype (ObservedContext Obs) := observedContextFintype Obs
  exact Finset.univ

end JALC
end LeanCfgProject