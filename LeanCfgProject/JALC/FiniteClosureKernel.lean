import LeanCfgProject.JALC.PaperFacingFullFiniteMain

namespace LeanCfgProject
namespace JALC
namespace FiniteClosureKernel

/-
Finite closure certificates for monotone predicate transformers.

The module is deliberately abstract.  A closure computation is represented by
a finite iteration height together with a proof that the iteration is stable at
that height.  The checked consequence is that the resulting predicate is a
fixed point and is contained in every pre-fixed point.
-/

universe u

/-- Predicate inclusion. -/
def PredSubset {α : Type u} (P Q : α → Prop) : Prop :=
  ∀ x, P x → Q x


/-- Monotonicity for predicate transformers. -/
def PredMonotone {α : Type u}
    (F : (α → Prop) → α → Prop) : Prop :=
  ∀ {P Q : α → Prop}, PredSubset P Q → PredSubset (F P) (F Q)


/-- Pre-fixed predicate for a transformer. -/
def PredPreFixed {α : Type u}
    (F : (α → Prop) → α → Prop)
    (P : α → Prop) : Prop :=
  PredSubset (F P) P


/-- Fixed predicate for a transformer. -/
def PredFixed {α : Type u}
    (F : (α → Prop) → α → Prop)
    (P : α → Prop) : Prop :=
  ∀ x, F P x ↔ P x


/-- Iteration from the empty predicate. -/
def Iter {α : Type u}
    (F : (α → Prop) → α → Prop) : Nat → α → Prop
  | 0 => fun _ => False
  | n + 1 => F (Iter F n)


/-- Stability at a finite iteration height. -/
def StableAt {α : Type u}
    (F : (α → Prop) → α → Prop)
    (n : Nat) : Prop :=
  ∀ x, F (Iter F n) x ↔ Iter F n x


/--
Every finite iterate is contained in every pre-fixed predicate.
-/
theorem iter_subset_prefixed
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    {Q : α → Prop}
    (closed : PredPreFixed F Q) :
    ∀ n : Nat, PredSubset (Iter F n) Q := by
  intro n
  induction n with
  | zero =>
      intro x hx
      cases hx
  | succ n ih =>
      intro x hx
      exact closed x (mono ih x hx)


/-- A stable iterate is a fixed point. -/
theorem stable_iter_fixed
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    {n : Nat}
    (stable : StableAt F n) :
    PredFixed F (Iter F n) := by
  intro x
  exact stable x


/-- A stable iterate is contained in every pre-fixed predicate. -/
theorem stable_iter_least_prefixed
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    {n : Nat}
    (_stable : StableAt F n)
    {Q : α → Prop}
    (closed : PredPreFixed F Q) :
    PredSubset (Iter F n) Q :=
  iter_subset_prefixed mono closed n


/-- Finite certificate that an iteration has stabilized. -/
structure ClosureCertificate {α : Type u}
    (F : (α → Prop) → α → Prop) : Type u where
  height : Nat
  stable : StableAt F height


/-- Predicate computed by a closure certificate. -/
def certifiedClosure {α : Type u}
    {F : (α → Prop) → α → Prop}
    (c : ClosureCertificate F) : α → Prop :=
  Iter F c.height


/-- A certified closure is a fixed point. -/
theorem certifiedClosure_fixed
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (c : ClosureCertificate F) :
    PredFixed F (certifiedClosure c) :=
  stable_iter_fixed c.stable


/-- A certified closure is contained in every pre-fixed predicate. -/
theorem certifiedClosure_least_prefixed
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (mono : PredMonotone F)
    (c : ClosureCertificate F)
    {Q : α → Prop}
    (closed : PredPreFixed F Q) :
    PredSubset (certifiedClosure c) Q :=
  stable_iter_least_prefixed mono c.stable closed


/--
A compact package for a certified monotone closure.
-/
structure CertifiedMonotoneClosure {α : Type u}
    (F : (α → Prop) → α → Prop) : Type u where
  monotone : PredMonotone F
  certificate : ClosureCertificate F


/-- The result predicate of a certified monotone closure. -/
def CertifiedMonotoneClosure.result
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (C : CertifiedMonotoneClosure F) : α → Prop :=
  certifiedClosure C.certificate


/-- The result of a certified monotone closure is fixed. -/
theorem CertifiedMonotoneClosure.result_fixed
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (C : CertifiedMonotoneClosure F) :
    PredFixed F C.result :=
  certifiedClosure_fixed C.certificate


/-- The result of a certified monotone closure is least among pre-fixed predicates. -/
theorem CertifiedMonotoneClosure.result_least_prefixed
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (C : CertifiedMonotoneClosure F)
    {Q : α → Prop}
    (closed : PredPreFixed F Q) :
    PredSubset C.result Q :=
  certifiedClosure_least_prefixed C.monotone C.certificate closed

end FiniteClosureKernel
end JALC
end LeanCfgProject
