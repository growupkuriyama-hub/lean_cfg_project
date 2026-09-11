import Mathlib

namespace LeanCfgProject
namespace SCLCompression

universe u v

/-- A length-`d` tuple, used for the tuple distributions in the SCL paper. -/
abbrev Tuple (α : Type u) (d : Nat) := Fin d → α

/-- Componentwise equality of finite observation types. -/
def SameType {α : Type u} {β : Type v} (h : α → β) {d : Nat}
    (x y : Tuple α d) : Prop :=
  ∀ i, h (x i) = h (y i)

/--
Abstract word-level unsafe pair: the two tuples share an accepting context but
have different complete tuple distributions.

The concrete SCL development will instantiate `Shared` and `EqualDist` with the
paper's tuple-context predicates.
-/
def Unsafe {α : Type u}
    (Shared EqualDist : (d : Nat) → Tuple α d → Tuple α d → Prop)
    (d : Nat) (x y : Tuple α d) : Prop :=
  Shared d x y ∧ ¬ EqualDist d x y

/--
The guarded word/context formulation of safety through arity `f`.
This abstracts condition (ii) of the paper's Safety Interface Theorem.
-/
def GuardedSafeThrough {α : Type u} {β : Type v}
    (Shared EqualDist : (d : Nat) → Tuple α d → Tuple α d → Prop)
    (h : α → β) (f : Nat) : Prop :=
  ∀ d, 1 ≤ d → d ≤ f → ∀ x y : Tuple α d,
    SameType h x y → Shared d x y → EqualDist d x y

/--
The semantic-clause formulation: every unsafe pair up to arity `f` is
separated in at least one coordinate.  This abstracts condition (iii) of the
Safety Interface Theorem.
-/
def SeparatesUnsafeThrough {α : Type u} {β : Type v}
    (Shared EqualDist : (d : Nat) → Tuple α d → Tuple α d → Prop)
    (h : α → β) (f : Nat) : Prop :=
  ∀ d, 1 ≤ d → d ≤ f → ∀ x y : Tuple α d,
    Unsafe Shared EqualDist d x y → ∃ i, h (x i) ≠ h (y i)

/-- Conditions (ii) and (iii) of the Safety Interface Theorem are equivalent. -/
theorem guardedSafe_iff_separatesUnsafe {α : Type u} {β : Type v}
    (Shared EqualDist : (d : Nat) → Tuple α d → Tuple α d → Prop)
    (h : α → β) (f : Nat) :
    GuardedSafeThrough Shared EqualDist h f ↔
      SeparatesUnsafeThrough Shared EqualDist h f := by
  classical
  constructor
  · intro hsafe d hdpos hdf x y hunsafe
    by_contra hnotsep
    have hsame : SameType h x y := by
      intro i
      by_contra hne
      exact hnotsep ⟨i, hne⟩
    exact hunsafe.2 (hsafe d hdpos hdf x y hsame hunsafe.1)
  · intro hsep d hdpos hdf x y hsame hshared
    by_contra hneq
    have hunsafe : Unsafe Shared EqualDist d x y := ⟨hshared, hneq⟩
    obtain ⟨i, hi⟩ := hsep d hdpos hdf x y hunsafe
    exact hi (hsame i)

/-- Kernel relation of an observation map. -/
def KernelRel {α : Type u} {β : Type v} (h : α → β) : α → α → Prop :=
  fun x y => h x = h y

/--
Relation-level separation of all unsafe clauses through arity `f`.  In the
paper, this is instantiated by a finite-index monoid congruence.
-/
def RelationSeparatesUnsafeThrough {α : Type u}
    (Shared EqualDist : (d : Nat) → Tuple α d → Tuple α d → Prop)
    (r : α → α → Prop) (f : Nat) : Prop :=
  ∀ d, 1 ≤ d → d ≤ f → ∀ x y : Tuple α d,
    Unsafe Shared EqualDist d x y → ∃ i, ¬ r (x i) (y i)

/-- Conditions (iii) and (iv) agree when the relation is the kernel of `h`. -/
theorem separatesUnsafe_iff_kernelRel {α : Type u} {β : Type v}
    (Shared EqualDist : (d : Nat) → Tuple α d → Tuple α d → Prop)
    (h : α → β) (f : Nat) :
    SeparatesUnsafeThrough Shared EqualDist h f ↔
      RelationSeparatesUnsafeThrough Shared EqualDist (KernelRel h) f := by
  rfl

/-- The abstract word/context, clause, and kernel interfaces coincide. -/
theorem safety_kernel_dictionary {α : Type u} {β : Type v}
    (Shared EqualDist : (d : Nat) → Tuple α d → Tuple α d → Prop)
    (h : α → β) (f : Nat) :
    GuardedSafeThrough Shared EqualDist h f ↔
      RelationSeparatesUnsafeThrough Shared EqualDist (KernelRel h) f := by
  rw [guardedSafe_iff_separatesUnsafe, separatesUnsafe_iff_kernelRel]

end SCLCompression
end LeanCfgProject
