import LeanCfgProject.JALC.RoundTripKernel

namespace LeanCfgProject
namespace JALC
namespace IntendedCopyEquiv

/-
Bijection kernel for intended typed copies.

This module shows that the intended-copy map is an equivalence between the
original state type and the subtype of typed states that are intended copies.
-/

universe u v

open InverseKernel


/-- The subtype of typed states that are intended copies. -/
abbrev IntendedSubtype {V : Type u} {M : Type v}
    (T : StateTyping V M) :=
  { s : TypedState V M // IsIntended T s }


/-- Send an original state to its intended typed copy as a subtype element. -/
def intendedCopyToSubtype {V : Type u} {M : Type v}
    (T : StateTyping V M) (X : V) : IntendedSubtype T :=
  ⟨intendedCopy T X, intendedCopy_isIntended T X⟩


/-- Read the original label from an intended typed copy. -/
def intendedSubtypeLabel {V : Type u} {M : Type v}
    (T : StateTyping V M) (s : IntendedSubtype T) : V :=
  s.val.label


/-- The label read from the intended copy of `X` is `X`. -/
theorem intendedCopyToSubtype_left_inverse {V : Type u} {M : Type v}
    (T : StateTyping V M) (X : V) :
    intendedSubtypeLabel T (intendedCopyToSubtype T X) = X := by
  rfl


/-- Every intended subtype element is recovered from its label. -/
theorem intendedCopyToSubtype_right_inverse {V : Type u} {M : Type v}
    (T : StateTyping V M) (s : IntendedSubtype T) :
    intendedCopyToSubtype T (intendedSubtypeLabel T s) = s := by
  rcases s.property with ⟨X, hX⟩
  apply Subtype.ext
  change intendedCopy T s.val.label = s.val
  have hlabel : X = s.val.label := by
    have h := congrArg (fun t : TypedState V M => t.label) hX
    simpa [intendedCopy] using h
  rw [← hlabel]
  exact hX


/-- Equivalence between original states and intended typed copies. -/
def intendedCopyEquiv {V : Type u} {M : Type v}
    (T : StateTyping V M) : V ≃ IntendedSubtype T where
  toFun := intendedCopyToSubtype T
  invFun := intendedSubtypeLabel T
  left_inv := intendedCopyToSubtype_left_inverse T
  right_inv := intendedCopyToSubtype_right_inverse T


/-- The equivalence sends `X` to its intended typed copy. -/
theorem intendedCopyEquiv_apply {V : Type u} {M : Type v}
    (T : StateTyping V M) (X : V) :
    intendedCopyEquiv T X = intendedCopyToSubtype T X := by
  rfl


/-- The value of the equivalence is the intended typed copy. -/
theorem intendedCopyEquiv_apply_val {V : Type u} {M : Type v}
    (T : StateTyping V M) (X : V) :
    (intendedCopyEquiv T X).val = intendedCopy T X := by
  rfl


/-- The inverse of the equivalence reads the label. -/
theorem intendedCopyEquiv_symm_apply {V : Type u} {M : Type v}
    (T : StateTyping V M) (s : IntendedSubtype T) :
    (intendedCopyEquiv T).symm s = intendedSubtypeLabel T s := by
  rfl


/--
Paper-facing bijection kernel.

The original state type is equivalent to the subtype of intended typed copies.
-/
theorem intended_copy_bijection_kernel {V : Type u} {M : Type v}
    (T : StateTyping V M) :
    Nonempty (V ≃ IntendedSubtype T) := by
  exact ⟨intendedCopyEquiv T⟩

end IntendedCopyEquiv
end JALC
end LeanCfgProject
