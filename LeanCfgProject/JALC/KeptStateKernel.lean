import LeanCfgProject.JALC.StartLanguageKernel

namespace LeanCfgProject
namespace JALC
namespace KeptStateKernel

/-
Kernel for passing from intended copies to the states kept by a typed
construction.

The main remaining mathematical burden in the paper is to prove that the
reachable productive typed states are exactly the intended copies.  This file
checks the consequence of that statement: once kept states coincide with
intended copies, the intended-copy map gives an equivalence from original
states to kept typed states.
-/

universe u v

open InverseKernel


/-- The subtype of typed states kept by a typed construction. -/
abbrev KeptSubtype {V : Type u} {M : Type v}
    (Kept : TypedState V M → Prop) :=
  { s : TypedState V M // Kept s }


/-- Send an original state to its kept intended copy. -/
def intendedCopyToKept {V : Type u} {M : Type v}
    (T : StateTyping V M)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (X : V) : KeptSubtype Kept :=
  ⟨intendedCopy T X, hKept X⟩


/-- Read the original label from a kept typed state. -/
def keptLabel {V : Type u} {M : Type v}
    (T : StateTyping V M)
    (Kept : TypedState V M → Prop)
    (s : KeptSubtype Kept) : V :=
  s.val.label


/-- The kept intended copy of `X` has label `X`. -/
theorem intendedCopyToKept_left_inverse {V : Type u} {M : Type v}
    (T : StateTyping V M)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (X : V) :
    keptLabel T Kept (intendedCopyToKept T Kept hKept X) = X := by
  rfl


/--
If every kept typed state is an intended copy, then every kept typed state is
recovered from its label.
-/
theorem intendedCopyToKept_right_inverse {V : Type u} {M : Type v}
    (T : StateTyping V M)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (hAll : ∀ s : TypedState V M, Kept s → IsIntended T s)
    (s : KeptSubtype Kept) :
    intendedCopyToKept T Kept hKept (keptLabel T Kept s) = s := by
  rcases hAll s.val s.property with ⟨X, hX⟩
  apply Subtype.ext
  unfold intendedCopyToKept keptLabel
  change intendedCopy T s.val.label = s.val
  have hlabel : X = s.val.label := by
    have h := congrArg (fun t : TypedState V M => t.label) hX
    simpa [intendedCopy] using h
  rw [← hlabel]
  exact hX


/--
Equivalence between original states and kept typed states, under the statement
that kept typed states are exactly the intended copies.
-/
def keptCopyEquiv {V : Type u} {M : Type v}
    (T : StateTyping V M)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (hAll : ∀ s : TypedState V M, Kept s → IsIntended T s) :
    V ≃ KeptSubtype Kept where
  toFun := intendedCopyToKept T Kept hKept
  invFun := keptLabel T Kept
  left_inv := intendedCopyToKept_left_inverse T Kept hKept
  right_inv := intendedCopyToKept_right_inverse T Kept hKept hAll


/-- Paper-facing kept-state equivalence kernel. -/
theorem kept_state_equivalence_kernel {V : Type u} {M : Type v}
    (T : StateTyping V M)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (hAll : ∀ s : TypedState V M, Kept s → IsIntended T s) :
    Nonempty (V ≃ KeptSubtype Kept) := by
  exact ⟨keptCopyEquiv T Kept hKept hAll⟩

end KeptStateKernel
end JALC
end LeanCfgProject
