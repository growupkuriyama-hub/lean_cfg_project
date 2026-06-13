import LeanCfgProject.JALC.PaperFacing

namespace LeanCfgProject
namespace JALC
namespace InverseKernel

/-
Kernel for the state-copy map used in the inverse representation argument.

This file does not attempt to formalize the full characterization theorem.
It checks the structural core needed later: every original state has a unique
intended typed copy, and the intended-copy map is injective.
-/

universe u v w


/-- A typed copy of an original state. -/
structure TypedState (V : Type u) (M : Type v) where
  label : V
  yt : M
  lt : M
  rt : M


/-- Type data assigned to original states. -/
structure StateTyping (V : Type u) (M : Type v) where
  yt : V → M
  lt : V → M
  rt : V → M


/-- The intended typed copy of an original state. -/
def intendedCopy {V : Type u} {M : Type v}
    (T : StateTyping V M) (X : V) : TypedState V M :=
  { label := X, yt := T.yt X, lt := T.lt X, rt := T.rt X }


/-- The intended copy remembers its original label. -/
theorem intendedCopy_label {V : Type u} {M : Type v}
    (T : StateTyping V M) (X : V) :
    (intendedCopy T X).label = X := by
  rfl


/-- The intended-copy map is injective. -/
theorem intendedCopy_injective {V : Type u} {M : Type v}
    (T : StateTyping V M) :
    Function.Injective (intendedCopy T) := by
  intro X Y h
  have hlabel := congrArg (fun s : TypedState V M => s.label) h
  simpa [intendedCopy] using hlabel


/-- Predicate saying that a typed state is an intended copy. -/
def IsIntended {V : Type u} {M : Type v}
    (T : StateTyping V M) (s : TypedState V M) : Prop :=
  ∃ X : V, intendedCopy T X = s


/-- Every original state gives an intended typed state. -/
theorem intendedCopy_isIntended {V : Type u} {M : Type v}
    (T : StateTyping V M) (X : V) :
    IsIntended T (intendedCopy T X) := by
  exact ⟨X, rfl⟩


/-- Intended representatives are unique. -/
theorem intendedCopy_unique_label {V : Type u} {M : Type v}
    (T : StateTyping V M) {X Y : V}
    (h : intendedCopy T X = intendedCopy T Y) :
    X = Y := by
  exact intendedCopy_injective T h


/-- Terminal rules over original states. -/
structure TerminalRule (V : Type u) (Sigma : Type w) where
  lhs : V
  terminal : Sigma


/-- Binary rules over original states. -/
structure BinaryRule (V : Type u) where
  parent : V
  left : V
  right : V


/-- Start-state declarations over original states. -/
structure StartRule (V : Type u) where
  state : V


/-- Terminal rules over intended typed copies. -/
structure TypedTerminalRule (V : Type u) (M : Type v) (Sigma : Type w) where
  lhs : TypedState V M
  terminal : Sigma


/-- Binary rules over intended typed copies. -/
structure TypedBinaryRule (V : Type u) (M : Type v) where
  parent : TypedState V M
  left : TypedState V M
  right : TypedState V M


/-- Start declarations over intended typed copies. -/
structure TypedStartRule (V : Type u) (M : Type v) where
  state : TypedState V M


/-- Lift a terminal rule to intended typed copies. -/
def liftTerminal {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (r : TerminalRule V Sigma) :
    TypedTerminalRule V M Sigma :=
  { lhs := intendedCopy T r.lhs, terminal := r.terminal }


/-- Lift a binary rule to intended typed copies. -/
def liftBinary {V : Type u} {M : Type v}
    (T : StateTyping V M) (r : BinaryRule V) :
    TypedBinaryRule V M :=
  { parent := intendedCopy T r.parent,
    left := intendedCopy T r.left,
    right := intendedCopy T r.right }


/-- Lift a start declaration to intended typed copies. -/
def liftStart {V : Type u} {M : Type v}
    (T : StateTyping V M) (s : StartRule V) :
    TypedStartRule V M :=
  { state := intendedCopy T s.state }


/-- Terminal-rule lifting is injective. -/
theorem liftTerminal_injective {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) :
    Function.Injective (liftTerminal T : TerminalRule V Sigma → TypedTerminalRule V M Sigma) := by
  intro r s h
  have hlhs : r.lhs = s.lhs := by
    have hlabel :=
      congrArg (fun tr : TypedTerminalRule V M Sigma => tr.lhs.label) h
    simpa [liftTerminal, intendedCopy] using hlabel
  have hterminal : r.terminal = s.terminal := by
    have hterm :=
      congrArg (fun tr : TypedTerminalRule V M Sigma => tr.terminal) h
    simpa [liftTerminal] using hterm
  cases r
  cases s
  simp_all


/-- Binary-rule lifting is injective. -/
theorem liftBinary_injective {V : Type u} {M : Type v}
    (T : StateTyping V M) :
    Function.Injective (liftBinary T : BinaryRule V → TypedBinaryRule V M) := by
  intro r s h
  have hparent : r.parent = s.parent := by
    have hlabel :=
      congrArg (fun br : TypedBinaryRule V M => br.parent.label) h
    simpa [liftBinary, intendedCopy] using hlabel
  have hleft : r.left = s.left := by
    have hlabel :=
      congrArg (fun br : TypedBinaryRule V M => br.left.label) h
    simpa [liftBinary, intendedCopy] using hlabel
  have hright : r.right = s.right := by
    have hlabel :=
      congrArg (fun br : TypedBinaryRule V M => br.right.label) h
    simpa [liftBinary, intendedCopy] using hlabel
  cases r
  cases s
  simp_all


/-- Start-rule lifting is injective. -/
theorem liftStart_injective {V : Type u} {M : Type v}
    (T : StateTyping V M) :
    Function.Injective (liftStart T : StartRule V → TypedStartRule V M) := by
  intro r s h
  have hstate : r.state = s.state := by
    have hlabel :=
      congrArg (fun sr : TypedStartRule V M => sr.state.label) h
    simpa [liftStart, intendedCopy] using hlabel
  cases r
  cases s
  simp_all

end InverseKernel
end JALC
end LeanCfgProject
