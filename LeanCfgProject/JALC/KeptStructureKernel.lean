import LeanCfgProject.JALC.PaperFacingAdvanced

namespace LeanCfgProject
namespace JALC
namespace KeptStructureKernel

/-
Rule structures restricted to kept typed states.

This module moves from the full lifted typed structure to the substructure
whose states are kept by a typed construction.  Under the condition that every
intended copy is kept, original rules lift to rules over kept states.
-/

universe u v w

open InverseKernel RoundTripKernel KeptStateKernel


/-- Terminal rule over kept typed states. -/
structure KeptTerminalRule {V : Type u} {M : Type v}
    (Kept : TypedState V M → Prop) (Sigma : Type w) where
  lhs : KeptSubtype Kept
  terminal : Sigma


/-- Binary rule over kept typed states. -/
structure KeptBinaryRule {V : Type u} {M : Type v}
    (Kept : TypedState V M → Prop) where
  parent : KeptSubtype Kept
  left : KeptSubtype Kept
  right : KeptSubtype Kept


/-- Start declaration over kept typed states. -/
structure KeptStartRule {V : Type u} {M : Type v}
    (Kept : TypedState V M → Prop) where
  state : KeptSubtype Kept


/-- A rule structure over kept typed states. -/
structure KeptStructure {V : Type u} {M : Type v}
    (Kept : TypedState V M → Prop) (Sigma : Type w) where
  terminal : KeptTerminalRule Kept Sigma → Prop
  binary : KeptBinaryRule Kept → Prop
  start : KeptStartRule Kept → Prop


/-- Lift a terminal rule to kept intended copies. -/
def liftTerminalKept {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (r : TerminalRule V Sigma) :
    KeptTerminalRule Kept Sigma :=
  { lhs := intendedCopyToKept T Kept hKept r.lhs,
    terminal := r.terminal }


/-- Lift a binary rule to kept intended copies. -/
def liftBinaryKept {V : Type u} {M : Type v}
    (T : StateTyping V M)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (r : BinaryRule V) :
    KeptBinaryRule Kept :=
  { parent := intendedCopyToKept T Kept hKept r.parent,
    left := intendedCopyToKept T Kept hKept r.left,
    right := intendedCopyToKept T Kept hKept r.right }


/-- Lift a start declaration to a kept intended copy. -/
def liftStartKept {V : Type u} {M : Type v}
    (T : StateTyping V M)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (r : StartRule V) :
    KeptStartRule Kept :=
  { state := intendedCopyToKept T Kept hKept r.state }


/-- Lift an original rule structure to kept intended copies. -/
def liftToKeptStructure {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X)) :
    KeptStructure Kept Sigma :=
  { terminal := fun tr =>
      ∃ r : TerminalRule V Sigma,
        G.terminal r ∧ liftTerminalKept T Kept hKept r = tr,
    binary := fun br =>
      ∃ r : BinaryRule V,
        G.binary r ∧ liftBinaryKept T Kept hKept r = br,
    start := fun sr =>
      ∃ r : StartRule V,
        G.start r ∧ liftStartKept T Kept hKept r = sr }


/-- Terminal-rule lifting to kept states is injective. -/
theorem liftTerminalKept_injective
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X)) :
    Function.Injective
      (liftTerminalKept T Kept hKept :
        TerminalRule V Sigma → KeptTerminalRule Kept Sigma) := by
  intro r s h
  have hlhs : r.lhs = s.lhs := by
    have hlabel :=
      congrArg (fun tr : KeptTerminalRule Kept Sigma => tr.lhs.val.label) h
    simpa [liftTerminalKept, intendedCopyToKept, intendedCopy] using hlabel
  have hterminal : r.terminal = s.terminal := by
    have hterm :=
      congrArg (fun tr : KeptTerminalRule Kept Sigma => tr.terminal) h
    simpa [liftTerminalKept] using hterm
  cases r
  cases s
  simp_all


/-- Binary-rule lifting to kept states is injective. -/
theorem liftBinaryKept_injective
    {V : Type u} {M : Type v}
    (T : StateTyping V M)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X)) :
    Function.Injective
      (liftBinaryKept T Kept hKept :
        BinaryRule V → KeptBinaryRule Kept) := by
  intro r s h
  have hparent : r.parent = s.parent := by
    have hlabel :=
      congrArg (fun br : KeptBinaryRule Kept => br.parent.val.label) h
    simpa [liftBinaryKept, intendedCopyToKept, intendedCopy] using hlabel
  have hleft : r.left = s.left := by
    have hlabel :=
      congrArg (fun br : KeptBinaryRule Kept => br.left.val.label) h
    simpa [liftBinaryKept, intendedCopyToKept, intendedCopy] using hlabel
  have hright : r.right = s.right := by
    have hlabel :=
      congrArg (fun br : KeptBinaryRule Kept => br.right.val.label) h
    simpa [liftBinaryKept, intendedCopyToKept, intendedCopy] using hlabel
  cases r
  cases s
  simp_all


/-- Start-rule lifting to kept states is injective. -/
theorem liftStartKept_injective
    {V : Type u} {M : Type v}
    (T : StateTyping V M)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X)) :
    Function.Injective
      (liftStartKept T Kept hKept :
        StartRule V → KeptStartRule Kept) := by
  intro r s h
  have hstate : r.state = s.state := by
    have hlabel :=
      congrArg (fun sr : KeptStartRule Kept => sr.state.val.label) h
    simpa [liftStartKept, intendedCopyToKept, intendedCopy] using hlabel
  cases r
  cases s
  simp_all


/-- Terminal rules are preserved by kept lifting. -/
theorem kept_terminal_preserved
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    {r : TerminalRule V Sigma}
    (h : G.terminal r) :
    (liftToKeptStructure T G Kept hKept).terminal
      (liftTerminalKept T Kept hKept r) := by
  exact ⟨r, h, rfl⟩


/-- Terminal rules are reflected by kept lifting. -/
theorem kept_terminal_reflected
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    {r : TerminalRule V Sigma}
    (h : (liftToKeptStructure T G Kept hKept).terminal
      (liftTerminalKept T Kept hKept r)) :
    G.terminal r := by
  rcases h with ⟨r', hr', heq⟩
  have hrr : r' = r := liftTerminalKept_injective T Kept hKept heq
  simpa [hrr] using hr'


/-- Binary rules are preserved by kept lifting. -/
theorem kept_binary_preserved
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    {r : BinaryRule V}
    (h : G.binary r) :
    (liftToKeptStructure T G Kept hKept).binary
      (liftBinaryKept T Kept hKept r) := by
  exact ⟨r, h, rfl⟩


/-- Binary rules are reflected by kept lifting. -/
theorem kept_binary_reflected
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    {r : BinaryRule V}
    (h : (liftToKeptStructure T G Kept hKept).binary
      (liftBinaryKept T Kept hKept r)) :
    G.binary r := by
  rcases h with ⟨r', hr', heq⟩
  have hrr : r' = r := liftBinaryKept_injective T Kept hKept heq
  simpa [hrr] using hr'


/-- Start declarations are preserved by kept lifting. -/
theorem kept_start_preserved
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    {r : StartRule V}
    (h : G.start r) :
    (liftToKeptStructure T G Kept hKept).start
      (liftStartKept T Kept hKept r) := by
  exact ⟨r, h, rfl⟩


/-- Start declarations are reflected by kept lifting. -/
theorem kept_start_reflected
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    {r : StartRule V}
    (h : (liftToKeptStructure T G Kept hKept).start
      (liftStartKept T Kept hKept r)) :
    G.start r := by
  rcases h with ⟨r', hr', heq⟩
  have hrr : r' = r := liftStartKept_injective T Kept hKept heq
  simpa [hrr] using hr'


/-- Terminal-rule equivalence for kept lifting. -/
theorem kept_terminal_lift_iff
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (r : TerminalRule V Sigma) :
    (liftToKeptStructure T G Kept hKept).terminal
      (liftTerminalKept T Kept hKept r) ↔ G.terminal r := by
  constructor
  · intro h
    exact kept_terminal_reflected T G Kept hKept h
  · intro h
    exact kept_terminal_preserved T G Kept hKept h


/-- Binary-rule equivalence for kept lifting. -/
theorem kept_binary_lift_iff
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (r : BinaryRule V) :
    (liftToKeptStructure T G Kept hKept).binary
      (liftBinaryKept T Kept hKept r) ↔ G.binary r := by
  constructor
  · intro h
    exact kept_binary_reflected T G Kept hKept h
  · intro h
    exact kept_binary_preserved T G Kept hKept h


/-- Start-rule equivalence for kept lifting. -/
theorem kept_start_lift_iff
    {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma)
    (Kept : TypedState V M → Prop)
    (hKept : ∀ X : V, Kept (intendedCopy T X))
    (r : StartRule V) :
    (liftToKeptStructure T G Kept hKept).start
      (liftStartKept T Kept hKept r) ↔ G.start r := by
  constructor
  · intro h
    exact kept_start_reflected T G Kept hKept h
  · intro h
    exact kept_start_preserved T G Kept hKept h

end KeptStructureKernel
end JALC
end LeanCfgProject
