import LeanCfgProject.JALC.InverseKernel

namespace LeanCfgProject
namespace JALC
namespace RoundTripKernel

/-
Rule-preservation kernel for the inverse representation argument.

This file checks that lifting rules along the intended-copy map preserves and
reflects terminal rules, binary rules, and start declarations.  It is a small
formal core of the eventual state-separated round-trip argument.
-/

universe u v w

open InverseKernel


/-- A grammar-like rule structure over original states. -/
structure UntypedStructure (V : Type u) (Sigma : Type w) where
  terminal : TerminalRule V Sigma → Prop
  binary : BinaryRule V → Prop
  start : StartRule V → Prop


/-- A grammar-like rule structure over typed state copies. -/
structure TypedStructure (V : Type u) (M : Type v) (Sigma : Type w) where
  terminal : TypedTerminalRule V M Sigma → Prop
  binary : TypedBinaryRule V M → Prop
  start : TypedStartRule V M → Prop


/-- Lift an untyped rule structure to intended typed copies. -/
def liftStructure {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma) :
    TypedStructure V M Sigma :=
  { terminal := fun tr => ∃ r, G.terminal r ∧ liftTerminal T r = tr,
    binary := fun br => ∃ r, G.binary r ∧ liftBinary T r = br,
    start := fun sr => ∃ r, G.start r ∧ liftStart T r = sr }


/-- Terminal rules are preserved by lifting. -/
theorem terminal_preserved {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    {r : TerminalRule V Sigma}
    (h : G.terminal r) :
    (liftStructure T G).terminal (liftTerminal T r) := by
  exact ⟨r, h, rfl⟩


/-- Terminal rules are reflected by lifting to intended copies. -/
theorem terminal_reflected {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    {r : TerminalRule V Sigma}
    (h : (liftStructure T G).terminal (liftTerminal T r)) :
    G.terminal r := by
  rcases h with ⟨r', hr', heq⟩
  have hrr : r' = r := liftTerminal_injective T heq
  simpa [hrr] using hr'


/-- Terminal-rule preservation and reflection as an equivalence. -/
theorem terminal_lift_iff {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    (r : TerminalRule V Sigma) :
    (liftStructure T G).terminal (liftTerminal T r) ↔ G.terminal r := by
  constructor
  · intro h
    exact terminal_reflected T G h
  · intro h
    exact terminal_preserved T G h


/-- Binary rules are preserved by lifting. -/
theorem binary_preserved {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    {r : BinaryRule V}
    (h : G.binary r) :
    (liftStructure T G).binary (liftBinary T r) := by
  exact ⟨r, h, rfl⟩


/-- Binary rules are reflected by lifting to intended copies. -/
theorem binary_reflected {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    {r : BinaryRule V}
    (h : (liftStructure T G).binary (liftBinary T r)) :
    G.binary r := by
  rcases h with ⟨r', hr', heq⟩
  have hrr : r' = r := liftBinary_injective T heq
  simpa [hrr] using hr'


/-- Binary-rule preservation and reflection as an equivalence. -/
theorem binary_lift_iff {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    (r : BinaryRule V) :
    (liftStructure T G).binary (liftBinary T r) ↔ G.binary r := by
  constructor
  · intro h
    exact binary_reflected T G h
  · intro h
    exact binary_preserved T G h


/-- Start declarations are preserved by lifting. -/
theorem start_preserved {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    {r : StartRule V}
    (h : G.start r) :
    (liftStructure T G).start (liftStart T r) := by
  exact ⟨r, h, rfl⟩


/-- Start declarations are reflected by lifting to intended copies. -/
theorem start_reflected {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    {r : StartRule V}
    (h : (liftStructure T G).start (liftStart T r)) :
    G.start r := by
  rcases h with ⟨r', hr', heq⟩
  have hrr : r' = r := liftStart_injective T heq
  simpa [hrr] using hr'


/-- Start preservation and reflection as an equivalence. -/
theorem start_lift_iff {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    (r : StartRule V) :
    (liftStructure T G).start (liftStart T r) ↔ G.start r := by
  constructor
  · intro h
    exact start_reflected T G h
  · intro h
    exact start_preserved T G h


/--
Combined rule preservation and reflection kernel.

This packages the three equivalences needed for the intended-copy rule graph.
-/
theorem rule_lift_kernel {V : Type u} {M : Type v} {Sigma : Type w}
    (T : StateTyping V M) (G : UntypedStructure V Sigma)
    (tr : TerminalRule V Sigma) (br : BinaryRule V) (sr : StartRule V) :
    ((liftStructure T G).terminal (liftTerminal T tr) ↔ G.terminal tr) ∧
    ((liftStructure T G).binary (liftBinary T br) ↔ G.binary br) ∧
    ((liftStructure T G).start (liftStart T sr) ↔ G.start sr) := by
  exact ⟨terminal_lift_iff T G tr,
    binary_lift_iff T G br,
    start_lift_iff T G sr⟩

end RoundTripKernel
end JALC
end LeanCfgProject
