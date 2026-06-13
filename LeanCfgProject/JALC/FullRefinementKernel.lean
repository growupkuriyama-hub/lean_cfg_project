import LeanCfgProject.JALC.PaperFacingKeptCorrectness

namespace LeanCfgProject
namespace JALC
namespace FullRefinementKernel

/-
Full all-copy typed-refinement kernel.

This module defines an abstract full typed refinement over all typed copies.
It uses a terminal type map tau : Sigma -> M as the finite observer on
letters.  The goal is to connect the already checked intended-copy lift to a
larger all-copy structure.
-/

universe u v w

open InverseKernel RoundTripKernel


/-- Binary transport equations for the intended state typing. -/
structure BinaryTransportCompatible {V : Type u} {M : Type v} [Monoid M]
    (T : StateTyping V M) (r : BinaryRule V) : Prop where
  yield_eq : T.yt r.left * T.yt r.right = T.yt r.parent
  left_left_eq : T.lt r.left = T.lt r.parent
  left_right_eq : T.rt r.left = T.yt r.right * T.rt r.parent
  right_left_eq : T.lt r.right = T.lt r.parent * T.yt r.left
  right_right_eq : T.rt r.right = T.rt r.parent


/-- Compatibility of original rules with the intended typing. -/
structure TypingCompatible {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (T : StateTyping V M)
    (G : UntypedStructure V Sigma) : Prop where
  terminal :
    ∀ r : TerminalRule V Sigma, G.terminal r → tau r.terminal = T.yt r.lhs
  binary :
    ∀ r : BinaryRule V, G.binary r → BinaryTransportCompatible T r
  start :
    ∀ r : StartRule V, G.start r → T.lt r.state = 1 ∧ T.rt r.state = 1


/-- Terminal rules of the full all-copy typed refinement. -/
def FullTerminalRule {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (tr : TypedTerminalRule V M Sigma) : Prop :=
  ∃ r : TerminalRule V Sigma,
    G.terminal r ∧
    r.lhs = tr.lhs.label ∧
    r.terminal = tr.terminal ∧
    tau tr.terminal = tr.lhs.yt


/-- Binary rules of the full all-copy typed refinement. -/
def FullBinaryRule {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (G : UntypedStructure V Sigma)
    (br : TypedBinaryRule V M) : Prop :=
  ∃ r : BinaryRule V,
    G.binary r ∧
    r.parent = br.parent.label ∧
    r.left = br.left.label ∧
    r.right = br.right.label ∧
    br.left.yt * br.right.yt = br.parent.yt ∧
    br.left.lt = br.parent.lt ∧
    br.left.rt = br.right.yt * br.parent.rt ∧
    br.right.lt = br.parent.lt * br.left.yt ∧
    br.right.rt = br.parent.rt


/-- Start declarations of the full all-copy typed refinement. -/
def FullStartRule {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (G : UntypedStructure V Sigma)
    (sr : TypedStartRule V M) : Prop :=
  ∃ r : StartRule V,
    G.start r ∧
    r.state = sr.state.label ∧
    sr.state.lt = 1 ∧
    sr.state.rt = 1


/-- The full all-copy typed refinement as a typed rule structure. -/
def fullTypedStructure {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) :
    TypedStructure V M Sigma :=
  { terminal := FullTerminalRule tau G,
    binary := FullBinaryRule G,
    start := FullStartRule G }


/-- The full refinement contains every compatible intended terminal rule. -/
theorem full_terminal_contains_intended
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    {r : TerminalRule V Sigma}
    (h : G.terminal r) :
    (fullTypedStructure tau G).terminal (liftTerminal T r) := by
  exact ⟨r, h, rfl, rfl, by
    simpa [liftTerminal, intendedCopy] using comp.terminal r h⟩


/-- The full refinement contains every compatible intended binary rule. -/
theorem full_binary_contains_intended
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    {r : BinaryRule V}
    (h : G.binary r) :
    (fullTypedStructure tau G).binary (liftBinary T r) := by
  let hb := comp.binary r h
  exact ⟨r, h, rfl, rfl, rfl,
    by simpa [liftBinary, intendedCopy] using hb.yield_eq,
    by simpa [liftBinary, intendedCopy] using hb.left_left_eq,
    by simpa [liftBinary, intendedCopy] using hb.left_right_eq,
    by simpa [liftBinary, intendedCopy] using hb.right_left_eq,
    by simpa [liftBinary, intendedCopy] using hb.right_right_eq⟩


/-- The full refinement contains every compatible intended start declaration. -/
theorem full_start_contains_intended
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G)
    {r : StartRule V}
    (h : G.start r) :
    (fullTypedStructure tau G).start (liftStart T r) := by
  rcases comp.start r h with ⟨hl, hr⟩
  exact ⟨r, h, rfl,
    by simpa [liftStart, intendedCopy] using hl,
    by simpa [liftStart, intendedCopy] using hr⟩


/-- Inclusion of one typed rule structure in another. -/
structure TypedStructureIncluded {V : Type u} {M : Type v} {Sigma : Type w}
    (H K : TypedStructure V M Sigma) : Prop where
  terminal :
    ∀ r : TypedTerminalRule V M Sigma, H.terminal r → K.terminal r
  binary :
    ∀ r : TypedBinaryRule V M, H.binary r → K.binary r
  start :
    ∀ r : TypedStartRule V M, H.start r → K.start r


/--
The intended-copy lift is included in the full all-copy typed refinement,
under the rule-typing compatibility assumptions.
-/
theorem liftStructure_included_in_full
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (T : StateTyping V M)
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (comp : TypingCompatible tau T G) :
    TypedStructureIncluded (liftStructure T G) (fullTypedStructure tau G) := by
  refine ⟨?_, ?_, ?_⟩
  · intro tr h
    rcases h with ⟨r, hr, heq⟩
    cases heq
    exact full_terminal_contains_intended T tau G comp hr
  · intro br h
    rcases h with ⟨r, hr, heq⟩
    cases heq
    exact full_binary_contains_intended T tau G comp hr
  · intro sr h
    rcases h with ⟨r, hr, heq⟩
    cases heq
    exact full_start_contains_intended T tau G comp hr

end FullRefinementKernel
end JALC
end LeanCfgProject
