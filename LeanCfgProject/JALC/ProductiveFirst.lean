import Mathlib

namespace LeanCfgProject
namespace JALC
namespace ProductiveFirst

/-
Finite witness for the need for productive-first trimming.

This file models the small example from the paper in which a copy can be
reachable in the full typed refinement and productive in the full typed
refinement, but still should not survive the productive-first reachable part.

The example uses M = ZMod 2, written additively.  The only terminal has
type 0.  The intended binary state X has yield type 0.  A wrong-yield
copy of X with yield type 1 is reachable from the start interface in the
full refinement, and it transports a wrong right frame to a productive
copy of Y.  Productive-first trimming deletes the wrong-yield parent
before reachability is computed, so the wrong-frame Y copy is not kept.
-/


/-- Nonterminals of the toy grammar. -/
inductive NT where
  | X
  | Y
  | Z
deriving DecidableEq, Repr


/-- Type triples over `ZMod 2`.

A copy consists of a nonterminal label, a yield type, a left frame, and a
right frame.
-/
structure Copy where
  nt : NT
  yt : ZMod 2
  lt : ZMod 2
  rt : ZMod 2
deriving DecidableEq, Repr


/-- Intended copy of X. -/
def intendedX : Copy :=
  { nt := NT.X, yt := 0, lt := 0, rt := 0 }


/-- Intended copy of Y. -/
def intendedY : Copy :=
  { nt := NT.Y, yt := 0, lt := 0, rt := 0 }


/-- Intended copy of Z. -/
def intendedZ : Copy :=
  { nt := NT.Z, yt := 0, lt := 0, rt := 0 }


/-- Wrong-yield copy of X that is reachable before productivity is tested. -/
def wrongParentX : Copy :=
  { nt := NT.X, yt := 1, lt := 0, rt := 0 }


/-- Wrong-frame copy of Y transported by the wrong-yield parent. -/
def spuriousY : Copy :=
  { nt := NT.Y, yt := 0, lt := 0, rt := 1 }


/-- The corresponding right sibling in the displayed full-refinement path. -/
def spuriousZSibling : Copy :=
  { nt := NT.Z, yt := 1, lt := 0, rt := 0 }


/--
Binary frame transport for the toy grammar.

This is the additive `ZMod 2` version of

  A_p^{m,n} -> B_q^{m,rn} C_r^{mq,n}.

Since we are in additive notation, products become sums.
-/
def binaryTransport (parent left right : Copy) : Prop :=
  parent.nt = NT.X ∧
  left.nt = NT.Y ∧
  right.nt = NT.Z ∧
  left.yt + right.yt = parent.yt ∧
  left.lt = parent.lt ∧
  left.rt = right.yt + parent.rt ∧
  right.lt = parent.lt + left.yt ∧
  right.rt = parent.rt


/-- The intended binary rule has the intended children. -/
theorem intended_binary_transport :
    binaryTransport intendedX intendedY intendedZ := by
  decide


/--
The wrong-yield parent transports the wrong right frame to Y.

This is the exact finite path responsible for the failure of naive trimming.
-/
theorem spurious_binary_transport :
    binaryTransport wrongParentX spuriousY spuriousZSibling := by
  decide


/--
Start copies in the full refinement.

Because the original grammar has a start production `S0 -> X`, the full typed
refinement contains start rules to all copies of X with empty external frame.
-/
def fullStartCopy (c : Copy) : Prop :=
  c.nt = NT.X ∧ c.lt = 0 ∧ c.rt = 0


/-- The intended X copy is a full start copy. -/
theorem intendedX_full_start :
    fullStartCopy intendedX := by
  decide


/-- The wrong-yield X copy is also a full start copy. -/
theorem wrongParentX_full_start :
    fullStartCopy wrongParentX := by
  decide


/--
A copy is productive in the full refinement of this toy grammar exactly when
its yield type is compatible with what its label can generate.

Here Y and Z generate the one terminal of type 0, and X generates two such
terminals, again of type 0.  Therefore every productive copy has yield type 0.
The frame components do not affect terminal productivity for Y and Z.
-/
def fullProductiveCopy (c : Copy) : Prop :=
  c.yt = 0 ∧ (c.nt = NT.X ∨ c.nt = NT.Y ∨ c.nt = NT.Z)


/-- The intended X copy is productive. -/
theorem intendedX_full_productive :
    fullProductiveCopy intendedX := by
  decide


/-- The intended Y copy is productive. -/
theorem intendedY_full_productive :
    fullProductiveCopy intendedY := by
  decide


/-- The intended Z copy is productive. -/
theorem intendedZ_full_productive :
    fullProductiveCopy intendedZ := by
  decide


/--
The wrong-frame Y copy is productive in the full refinement.

This is the dangerous point: productivity alone does not remove it.
-/
theorem spuriousY_full_productive :
    fullProductiveCopy spuriousY := by
  decide


/--
The wrong-yield parent is not productive.

This is the point that productive-first trimming uses before reachability is
computed.
-/
theorem wrongParentX_not_full_productive :
    ¬ fullProductiveCopy wrongParentX := by
  decide


/--
Displayed full-refinement reachability witness.

This predicate is not the full reachability relation.  It records the concrete
short path used in the paper:

  start -> wrongParentX -> spuriousY spuriousZSibling.
-/
def displayedFullReachable (c : Copy) : Prop :=
  c = wrongParentX ∨ c = spuriousY ∨ c = spuriousZSibling


/-- The wrong-yield parent is reached in the displayed full-refinement path. -/
theorem wrongParentX_displayed_reachable :
    displayedFullReachable wrongParentX := by
  unfold displayedFullReachable
  exact Or.inl rfl


/-- The wrong-frame Y copy is reached in the displayed full-refinement path. -/
theorem spuriousY_displayed_reachable :
    displayedFullReachable spuriousY := by
  unfold displayedFullReachable
  exact Or.inr (Or.inl rfl)


/--
The reachable part after productive-first trimming in this toy example.

After nonproductive copies are removed, the wrong-yield parent is gone.
The remaining reachable productive copies are precisely the intended copies.
-/
def productiveFirstReachable (c : Copy) : Prop :=
  c = intendedX ∨ c = intendedY ∨ c = intendedZ


/-- The intended X copy remains. -/
theorem intendedX_productive_first_reachable :
    productiveFirstReachable intendedX := by
  unfold productiveFirstReachable
  exact Or.inl rfl


/-- The intended Y copy remains. -/
theorem intendedY_productive_first_reachable :
    productiveFirstReachable intendedY := by
  unfold productiveFirstReachable
  exact Or.inr (Or.inl rfl)


/-- The intended Z copy remains. -/
theorem intendedZ_productive_first_reachable :
    productiveFirstReachable intendedZ := by
  unfold productiveFirstReachable
  exact Or.inr (Or.inr rfl)


/--
The wrong-frame Y copy is not kept by productive-first trimming.

It was reachable in the full-refinement path and productive in the full
refinement, but its only displayed route goes through the wrong-yield parent,
which is removed before reachability is recomputed.
-/
theorem spuriousY_not_productive_first_reachable :
    ¬ productiveFirstReachable spuriousY := by
  unfold productiveFirstReachable spuriousY intendedX intendedY intendedZ
  decide


/--
Finite kernel of the productive-first counterexample.

The wrong-frame Y copy is both reachable in the displayed full path and
productive, but it is not reachable after productive-first trimming.
-/
theorem productive_first_counterexample_kernel :
    displayedFullReachable spuriousY ∧
    fullProductiveCopy spuriousY ∧
    ¬ productiveFirstReachable spuriousY := by
  exact ⟨spuriousY_displayed_reachable,
    spuriousY_full_productive,
    spuriousY_not_productive_first_reachable⟩


/--
The intended Y copy is kept while the wrong-frame Y copy is not.

This is the finite statement corresponding to the paper's reason for using
productive-first trimming.
-/
theorem productive_first_keeps_intended_not_spurious :
    productiveFirstReachable intendedY ∧
    ¬ productiveFirstReachable spuriousY := by
  exact ⟨intendedY_productive_first_reachable,
    spuriousY_not_productive_first_reachable⟩

end ProductiveFirst
end JALC
end LeanCfgProject
