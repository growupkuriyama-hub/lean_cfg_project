import LeanCfgProject.FixedHCFG.V60WindowShortcut

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Thickness-bounded replacement of the off-path sibling subtrees occurring on a
marked unary chain.

This is the second local operation in manuscript Lemma `window-typed-yield`.
After repeated labels on a marked chain have been shortcut, every binary edge
on that chain has exactly one sibling subtree containing no marked leaf.  The
paper replaces each such sibling by a shortest terminal derivation of the same
root nonterminal, of length at most `tau_G`.  The definitions and bounds below
formalize that operation directly on `V60DerivationContext`.
-/

namespace V60DerivationContext

variable {N : Type v} {Sigma : Type u}
variable {terminal : V60TerminalRules N Sigma}
variable {binary : V60BinaryRules N}

/-- Total terminal material surrounding the hole of a one-hole context. -/
def terminalMaterialLength {A H : N}
    (ctx : V60DerivationContext terminal binary A H) : Nat :=
  (leftWord ctx).length + (rightWord ctx).length

/--
Replace every off-path sibling tree by another tree with the same root label.
The distinguished root-to-hole spine, its labels, and all grammar rules on that
spine are untouched.
-/
def shortenSiblings
    (shorten : ∀ {A : N},
      V60DerivationTree terminal binary A →
        V60DerivationTree terminal binary A)
    {A H : N} :
    V60DerivationContext terminal binary A H →
      V60DerivationContext terminal binary A H
  | .hole A => .hole A
  | .left A B C H hrule sub rightTree =>
      .left A B C H hrule
        (shortenSiblings shorten sub) (shorten rightTree)
  | .right A B C H hrule leftTree sub =>
      .right A B C H hrule
        (shorten leftTree) (shortenSiblings shorten sub)

/-- Sibling replacement does not change the number of marked-spine edges. -/
theorem depth_shortenSiblings
    (shorten : ∀ {A : N},
      V60DerivationTree terminal binary A →
        V60DerivationTree terminal binary A)
    {A H : N}
    (ctx : V60DerivationContext terminal binary A H) :
    depth (shortenSiblings shorten ctx) = depth ctx := by
  induction ctx with
  | hole A => rfl
  | left A B C H hrule sub rightTree ih =>
      simp [shortenSiblings, depth, ih]
  | right A B C H hrule leftTree sub ih =>
      simp [shortenSiblings, depth, ih]

/--
If every replacement sibling has terminal yield of length at most `tau`, the
whole terminal material contributed by a context of depth `d` is at most
`d*tau`.  This is exactly the per-retained-node charge used in the paper.
-/
theorem terminalMaterialLength_shortenSiblings_le
    (tau : Nat)
    (shorten : ∀ {A : N},
      V60DerivationTree terminal binary A →
        V60DerivationTree terminal binary A)
    (hShort : ∀ {A : N} (t : V60DerivationTree terminal binary A),
      (V60DerivationTree.yield (shorten t)).length ≤ tau)
    {A H : N}
    (ctx : V60DerivationContext terminal binary A H) :
    terminalMaterialLength (shortenSiblings shorten ctx) ≤
      depth ctx * tau := by
  induction ctx with
  | hole A =>
      simp [terminalMaterialLength, shortenSiblings, depth, leftWord, rightWord]
  | left A B C H hrule sub rightTree ih =>
      have hs := hShort rightTree
      have hsum := Nat.add_le_add ih hs
      simpa [terminalMaterialLength, shortenSiblings, leftWord, rightWord,
        depth, List.length_append, Nat.add_mul, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hsum
  | right A B C H hrule leftTree sub ih =>
      have hs := hShort leftTree
      have hsum := Nat.add_le_add hs ih
      simpa [terminalMaterialLength, shortenSiblings, leftWord, rightWord,
        depth, List.length_append, Nat.add_mul, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hsum

end V60DerivationContext

/--
A productive concrete tree has a same-root concrete derivation whose yield is
bounded by the manuscript thickness parameter.
-/
theorem v60_exists_short_tree_of_base_thickness
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (tau : Nat)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {A : N}
    (t : V60DerivationTree terminal binary A) :
    ∃ t' : V60DerivationTree terminal binary A,
      (V60DerivationTree.yield t').length ≤ tau := by
  have hProductive :
      ∃ w : Word Sigma, V60UntypedDerives terminal binary A w :=
    ⟨V60DerivationTree.yield t, V60DerivationTree.toUntypedDerives t⟩
  obtain ⟨z, dz, hz⟩ := hThickness A hProductive
  obtain ⟨t', ht'⟩ := V60DerivationTree.exists_tree_of_untyped_derives dz
  refine ⟨t', ?_⟩
  rw [ht']
  exact hz

/-- A canonical choice of a thickness-bounded same-root replacement tree. -/
noncomputable def v60ThicknessShortTree
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (tau : Nat)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {A : N}
    (t : V60DerivationTree terminal binary A) :
    V60DerivationTree terminal binary A :=
  Classical.choose
    (v60_exists_short_tree_of_base_thickness tau hThickness t)

/-- The chosen replacement realizes the promised thickness bound. -/
theorem v60ThicknessShortTree_length_le
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (tau : Nat)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {A : N}
    (t : V60DerivationTree terminal binary A) :
    (V60DerivationTree.yield
      (v60ThicknessShortTree tau hThickness t)).length ≤ tau := by
  exact Classical.choose_spec
    (v60_exists_short_tree_of_base_thickness tau hThickness t)

namespace V60DerivationContext

/-- Replace every off-path sibling by the chosen thickness-bounded tree. -/
noncomputable def shortenSiblingsByThickness
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (tau : Nat)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {A H : N}
    (ctx : V60DerivationContext terminal binary A H) :
    V60DerivationContext terminal binary A H :=
  shortenSiblings
    (fun {A} t =>
      v60ThicknessShortTree
        (terminal := terminal) (binary := binary) tau hThickness t)
    ctx

/-- Thickness shortening leaves the marked-spine depth unchanged. -/
theorem depth_shortenSiblingsByThickness
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (tau : Nat)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {A H : N}
    (ctx : V60DerivationContext terminal binary A H) :
    depth (shortenSiblingsByThickness tau hThickness ctx) = depth ctx := by
  exact depth_shortenSiblings
    (fun {A} t =>
      v60ThicknessShortTree
        (terminal := terminal) (binary := binary) tau hThickness t)
    ctx

/--
Concrete manuscript bound: after replacing all unmarked siblings on a chain,
their total terminal contribution is at most `depth * tau`.
-/
theorem terminalMaterialLength_shortenSiblingsByThickness_le
    {N : Type v} {Sigma : Type u}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (tau : Nat)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {A H : N}
    (ctx : V60DerivationContext terminal binary A H) :
    terminalMaterialLength
      (shortenSiblingsByThickness tau hThickness ctx) ≤
        depth ctx * tau := by
  apply terminalMaterialLength_shortenSiblings_le tau
    (fun {A} t =>
      v60ThicknessShortTree
        (terminal := terminal) (binary := binary) tau hThickness t)
  intro A t
  exact v60ThicknessShortTree_length_le tau hThickness t

end V60DerivationContext

end FixedHCFG
end LeanCfgProject
