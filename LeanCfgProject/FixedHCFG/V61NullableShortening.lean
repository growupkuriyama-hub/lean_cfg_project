import LeanCfgProject.FixedHCFG.V61NullableSpine

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Thickness-bounded shortening along the cycle-free root-to-terminal path used in
Appendix A of TCS revision v61.

The intermediate binary grammar may contain epsilon rules.  Accordingly, the
thickness hypothesis below bounds a same-root replacement for every concrete
subtree, and such a replacement may have empty yield.  This is precisely what
the manuscript needs for off-path nullable siblings.
-/

/-- Concrete thickness bound for the intermediate nullable binary grammar. -/
def V61NullableThicknessBound
    {N : Type v} {Sigma : Type u}
    (epsilon : V61EpsilonRules N)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N)
    (tau : Nat) : Prop :=
  ∀ {A : N} (t : V61NullableDerivationTree epsilon terminal binary A),
    ∃ t' : V61NullableDerivationTree epsilon terminal binary A,
      (V61NullableDerivationTree.yield t').length ≤ tau

namespace V61NullableDerivationContext

variable {N : Type v} {Sigma : Type u}
variable {epsilon : V61EpsilonRules N}
variable {terminal : V60TerminalRules N Sigma}
variable {binary : V60BinaryRules N}

/-- Total terminal material outside the distinguished hole. -/
def terminalMaterialLength {A H : N}
    (ctx : V61NullableDerivationContext epsilon terminal binary A H) : Nat :=
  (leftWord ctx).length + (rightWord ctx).length

/-- Replace every off-path sibling by another same-root nullable tree. -/
def shortenSiblings
    (shorten : ∀ {A : N},
      V61NullableDerivationTree epsilon terminal binary A →
        V61NullableDerivationTree epsilon terminal binary A)
    {A H : N} :
    V61NullableDerivationContext epsilon terminal binary A H →
      V61NullableDerivationContext epsilon terminal binary A H
  | .hole A => .hole A
  | .left A B C H hrule sub rightTree =>
      .left A B C H hrule
        (shortenSiblings shorten sub) (shorten rightTree)
  | .right A B C H hrule leftTree sub =>
      .right A B C H hrule
        (shorten leftTree) (shortenSiblings shorten sub)

/-- Sibling replacement preserves root-to-hole depth. -/
theorem depth_shortenSiblings
    (shorten : ∀ {A : N},
      V61NullableDerivationTree epsilon terminal binary A →
        V61NullableDerivationTree epsilon terminal binary A)
    {A H : N}
    (ctx : V61NullableDerivationContext epsilon terminal binary A H) :
    depth (shortenSiblings shorten ctx) = depth ctx := by
  induction ctx with
  | hole A => rfl
  | left A B C H hrule sub rightTree ih =>
      simp [shortenSiblings, depth, ih]
  | right A B C H hrule leftTree sub ih =>
      simp [shortenSiblings, depth, ih]

/--
If every replacement sibling has frontier length at most `tau`, the terminal
material surrounding the hole is bounded by `depth * tau`.
-/
theorem terminalMaterialLength_shortenSiblings_le
    (tau : Nat)
    (shorten : ∀ {A : N},
      V61NullableDerivationTree epsilon terminal binary A →
        V61NullableDerivationTree epsilon terminal binary A)
    (hShort : ∀ {A : N}
      (t : V61NullableDerivationTree epsilon terminal binary A),
      (V61NullableDerivationTree.yield (shorten t)).length ≤ tau)
    {A H : N}
    (ctx : V61NullableDerivationContext epsilon terminal binary A H) :
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

end V61NullableDerivationContext

/-- Choose a thickness-bounded same-root replacement tree. -/
noncomputable def v61NullableShortTree
    {N : Type v} {Sigma : Type u}
    {epsilon : V61EpsilonRules N}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (tau : Nat)
    (hThickness : V61NullableThicknessBound epsilon terminal binary tau)
    {A : N}
    (t : V61NullableDerivationTree epsilon terminal binary A) :
    V61NullableDerivationTree epsilon terminal binary A :=
  Classical.choose (hThickness t)

/-- The chosen nullable replacement realizes the thickness bound. -/
theorem v61NullableShortTree_length_le
    {N : Type v} {Sigma : Type u}
    {epsilon : V61EpsilonRules N}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (tau : Nat)
    (hThickness : V61NullableThicknessBound epsilon terminal binary tau)
    {A : N}
    (t : V61NullableDerivationTree epsilon terminal binary A) :
    (V61NullableDerivationTree.yield
      (v61NullableShortTree tau hThickness t)).length ≤ tau := by
  exact Classical.choose_spec (hThickness t)

namespace V61NullableDerivationContext

/-- Shorten all off-path siblings using the intermediate-grammar thickness. -/
noncomputable def shortenSiblingsByThickness
    {N : Type v} {Sigma : Type u}
    {epsilon : V61EpsilonRules N}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (tau : Nat)
    (hThickness : V61NullableThicknessBound epsilon terminal binary tau)
    {A H : N}
    (ctx : V61NullableDerivationContext epsilon terminal binary A H) :
    V61NullableDerivationContext epsilon terminal binary A H :=
  shortenSiblings
    (fun {A} t => v61NullableShortTree tau hThickness t) ctx

/-- Concrete off-path material bound after thickness shortening. -/
theorem terminalMaterialLength_shortenSiblingsByThickness_le
    {N : Type v} {Sigma : Type u}
    {epsilon : V61EpsilonRules N}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (tau : Nat)
    (hThickness : V61NullableThicknessBound epsilon terminal binary tau)
    {A H : N}
    (ctx : V61NullableDerivationContext epsilon terminal binary A H) :
    terminalMaterialLength
      (shortenSiblingsByThickness tau hThickness ctx) ≤ depth ctx * tau := by
  exact terminalMaterialLength_shortenSiblings_le tau
    (fun {A} t => v61NullableShortTree tau hThickness t)
    (fun {_} t => v61NullableShortTree_length_le tau hThickness t)
    ctx

end V61NullableDerivationContext

/--
Core v61 Appendix A lemma.  If `A` has any nonempty terminal derivation in the
intermediate binary grammar, then it has one of length at most
`1 + |N| * tau`.  The proof chooses one terminal leaf, deletes repeated labels
on its root path, and shortens every off-path sibling; nullable siblings may
contribute epsilon.
-/
theorem v61_exists_short_nonempty_tree
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    {epsilon : V61EpsilonRules N}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N}
    (tau : Nat)
    (hThickness : V61NullableThicknessBound epsilon terminal binary tau)
    {A : N}
    (t : V61NullableDerivationTree epsilon terminal binary A)
    (hNonempty : V61NullableDerivationTree.yield t ≠ []) :
    ∃ t' : V61NullableDerivationTree epsilon terminal binary A,
      V61NullableDerivationTree.yield t' ≠ [] ∧
      (V61NullableDerivationTree.yield t').length ≤
        1 + Fintype.card N * tau := by
  obtain ⟨B, a, hterm, ctx, hctx⟩ :=
    V61NullableDerivationContext.exists_terminal_hole_of_yield_ne_nil
      t hNonempty
  obtain ⟨simple, hDepth⟩ :=
    V61NullableDerivationSpine.exists_context_with_depth_succ_le_card ctx
  let short :=
    V61NullableDerivationContext.shortenSiblingsByThickness
      tau hThickness simple
  let leaf : V61NullableDerivationTree epsilon terminal binary B :=
    .terminal B a hterm
  let t' := V61NullableDerivationContext.plug short leaf
  refine ⟨t', ?_, ?_⟩
  · rw [V61NullableDerivationContext.yield_plug]
    simp [leaf, V61NullableDerivationTree.yield]
  · have hMat :=
      V61NullableDerivationContext.terminalMaterialLength_shortenSiblingsByThickness_le
        tau hThickness simple
    have hDepthLe : V61NullableDerivationContext.depth simple ≤ Fintype.card N := by
      omega
    have hMul :
        V61NullableDerivationContext.depth simple * tau ≤
          Fintype.card N * tau :=
      Nat.mul_le_mul_right tau hDepthLe
    rw [V61NullableDerivationContext.yield_plug]
    simp only [leaf, V61NullableDerivationTree.yield, List.length_append,
      List.length_singleton]
    unfold short at hMat ⊢
    unfold V61NullableDerivationContext.terminalMaterialLength at hMat
    omega

end FixedHCFG
end LeanCfgProject
