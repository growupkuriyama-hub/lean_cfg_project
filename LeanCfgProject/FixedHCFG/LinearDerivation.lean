import Mathlib.Data.List.Nodup
import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.LinearSpine

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Strict-linear derivations for Section 7 of the TCS manuscript.

This file isolates exactly the post-refinement grammar shape used in Section 7:
non-start rules are `X → aY`, `X → Ya`, or `X → a`.  The monoid typing has
already been enforced when the retained typed states and rules are extracted,
so the cycle-deletion and length arguments below depend only on this strict
linear rule shape.
-/

/-- The retained strict-linear grammar underlying the typed grammar `H`. -/
structure StrictLinearGrammar (W : Type v) (Sigma : Type u) where
  leftRule : W → Sigma → W → Prop
  rightRule : W → W → Sigma → Prop
  terminalRule : W → Sigma → Prop
  startState : W → Prop
  hasEpsilon : Prop

/-- Terminal derivations in a strict-linear grammar. -/
inductive LinearDerives {W : Type v} {Sigma : Type u}
    (G : StrictLinearGrammar W Sigma) : W → Word Sigma → Prop
  | terminal {X : W} {a : Sigma}
      (hrule : G.terminalRule X a) :
      LinearDerives G X [a]
  | left {X Y : W} {a : Sigma} {w : Word Sigma}
      (hrule : G.leftRule X a Y)
      (child : LinearDerives G Y w) :
      LinearDerives G X (a :: w)
  | right {X Y : W} {a : Sigma} {w : Word Sigma}
      (hrule : G.rightRule X Y a)
      (child : LinearDerives G Y w) :
      LinearDerives G X (w ++ [a])

namespace LinearDerives

/-- The unique nonterminal spine of a strict-linear terminal derivation. -/
def spine {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X : W} {w : Word Sigma}
    (d : LinearDerives G X w) : List W :=
  match d with
  | .terminal _ => [X]
  | .left _ child => X :: spine child
  | .right _ child => X :: spine child

/-- Each spine state contributes exactly one terminal to the final yield. -/
theorem yield_length_eq_spine_length
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X : W} {w : Word Sigma}
    (d : LinearDerives G X w) :
    w.length = (spine d).length := by
  induction d with
  | terminal hrule => rfl
  | left hrule child ih =>
      simp only [List.length_cons, spine]
      omega
  | right hrule child ih =>
      simp only [List.length_append, List.length_singleton, spine, List.length_cons]
      omega

/--
If a state occurs on the spine, the suffix beginning at that occurrence is
itself a terminal derivation from that state.  Its yield cannot be longer than
the yield of the whole derivation.
-/
theorem suffix_of_mem_spine
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X Z : W} {w : Word Sigma}
    (d : LinearDerives G X w)
    (hZ : Z ∈ spine d) :
    ∃ z : Word Sigma, LinearDerives G Z z ∧ z.length ≤ w.length := by
  induction d with
  | @terminal X a hrule =>
      simp only [spine, List.mem_singleton] at hZ
      subst Z
      exact ⟨[a], LinearDerives.terminal hrule, le_rfl⟩
  | @left X Y a w hrule child ih =>
      simp only [spine, List.mem_cons] at hZ
      rcases hZ with hZX | hZ
      · subst Z
        exact ⟨a :: w, LinearDerives.left hrule child, le_rfl⟩
      · obtain ⟨z, hz, hlen⟩ := ih hZ
        refine ⟨z, hz, ?_⟩
        simp only [List.length_cons]
        omega
  | @right X Y a w hrule child ih =>
      simp only [spine, List.mem_cons] at hZ
      rcases hZ with hZX | hZ
      · subst Z
        exact ⟨w ++ [a], LinearDerives.right hrule child, le_rfl⟩
      · obtain ⟨z, hz, hlen⟩ := ih hZ
        refine ⟨z, hz, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega

/--
Derivation-level cycle deletion (Lemma 7.3 / Remark 7.4 consequence): if the
spine repeats a state, there is another terminal derivation from the same root
with strictly shorter yield.  The new yield need not equal the old yield.
-/
theorem exists_shorter_of_spine_not_nodup
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X : W} {w : Word Sigma}
    (d : LinearDerives G X w)
    (hdup : ¬(spine d).Nodup) :
    ∃ z : Word Sigma, LinearDerives G X z ∧ z.length < w.length := by
  induction d with
  | @terminal X a hrule =>
      exact (hdup (List.nodup_singleton X)).elim
  | @left X Y a w hrule child ih =>
      have hdupCons : ¬(X :: spine child).Nodup := by
        simpa only [spine] using hdup
      by_cases hmem : X ∈ spine child
      · obtain ⟨z, hz, hlen⟩ := suffix_of_mem_spine child hmem
        refine ⟨z, hz, ?_⟩
        simp only [List.length_cons]
        omega
      · have hChildDup : ¬(spine child).Nodup := by
          intro hnd
          exact hdupCons (hnd.cons hmem)
        obtain ⟨z, hz, hshort⟩ := ih hChildDup
        refine ⟨a :: z, LinearDerives.left hrule hz, ?_⟩
        simp only [List.length_cons]
        omega
  | @right X Y a w hrule child ih =>
      have hdupCons : ¬(X :: spine child).Nodup := by
        simpa only [spine] using hdup
      by_cases hmem : X ∈ spine child
      · obtain ⟨z, hz, hlen⟩ := suffix_of_mem_spine child hmem
        refine ⟨z, hz, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · have hChildDup : ¬(spine child).Nodup := by
          intro hnd
          exact hdupCons (hnd.cons hmem)
        obtain ⟨z, hz, hshort⟩ := ih hChildDup
        refine ⟨z ++ [a], LinearDerives.right hrule hz, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega

end LinearDerives

/-- A derivation whose yield has minimum possible length from its root state. -/
def LinearYieldMinimal
    {W : Type v} {Sigma : Type u}
    (G : StrictLinearGrammar W Sigma) (X : W) (w : Word Sigma) : Prop :=
  LinearDerives G X w ∧
    ∀ z : Word Sigma, LinearDerives G X z → w.length ≤ z.length

/-- Lemma 7.5: a minimum-length strict-linear derivation has a simple spine. -/
theorem lemma_7_5_minimal_spine_nodup
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X : W} {w : Word Sigma}
    (hmin : LinearYieldMinimal G X w) :
    (LinearDerives.spine hmin.1).Nodup := by
  by_contra hdup
  obtain ⟨z, hz, hshort⟩ :=
    LinearDerives.exists_shorter_of_spine_not_nodup hmin.1 hdup
  exact (Nat.not_lt_of_ge (hmin.2 z hz)) hshort

/-- Lemma 7.5: every minimum-length yield has length at most `|W|`. -/
theorem lemma_7_5_minimal_yield_length_le
    {W : Type v} {Sigma : Type u} [Fintype W]
    {G : StrictLinearGrammar W Sigma} {X : W} {w : Word Sigma}
    (hmin : LinearYieldMinimal G X w) :
    w.length ≤ Fintype.card W := by
  have hSimple := lemma_7_5_minimal_spine_nodup hmin
  rw [LinearDerives.yield_length_eq_spine_length hmin.1]
  exact hSimple.length_le_card

/-- Reachable occurrence of a state, recording its two-sided terminal context. -/
inductive LinearOccurs {W : Type v} {Sigma : Type u}
    (G : StrictLinearGrammar W Sigma) : W → Word Sigma → Word Sigma → Prop
  | start {X : W}
      (hstart : G.startState X) :
      LinearOccurs G X [] []
  | left {X Y : W} {a : Sigma} {u v : Word Sigma}
      (parent : LinearOccurs G X u v)
      (hrule : G.leftRule X a Y) :
      LinearOccurs G Y (u ++ [a]) v
  | right {X Y : W} {a : Sigma} {u v : Word Sigma}
      (parent : LinearOccurs G X u v)
      (hrule : G.rightRule X Y a) :
      LinearOccurs G Y u ([a] ++ v)

namespace LinearOccurs

/-- The unique start-to-occurrence spine. -/
def spine {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X : W} {u v : Word Sigma}
    (d : LinearOccurs G X u v) : List W :=
  match d with
  | .start _ => [X]
  | .left parent _ => (spine parent).concat X
  | .right parent _ => (spine parent).concat X

/-- Number of strict-linear steps below the start rule. -/
def depth {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X : W} {u v : Word Sigma}
    (d : LinearOccurs G X u v) : Nat :=
  match d with
  | .start _ => 0
  | .left parent _ => depth parent + 1
  | .right parent _ => depth parent + 1

/-- The external context contains exactly one terminal per spine step. -/
theorem context_length_eq_depth
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X : W} {u v : Word Sigma}
    (d : LinearOccurs G X u v) :
    u.length + v.length = depth d := by
  induction d with
  | start hstart => rfl
  | left parent hrule ih =>
      simp only [List.length_append, List.length_singleton, depth]
      omega
  | right parent hrule ih =>
      simp only [List.length_append, List.length_singleton, depth]
      omega

/-- The occurrence spine has one more state than its number of steps. -/
theorem spine_length_eq_depth_succ
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X : W} {u v : Word Sigma}
    (d : LinearOccurs G X u v) :
    (spine d).length = depth d + 1 := by
  induction d with
  | start hstart => rfl
  | left parent hrule ih =>
      simp only [spine, List.length_concat, depth]
      omega
  | right parent hrule ih =>
      simp only [spine, List.length_concat, depth]
      omega

/--
An earlier state on the occurrence spine is itself reachable with context no
longer than the context of the final state.
-/
theorem prefix_of_mem_spine
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X Z : W} {u v : Word Sigma}
    (d : LinearOccurs G X u v)
    (hZ : Z ∈ spine d) :
    ∃ u' v' : Word Sigma,
      LinearOccurs G Z u' v' ∧
        u'.length + v'.length ≤ u.length + v.length := by
  induction d with
  | @start X hstart =>
      simp only [spine, List.mem_singleton] at hZ
      subst Z
      exact ⟨[], [], LinearOccurs.start hstart, le_rfl⟩
  | @left X Y a u v parent hrule ih =>
      simp only [spine, List.mem_concat] at hZ
      rcases hZ with hZ | hZY
      · obtain ⟨u', v', hocc, hlen⟩ := ih hZ
        refine ⟨u', v', hocc, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · subst Z
        exact ⟨u ++ [a], v, LinearOccurs.left parent hrule, le_rfl⟩
  | @right X Y a u v parent hrule ih =>
      simp only [spine, List.mem_concat] at hZ
      rcases hZ with hZ | hZY
      · obtain ⟨u', v', hocc, hlen⟩ := ih hZ
        refine ⟨u', v', hocc, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · subst Z
        exact ⟨u, [a] ++ v, LinearOccurs.right parent hrule, le_rfl⟩

/--
Occurrence-level cycle deletion: a repeated state on a start-to-state spine can
be removed while preserving the final state and strictly shortening its outer
context.
-/
theorem exists_shorter_context_of_spine_not_nodup
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X : W} {u v : Word Sigma}
    (d : LinearOccurs G X u v)
    (hdup : ¬(spine d).Nodup) :
    ∃ u' v' : Word Sigma,
      LinearOccurs G X u' v' ∧
        u'.length + v'.length < u.length + v.length := by
  induction d with
  | @start X hstart =>
      exact (hdup (List.nodup_singleton X)).elim
  | @left X Y a u v parent hrule ih =>
      have hdupConcat : ¬(spine parent).concat Y |>.Nodup := by
        simpa only [spine] using hdup
      by_cases hmem : Y ∈ spine parent
      · obtain ⟨u', v', hocc, hlen⟩ := prefix_of_mem_spine parent hmem
        refine ⟨u', v', hocc, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · have hParentDup : ¬(spine parent).Nodup := by
          intro hnd
          exact hdupConcat ((List.nodup_concat _ _).2 ⟨hmem, hnd⟩)
        obtain ⟨u', v', hocc, hshort⟩ := ih hParentDup
        refine ⟨u' ++ [a], v', LinearOccurs.left hocc hrule, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega
  | @right X Y a u v parent hrule ih =>
      have hdupConcat : ¬(spine parent).concat Y |>.Nodup := by
        simpa only [spine] using hdup
      by_cases hmem : Y ∈ spine parent
      · obtain ⟨u', v', hocc, hlen⟩ := prefix_of_mem_spine parent hmem
        refine ⟨u', v', hocc, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · have hParentDup : ¬(spine parent).Nodup := by
          intro hnd
          exact hdupConcat ((List.nodup_concat _ _).2 ⟨hmem, hnd⟩)
        obtain ⟨u', v', hocc, hshort⟩ := ih hParentDup
        refine ⟨u', [a] ++ v', LinearOccurs.right hocc hrule, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega

end LinearOccurs

/-- A reachable context of minimum total length for a fixed retained state. -/
def LinearContextMinimal
    {W : Type v} {Sigma : Type u}
    (G : StrictLinearGrammar W Sigma) (X : W)
    (u v : Word Sigma) : Prop :=
  LinearOccurs G X u v ∧
    ∀ u' v' : Word Sigma,
      LinearOccurs G X u' v' →
        u.length + v.length ≤ u'.length + v'.length

/-- Lemma 7.6: a minimum-length occurrence context has a simple spine. -/
theorem lemma_7_6_minimal_context_spine_nodup
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X : W} {u v : Word Sigma}
    (hmin : LinearContextMinimal G X u v) :
    (LinearOccurs.spine hmin.1).Nodup := by
  by_contra hdup
  obtain ⟨u', v', hocc, hshort⟩ :=
    LinearOccurs.exists_shorter_context_of_spine_not_nodup hmin.1 hdup
  exact (Nat.not_lt_of_ge (hmin.2 u' v' hocc)) hshort

/-- Lemma 7.6: the canonical minimum context has length at most `|W|-1`. -/
theorem lemma_7_6_minimal_context_length_le
    {W : Type v} {Sigma : Type u} [Fintype W]
    {G : StrictLinearGrammar W Sigma} {X : W} {u v : Word Sigma}
    (hmin : LinearContextMinimal G X u v) :
    u.length + v.length ≤ Fintype.card W - 1 := by
  have hSimple := lemma_7_6_minimal_context_spine_nodup hmin
  have hCard : (LinearOccurs.spine hmin.1).length ≤ Fintype.card W :=
    hSimple.length_le_card
  have hCtx := LinearOccurs.context_length_eq_depth hmin.1
  have hSpine := LinearOccurs.spine_length_eq_depth_succ hmin.1
  omega

end FixedHCFG
end LeanCfgProject
