import Mathlib.Data.List.Nodup
import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60WitnessBounds

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Exact-v60 dependency-spine machinery for the context part of the fixed-window
argument.

A canonical occurrence spine follows the retained typed dependency path and
expands every off-path sibling by its canonical yield `omega`.  Finite-state
cycle deletion then gives a simple spine.  Consequently, any uniform bound on
canonical sibling yields automatically gives a bounded successful context.
This discharges the graph-theoretic part of manuscript Lemma `window-context`;
only the fixed-window derivation-tree bound for the yields themselves remains
special to `h_{k,l}`.
-/

/--
A successful occurrence whose off-spine siblings have already been replaced
by their canonical yields.
-/
inductive V60CanonicalOccursSpine
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N) :
    V60KeptState Obs terminal binary start →
      List (V60KeptState Obs terminal binary start) →
      Word Sigma → Word Sigma → Prop
  | start {X : V60KeptState Obs terminal binary start}
      (hstart : V60KeptStart X) :
      V60CanonicalOccursSpine Obs terminal binary start X [X] [] []
  | left {X Y Z : V60KeptState Obs terminal binary start}
      {sp : List (V60KeptState Obs terminal binary start)}
      {u v : Word Sigma}
      (parent : V60CanonicalOccursSpine Obs terminal binary start X sp u v)
      (hrule : V60KeptBinary X Y Z) :
      V60CanonicalOccursSpine Obs terminal binary start Y (sp.concat Y)
        u (v60CanonicalOmega Z ++ v)
  | right {X Y Z : V60KeptState Obs terminal binary start}
      {sp : List (V60KeptState Obs terminal binary start)}
      {u v : Word Sigma}
      (parent : V60CanonicalOccursSpine Obs terminal binary start X sp u v)
      (hrule : V60KeptBinary X Y Z) :
      V60CanonicalOccursSpine Obs terminal binary start Z (sp.concat Z)
        (u ++ v60CanonicalOmega Y) v

namespace V60CanonicalOccursSpine

/-- Forgetting the spine gives an ordinary successful typed occurrence. -/
theorem toTypedOccurs
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    {X : V60KeptState Obs terminal binary start}
    {sp : List (V60KeptState Obs terminal binary start)}
    {u v : Word Sigma}
    (d : V60CanonicalOccursSpine Obs terminal binary start X sp u v) :
    V60TypedOccurs Obs terminal binary start X.1 u v := by
  induction d with
  | start hstart =>
      exact v60_kept_start_occurs_empty Obs terminal binary start _ hstart
  | @left X Y Z sp u v parent hrule ih =>
      exact V60TypedOccurs.left ih hrule.1 hrule.2
        (v60CanonicalOmega_spec Z)
  | @right X Y Z sp u v parent hrule ih =>
      exact V60TypedOccurs.right ih hrule.1 hrule.2
        (v60CanonicalOmega_spec Y)

/--
Every ordinary successful occurrence of a productive state can be converted
into one whose sibling subtrees use canonical yields.
-/
theorem exists_canonical_spine_of_typed_occurs
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    {X : V60TypedNT N Obs} {u v : Word Sigma}
    (hOcc : V60TypedOccurs Obs terminal binary start X u v)
    (hKeep : V60TypedKept Obs terminal binary start X) :
    ∃ (sp : List (V60KeptState Obs terminal binary start))
      (u' v' : Word Sigma),
      V60CanonicalOccursSpine Obs terminal binary start
        (⟨X, hKeep⟩ : V60KeptState Obs terminal binary start) sp u' v' := by
  induction hOcc generalizing hKeep with
  | @start A p hStart =>
      let X0 : V60KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := p }, hKeep⟩
      exact ⟨[X0], [], [], V60CanonicalOccursSpine.start hStart⟩
  | @left A B C p q r u v y parent hrule hproduct rightDeriv ih =>
      rcases hKeep.1 with ⟨x, leftDeriv⟩
      have hParentKeep : V60TypedKept Obs terminal binary start
          { label := A, yieldType := p } := by
        constructor
        · exact ⟨x ++ y,
            V60YieldTypedDerives.binary hrule hproduct leftDeriv rightDeriv⟩
        · exact ⟨u, v, parent⟩
      have hRightKeep : V60TypedKept Obs terminal binary start
          { label := C, yieldType := r } := by
        constructor
        · exact ⟨y, rightDeriv⟩
        · exact ⟨u ++ x, v,
            V60TypedOccurs.right parent hrule hproduct leftDeriv⟩
      obtain ⟨sp, u', v', hsp⟩ := ih hParentKeep
      let PX : V60KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := p }, hParentKeep⟩
      let YX : V60KeptState Obs terminal binary start :=
        ⟨{ label := B, yieldType := q }, hKeep⟩
      let ZX : V60KeptState Obs terminal binary start :=
        ⟨{ label := C, yieldType := r }, hRightKeep⟩
      have hRule : V60KeptBinary PX YX ZX := by
        exact ⟨hrule, hproduct⟩
      refine ⟨sp.concat YX, u', v60CanonicalOmega ZX ++ v', ?_⟩
      simpa [PX, YX, ZX] using
        (V60CanonicalOccursSpine.left hsp hRule)
  | @right A B C p q r u v x parent hrule hproduct leftDeriv ih =>
      rcases hKeep.1 with ⟨y, rightDeriv⟩
      have hParentKeep : V60TypedKept Obs terminal binary start
          { label := A, yieldType := p } := by
        constructor
        · exact ⟨x ++ y,
            V60YieldTypedDerives.binary hrule hproduct leftDeriv rightDeriv⟩
        · exact ⟨u, v, parent⟩
      have hLeftKeep : V60TypedKept Obs terminal binary start
          { label := B, yieldType := q } := by
        constructor
        · exact ⟨x, leftDeriv⟩
        · exact ⟨u, y ++ v,
            V60TypedOccurs.left parent hrule hproduct rightDeriv⟩
      obtain ⟨sp, u', v', hsp⟩ := ih hParentKeep
      let PX : V60KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := p }, hParentKeep⟩
      let YX : V60KeptState Obs terminal binary start :=
        ⟨{ label := B, yieldType := q }, hLeftKeep⟩
      let ZX : V60KeptState Obs terminal binary start :=
        ⟨{ label := C, yieldType := r }, hKeep⟩
      have hRule : V60KeptBinary PX YX ZX := by
        exact ⟨hrule, hproduct⟩
      refine ⟨sp.concat ZX, u' ++ v60CanonicalOmega YX, v', ?_⟩
      simpa [PX, YX, ZX] using
        (V60CanonicalOccursSpine.right hsp hRule)

/-- Any state occurring on a canonical spine is itself reachable by a prefix. -/
theorem prefix_of_mem_spine
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    {X Z : V60KeptState Obs terminal binary start}
    {sp : List (V60KeptState Obs terminal binary start)}
    {u v : Word Sigma}
    (d : V60CanonicalOccursSpine Obs terminal binary start X sp u v)
    (hZ : Z ∈ sp) :
    ∃ (sp' : List (V60KeptState Obs terminal binary start))
      (u' v' : Word Sigma),
      V60CanonicalOccursSpine Obs terminal binary start Z sp' u' v' ∧
        sp'.length ≤ sp.length := by
  induction d with
  | @start X hstart =>
      simp only [List.mem_singleton] at hZ
      subst Z
      exact ⟨[X], [], [], V60CanonicalOccursSpine.start hstart, le_rfl⟩
  | @left X Y Z0 sp u v parent hrule ih =>
      rw [List.concat_eq_append] at hZ
      rcases List.mem_append.mp hZ with hZ | hZY
      · obtain ⟨sp', u', v', hpre, hlen⟩ := ih hZ
        refine ⟨sp', u', v', hpre, ?_⟩
        simp only [List.length_concat]
        omega
      · have hEq : Z = Y := List.mem_singleton.mp hZY
        subst Z
        exact ⟨sp.concat Y, u, v60CanonicalOmega Z0 ++ v,
          V60CanonicalOccursSpine.left parent hrule, le_rfl⟩
  | @right X Y0 Z sp u v parent hrule ih =>
      rw [List.concat_eq_append] at hZ
      rcases List.mem_append.mp hZ with hZ | hZZ
      · obtain ⟨sp', u', v', hpre, hlen⟩ := ih hZ
        refine ⟨sp', u', v', hpre, ?_⟩
        simp only [List.length_concat]
        omega
      · have hEq : Z = Z := List.mem_singleton.mp hZZ
        exact ⟨sp.concat Z, u ++ v60CanonicalOmega Y0, v,
          V60CanonicalOccursSpine.right parent hrule, le_rfl⟩

/-- A repeated retained typed state can be deleted from a canonical spine. -/
theorem exists_shorter_spine_of_not_nodup
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    {X : V60KeptState Obs terminal binary start}
    {sp : List (V60KeptState Obs terminal binary start)}
    {u v : Word Sigma}
    (d : V60CanonicalOccursSpine Obs terminal binary start X sp u v)
    (hdup : ¬ sp.Nodup) :
    ∃ (sp' : List (V60KeptState Obs terminal binary start))
      (u' v' : Word Sigma),
      V60CanonicalOccursSpine Obs terminal binary start X sp' u' v' ∧
        sp'.length < sp.length := by
  induction d with
  | @start X hstart =>
      exact (hdup (List.nodup_singleton X)).elim
  | @left X Y Z sp u v parent hrule ih =>
      by_cases hmem : Y ∈ sp
      · obtain ⟨sp', u', v', hpre, hlen⟩ := prefix_of_mem_spine parent hmem
        refine ⟨sp', u', v', hpre, ?_⟩
        simp only [List.length_concat]
        omega
      · have hParentDup : ¬ sp.Nodup := by
          intro hnd
          exact hdup ((List.nodup_concat _ _).mpr ⟨hmem, hnd⟩)
        obtain ⟨sp', u', v', hshort, hlen⟩ := ih hParentDup
        refine ⟨sp'.concat Y, u', v60CanonicalOmega Z ++ v',
          V60CanonicalOccursSpine.left hshort hrule, ?_⟩
        simp only [List.length_concat]
        omega
  | @right X Y Z sp u v parent hrule ih =>
      by_cases hmem : Z ∈ sp
      · obtain ⟨sp', u', v', hpre, hlen⟩ := prefix_of_mem_spine parent hmem
        refine ⟨sp', u', v', hpre, ?_⟩
        simp only [List.length_concat]
        omega
      · have hParentDup : ¬ sp.Nodup := by
          intro hnd
          exact hdup ((List.nodup_concat _ _).mpr ⟨hmem, hnd⟩)
        obtain ⟨sp', u', v', hshort, hlen⟩ := ih hParentDup
        refine ⟨sp'.concat Z, u' ++ v60CanonicalOmega Y, v',
          V60CanonicalOccursSpine.right hshort hrule, ?_⟩
        simp only [List.length_concat]
        omega

/-- Every canonical occurrence admits a simple (cycle-free) retained-state spine. -/
theorem exists_nodup_spine
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    {X : V60KeptState Obs terminal binary start}
    {sp : List (V60KeptState Obs terminal binary start)}
    {u v : Word Sigma}
    (d : V60CanonicalOccursSpine Obs terminal binary start X sp u v) :
    ∃ (sp' : List (V60KeptState Obs terminal binary start))
      (u' v' : Word Sigma),
      V60CanonicalOccursSpine Obs terminal binary start X sp' u' v' ∧
        sp'.Nodup := by
  let P : Nat → Prop := fun n =>
    ∃ (sp' : List (V60KeptState Obs terminal binary start))
      (u' v' : Word Sigma),
      V60CanonicalOccursSpine Obs terminal binary start X sp' u' v' ∧
        sp'.length = n
  have hP : ∃ n, P n := ⟨sp.length, sp, u, v, d, rfl⟩
  obtain ⟨sp0, u0, v0, d0, hlen0⟩ := Nat.find_spec hP
  refine ⟨sp0, u0, v0, d0, ?_⟩
  by_contra hdup
  obtain ⟨sp1, u1, v1, d1, hshort⟩ :=
    exists_shorter_spine_of_not_nodup d0 hdup
  have hP1 : P sp1.length := ⟨sp1, u1, v1, d1, rfl⟩
  have hmin : Nat.find hP ≤ sp1.length := Nat.find_min' hP hP1
  rw [hlen0] at hshort
  omega

/--
If every canonical sibling yield has length at most `B`, a canonical occurrence
context costs at most one `B` per state on its spine.
-/
theorem context_length_le_spine_mul
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    {X : V60KeptState Obs terminal binary start}
    {sp : List (V60KeptState Obs terminal binary start)}
    {u v : Word Sigma} {B : Nat}
    (d : V60CanonicalOccursSpine Obs terminal binary start X sp u v)
    (hOmega : ∀ Y : V60KeptState Obs terminal binary start,
      (v60CanonicalOmega Y).length ≤ B) :
    u.length + v.length ≤ sp.length * B := by
  induction d with
  | start hstart => simp
  | @left X Y Z sp u v parent hrule ih =>
      have hz := hOmega Z
      simp only [List.length_append, List.length_concat]
      rw [Nat.add_mul]
      omega
  | @right X Y Z sp u v parent hrule ih =>
      have hy := hOmega Y
      simp only [List.length_append, List.length_concat]
      rw [Nat.add_mul]
      omega

end V60CanonicalOccursSpine

/--
Generic finite-state form of the shortest dependency-path argument: a uniform
canonical-yield bound `B` gives every retained typed state a successful context
of length at most `N_t * B`, where `N_t` is the number of retained typed states.
-/
theorem v60_exists_short_context_of_canonical_yield_bound
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    [Finite N]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (B : Nat)
    (hOmega : ∀ Y : V60KeptState Obs terminal binary start,
      (v60CanonicalOmega Y).length ≤ B)
    (X : V60KeptState Obs terminal binary start) :
    ∃ u v : Word Sigma,
      V60TypedOccurs Obs terminal binary start X.1 u v ∧
        u.length + v.length ≤
          Fintype.card (V60KeptState Obs terminal binary start) * B := by
  letI : Fintype (V60KeptState Obs terminal binary start) :=
    Fintype.ofFinite _
  rcases X.property.2 with ⟨u0, v0, hOcc⟩
  obtain ⟨sp0, u1, v1, d0⟩ :=
    V60CanonicalOccursSpine.exists_canonical_spine_of_typed_occurs
      Obs terminal binary start hOcc X.property
  obtain ⟨sp, u, v, d, hnd⟩ :=
    V60CanonicalOccursSpine.exists_nodup_spine d0
  have hPath : sp.length ≤
      Fintype.card (V60KeptState Obs terminal binary start) :=
    hnd.length_le_card
  have hCtx : u.length + v.length ≤ sp.length * B :=
    V60CanonicalOccursSpine.context_length_le_spine_mul d hOmega
  have hMul : sp.length * B ≤
      Fintype.card (V60KeptState Obs terminal binary start) * B :=
    Nat.mul_le_mul_right B hPath
  exact ⟨u, v, V60CanonicalOccursSpine.toTypedOccurs d,
    le_trans hCtx hMul⟩

end FixedHCFG
end LeanCfgProject
