import Mathlib.Data.List.Nodup
import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.LinearSpine

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Strict-linear derivations for Section 7 of the TCS manuscript.

The spine is carried as an explicit index of each derivation proposition.  This
avoids eliminating proof objects into data while still exposing exactly the
finite path on which Lemmas 7.3, 7.5, and 7.6 operate.
-/

/-- The retained strict-linear grammar underlying the typed grammar `H`. -/
structure StrictLinearGrammar (W : Type v) (Sigma : Type u) where
  leftRule : W → Sigma → W → Prop
  rightRule : W → W → Sigma → Prop
  terminalRule : W → Sigma → Prop
  startState : W → Prop
  hasEpsilon : Prop

/-- Terminal derivations together with their unique nonterminal spine. -/
inductive LinearDerivesSpine {W : Type v} {Sigma : Type u}
    (G : StrictLinearGrammar W Sigma) : W → List W → Word Sigma → Prop
  | terminal {X : W} {a : Sigma}
      (hrule : G.terminalRule X a) :
      LinearDerivesSpine G X [X] [a]
  | left {X Y : W} {a : Sigma} {sp : List W} {w : Word Sigma}
      (hrule : G.leftRule X a Y)
      (child : LinearDerivesSpine G Y sp w) :
      LinearDerivesSpine G X (X :: sp) (a :: w)
  | right {X Y : W} {a : Sigma} {sp : List W} {w : Word Sigma}
      (hrule : G.rightRule X Y a)
      (child : LinearDerivesSpine G Y sp w) :
      LinearDerivesSpine G X (X :: sp) (w ++ [a])

/-- Ordinary derivability forgets the explicit spine index. -/
def LinearDerives {W : Type v} {Sigma : Type u}
    (G : StrictLinearGrammar W Sigma) (X : W) (w : Word Sigma) : Prop :=
  ∃ sp : List W, LinearDerivesSpine G X sp w

namespace LinearDerivesSpine

/-- Each spine state contributes exactly one terminal to the final yield. -/
theorem yield_length_eq_spine_length
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X : W} {sp : List W} {w : Word Sigma}
    (d : LinearDerivesSpine G X sp w) :
    w.length = sp.length := by
  induction d with
  | terminal hrule => rfl
  | left hrule child ih => simp [ih]
  | right hrule child ih => simp [ih]

/--
If a state occurs on the spine, the suffix beginning at that occurrence is
itself a terminal derivation from that state.  Its yield is no longer than the
original yield.
-/
theorem suffix_of_mem_spine
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X Z : W}
    {sp : List W} {w : Word Sigma}
    (d : LinearDerivesSpine G X sp w)
    (hZ : Z ∈ sp) :
    ∃ sp' : List W, ∃ z : Word Sigma,
      LinearDerivesSpine G Z sp' z ∧ z.length ≤ w.length := by
  induction d with
  | @terminal X a hrule =>
      simp only [List.mem_singleton] at hZ
      subst Z
      exact ⟨[X], [a], LinearDerivesSpine.terminal hrule, le_rfl⟩
  | @left X Y a sp w hrule child ih =>
      rcases List.mem_cons.mp hZ with hZX | hZ
      · subst Z
        exact ⟨X :: sp, a :: w, LinearDerivesSpine.left hrule child, le_rfl⟩
      · obtain ⟨sp', z, hz, hlen⟩ := ih hZ
        refine ⟨sp', z, hz, ?_⟩
        simp only [List.length_cons]
        omega
  | @right X Y a sp w hrule child ih =>
      rcases List.mem_cons.mp hZ with hZX | hZ
      · subst Z
        exact ⟨X :: sp, w ++ [a], LinearDerivesSpine.right hrule child, le_rfl⟩
      · obtain ⟨sp', z, hz, hlen⟩ := ih hZ
        refine ⟨sp', z, hz, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega

/--
Derivation-level Lemma 7.3: a repeated state on a strict-linear terminal spine
can be deleted, producing another derivation from the same root with strictly
shorter yield.  As in the manuscript, the new yield need not equal the old one.
-/
theorem exists_shorter_of_spine_not_nodup
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X : W}
    {sp : List W} {w : Word Sigma}
    (d : LinearDerivesSpine G X sp w)
    (hdup : ¬ sp.Nodup) :
    ∃ sp' : List W, ∃ z : Word Sigma,
      LinearDerivesSpine G X sp' z ∧ z.length < w.length := by
  induction d with
  | @terminal X a hrule =>
      exact (hdup (List.nodup_singleton X)).elim
  | @left X Y a sp w hrule child ih =>
      by_cases hmem : X ∈ sp
      · obtain ⟨sp', z, hz, hlen⟩ := suffix_of_mem_spine child hmem
        refine ⟨sp', z, hz, ?_⟩
        simp only [List.length_cons]
        omega
      · have hChildDup : ¬ sp.Nodup := by
          intro hnd
          exact hdup (List.nodup_cons.mpr ⟨hmem, hnd⟩)
        obtain ⟨sp', z, hz, hshort⟩ := ih hChildDup
        refine ⟨X :: sp', a :: z, LinearDerivesSpine.left hrule hz, ?_⟩
        simp only [List.length_cons]
        omega
  | @right X Y a sp w hrule child ih =>
      by_cases hmem : X ∈ sp
      · obtain ⟨sp', z, hz, hlen⟩ := suffix_of_mem_spine child hmem
        refine ⟨sp', z, hz, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · have hChildDup : ¬ sp.Nodup := by
          intro hnd
          exact hdup (List.nodup_cons.mpr ⟨hmem, hnd⟩)
        obtain ⟨sp', z, hz, hshort⟩ := ih hChildDup
        refine ⟨X :: sp', z ++ [a], LinearDerivesSpine.right hrule hz, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega

end LinearDerivesSpine

/-- A derivable word having minimum possible length from a fixed root state. -/
def LinearYieldMinimal
    {W : Type v} {Sigma : Type u}
    (G : StrictLinearGrammar W Sigma) (X : W) (w : Word Sigma) : Prop :=
  LinearDerives G X w ∧
    ∀ z : Word Sigma, LinearDerives G X z → w.length ≤ z.length

/-- Lemma 7.5: a minimum-length strict-linear derivation has a simple spine. -/
theorem lemma_7_5_minimal_has_simple_spine
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X : W} {w : Word Sigma}
    (hmin : LinearYieldMinimal G X w) :
    ∃ sp : List W, LinearDerivesSpine G X sp w ∧ sp.Nodup := by
  rcases hmin.1 with ⟨sp, d⟩
  refine ⟨sp, d, ?_⟩
  by_contra hdup
  obtain ⟨sp', z, hz, hshort⟩ :=
    LinearDerivesSpine.exists_shorter_of_spine_not_nodup d hdup
  have hge := hmin.2 z ⟨sp', hz⟩
  exact (Nat.not_lt_of_ge hge) hshort

/-- Lemma 7.5: every minimum-length yield has length at most `|W|`. -/
theorem lemma_7_5_minimal_yield_length_le
    {W : Type v} {Sigma : Type u} [Fintype W]
    {G : StrictLinearGrammar W Sigma} {X : W} {w : Word Sigma}
    (hmin : LinearYieldMinimal G X w) :
    w.length ≤ Fintype.card W := by
  obtain ⟨sp, d, hSimple⟩ := lemma_7_5_minimal_has_simple_spine hmin
  rw [LinearDerivesSpine.yield_length_eq_spine_length d]
  exact hSimple.length_le_card

/-- Reachable occurrence of a state with an explicit start-to-state spine. -/
inductive LinearOccursSpine {W : Type v} {Sigma : Type u}
    (G : StrictLinearGrammar W Sigma) : W → List W → Word Sigma → Word Sigma → Prop
  | start {X : W}
      (hstart : G.startState X) :
      LinearOccursSpine G X [X] [] []
  | left {X Y : W} {a : Sigma} {sp : List W} {u v : Word Sigma}
      (parent : LinearOccursSpine G X sp u v)
      (hrule : G.leftRule X a Y) :
      LinearOccursSpine G Y (sp.concat Y) (u ++ [a]) v
  | right {X Y : W} {a : Sigma} {sp : List W} {u v : Word Sigma}
      (parent : LinearOccursSpine G X sp u v)
      (hrule : G.rightRule X Y a) :
      LinearOccursSpine G Y (sp.concat Y) u ([a] ++ v)

/-- Ordinary occurrence forgets its explicit spine. -/
def LinearOccurs {W : Type v} {Sigma : Type u}
    (G : StrictLinearGrammar W Sigma) (X : W)
    (u v : Word Sigma) : Prop :=
  ∃ sp : List W, LinearOccursSpine G X sp u v

namespace LinearOccursSpine

/-- A strict-linear occurrence has one terminal of outer context per spine edge. -/
theorem context_succ_eq_spine_length
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X : W}
    {sp : List W} {u v : Word Sigma}
    (d : LinearOccursSpine G X sp u v) :
    u.length + v.length + 1 = sp.length := by
  induction d with
  | start hstart => rfl
  | left parent hrule ih =>
      simp only [List.length_append, List.length_singleton, List.length_concat]
      omega
  | right parent hrule ih =>
      simp only [List.length_append, List.length_singleton, List.length_concat]
      omega

/--
An earlier state on an occurrence spine is itself reachable with no longer an
outer context than the final state.
-/
theorem prefix_of_mem_spine
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X Z : W}
    {sp : List W} {u v : Word Sigma}
    (d : LinearOccursSpine G X sp u v)
    (hZ : Z ∈ sp) :
    ∃ sp' : List W, ∃ u' v' : Word Sigma,
      LinearOccursSpine G Z sp' u' v' ∧
        u'.length + v'.length ≤ u.length + v.length := by
  induction d with
  | @start X hstart =>
      simp only [List.mem_singleton] at hZ
      subst Z
      exact ⟨[X], [], [], LinearOccursSpine.start hstart, le_rfl⟩
  | @left X Y a sp u v parent hrule ih =>
      rw [List.concat_eq_append] at hZ
      rcases List.mem_append.mp hZ with hZ | hZY
      · obtain ⟨sp', u', v', hocc, hlen⟩ := ih hZ
        refine ⟨sp', u', v', hocc, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · have hEq : Z = Y := List.mem_singleton.mp hZY
        subst Z
        exact ⟨sp.concat Y, u ++ [a], v,
          LinearOccursSpine.left parent hrule, le_rfl⟩
  | @right X Y a sp u v parent hrule ih =>
      rw [List.concat_eq_append] at hZ
      rcases List.mem_append.mp hZ with hZ | hZY
      · obtain ⟨sp', u', v', hocc, hlen⟩ := ih hZ
        refine ⟨sp', u', v', hocc, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · have hEq : Z = Y := List.mem_singleton.mp hZY
        subst Z
        exact ⟨sp.concat Y, u, [a] ++ v,
          LinearOccursSpine.right parent hrule, le_rfl⟩

/--
Occurrence-level Lemma 7.3: a repeated state on the start-to-state spine can
be deleted while preserving the final state and strictly shortening its outer
context.
-/
theorem exists_shorter_context_of_spine_not_nodup
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X : W}
    {sp : List W} {u v : Word Sigma}
    (d : LinearOccursSpine G X sp u v)
    (hdup : ¬ sp.Nodup) :
    ∃ sp' : List W, ∃ u' v' : Word Sigma,
      LinearOccursSpine G X sp' u' v' ∧
        u'.length + v'.length < u.length + v.length := by
  induction d with
  | @start X hstart =>
      exact (hdup (List.nodup_singleton X)).elim
  | @left X Y a sp u v parent hrule ih =>
      by_cases hmem : Y ∈ sp
      · obtain ⟨sp', u', v', hocc, hlen⟩ := prefix_of_mem_spine parent hmem
        refine ⟨sp', u', v', hocc, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · have hParentDup : ¬ sp.Nodup := by
          intro hnd
          exact hdup ((List.nodup_concat _ _).mpr ⟨hmem, hnd⟩)
        obtain ⟨sp', u', v', hocc, hshort⟩ := ih hParentDup
        refine ⟨sp'.concat Y, u' ++ [a], v',
          LinearOccursSpine.left hocc hrule, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega
  | @right X Y a sp u v parent hrule ih =>
      by_cases hmem : Y ∈ sp
      · obtain ⟨sp', u', v', hocc, hlen⟩ := prefix_of_mem_spine parent hmem
        refine ⟨sp', u', v', hocc, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · have hParentDup : ¬ sp.Nodup := by
          intro hnd
          exact hdup ((List.nodup_concat _ _).mpr ⟨hmem, hnd⟩)
        obtain ⟨sp', u', v', hocc, hshort⟩ := ih hParentDup
        refine ⟨sp'.concat Y, u', [a] ++ v',
          LinearOccursSpine.right hocc hrule, ?_⟩
        simp only [List.length_append, List.length_singleton]
        omega

end LinearOccursSpine

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
theorem lemma_7_6_minimal_context_has_simple_spine
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X : W} {u v : Word Sigma}
    (hmin : LinearContextMinimal G X u v) :
    ∃ sp : List W, LinearOccursSpine G X sp u v ∧ sp.Nodup := by
  rcases hmin.1 with ⟨sp, d⟩
  refine ⟨sp, d, ?_⟩
  by_contra hdup
  obtain ⟨sp', u', v', hocc, hshort⟩ :=
    LinearOccursSpine.exists_shorter_context_of_spine_not_nodup d hdup
  have hge := hmin.2 u' v' ⟨sp', hocc⟩
  exact (Nat.not_lt_of_ge hge) hshort

/-- Lemma 7.6: the canonical minimum context has length at most `|W|-1`. -/
theorem lemma_7_6_minimal_context_length_le
    {W : Type v} {Sigma : Type u} [Fintype W]
    {G : StrictLinearGrammar W Sigma} {X : W} {u v : Word Sigma}
    (hmin : LinearContextMinimal G X u v) :
    u.length + v.length ≤ Fintype.card W - 1 := by
  obtain ⟨sp, d, hSimple⟩ := lemma_7_6_minimal_context_has_simple_spine hmin
  have hCard : sp.length ≤ Fintype.card W := hSimple.length_le_card
  have hLen := LinearOccursSpine.context_succ_eq_spine_length d
  omega

end FixedHCFG
end LeanCfgProject
