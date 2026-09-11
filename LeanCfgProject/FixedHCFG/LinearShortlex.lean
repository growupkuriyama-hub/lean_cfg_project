import LeanCfgProject.FixedHCFG.LinearDerivation
import LeanCfgProject.FixedHCFG.ShortlexWitness

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Manuscript-faithful shortlex bridge for the linear length bounds.

Section 4 orders context pairs lexicographically by shortlex on the left word
and then shortlex on the right word.  For Lemma 7.6 it is therefore not enough
to say that cycle deletion decreases total context length.  The lemmas below
prove the stronger fact actually needed: deleting a repeated strict-linear
spine segment produces a *lexicographically shortlex-smaller* context pair.
This yields the manuscript bound for the canonical `chi` order exactly as
stated in Section 4.
-/

/-- A shortlex-minimal terminal yield for a retained strict-linear state. -/
def LinearYieldShortlexMinimal
    {W : Type v} {Sigma : Type u} [LT Sigma]
    (G : StrictLinearGrammar W Sigma) (X : W) (w : Word Sigma) : Prop :=
  LinearDerives G X w ∧
    ∀ z : Word Sigma, LinearDerives G X z → ¬ WordShortlex z w

/-- Shortlex minimality implies minimum length. -/
theorem linearYieldShortlexMinimal_to_lengthMinimal
    {W : Type v} {Sigma : Type u} [LinearOrder Sigma]
    {G : StrictLinearGrammar W Sigma} {X : W} {w : Word Sigma}
    (hmin : LinearYieldShortlexMinimal G X w) :
    LinearYieldMinimal G X w := by
  refine ⟨hmin.1, ?_⟩
  intro z hz
  by_contra hnot
  have hlt : z.length < w.length := Nat.lt_of_not_ge hnot
  have hslex : WordShortlex z w := List.Shortlex.of_length_lt hlt
  exact hmin.2 z hz hslex

/-- Lemma 7.5 directly in the manuscript's shortlex formulation. -/
theorem lemma_7_5_shortlex_yield_length_le
    {W : Type v} {Sigma : Type u} [LinearOrder Sigma] [Fintype W]
    {G : StrictLinearGrammar W Sigma} {X : W} {w : Word Sigma}
    (hmin : LinearYieldShortlexMinimal G X w) :
    w.length ≤ Fintype.card W := by
  exact lemma_7_5_minimal_yield_length_le
    (linearYieldShortlexMinimal_to_lengthMinimal hmin)

namespace LinearOccursSpine

/--
If `Z` occurs earlier on an occurrence spine ending at `(u,v)`, then its
context `(u',v')` differs from the final context only by terminal material
added on the right of `u'` and on the left of `v'`.
-/
theorem earlier_context_factors
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} {X Z : W}
    {sp : List W} {u v : Word Sigma}
    (d : LinearOccursSpine G X sp u v)
    (hZ : Z ∈ sp) :
    ∃ sp' : List W, ∃ u' v' l r : Word Sigma,
      LinearOccursSpine G Z sp' u' v' ∧
        u = u' ++ l ∧ v = r ++ v' := by
  induction d with
  | @start X hstart =>
      simp only [List.mem_singleton] at hZ
      subst Z
      exact ⟨[X], [], [], [], [], LinearOccursSpine.start hstart, rfl, rfl⟩
  | @left X Y a sp u v parent hrule ih =>
      rw [List.concat_eq_append] at hZ
      rcases List.mem_append.mp hZ with hZ | hZY
      · obtain ⟨sp', u', v', l, r, hocc, hu, hv⟩ := ih hZ
        refine ⟨sp', u', v', l ++ [a], r, hocc, ?_, hv⟩
        rw [hu]
        simp only [List.append_assoc]
      · have hEq : Z = Y := List.mem_singleton.mp hZY
        subst Z
        exact ⟨sp.concat Y, u ++ [a], v, [], [],
          LinearOccursSpine.left parent hrule, by simp, by simp⟩
  | @right X Y a sp u v parent hrule ih =>
      rw [List.concat_eq_append] at hZ
      rcases List.mem_append.mp hZ with hZ | hZY
      · obtain ⟨sp', u', v', l, r, hocc, hu, hv⟩ := ih hZ
        refine ⟨sp', u', v', l, [a] ++ r, hocc, hu, ?_⟩
        rw [hv]
        simp only [List.append_assoc]
      · have hEq : Z = Y := List.mem_singleton.mp hZY
        subst Z
        exact ⟨sp.concat Y, u, [a] ++ v, [], [],
          LinearOccursSpine.right parent hrule, by simp, by simp⟩

/--
Strengthened cycle deletion for Lemma 7.6: the replacement occurrence is
smaller in the exact lexicographic-shortlex order used to define `chi`.
-/
theorem exists_contextShortlex_smaller_of_spine_not_nodup
    {W : Type v} {Sigma : Type u} [LinearOrder Sigma]
    {G : StrictLinearGrammar W Sigma} {X : W}
    {sp : List W} {u v : Word Sigma}
    (d : LinearOccursSpine G X sp u v)
    (hdup : ¬ sp.Nodup) :
    ∃ sp' : List W, ∃ u' v' : Word Sigma,
      LinearOccursSpine G X sp' u' v' ∧
        ContextShortlex (u', v') (u, v) := by
  induction d with
  | @start X hstart =>
      exact (hdup (List.nodup_singleton X)).elim
  | @left X Y a sp u v parent hrule ih =>
      by_cases hmem : Y ∈ sp
      · obtain ⟨sp', u', v', l, r, hocc, hu, hv⟩ :=
          earlier_context_factors parent hmem
        have hlen : u'.length < (u ++ [a]).length := by
          rw [hu]
          simp only [List.length_append, List.length_singleton]
          omega
        have hword : WordShortlex u' (u ++ [a]) :=
          List.Shortlex.of_length_lt hlen
        exact ⟨sp', u', v', hocc, Prod.Lex.left _ _ hword⟩
      · have hParentDup : ¬ sp.Nodup := by
          intro hnd
          exact hdup ((List.nodup_concat _ _).mpr ⟨hmem, hnd⟩)
        obtain ⟨sp', u', v', hocc, hsmall⟩ := ih hParentDup
        refine ⟨sp'.concat Y, u' ++ [a], v',
          LinearOccursSpine.left hocc hrule, ?_⟩
        cases hsmall with
        | left v₁ v₂ hu =>
            exact Prod.Lex.left _ _ (wordShortlex_append_right_same hu [a])
        | right common hv =>
            exact Prod.Lex.right _ hv
  | @right X Y a sp u v parent hrule ih =>
      by_cases hmem : Y ∈ sp
      · obtain ⟨sp', u', v', l, r, hocc, hu, hv⟩ :=
          earlier_context_factors parent hmem
        cases l with
        | nil =>
            have huEq : u = u' := by simpa using hu
            subst u
            have hvLen : v'.length < ([a] ++ v).length := by
              rw [hv]
              simp only [List.length_append, List.length_singleton]
              omega
            have hvSmall : WordShortlex v' ([a] ++ v) :=
              List.Shortlex.of_length_lt hvLen
            exact ⟨sp', u', v', hocc, by
              simpa using (Prod.Lex.right u' hvSmall)⟩
        | cons b l =>
            have huLen : u'.length < u.length := by
              rw [hu]
              simp only [List.length_append, List.length_cons]
              omega
            have huSmall : WordShortlex u' u :=
              List.Shortlex.of_length_lt huLen
            exact ⟨sp', u', v', hocc, Prod.Lex.left _ _ huSmall⟩
      · have hParentDup : ¬ sp.Nodup := by
          intro hnd
          exact hdup ((List.nodup_concat _ _).mpr ⟨hmem, hnd⟩)
        obtain ⟨sp', u', v', hocc, hsmall⟩ := ih hParentDup
        refine ⟨sp'.concat Y, u', [a] ++ v',
          LinearOccursSpine.right hocc hrule, ?_⟩
        cases hsmall with
        | left v₁ v₂ hu =>
            exact Prod.Lex.left _ _ hu
        | right common hv =>
            exact Prod.Lex.right _ (List.Shortlex.append_left hv [a])

end LinearOccursSpine

/-- A context pair minimal in the exact Section-4 lexicographic shortlex order. -/
def LinearContextShortlexMinimal
    {W : Type v} {Sigma : Type u} [LT Sigma]
    (G : StrictLinearGrammar W Sigma) (X : W)
    (u v : Word Sigma) : Prop :=
  LinearOccurs G X u v ∧
    ∀ u' v' : Word Sigma,
      LinearOccurs G X u' v' →
        ¬ ContextShortlex (u', v') (u, v)

/-- A lexicographic-shortlex minimum context has a simple strict-linear spine. -/
theorem lemma_7_6_shortlex_context_has_simple_spine
    {W : Type v} {Sigma : Type u} [LinearOrder Sigma]
    {G : StrictLinearGrammar W Sigma} {X : W} {u v : Word Sigma}
    (hmin : LinearContextShortlexMinimal G X u v) :
    ∃ sp : List W, LinearOccursSpine G X sp u v ∧ sp.Nodup := by
  rcases hmin.1 with ⟨sp, d⟩
  refine ⟨sp, d, ?_⟩
  by_contra hdup
  obtain ⟨sp', u', v', hocc, hsmall⟩ :=
    LinearOccursSpine.exists_contextShortlex_smaller_of_spine_not_nodup d hdup
  exact hmin.2 u' v' ⟨sp', hocc⟩ hsmall

/-- Lemma 7.6 in the manuscript's actual lexicographic-shortlex formulation. -/
theorem lemma_7_6_shortlex_context_length_le
    {W : Type v} {Sigma : Type u} [LinearOrder Sigma] [Fintype W]
    {G : StrictLinearGrammar W Sigma} {X : W} {u v : Word Sigma}
    (hmin : LinearContextShortlexMinimal G X u v) :
    u.length + v.length ≤ Fintype.card W - 1 := by
  obtain ⟨sp, d, hSimple⟩ :=
    lemma_7_6_shortlex_context_has_simple_spine hmin
  have hCard : sp.length ≤ Fintype.card W := hSimple.length_le_card
  have hLen := LinearOccursSpine.context_succ_eq_spine_length d
  omega

end FixedHCFG
end LeanCfgProject
