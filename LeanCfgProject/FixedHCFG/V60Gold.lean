import LeanCfgProject.FixedHCFG.V60Identification

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
The two-case Gold convergence argument from the v60 TCS manuscript.

This file works at the language level of the conservative wrapper.  Because a
no-rebuild step leaves the previous hypothesis literally unchanged, and the
first rebuild after the characteristic witness set is exact, the semantic
argument mirrors the manuscript's syntactic stabilization proof.
-/

/-- If stage `n` does not rebuild, then processing `text n` leaves the hypothesis unchanged. -/
theorem v60_no_rebuild_step
    {Sigma : Type u} (Obs : Observer Sigma) (text : Nat → Word Sigma)
    (n : Nat)
    (hNo : ¬ V60RebuildsAt Obs text n) :
    V60ConservativeHypothesis Obs text (n + 1) =
      V60ConservativeHypothesis Obs text n := by
  classical
  have hmem : V60ConservativeHypothesis Obs text n (text n) := by
    unfold V60RebuildsAt at hNo
    exact Classical.byContradiction hNo
  rw [v60ConservativeHypothesis_succ]
  unfold V60ConservativeStep
  rw [if_pos hmem]

/-- No rebuilds on the next `d` stages make the conservative hypothesis constant. -/
theorem v60_no_rebuild_constant_delta
    {Sigma : Type u} (Obs : Observer Sigma) (text : Nat → Word Sigma)
    (a d : Nat)
    (hNo : ∀ k : Nat, k < d → ¬ V60RebuildsAt Obs text (a + k)) :
    V60ConservativeHypothesis Obs text (a + d) =
      V60ConservativeHypothesis Obs text a := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hPrefix : ∀ k : Nat, k < d → ¬ V60RebuildsAt Obs text (a + k) := by
        intro k hk
        exact hNo k (Nat.lt_trans hk (Nat.lt_succ_self d))
      have hIH := ih hPrefix
      have hAt : ¬ V60RebuildsAt Obs text (a + d) :=
        hNo d (Nat.lt_succ_self d)
      have hStep := v60_no_rebuild_step Obs text (a + d) hAt
      calc
        V60ConservativeHypothesis Obs text (a + Nat.succ d) =
            V60ConservativeHypothesis Obs text ((a + d) + 1) := by
              simp [Nat.add_assoc]
        _ = V60ConservativeHypothesis Obs text (a + d) := hStep
        _ = V60ConservativeHypothesis Obs text a := hIH

/--
The no-rebuild branch of Corollary 5.8: if no change occurs from stage `n0`
onward, the hypothesis after processing `text n0` is already the target.
-/
theorem v60_no_rebuild_tail_exact
    {Sigma : Type u} (Obs : Observer Sigma)
    (L : Language Sigma) (text : Nat → Word Sigma)
    (hText : TextFor L text)
    (hSub : HSubstitutableV60 Obs L)
    (n0 : Nat)
    (hNo : ∀ n : Nat, n0 ≤ n → ¬ V60RebuildsAt Obs text n) :
    V60ConservativeHypothesis Obs text (n0 + 1) = L := by
  classical
  apply Set.Subset.antisymm
  · exact v60ConservativeHypothesis_subset_target Obs L text hText hSub (n0 + 1)
  · intro w hw
    obtain ⟨i, hEq⟩ := hText.complete w hw
    by_cases hi : i ≤ n0
    · have hPrefix : w ∈ PrefixSample text n0 := ⟨i, hi, hEq⟩
      exact v60PrefixSample_subset_conservative Obs text n0 hPrefix
    · have hlt : n0 < i := Nat.lt_of_not_ge hi
      have hle : n0 + 1 ≤ i := Nat.succ_le_of_lt hlt
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      have hConst :
          V60ConservativeHypothesis Obs text ((n0 + 1) + d) =
            V60ConservativeHypothesis Obs text (n0 + 1) := by
        exact v60_no_rebuild_constant_delta Obs text (n0 + 1) d (by
          intro k hk
          apply hNo ((n0 + 1) + k)
          exact Nat.le_trans (Nat.le_add_right n0 1)
            (Nat.le_add_right (n0 + 1) k))
      have hNoI : ¬ V60RebuildsAt Obs text ((n0 + 1) + d) := by
        apply hNo ((n0 + 1) + d)
        exact Nat.le_trans (Nat.le_add_right n0 1)
          (Nat.le_add_right (n0 + 1) d)
      have hMemI :
          V60ConservativeHypothesis Obs text ((n0 + 1) + d)
            (text ((n0 + 1) + d)) := by
        unfold V60RebuildsAt at hNoI
        exact Classical.byContradiction hNoI
      have hMemStart :
          V60ConservativeHypothesis Obs text (n0 + 1)
            (text ((n0 + 1) + d)) := by
        rw [← hConst]
        exact hMemI
      rw [← hEq]
      exact hMemStart

/--
Corollary 5.8 in the exact v60 two-case form: every positive text eventually
stabilizes at the target language.
-/
theorem v60_gold_identification
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W)
    (hWitnessFinite : B.witnessSet.Finite)
    (hWitnessTarget : B.witnessSet ⊆ V60BasisLanguage B)
    (hSub : HSubstitutableV60 Obs (V60BasisLanguage B))
    (text : Nat → Word Sigma)
    (hText : TextFor (V60BasisLanguage B) text) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      V60ConservativeHypothesis Obs text n = V60BasisLanguage B := by
  classical
  obtain ⟨n0, hCover⟩ :=
    v60_witness_eventually_seen B hWitnessFinite hWitnessTarget text hText
  by_cases hSome : ∃ n : Nat, n0 ≤ n ∧ V60RebuildsAt Obs text n
  · rcases hSome with ⟨n, hn0, hRebuild⟩
    have hWitnessN : B.witnessSet ⊆ PrefixSample text n := hCover n hn0
    have hExact :
        V60ConservativeHypothesis Obs text (n + 1) = V60BasisLanguage B :=
      v60_rebuild_exact_after_witness B hSub text hText n hWitnessN hRebuild
    refine ⟨n + 1, ?_⟩
    intro m hm
    exact v60_exact_persists Obs (V60BasisLanguage B) text hText
      (n + 1) hExact m hm
  · have hNo : ∀ n : Nat, n0 ≤ n → ¬ V60RebuildsAt Obs text n := by
      intro n hn0 hRebuild
      exact hSome ⟨n, hn0, hRebuild⟩
    have hExact :
        V60ConservativeHypothesis Obs text (n0 + 1) = V60BasisLanguage B :=
      v60_no_rebuild_tail_exact Obs (V60BasisLanguage B) text hText hSub n0 hNo
    refine ⟨n0 + 1, ?_⟩
    intro m hm
    exact v60_exact_persists Obs (V60BasisLanguage B) text hText
      (n0 + 1) hExact m hm

end FixedHCFG
end LeanCfgProject
