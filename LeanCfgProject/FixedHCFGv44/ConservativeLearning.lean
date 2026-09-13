import LeanCfgProject.FixedHCFGv44.Reconstruction

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-- A positive text enumerating every word of `L`. -/
structure TextFor {Sigma : Type u} (L : Language Sigma)
    (text : Nat → Word Sigma) : Prop where
  positive : ∀ i : Nat, text i ∈ L
  complete : ∀ w : Word Sigma, w ∈ L → ∃ i : Nat, text i = w

/-- The examples seen strictly before stage `n`. -/
def Seen {Sigma : Type u}
    (text : Nat → Word Sigma) (n : Nat) : Language Sigma :=
  fun w => ∃ i : Nat, i < n ∧ text i = w

/-- Seen data are monotone in the stage number. -/
theorem seen_mono {Sigma : Type u}
    {text : Nat → Word Sigma} {m n : Nat} (hmn : m ≤ n) :
    Seen text m ⊆ Seen text n := by
  intro w hw
  rcases hw with ⟨i, hi, hEq⟩
  exact ⟨i, lt_of_lt_of_le hi hmn, hEq⟩

/-- Every seen prefix of a positive text stays inside the target. -/
theorem seen_subset_target
    {Sigma : Type u} {L : Language Sigma}
    {text : Nat → Word Sigma}
    (hText : TextFor L text) (n : Nat) :
    Seen text n ⊆ L := by
  intro w hw
  rcases hw with ⟨i, hi, hEq⟩
  rw [← hEq]
  exact hText.positive i

/-- The current datum has been seen at the next stage. -/
theorem current_mem_seen_succ
    {Sigma : Type u} (text : Nat → Word Sigma) (n : Nat) :
    text n ∈ Seen text (n + 1) := by
  exact ⟨n, Nat.lt_succ_self n, rfl⟩

/-- A datum seen by stage `n+1` is old or is exactly the new datum. -/
theorem seen_succ_cases
    {Sigma : Type u} {text : Nat → Word Sigma} {n : Nat} {w : Word Sigma}
    (hw : w ∈ Seen text (n + 1)) :
    w ∈ Seen text n ∨ text n = w := by
  rcases hw with ⟨i, hi, hEq⟩
  by_cases hOld : i < n
  · exact Or.inl ⟨i, hOld, hEq⟩
  · have hin : i ≤ n := Nat.le_of_lt_succ hi
    have hni : n ≤ i := Nat.le_of_not_gt hOld
    have hEqIdx : i = n := Nat.le_antisymm hin hni
    subst i
    exact Or.inr hEq

/--
The conservative v44 learner at the language level.

Stage `0` is the fixed empty hypothesis.  At stage `n+1`, after reading
`text n`, the learner keeps its previous hypothesis if the new datum is
already generated; otherwise it rebuilds from the entire accumulated set
`Seen text (n+1)`.
-/
noncomputable def ConservativeHyp {Sigma : Type u}
    (Obs : Observer Sigma) (text : Nat → Word Sigma) : Nat → Language Sigma
  | 0 => ∅
  | n + 1 => by
      classical
      exact if text n ∈ ConservativeHyp Obs text n then
        ConservativeHyp Obs text n
      else
        HypLanguage Obs (Seen text (n + 1))

/-- The conservative hypothesis always contains all data seen so far. -/
theorem seen_subset_conservative
    {Sigma : Type u} (Obs : Observer Sigma)
    (text : Nat → Word Sigma) :
    ∀ n : Nat, Seen text n ⊆ ConservativeHyp Obs text n := by
  intro n
  induction n with
  | zero =>
      intro w hw
      rcases hw with ⟨i, hi, hEq⟩
      exact (Nat.not_lt_zero i hi).elim
  | succ n ih =>
      intro w hw
      classical
      by_cases hKeep : text n ∈ ConservativeHyp Obs text n
      · rw [ConservativeHyp]
        simp only [hKeep, if_pos]
        rcases seen_succ_cases hw with hOld | hNew
        · exact ih hOld
        · simpa [hNew] using hKeep
      · rw [ConservativeHyp]
        simp only [hKeep, if_neg]
        exact lemma_sample_consistency Obs (Seen text (n + 1)) hw

/-- Every conservative hypothesis remains sound for a positive target text. -/
theorem conservative_subset_target
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    (text : Nat → Word Sigma)
    (hText : TextFor (BasisLanguage B) text)
    (hSub : HSubstitutable Obs (BasisLanguage B)) :
    ∀ n : Nat, ConservativeHyp Obs text n ⊆ BasisLanguage B := by
  intro n
  induction n with
  | zero =>
      intro w hw
      exact hw.elim
  | succ n ih =>
      classical
      by_cases hKeep : text n ∈ ConservativeHyp Obs text n
      · rw [ConservativeHyp]
        simp only [hKeep, if_pos]
        exact ih
      · rw [ConservativeHyp]
        simp only [hKeep, if_neg]
        exact theorem_soundness Obs (Seen text (n + 1))
          (BasisLanguage B) (seen_subset_target hText (n + 1)) hSub

/-- Once the conservative hypothesis is exact, the next datum cannot trigger a rebuild. -/
theorem exact_hypothesis_next
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    (text : Nat → Word Sigma)
    (hText : TextFor (BasisLanguage B) text)
    (n : Nat)
    (hExact : ConservativeHyp Obs text n = BasisLanguage B) :
    ConservativeHyp Obs text (n + 1) = BasisLanguage B := by
  classical
  have hMem : text n ∈ ConservativeHyp Obs text n := by
    rw [hExact]
    exact hText.positive n
  rw [ConservativeHyp]
  simp only [hMem, if_pos]
  exact hExact

/-- Exactness persists forever once reached. -/
theorem exact_hypothesis_stable
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    (text : Nat → Word Sigma)
    (hText : TextFor (BasisLanguage B) text)
    {n m : Nat}
    (hnm : n ≤ m)
    (hExact : ConservativeHyp Obs text n = BasisLanguage B) :
    ConservativeHyp Obs text m = BasisLanguage B := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction k with
  | zero =>
      simpa using hExact
  | succ k ih =>
      have hNext := exact_hypothesis_next B text hText (n + k) ih
      simpa [Nat.add_assoc] using hNext

/-- Every finite witness set is eventually contained in all later seen sets. -/
theorem finite_observations_eventually_seen
    {Sigma : Type u}
    (S : Language Sigma)
    (hFinite : S.Finite)
    (text : Nat → Word Sigma)
    (hSeen : ∀ w : Word Sigma, w ∈ S → ∃ i : Nat, text i = w) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → S ⊆ Seen text n := by
  classical
  let sFin : Finset (Word Sigma) := hFinite.toFinset
  have hSub : ∀ w : Word Sigma, w ∈ sFin → w ∈ S := by
    intro w hw
    simpa [sFin] using hw
  have coverFin :
      ∀ s : Finset (Word Sigma),
        (∀ w : Word Sigma, w ∈ s → w ∈ S) →
        ∃ N : Nat, ∀ n : Nat, N ≤ n →
          ∀ w : Word Sigma, w ∈ s → w ∈ Seen text n := by
    intro s hs
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨0, by
          intro n hn w hw
          simp at hw⟩
    | @insert a s ha ih =>
        have haS : a ∈ S := hs a (by simp)
        have hsS : ∀ w : Word Sigma, w ∈ s → w ∈ S := by
          intro w hw
          exact hs w (by simp [hw])
        obtain ⟨ia, hia⟩ := hSeen a haS
        obtain ⟨N, hN⟩ := ih hsS
        refine ⟨max (ia + 1) N, ?_⟩
        intro n hmax w hw
        simp only [Finset.mem_insert] at hw
        rcases hw with rfl | hw
        · refine ⟨ia, ?_, hia⟩
          exact lt_of_lt_of_le (Nat.lt_succ_self ia)
            (le_trans (Nat.le_max_left (ia + 1) N) hmax)
        · exact hN n (le_trans (Nat.le_max_right (ia + 1) N) hmax) w hw
  obtain ⟨N, hN⟩ := coverFin sFin hSub
  refine ⟨N, ?_⟩
  intro n hn w hw
  have hwFin : w ∈ sFin := by
    simpa [sFin] using hw
  exact hN n hn w hwFin

/-- If no trigger occurs from stage `N` onward, the hypothesis stays constant. -/
theorem conservative_constant_of_no_trigger
    {Sigma : Type u}
    (Obs : Observer Sigma) (text : Nat → Word Sigma)
    (N : Nat)
    (hNo : ∀ n : Nat, N ≤ n → text n ∈ ConservativeHyp Obs text n) :
    ∀ n : Nat, N ≤ n →
      ConservativeHyp Obs text n = ConservativeHyp Obs text N := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => rfl
  | succ k ih =>
      have hNk : N ≤ N + k := Nat.le_add_right N k
      have hMem := hNo (N + k) hNk
      rw [ConservativeHyp]
      simp only [hMem, if_pos]
      exact ih

/--
If the characteristic witnesses are already contained in the accumulated data,
then any subsequent conservative rebuild is exact and is therefore the last
possible hypothesis change.
-/
theorem rebuild_after_characteristic_cover_is_exact
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    (text : Nat → Word Sigma)
    (hText : TextFor (BasisLanguage B) text)
    (hSub : HSubstitutable Obs (BasisLanguage B))
    (n : Nat)
    (hCover : B.CS ⊆ Seen text (n + 1))
    (hTrigger : text n ∉ ConservativeHyp Obs text n) :
    ConservativeHyp Obs text (n + 1) = BasisLanguage B := by
  classical
  rw [ConservativeHyp]
  simp only [hTrigger, if_neg]
  exact theorem_exact_reconstruction B (Seen text (n + 1))
    hCover (seen_subset_target hText (n + 1)) hSub

/--
v44 Gold identification theorem, semantic form.  Once the finite witness set
has appeared, either there is a later rebuild (which is exact and final) or no
later rebuild occurs, in which case exhaustivity of the text forces the
already-stable sound hypothesis to equal the target.
-/
theorem corollary_gold_identification
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    (hCSFinite : B.CS.Finite)
    (hCSTarget : B.CS ⊆ BasisLanguage B)
    (hSub : HSubstitutable Obs (BasisLanguage B))
    (text : Nat → Word Sigma)
    (hText : TextFor (BasisLanguage B) text) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ConservativeHyp Obs text n = BasisLanguage B := by
  have hSeen : ∀ w : Word Sigma, w ∈ B.CS → ∃ i : Nat, text i = w := by
    intro w hw
    exact hText.complete w (hCSTarget hw)
  obtain ⟨N, hCover⟩ :=
    finite_observations_eventually_seen B.CS hCSFinite text hSeen
  by_cases hTrigger :
      ∃ n : Nat, N ≤ n ∧ text n ∉ ConservativeHyp Obs text n
  · rcases hTrigger with ⟨n, hn, hMiss⟩
    have hCoverSucc : B.CS ⊆ Seen text (n + 1) :=
      hCover (n + 1) (le_trans hn (Nat.le_succ n))
    have hExact := rebuild_after_characteristic_cover_is_exact
      B text hText hSub n hCoverSucc hMiss
    refine ⟨n + 1, ?_⟩
    intro m hm
    exact exact_hypothesis_stable B text hText hm hExact
  · have hNo : ∀ n : Nat, N ≤ n →
        text n ∈ ConservativeHyp Obs text n := by
      intro n hn
      by_contra hMiss
      exact hTrigger ⟨n, hn, hMiss⟩
    have hConst := conservative_constant_of_no_trigger Obs text N hNo
    have hSound : ConservativeHyp Obs text N ⊆ BasisLanguage B :=
      conservative_subset_target B text hText hSub N
    have hComplete : BasisLanguage B ⊆ ConservativeHyp Obs text N := by
      intro w hw
      obtain ⟨i, hEq⟩ := hText.complete w hw
      by_cases hi : i < N
      · have hwSeen : w ∈ Seen text N := ⟨i, hi, hEq⟩
        exact seen_subset_conservative Obs text N hwSeen
      · have hNi : N ≤ i := Nat.le_of_not_gt hi
        have hMem := hNo i hNi
        have hCi := hConst i hNi
        rw [hCi] at hMem
        simpa [hEq] using hMem
    have hExactN : ConservativeHyp Obs text N = BasisLanguage B :=
      Set.Subset.antisymm hSound hComplete
    refine ⟨N, ?_⟩
    intro n hn
    calc
      ConservativeHyp Obs text n = ConservativeHyp Obs text N := hConst n hn
      _ = BasisLanguage B := hExactN

end FixedHCFGv44
end LeanCfgProject
