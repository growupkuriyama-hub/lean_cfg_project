import LeanCfgProject.FixedHCFG.V60Reconstruction
import LeanCfgProject.FixedHCFG.Identification

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
The conservative sequential learner of the v60 TCS manuscript, now over the
exact nonempty-factor batch kernel `V60StartDerives`.
-/

/-- Language of the exact v60 batch reconstruction operator on `K`. -/
def V60BatchLanguage {Sigma : Type u} (Obs : Observer Sigma)
    (K : Language Sigma) : Language Sigma :=
  fun w => V60StartDerives Obs K w

/-- One v60 conservative update. -/
noncomputable def V60ConservativeStep
    {Sigma : Type u} (Obs : Observer Sigma) (text : Nat → Word Sigma)
    (n : Nat) (H : Language Sigma) : Language Sigma := by
  classical
  exact if H (text n) then H else V60BatchLanguage Obs (PrefixSample text n)

/-- `H_0` is empty; `H_{n+1}` processes the example `text n`. -/
noncomputable def V60ConservativeHypothesis
    {Sigma : Type u} (Obs : Observer Sigma) (text : Nat → Word Sigma) :
    Nat → Language Sigma
  | 0 => fun _ => False
  | n + 1 => V60ConservativeStep Obs text n (V60ConservativeHypothesis Obs text n)

@[simp] theorem v60ConservativeHypothesis_zero
    {Sigma : Type u} (Obs : Observer Sigma) (text : Nat → Word Sigma) :
    V60ConservativeHypothesis Obs text 0 = (fun _ => False) := by
  rfl

theorem v60ConservativeHypothesis_succ
    {Sigma : Type u} (Obs : Observer Sigma) (text : Nat → Word Sigma)
    (n : Nat) :
    V60ConservativeHypothesis Obs text (n + 1) =
      V60ConservativeStep Obs text n (V60ConservativeHypothesis Obs text n) := by
  rfl

/-- Stage `n` rebuilds iff the newly read positive example is missed. -/
def V60RebuildsAt
    {Sigma : Type u} (Obs : Observer Sigma) (text : Nat → Word Sigma)
    (n : Nat) : Prop :=
  ¬ V60ConservativeHypothesis Obs text n (text n)

/-- Every exact-v60 conservative hypothesis is sound for the target language. -/
theorem v60ConservativeHypothesis_subset_target
    {Sigma : Type u} (Obs : Observer Sigma)
    (L : Language Sigma) (text : Nat → Word Sigma)
    (hText : TextFor L text)
    (hSub : HSubstitutableV60 Obs L) :
    ∀ n : Nat, V60ConservativeHypothesis Obs text n ⊆ L := by
  intro n
  induction n with
  | zero =>
      intro w hw
      exact False.elim hw
  | succ n ih =>
      classical
      rw [v60ConservativeHypothesis_succ]
      unfold V60ConservativeStep
      by_cases hmem : V60ConservativeHypothesis Obs text n (text n)
      · rw [if_pos hmem]
        exact ih
      · rw [if_neg hmem]
        intro w hw
        exact v60_start_soundness Obs (PrefixSample text n) L
          (prefixSample_subset_target hText n) hSub hw

/-- After processing `text n`, the hypothesis covers the whole prefix through `n`. -/
theorem v60PrefixSample_subset_conservative
    {Sigma : Type u} (Obs : Observer Sigma) (text : Nat → Word Sigma) :
    ∀ n : Nat,
      PrefixSample text n ⊆ V60ConservativeHypothesis Obs text (n + 1) := by
  intro n
  induction n with
  | zero =>
      classical
      rw [v60ConservativeHypothesis_succ]
      unfold V60ConservativeStep
      have hmiss : ¬ V60ConservativeHypothesis Obs text 0 (text 0) := by
        simp [V60ConservativeHypothesis]
      rw [if_neg hmiss]
      exact v60_sample_consistency Obs (PrefixSample text 0)
  | succ n ih =>
      classical
      rw [v60ConservativeHypothesis_succ]
      unfold V60ConservativeStep
      by_cases hmem : V60ConservativeHypothesis Obs text (n + 1) (text (n + 1))
      · rw [if_pos hmem]
        intro w hw
        rcases hw with ⟨i, hi, rfl⟩
        rcases Nat.lt_or_eq_of_le hi with hlt | rfl
        · have hle : i ≤ n := Nat.le_of_lt_succ hlt
          exact ih ⟨i, hle, rfl⟩
        · exact hmem
      · rw [if_neg hmem]
        exact v60_sample_consistency Obs (PrefixSample text (n + 1))

/-- If the witness set has appeared, every subsequent rebuild is exact. -/
theorem v60_rebuild_exact_after_witness
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W)
    (hSub : HSubstitutableV60 Obs (V60BasisLanguage B))
    (text : Nat → Word Sigma)
    (hText : TextFor (V60BasisLanguage B) text)
    (n : Nat)
    (hWitness : B.witnessSet ⊆ PrefixSample text n)
    (hRebuild : V60RebuildsAt Obs text n) :
    V60ConservativeHypothesis Obs text (n + 1) = V60BasisLanguage B := by
  classical
  have hKL : PrefixSample text n ⊆ V60BasisLanguage B :=
    prefixSample_subset_target hText n
  have hExact :
      V60BatchLanguage Obs (PrefixSample text n) = V60BasisLanguage B := by
    ext w
    exact v60_exact_reconstruction B (PrefixSample text n)
      hWitness hKL hSub w
  unfold V60RebuildsAt at hRebuild
  rw [v60ConservativeHypothesis_succ]
  unfold V60ConservativeStep
  rw [if_neg hRebuild]
  exact hExact

/-- Exactness is absorbing: a positive text can never trigger a later rebuild. -/
theorem v60_exact_is_absorbing
    {Sigma : Type u} (Obs : Observer Sigma)
    (L : Language Sigma) (text : Nat → Word Sigma)
    (hText : TextFor L text)
    (n : Nat)
    (hExact : V60ConservativeHypothesis Obs text n = L) :
    V60ConservativeHypothesis Obs text (n + 1) = L := by
  classical
  have hmem : V60ConservativeHypothesis Obs text n (text n) := by
    rw [hExact]
    exact hText.positive n
  rw [v60ConservativeHypothesis_succ]
  unfold V60ConservativeStep
  rw [if_pos hmem]
  exact hExact

/-- Once exact, all later hypotheses remain exactly the target language. -/
theorem v60_exact_persists
    {Sigma : Type u} (Obs : Observer Sigma)
    (L : Language Sigma) (text : Nat → Word Sigma)
    (hText : TextFor L text)
    (n : Nat)
    (hExact : V60ConservativeHypothesis Obs text n = L) :
    ∀ m : Nat, n ≤ m → V60ConservativeHypothesis Obs text m = L := by
  intro m hnm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction d with
  | zero => simpa using hExact
  | succ d ih =>
      have hstep := v60_exact_is_absorbing Obs L text hText (n + d) ih
      simpa [Nat.add_assoc] using hstep

/--
The v60 mind-change bound in direct form: once the witness set is present,
there cannot be two distinct later rebuild stages.
-/
theorem v60_at_most_one_rebuild_after_witness
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W)
    (hSub : HSubstitutableV60 Obs (V60BasisLanguage B))
    (text : Nat → Word Sigma)
    (hText : TextFor (V60BasisLanguage B) text)
    (n0 n m : Nat)
    (hWitness0 : B.witnessSet ⊆ PrefixSample text n0)
    (hn0 : n0 ≤ n)
    (hnm : n < m)
    (hnRebuild : V60RebuildsAt Obs text n) :
    ¬ V60RebuildsAt Obs text m := by
  intro hmRebuild
  have hWitnessN : B.witnessSet ⊆ PrefixSample text n := by
    intro w hw
    rcases hWitness0 hw with ⟨i, hi, hEq⟩
    exact ⟨i, le_trans hi hn0, hEq⟩
  have hExactN :=
    v60_rebuild_exact_after_witness B hSub text hText n hWitnessN hnRebuild
  have hle : n + 1 ≤ m := Nat.succ_le_of_lt hnm
  have hExactM :=
    v60_exact_persists Obs (V60BasisLanguage B) text hText (n + 1)
      hExactN m hle
  unfold V60RebuildsAt at hmRebuild
  apply hmRebuild
  rw [hExactM]
  exact hText.positive m

/-- The finite v60 witness set is eventually contained in the positive text. -/
theorem v60_witness_eventually_seen
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W)
    (hFinite : B.witnessSet.Finite)
    (hWitnessTarget : B.witnessSet ⊆ V60BasisLanguage B)
    (text : Nat → Word Sigma)
    (hText : TextFor (V60BasisLanguage B) text) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → B.witnessSet ⊆ PrefixSample text n := by
  have hSeen : ∀ w : Word Sigma, w ∈ B.witnessSet → ∃ i : Nat, text i = w := by
    intro w hw
    exact hText.complete w (hWitnessTarget hw)
  exact finite_observations_eventually_seen B.witnessSet hFinite text hSeen

end FixedHCFG
end LeanCfgProject
