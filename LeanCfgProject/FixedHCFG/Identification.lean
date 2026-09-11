import LeanCfgProject.FixedHCFG.Reconstruction

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-- A positive text enumerating every word of `L`. -/
structure TextFor {Sigma : Type u} (L : Language Sigma)
    (text : Nat → Word Sigma) : Prop where
  positive : ∀ i : Nat, text i ∈ L
  complete : ∀ w : Word Sigma, w ∈ L → ∃ i : Nat, text i = w

/-- The set of examples seen up to time `n` (inclusive). -/
def PrefixSample {Sigma : Type u}
    (text : Nat → Word Sigma) (n : Nat) : Language Sigma :=
  fun w => ∃ i : Nat, i ≤ n ∧ text i = w

/-- Every prefix sample of a positive text is contained in the target language. -/
theorem prefixSample_subset_target
    {Sigma : Type u} {L : Language Sigma}
    {text : Nat → Word Sigma}
    (hText : TextFor L text) (n : Nat) :
    PrefixSample text n ⊆ L := by
  intro w hw
  rcases hw with ⟨i, hi, hEq⟩
  rw [← hEq]
  exact hText.positive i

/--
A finite set of observations is eventually contained in every sufficiently
long prefix of an exhaustive text.
-/
theorem finite_observations_eventually_seen
    {Sigma : Type u}
    (S : Language Sigma)
    (hFinite : S.Finite)
    (text : Nat → Word Sigma)
    (hSeen : ∀ w : Word Sigma, w ∈ S → ∃ i : Nat, text i = w) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → S ⊆ PrefixSample text n := by
  classical
  let sFin : Finset (Word Sigma) := hFinite.toFinset
  have hSub : ∀ w : Word Sigma, w ∈ sFin → w ∈ S := by
    intro w hw
    simpa [sFin] using hw
  have coverFin :
      ∀ s : Finset (Word Sigma),
        (∀ w : Word Sigma, w ∈ s → w ∈ S) →
        ∃ N : Nat, ∀ n : Nat, N ≤ n →
          ∀ w : Word Sigma, w ∈ s → w ∈ PrefixSample text n := by
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
        refine ⟨max ia N, ?_⟩
        intro n hmax w hw
        simp only [Finset.mem_insert] at hw
        rcases hw with rfl | hw
        · exact ⟨ia, le_trans (Nat.le_max_left ia N) hmax, hia⟩
        · exact hN n (le_trans (Nat.le_max_right ia N) hmax) w hw
  obtain ⟨N, hN⟩ := coverFin sFin hSub
  refine ⟨N, ?_⟩
  intro n hn w hw
  have hwFin : w ∈ sFin := by
    simpa [sFin] using hw
  exact hN n hn w hwFin

/--
Corollary 5.8, semantic form: on every positive text for the target basis
language, the canonical learner eventually has exactly the target language at
every later stage.

This formalizes language stabilization (the part used by identification in the
limit); it deliberately does not identify grammars syntactically, only their
languages.
-/
theorem corollary_5_8_semantic_identification
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    (hCSFinite : B.CS.Finite)
    (hCSTarget : B.CS ⊆ BasisLanguage B)
    (hSub : HSubstitutable Obs (BasisLanguage B))
    (text : Nat → Word Sigma)
    (hText : TextFor (BasisLanguage B) text) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ w : Word Sigma,
        StartDerives Obs (PrefixSample text n) w ↔ BasisLanguage B w := by
  have hSeen : ∀ w : Word Sigma, w ∈ B.CS → ∃ i : Nat, text i = w := by
    intro w hw
    exact hText.complete w (hCSTarget hw)
  obtain ⟨N, hCover⟩ :=
    finite_observations_eventually_seen B.CS hCSFinite text hSeen
  refine ⟨N, ?_⟩
  intro n hn w
  have hCSK : B.CS ⊆ PrefixSample text n := hCover n hn
  have hKL : PrefixSample text n ⊆ BasisLanguage B :=
    prefixSample_subset_target hText n
  exact theorem_5_7_exact_reconstruction B (PrefixSample text n)
    hCSK hKL hSub w

end FixedHCFG
end LeanCfgProject
