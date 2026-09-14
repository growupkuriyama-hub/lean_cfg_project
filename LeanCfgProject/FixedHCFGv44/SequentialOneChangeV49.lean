import LeanCfgProject.FixedHCFGv44.CanonicalReconstruction
import LeanCfgProject.FixedHCFGv44.WitnessSetV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
TCS v49 strengthens the prose form of `cor:ilt`: once the finite witness set
has appeared, at most one further conservative hypothesis change can occur.
The existing Gold proof already contains the ingredients for this statement;
this file isolates the exact one-change invariant explicitly.
-/

/--
After a reconstruction basis's characteristic set is covered, two distinct
later trigger stages are impossible.  Equivalently, there is at most one
subsequent conservative rebuild.
-/
theorem conservative_at_most_one_trigger_after_cover_v49
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    (text : Nat → Word Sigma)
    (hText : TextFor (BasisLanguage B) text)
    (hSub : HSubstitutable Obs (BasisLanguage B))
    (n0 : Nat)
    (hCover : B.CS ⊆ Seen text n0) :
    ∀ n m : Nat,
      n0 ≤ n → n0 ≤ m →
      text n ∉ ConservativeHyp Obs text n →
      text m ∉ ConservativeHyp Obs text m →
      n = m := by
  intro n m hn hm hTrigN hTrigM
  by_contra hne
  rcases lt_or_gt_of_ne hne with hnm | hmn
  · have hCoverSucc : B.CS ⊆ Seen text (n + 1) := by
      exact Set.Subset.trans hCover
        (seen_mono (le_trans hn (Nat.le_succ n)))
    have hExactN1 :
        ConservativeHyp Obs text (n + 1) = BasisLanguage B :=
      rebuild_after_characteristic_cover_is_exact
        B text hText hSub n hCoverSucc hTrigN
    have hExactM : ConservativeHyp Obs text m = BasisLanguage B :=
      exact_hypothesis_stable B text hText
        (Nat.succ_le_of_lt hnm) hExactN1
    apply hTrigM
    rw [hExactM]
    exact hText.positive m
  · have hCoverSucc : B.CS ⊆ Seen text (m + 1) := by
      exact Set.Subset.trans hCover
        (seen_mono (le_trans hm (Nat.le_succ m)))
    have hExactM1 :
        ConservativeHyp Obs text (m + 1) = BasisLanguage B :=
      rebuild_after_characteristic_cover_is_exact
        B text hText hSub m hCoverSucc hTrigM
    have hExactN : ConservativeHyp Obs text n = BasisLanguage B :=
      exact_hypothesis_stable B text hText
        (Nat.succ_le_of_lt hmn) hExactM1
    apply hTrigN
    rw [hExactN]
    exact hText.positive n

/--
Canonical SSBNF form of the previous theorem, using the manuscript's v49
witness notation `W(\widetilde G)`.
-/
theorem canonical_at_most_one_trigger_after_witness_cover_v49
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart))
    (text : Nat → Word Sigma)
    (hText : TextFor
      (UntypedStartLanguage terminal binary start epsilonStart) text)
    (n0 : Nat)
    (hCover : WitnessSetV49 (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart ⊆ Seen text n0) :
    ∀ n m : Nat,
      n0 ≤ n → n0 ≤ m →
      text n ∉ ConservativeHyp Obs text n →
      text m ∉ ConservativeHyp Obs text m →
      n = m := by
  let B := canonicalReconstructionBasis Obs terminal binary start epsilonStart
  have hLangEq : BasisLanguage B =
      UntypedStartLanguage terminal binary start epsilonStart := by
    simpa [B] using
      canonicalBasisLanguage_eq_untyped
        Obs terminal binary start epsilonStart
  have hText' : TextFor (BasisLanguage B) text := by
    rw [hLangEq]
    exact hText
  have hSub' : HSubstitutable Obs (BasisLanguage B) := by
    rw [hLangEq]
    exact hSub
  have hCover' : B.CS ⊆ Seen text n0 := by
    simpa [B, canonicalReconstructionBasis, WitnessSetV49] using hCover
  exact conservative_at_most_one_trigger_after_cover_v49
    B text hText' hSub' n0 hCover'

/--
If a trigger occurs after the v49 witness set is covered, that rebuild is
exact and exactness persists forever.  This is the operational form of the
"at most one further hypothesis change" sentence in `cor:ilt`.
-/
theorem canonical_trigger_after_witness_cover_is_final_v49
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart))
    (text : Nat → Word Sigma)
    (hText : TextFor
      (UntypedStartLanguage terminal binary start epsilonStart) text)
    (n0 n : Nat)
    (hn : n0 ≤ n)
    (hCover : WitnessSetV49 (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart ⊆ Seen text n0)
    (hTrigger : text n ∉ ConservativeHyp Obs text n) :
    ∀ m : Nat, n + 1 ≤ m →
      ConservativeHyp Obs text m =
        UntypedStartLanguage terminal binary start epsilonStart := by
  let B := canonicalReconstructionBasis Obs terminal binary start epsilonStart
  have hLangEq : BasisLanguage B =
      UntypedStartLanguage terminal binary start epsilonStart := by
    simpa [B] using
      canonicalBasisLanguage_eq_untyped
        Obs terminal binary start epsilonStart
  have hText' : TextFor (BasisLanguage B) text := by
    rw [hLangEq]
    exact hText
  have hSub' : HSubstitutable Obs (BasisLanguage B) := by
    rw [hLangEq]
    exact hSub
  have hCoverB : B.CS ⊆ Seen text n0 := by
    simpa [B, canonicalReconstructionBasis, WitnessSetV49] using hCover
  have hCoverSucc : B.CS ⊆ Seen text (n + 1) := by
    exact Set.Subset.trans hCoverB
      (seen_mono (le_trans hn (Nat.le_succ n)))
  have hExactN1 : ConservativeHyp Obs text (n + 1) = BasisLanguage B :=
    rebuild_after_characteristic_cover_is_exact
      B text hText' hSub' n hCoverSucc hTrigger
  intro m hm
  calc
    ConservativeHyp Obs text m = BasisLanguage B :=
      exact_hypothesis_stable B text hText' hm hExactN1
    _ = UntypedStartLanguage terminal binary start epsilonStart := hLangEq

end FixedHCFGv44
end LeanCfgProject
