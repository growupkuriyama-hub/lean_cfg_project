import Mathlib
import LeanCfgProject.FixedHCFGv44.LinearCharacteristicPolynomialV47

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
The manuscript measures a finite sample by

  ||D|| = sum_{w in D} (|w| + 1).

For the v47 linear argument, the exact canonical sample is a sub-finset of the
finite image of `CanonicalCSIndex`.  The index image may contain duplicates and
always contains the optional epsilon slot, so it is a convenient uniform upper
envelope.  We first bound the norm of that envelope and then inherit the same
polynomial bound for the exact canonical sample.
-/

/-- A nonnegative sum over a finite image is bounded by the corresponding sum
before quotienting duplicate image points. -/
theorem sum_image_le_sum_nat_v47
    {α β : Type*} [DecidableEq β]
    (s : Finset α) (g : α → β) (f : β → Nat) :
    Finset.sum (s.image g) f ≤ Finset.sum s (fun x => f (g x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hmem : g a ∈ s.image g
      · simp [Finset.image_insert, ha, hmem]
        omega
      · simpa [Finset.image_insert, ha, hmem] using
          Nat.add_le_add_left ih (f (g a))

/-- The finite image of all canonical characteristic-data indices. -/
noncomputable def canonicalCSCoverV47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N} : Finset (Word Sigma) := by
  classical
  exact Finset.univ.image
    (fun i : CanonicalCSIndex (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) => canonicalCSIndexWord i)

/-- Every actual canonical characteristic word lies in the finite index image. -/
theorem canonicalCS_mem_cover_v47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop) {z : Word Sigma}
    (hz : CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart z) :
    z ∈ canonicalCSCoverV47 (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) := by
  classical
  rcases canonicalCS_covered_by_index epsilonStart hz with ⟨i, rfl⟩
  simp [canonicalCSCoverV47]

/-- The exact canonical characteristic sample as a finite set of words. -/
noncomputable def canonicalCSFinsetV47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop) : Finset (Word Sigma) := by
  classical
  exact (canonicalCSCoverV47 (Obs := Obs) (terminal := terminal)
    (binary := binary) (start := start)).filter
      (fun z => CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart z)

/-- The finite representation is exact: membership is precisely `CanonicalCS`. -/
theorem mem_canonicalCSFinsetV47_iff
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop) (z : Word Sigma) :
    z ∈ canonicalCSFinsetV47 (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart ↔
      CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart z := by
  classical
  simp only [canonicalCSFinsetV47, Finset.mem_filter]
  constructor
  · intro hz
    exact hz.2
  · intro hz
    exact ⟨canonicalCS_mem_cover_v47 epsilonStart hz, hz⟩

/-- Every index word is canonical for the harmless envelope choice `epsilonStart = True`. -/
theorem canonicalCSIndexWord_mem_true_v47
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (i : CanonicalCSIndex (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start)) :
    CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) True (canonicalCSIndexWord i) := by
  rcases i with X | i
  · exact Or.inl ⟨X, rfl⟩
  · rcases i with p | i
    · exact Or.inr (Or.inl ⟨p.1.1, p.1.2, p.2, rfl⟩)
    · rcases i with p | u
      · exact Or.inr (Or.inr (Or.inl
          ⟨p.1.1, p.1.2.1, p.1.2.2, p.2, rfl⟩))
      · cases u
        exact Or.inr (Or.inr (Or.inr ⟨rfl, trivial⟩))

/-- Uniform `4 n_t` word-length bound, now for every index in the finite envelope. -/
theorem canonicalCSIndexWord_length_le_actual_v47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (S : TypedLinearSpineShape Obs terminal binary start)
    (i : CanonicalCSIndex (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start)) :
    (canonicalCSIndexWord i).length ≤
      4 * Fintype.card (KeptState Obs terminal binary start) := by
  exact canonicalCS_word_length_le_actual_v47 True S
    (canonicalCSIndexWord_mem_true_v47 i)

/-- Manuscript sample norm of the exact canonical characteristic sample. -/
noncomputable def canonicalCSNormV47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop) : Nat :=
  Finset.sum
    (canonicalCSFinsetV47 (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart)
    (fun z => z.length + 1)

/-- Norm of the full finite index-image envelope. -/
noncomputable def canonicalCSCoverNormV47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N} : Nat :=
  Finset.sum
    (canonicalCSCoverV47 (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start))
    (fun z => z.length + 1)

/-- Filtering the envelope to the exact sample can only decrease its norm. -/
theorem canonicalCSNorm_le_coverNorm_v47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop) :
    canonicalCSNormV47 (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart ≤
      canonicalCSCoverNormV47 (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) := by
  classical
  unfold canonicalCSNormV47 canonicalCSCoverNormV47 canonicalCSFinsetV47
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/--
The full index image has norm at most
`|CanonicalCSIndex| * (4 n_t + 1)`.
-/
theorem canonicalCSCoverNorm_le_index_v47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (S : TypedLinearSpineShape Obs terminal binary start) :
    canonicalCSCoverNormV47 (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) ≤
      Fintype.card
          (CanonicalCSIndex (Obs := Obs) (terminal := terminal)
            (binary := binary) (start := start)) *
        (4 * Fintype.card (KeptState Obs terminal binary start) + 1) := by
  classical
  let f : CanonicalCSIndex (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) → Word Sigma :=
    fun i => canonicalCSIndexWord i
  unfold canonicalCSCoverNormV47 canonicalCSCoverV47
  change Finset.sum (Finset.univ.image f) (fun z => z.length + 1) ≤ _
  calc
    Finset.sum (Finset.univ.image f) (fun z => z.length + 1) ≤
        Finset.sum (Finset.univ : Finset
          (CanonicalCSIndex (Obs := Obs) (terminal := terminal)
            (binary := binary) (start := start)))
          (fun i => (f i).length + 1) := by
      exact sum_image_le_sum_nat_v47
        (Finset.univ : Finset
          (CanonicalCSIndex (Obs := Obs) (terminal := terminal)
            (binary := binary) (start := start)))
        f (fun z : Word Sigma => z.length + 1)
    _ ≤ Finset.sum (Finset.univ : Finset
          (CanonicalCSIndex (Obs := Obs) (terminal := terminal)
            (binary := binary) (start := start)))
          (fun _ => 4 * Fintype.card (KeptState Obs terminal binary start) + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hLen := canonicalCSIndexWord_length_le_actual_v47 S i
      change (canonicalCSIndexWord i).length + 1 ≤ _
      omega
    _ = Fintype.card
          (CanonicalCSIndex (Obs := Obs) (terminal := terminal)
            (binary := binary) (start := start)) *
        (4 * Fintype.card (KeptState Obs terminal binary start) + 1) := by
      simp

/--
Explicit polynomial bound for the manuscript norm `||W||` of the exact
canonical characteristic sample.
-/
theorem canonicalCSNorm_polynomial_le_v47
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop)
    (S : TypedLinearSpineShape Obs terminal binary start) :
    canonicalCSNormV47 (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart ≤
      (Fintype.card (KeptState Obs terminal binary start) +
        Fintype.card (KeptState Obs terminal binary start) * Fintype.card Sigma +
        Fintype.card (KeptState Obs terminal binary start) ^ 3 + 1) *
      (4 * Fintype.card (KeptState Obs terminal binary start) + 1) := by
  have hExact := canonicalCSNorm_le_coverNorm_v47
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
    epsilonStart
  have hCover := canonicalCSCoverNorm_le_index_v47
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start) S
  have hCard := canonicalCSIndex_card_polynomial_le_v47
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
  exact le_trans (le_trans hExact hCover)
    (Nat.mul_le_mul_right
      (4 * Fintype.card (KeptState Obs terminal binary start) + 1) hCard)

end FixedHCFGv44
end LeanCfgProject
