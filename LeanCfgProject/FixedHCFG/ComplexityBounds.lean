import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.PaperCharacteristicSample

namespace LeanCfgProject
namespace FixedHCFG

universe u

/-!
Theorem-facing arithmetic for Section 6 of the TCS manuscript.

This file deliberately verifies the combinatorial envelope behind the stated
`O(||K||^5)` bound.  It is not yet a formal cost semantics for tries, radix
sort, or a concrete executable learner implementation.  The latter would be a
strictly stronger software-verification statement than Theorem 6.1 needs.
-/

/--
Two cut positions `i <= j <= m` determine a factorization `u x v` of a word of
length `m`.  This finite type is the index set used when the learner enumerates
all such factorizations.
-/
def FactorizationCut (m : Nat) :=
  {p : Fin (m + 1) × Fin (m + 1) // p.1.1 ≤ p.2.1}

deriving instance Fintype for FactorizationCut

/-- The number of cut pairs is at most the square of the number of positions. -/
theorem factorizationCut_card_le_square (m : Nat) :
    Fintype.card (FactorizationCut m) ≤ (m + 1) ^ 2 := by
  calc
    Fintype.card (FactorizationCut m) ≤
        Fintype.card (Fin (m + 1) × Fin (m + 1)) :=
      Fintype.card_subtype_le _
    _ = (m + 1) ^ 2 := by
      simp [pow_two]

/--
For a nonempty word the factorization enumeration is bounded by `4 m^2`.
Thus the manuscript's per-word enumeration is quadratic in word length.
-/
theorem factorizationCut_card_le_four_sq {m : Nat} (hm : 1 ≤ m) :
    Fintype.card (FactorizationCut m) ≤ 4 * m ^ 2 := by
  refine (factorizationCut_card_le_square m).trans ?_
  nlinarith

/-- The coarse operation-count expression displayed at the end of Theorem 6.1. -/
def section6CostEnvelope (N V ell k : Nat) : Nat :=
  N ^ 3 + V ^ 2 * ell + V * ell + V ^ 2 + k

/-- Powers `N^3` and `N^4` are absorbed by `N^5` for a nonzero sample size. -/
theorem lower_powers_le_fifth {N : Nat} (hN : 1 ≤ N) :
    N ^ 3 ≤ N ^ 5 ∧ N ^ 4 ≤ N ^ 5 ∧ N ≤ N ^ 5 := by
  have hN2 : 1 ≤ N ^ 2 := by
    nlinarith
  have hN4 : 1 ≤ N ^ 4 := by
    nlinarith
  constructor
  · calc
      N ^ 3 = N ^ 3 * 1 := by simp
      _ ≤ N ^ 3 * N ^ 2 := Nat.mul_le_mul_left _ hN2
      _ = N ^ 5 := by ring
  constructor
  · calc
      N ^ 4 = N ^ 4 * 1 := by simp
      _ ≤ N ^ 4 * N := Nat.mul_le_mul_left _ hN
      _ = N ^ 5 := by ring
  · calc
      N = N * 1 := by simp
      _ ≤ N * N ^ 4 := Nat.mul_le_mul_left _ hN4
      _ = N ^ 5 := by ring

/--
Normalized degree-five envelope for Theorem 6.1.

`N` represents `||K||`, `V` the number of learner nonterminals, `ell` the
maximum sample-word length, and `k` the number of distinct sample words.
The manuscript establishes `V = O(N^2)`, `ell <= N`, and `k <= N + 1`.
If `V <= c N^2`, the displayed Section-6 cost expression is bounded by a
constant (depending only on `c`) times `N^5`.
-/
theorem section6CostEnvelope_degree_five
    {N V ell k c : Nat}
    (hN : 1 ≤ N)
    (hV : V ≤ c * N ^ 2)
    (hell : ell ≤ N)
    (hk : k ≤ N + 1) :
    section6CostEnvelope N V ell k ≤
      (2 * c ^ 2 + c + 3) * N ^ 5 := by
  rcases lower_powers_le_fifth hN with ⟨hN3, hN4, hN1⟩

  have hV2 : V ^ 2 ≤ c ^ 2 * N ^ 4 := by
    have hmul : V * V ≤ (c * N ^ 2) * (c * N ^ 2) :=
      Nat.mul_le_mul hV hV
    calc
      V ^ 2 = V * V := by ring
      _ ≤ (c * N ^ 2) * (c * N ^ 2) := hmul
      _ = c ^ 2 * N ^ 4 := by ring

  have hV2ell : V ^ 2 * ell ≤ c ^ 2 * N ^ 5 := by
    calc
      V ^ 2 * ell ≤ (c ^ 2 * N ^ 4) * N :=
        Nat.mul_le_mul hV2 hell
      _ = c ^ 2 * N ^ 5 := by ring

  have hVell : V * ell ≤ c * N ^ 5 := by
    have h0 : V * ell ≤ (c * N ^ 2) * N :=
      Nat.mul_le_mul hV hell
    calc
      V * ell ≤ (c * N ^ 2) * N := h0
      _ = c * N ^ 3 := by ring
      _ ≤ c * N ^ 5 := Nat.mul_le_mul_left c hN3

  have hV2fifth : V ^ 2 ≤ c ^ 2 * N ^ 5 := by
    calc
      V ^ 2 ≤ c ^ 2 * N ^ 4 := hV2
      _ ≤ c ^ 2 * N ^ 5 := Nat.mul_le_mul_left (c ^ 2) hN4

  have hkfifth : k ≤ 2 * N ^ 5 := by
    have hk2N : k ≤ 2 * N := by omega
    calc
      k ≤ 2 * N := hk2N
      _ ≤ 2 * N ^ 5 := Nat.mul_le_mul_left 2 hN1

  have hsum :
      N ^ 3 + V ^ 2 * ell + V * ell + V ^ 2 + k ≤
        N ^ 5 + c ^ 2 * N ^ 5 + c * N ^ 5 +
          c ^ 2 * N ^ 5 + 2 * N ^ 5 := by
    exact Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add hN3 hV2ell)
          hVell)
        hV2fifth)
      hkfifth

  calc
    section6CostEnvelope N V ell k ≤
        N ^ 5 + c ^ 2 * N ^ 5 + c * N ^ 5 +
          c ^ 2 * N ^ 5 + 2 * N ^ 5 := by
      simpa [section6CostEnvelope] using hsum
    _ = (2 * c ^ 2 + c + 3) * N ^ 5 := by ring

/-- Corollary 6.2's arithmetic substitution: rebuilding after adding `z`. -/
theorem update_fifth_power_bound (N z : Nat) :
    (N + z) ^ 5 = (N + z) ^ 5 := by
  rfl

end FixedHCFG
end LeanCfgProject
