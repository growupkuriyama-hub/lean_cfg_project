import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import LeanCfgProject.FixedHCFGv44.ConservativeLearning

namespace LeanCfgProject
namespace FixedHCFGv44

/-!
Arithmetic/combinatorial envelope for revised v44 Section 6.

This verifies the counting argument behind Theorem `thm:poly-build`: quadratic
substring/factor enumeration, cubic four-factor cut enumeration, quadratic
pairing of observed learner nonterminals, and the safe coarse `O(||K||^5)`
explicit-output bound.  It intentionally does not claim a low-level cost
semantics for a particular parser or string-table implementation.
-/

/-- Two ordered cuts index a factorization `u x v`. -/
def FactorizationCut (m : Nat) :=
  {p : Fin (m + 1) × Fin (m + 1) // p.1.1 ≤ p.2.1}

deriving instance Fintype for FactorizationCut

/-- The number of factorization cut pairs is at most `(m+1)^2`. -/
theorem factorizationCut_card_le_square (m : Nat) :
    Fintype.card (FactorizationCut m) ≤ (m + 1) ^ 2 := by
  calc
    Fintype.card (FactorizationCut m) ≤
        Fintype.card (Fin (m + 1) × Fin (m + 1)) :=
      Fintype.card_subtype_le _
    _ = (m + 1) ^ 2 := by
      simp [pow_two]

/-- Three ordered cuts index a four-factor decomposition `u x y v`. -/
def FourFactorCut (m : Nat) :=
  {p : Fin (m + 1) × Fin (m + 1) × Fin (m + 1) //
    p.1.1 ≤ p.2.1.1 ∧ p.2.1.1 ≤ p.2.2.1}

deriving instance Fintype for FourFactorCut

/-- The number of four-factor cut triples is at most `(m+1)^3`. -/
theorem fourFactorCut_card_le_cube (m : Nat) :
    Fintype.card (FourFactorCut m) ≤ (m + 1) ^ 3 := by
  calc
    Fintype.card (FourFactorCut m) ≤
        Fintype.card
          (Fin (m + 1) × Fin (m + 1) × Fin (m + 1)) :=
      Fintype.card_subtype_le _
    _ = (m + 1) ^ 3 := by
      simp
      ring

/-- For nonempty words, the cut-pair count is `O(m^2)`. -/
theorem factorizationCut_card_le_four_sq {m : Nat} (hm : 1 ≤ m) :
    Fintype.card (FactorizationCut m) ≤ 4 * m ^ 2 := by
  refine (factorizationCut_card_le_square m).trans ?_
  nlinarith

/-- For nonempty words, the four-factor cut count is `O(m^3)`. -/
theorem fourFactorCut_card_le_eight_cube {m : Nat} (hm : 1 ≤ m) :
    Fintype.card (FourFactorCut m) ≤ 8 * m ^ 3 := by
  refine (fourFactorCut_card_le_cube m).trans ?_
  have h2 : m + 1 ≤ 2 * m := by omega
  have hmul :
      (m + 1) * (m + 1) * (m + 1) ≤
        (2 * m) * (2 * m) * (2 * m) :=
    Nat.mul_le_mul (Nat.mul_le_mul h2 h2) h2
  calc
    (m + 1) ^ 3 = (m + 1) * (m + 1) * (m + 1) := by ring
    _ ≤ (2 * m) * (2 * m) * (2 * m) := hmul
    _ = 8 * m ^ 3 := by ring

/-- Every power through four is absorbed by the fifth power for `N ≥ 1`. -/
theorem lower_powers_le_fifth {N : Nat} (hN : 1 ≤ N) :
    N ≤ N ^ 5 ∧ N ^ 2 ≤ N ^ 5 ∧ N ^ 3 ≤ N ^ 5 ∧ N ^ 4 ≤ N ^ 5 := by
  have hN2one : 1 ≤ N ^ 2 := by nlinarith
  have hN3one : 1 ≤ N ^ 3 := by nlinarith
  have hN4one : 1 ≤ N ^ 4 := by nlinarith
  constructor
  · calc
      N = N * 1 := by simp
      _ ≤ N * N ^ 4 := Nat.mul_le_mul_left N hN4one
      _ = N ^ 5 := by ring
  constructor
  · calc
      N ^ 2 = N ^ 2 * 1 := by simp
      _ ≤ N ^ 2 * N ^ 3 := Nat.mul_le_mul_left (N ^ 2) hN3one
      _ = N ^ 5 := by ring
  constructor
  · calc
      N ^ 3 = N ^ 3 * 1 := by simp
      _ ≤ N ^ 3 * N ^ 2 := Nat.mul_le_mul_left (N ^ 3) hN2one
      _ = N ^ 5 := by ring
  · calc
      N ^ 4 = N ^ 4 * 1 := by simp
      _ ≤ N ^ 4 * N := Nat.mul_le_mul_left (N ^ 4) hN
      _ = N ^ 5 := by ring

/--
A direct explicit-output envelope matching the revised proof.

* `N^2`: cached substring values / factor enumeration;
* `N^3`: Rule-(1) candidate decompositions;
* `N^4`: explicitly writing Rule-(1) keys of length `O(N)`;
* `2 * V^2 * N`: Rules (2) and (3), each with `V^2` candidates and `O(N)` keys;
* `V * N + N`: lower-order terminal/start bookkeeping.
-/
def v44BuildEnvelope (N V : Nat) : Nat :=
  N ^ 2 + N ^ 3 + N ^ 4 + 2 * V ^ 2 * N + V * N + N

/--
The revised Section-6 envelope is degree five once the observed learner-state
count satisfies `V ≤ c N^2`.
-/
theorem v44BuildEnvelope_degree_five
    {N V c : Nat}
    (hN : 1 ≤ N)
    (hV : V ≤ c * N ^ 2) :
    v44BuildEnvelope N V ≤ (2 * c ^ 2 + c + 4) * N ^ 5 := by
  rcases lower_powers_le_fifth hN with ⟨hN1, hN2, hN3, hN4⟩
  have hV2 : V ^ 2 ≤ c ^ 2 * N ^ 4 := by
    have hmul : V * V ≤ (c * N ^ 2) * (c * N ^ 2) :=
      Nat.mul_le_mul hV hV
    calc
      V ^ 2 = V * V := by ring
      _ ≤ (c * N ^ 2) * (c * N ^ 2) := hmul
      _ = c ^ 2 * N ^ 4 := by ring
  have hV2N : V ^ 2 * N ≤ c ^ 2 * N ^ 5 := by
    calc
      V ^ 2 * N ≤ (c ^ 2 * N ^ 4) * N :=
        Nat.mul_le_mul_right N hV2
      _ = c ^ 2 * N ^ 5 := by ring
  have h2V2N : 2 * V ^ 2 * N ≤ 2 * c ^ 2 * N ^ 5 := by
    calc
      2 * V ^ 2 * N = 2 * (V ^ 2 * N) := by ring
      _ ≤ 2 * (c ^ 2 * N ^ 5) := Nat.mul_le_mul_left 2 hV2N
      _ = 2 * c ^ 2 * N ^ 5 := by ring
  have hVN0 : V * N ≤ c * N ^ 3 := by
    calc
      V * N ≤ (c * N ^ 2) * N := Nat.mul_le_mul_right N hV
      _ = c * N ^ 3 := by ring
  have hVN : V * N ≤ c * N ^ 5 :=
    hVN0.trans (Nat.mul_le_mul_left c hN3)
  have hsum :
      N ^ 2 + N ^ 3 + N ^ 4 + 2 * V ^ 2 * N + V * N + N ≤
        N ^ 5 + N ^ 5 + N ^ 5 + 2 * c ^ 2 * N ^ 5 +
          c * N ^ 5 + N ^ 5 := by
    exact Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add hN2 hN3)
            hN4)
          h2V2N)
        hVN)
      hN1
  calc
    v44BuildEnvelope N V ≤
        N ^ 5 + N ^ 5 + N ^ 5 + 2 * c ^ 2 * N ^ 5 +
          c * N ^ 5 + N ^ 5 := by
      simpa [v44BuildEnvelope] using hsum
    _ = (2 * c ^ 2 + c + 4) * N ^ 5 := by ring

end FixedHCFGv44
end LeanCfgProject
