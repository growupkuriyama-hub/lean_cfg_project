import Mathlib.Tactic
import LeanCfgProject.FiniteSaturation

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

/-
Finite stopping core.

This file isolates the purely numerical core behind finite saturation stopping.

It proves that a monotone sequence of natural numbers bounded by `B` must have
a local fixed point `f (N+1) = f N` for some `N ≤ B`.

This is deliberately separated from the `Set.ncard`/finite-saturation measure
argument.  The next layer can use this theorem after defining a cardinality
measure for saturation stages.
-/

/--
A monotone bounded sequence of natural numbers has a local stopping point
within the bound.

This is the arithmetic core for finite saturation stopping: if a monotone
measure cannot exceed `B`, it cannot strictly increase for all stages
`0, 1, ..., B`.
-/
theorem exists_le_eq_succ_of_monotone_bounded
    {f : Nat → Nat}
    (hmono : Monotone f)
    {B : Nat}
    (hb : ∀ n : Nat, f n ≤ B) :
    ∃ N ≤ B, f (N + 1) = f N := by
  by_contra h
  push_neg at h
  -- If there is no local equality up to `B`, monotonicity makes the sequence
  -- strictly increase at every stage `n ≤ B`.
  have hstrict : ∀ n : Nat, n ≤ B → f n < f (n + 1) := by
    intro n hn
    have hle : f n ≤ f (n + 1) := hmono (Nat.le_succ n)
    have hne : f n ≠ f (n + 1) := by
      exact Ne.symm (h n hn)
    exact lt_of_le_of_ne hle hne
  -- Hence after `k` steps the value has increased by at least `k`.
  have key : ∀ k : Nat, k ≤ B + 1 → f 0 + k ≤ f k := by
    intro k hk
    induction k with
    | zero =>
        simp
    | succ k ih =>
        have hkB : k ≤ B := by omega
        have ihk : f 0 + k ≤ f k := ih (by omega)
        have hlt : f k < f (k + 1) := hstrict k hkB
        omega
  have hKey : f 0 + (B + 1) ≤ f (B + 1) :=
    key (B + 1) (le_refl _)
  have hBound : f (B + 1) ≤ B := hb (B + 1)
  omega

/--
Bound-free corollary: a monotone sequence bounded by `B` has some local
stopping point.
-/
theorem exists_eq_succ_of_monotone_bounded
    {f : Nat → Nat}
    (hmono : Monotone f)
    {B : Nat}
    (hb : ∀ n : Nat, f n ≤ B) :
    ∃ N : Nat, f (N + 1) = f N := by
  obtain ⟨N, _hNB, hN⟩ :=
    exists_le_eq_succ_of_monotone_bounded hmono hb
  exact ⟨N, hN⟩

/--
Contrapositive-style helper: if a monotone sequence has no local fixed point up
to `B`, then its value at `B+1` must exceed `B`.

This form is sometimes easier to use when deriving contradictions from finite
cardinality bounds.
-/
theorem lt_of_no_eq_succ_of_monotone
    {f : Nat → Nat}
    (hmono : Monotone f)
    {B : Nat}
    (hneq : ∀ N : Nat, N ≤ B → f (N + 1) ≠ f N) :
    B < f (B + 1) := by
  have hstrict : ∀ n : Nat, n ≤ B → f n < f (n + 1) := by
    intro n hn
    have hle : f n ≤ f (n + 1) := hmono (Nat.le_succ n)
    have hne : f n ≠ f (n + 1) := by
      exact Ne.symm (hneq n hn)
    exact lt_of_le_of_ne hle hne
  have key : ∀ k : Nat, k ≤ B + 1 → f 0 + k ≤ f k := by
    intro k hk
    induction k with
    | zero =>
        simp
    | succ k ih =>
        have hkB : k ≤ B := by omega
        have ihk : f 0 + k ≤ f k := ih (by omega)
        have hlt : f k < f (k + 1) := hstrict k hkB
        omega
  have hKey : f 0 + (B + 1) ≤ f (B + 1) :=
    key (B + 1) (le_refl _)
  omega

end LeanCfgProject
