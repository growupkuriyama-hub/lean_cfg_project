import LeanCfgProject.FixedHCFGv44.ClarkDyckStrictnessV49

namespace LeanCfgProject
namespace FixedHCFGv44

/-!
Operational lemmas preparing the first-return decomposition of `Dyck1`.
These are the semantic ingredients needed to identify the manuscript grammar
`S -> a S b S | lambda` (or its binary SSBNF reification) with the deterministic
counter presentation already used by the obstruction proof.
-/

/-- Dyck words are closed under concatenation. -/
theorem dyck1_append_v49
    {x y : Word DyckLetter}
    (hx : x ∈ Dyck1) (hy : y ∈ Dyck1) :
    x ++ y ∈ Dyck1 := by
  change dyckRun 0 x = some 0 at hx
  change dyckRun 0 y = some 0 at hy
  change dyckRun 0 (x ++ y) = some 0
  rw [dyckRun_append, hx]
  simpa using hy

/-- Wrapping a Dyck word in one matching pair gives a Dyck word. -/
theorem dyck1_wrap_v49
    {x : Word DyckLetter}
    (hx : x ∈ Dyck1) :
    DyckLetter.a :: (x ++ [DyckLetter.b]) ∈ Dyck1 := by
  change dyckRun 0 (DyckLetter.a :: (x ++ [DyckLetter.b])) = some 0
  change dyckRun 1 (x ++ [DyckLetter.b]) = some 0
  rw [dyckRun_append, dyck1_run_from_depth 1 hx]
  simp [dyckRun]

/-- The constructive half of the recursive Dyck equation
`D = {epsilon} union a D b D`. -/
theorem dyck1_wrap_append_v49
    {x y : Word DyckLetter}
    (hx : x ∈ Dyck1) (hy : y ∈ Dyck1) :
    DyckLetter.a :: (x ++ DyckLetter.b :: y) ∈ Dyck1 := by
  have hWrap : DyckLetter.a :: (x ++ [DyckLetter.b]) ∈ Dyck1 :=
    dyck1_wrap_v49 hx
  have hCat := dyck1_append_v49 hWrap hy
  simpa only [List.cons_append, List.append_assoc, List.singleton_append] using hCat

/-- A nonempty Dyck word must begin with the opening letter `a`. -/
theorem dyck1_nonempty_starts_a_v49
    {w : Word DyckLetter}
    (hw : w ∈ Dyck1) (hne : w ≠ []) :
    ∃ r : Word DyckLetter, w = DyckLetter.a :: r := by
  cases w with
  | nil => exact (hne rfl).elim
  | cons c r =>
      cases c with
      | a => exact ⟨r, rfl⟩
      | b =>
          change dyckRun 0 (DyckLetter.b :: r) = some 0 at hw
          simp [dyckRun] at hw

/-- After the first opening letter of a nonempty Dyck word, the remaining scan
starts at depth one and eventually returns to zero. -/
theorem dyck1_tail_runs_one_to_zero_v49
    {r : Word DyckLetter}
    (h : DyckLetter.a :: r ∈ Dyck1) :
    dyckRun 1 r = some 0 := by
  exact h

end FixedHCFGv44
end LeanCfgProject
