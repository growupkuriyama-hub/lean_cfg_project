import LeanCfgProject.FixedHCFGv44.ClarkCongruentialInitialSetV49
import LeanCfgProject.FixedHCFGv44.DyckObstructionV47

namespace LeanCfgProject
namespace FixedHCFGv44

universe v

/-!
Strictness core for TCS v49 Proposition `prop:clark-congruential-comparison`.

The manuscript uses the one-bracket Dyck language as the strictness witness.
Its one-nonterminal grammar is congruential because replacing one balanced
Dyck factor by another balanced Dyck factor preserves membership in every
surrounding context.  We prove that language-theoretic statement directly for
our deterministic-counter presentation of `D_1`.
-/

/--
If a Dyck scan succeeds from depth `d` with final depth `e`, then starting `k`
levels deeper also succeeds and finishes `k` levels deeper.
-/
theorem dyckRun_shift_success
    (k : Nat) {d e : Nat} {w : Word DyckLetter}
    (h : dyckRun d w = some e) :
    dyckRun (d + k) w = some (e + k) := by
  induction w generalizing d e with
  | nil =>
      simp [dyckRun] at h ⊢
      omega
  | cons c w ih =>
      cases c with
      | a =>
          simp only [dyckRun] at h ⊢
          have h' := ih (d := d + 1) (e := e) h
          convert h' using 1 <;> omega
      | b =>
          cases d with
          | zero =>
              simp [dyckRun] at h
          | succ d =>
              simp only [dyckRun] at h
              have h' := ih (d := d) (e := e) h
              simpa [Nat.succ_add] using h'

/-- A balanced Dyck word is neutral when scanned from any initial depth. -/
theorem dyck1_run_from_depth
    (d : Nat) {w : Word DyckLetter}
    (hw : w ∈ Dyck1) :
    dyckRun d w = some d := by
  have h := dyckRun_shift_success d (d := 0) (e := 0) (w := w) hw
  simpa using h

/--
Replacing a balanced Dyck factor by any other balanced Dyck factor preserves
membership in an arbitrary two-sided context.
-/
theorem dyck1_balanced_replacement
    {x y p q : Word DyckLetter}
    (hx : x ∈ Dyck1) (hy : y ∈ Dyck1)
    (hpxq : p ++ x ++ q ∈ Dyck1) :
    p ++ y ++ q ∈ Dyck1 := by
  change dyckRun 0 (p ++ x ++ q) = some 0 at hpxq
  change dyckRun 0 (p ++ y ++ q) = some 0
  have hpxq' : dyckRun 0 (p ++ (x ++ q)) = some 0 := by
    simpa only [List.append_assoc] using hpxq
  rw [dyckRun_append] at hpxq'
  cases hp : dyckRun 0 p with
  | none =>
      simp [hp] at hpxq'
  | some d =>
      have hxD : dyckRun d x = some d := dyck1_run_from_depth d hx
      have hyD : dyckRun d y = some d := dyck1_run_from_depth d hy
      have hq : dyckRun d q = some 0 := by
        simpa [dyckRun_append, hxD] using hpxq'
      have hpyq : dyckRun 0 (p ++ (y ++ q)) = some 0 := by
        rw [dyckRun_append, hp]
        simp [dyckRun_append, hyD, hq]
      simpa only [List.append_assoc] using hpyq

/-- All balanced Dyck words lie in one syntactic congruence class of `D_1`. -/
theorem dyck1_syntacticallyHomogeneous_v49 :
    SyntacticallyHomogeneousV49 Dyck1 Dyck1 := by
  intro x hx y hy
  intro p q
  constructor
  · intro hpxq
    exact dyck1_balanced_replacement hx hy hpxq
  · intro hpyq
    exact dyck1_balanced_replacement hy hx hpyq

/--
The manuscript strictness witness: `D_1` has the one-class congruential
property used by the grammar `S -> a S b S | lambda`, but lies outside every
finite-monoid substitutable slice.
-/
theorem dyck1_clark_strictness_core_v49 :
    SyntacticallyHomogeneousV49 Dyck1 Dyck1 ∧
      ¬ RecognizablySubstitutableAt.{0, v} Dyck1 := by
  exact ⟨dyck1_syntacticallyHomogeneous_v49,
    corollary_dyck_not_rs_v47⟩

end FixedHCFGv44
end LeanCfgProject
