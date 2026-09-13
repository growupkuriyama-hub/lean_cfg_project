import LeanCfgProject.FixedHCFGv44.BoundaryObstructionsV47
import Mathlib.Tactic

namespace LeanCfgProject
namespace FixedHCFGv44

universe v

/-!
Concrete formalization of manuscript Corollary `cor:dyck-not-rs`.

The manuscript writes the one-bracket Dyck language as the words over
`{a,b}` whose prefix balance never becomes negative and whose final balance is
zero.  Here we use the equivalent deterministic counter presentation: `a`
increments the depth, `b` decrements it, and attempting to read `b` at depth
zero rejects.

The obstruction family is exactly the manuscript family
`Xi = { b^i a^i | i >= 1 }`.
-/

inductive DyckLetter
  | a
  | b
  deriving DecidableEq, Fintype

/-- Deterministic depth scan for the one-bracket Dyck language. -/
def dyckRun : Nat → Word DyckLetter → Option Nat
  | d, [] => some d
  | d, DyckLetter.a :: w => dyckRun (d + 1) w
  | 0, DyckLetter.b :: w => none
  | Nat.succ d, DyckLetter.b :: w => dyckRun d w

/-- A block `a^n`. -/
def dyckAs (n : Nat) : Word DyckLetter :=
  List.replicate n DyckLetter.a

/-- A block `b^n`. -/
def dyckBs (n : Nat) : Word DyckLetter :=
  List.replicate n DyckLetter.b

/-- The operational presentation of the manuscript language `D_1`. -/
def Dyck1 : Language DyckLetter :=
  fun w => dyckRun 0 w = some 0

/-- Scanning concatenation is Kleisli composition of the partial depth scan. -/
theorem dyckRun_append (d : Nat) (x y : Word DyckLetter) :
    dyckRun d (x ++ y) =
      (dyckRun d x).bind (fun d' => dyckRun d' y) := by
  induction x generalizing d with
  | nil =>
      simp [dyckRun]
  | cons c x ih =>
      cases c with
      | a =>
          simp [dyckRun, ih]
      | b =>
          cases d with
          | zero => simp [dyckRun]
          | succ d => simp [dyckRun, ih]

/-- Reading `a^n` raises the depth by `n`. -/
theorem dyckRun_as (d n : Nat) :
    dyckRun d (dyckAs n) = some (d + n) := by
  induction n generalizing d with
  | zero =>
      simp [dyckAs, dyckRun]
  | succ n ih =>
      simp [dyckAs, dyckRun, ih, Nat.add_assoc]

/-- Reading at most the available number of `b` symbols lowers the depth. -/
theorem dyckRun_bs_le (d n : Nat) (h : n ≤ d) :
    dyckRun d (dyckBs n) = some (d - n) := by
  induction n generalizing d with
  | zero =>
      simp [dyckBs, dyckRun]
  | succ n ih =>
      cases d with
      | zero => omega
      | succ d =>
          have h' : n ≤ d := by omega
          simp [dyckBs, dyckRun, ih d h']

/-- Too many closing symbols force underflow. -/
theorem dyckRun_bs_gt (d n : Nat) (h : d < n) :
    dyckRun d (dyckBs n) = none := by
  induction n generalizing d with
  | zero => omega
  | succ n ih =>
      cases d with
      | zero =>
          simp [dyckBs, dyckRun]
      | succ d =>
          have h' : d < n := by omega
          simpa [dyckBs, dyckRun] using ih d h'

/-- The four-block word `a^j b^i a^i b^j` is Dyck whenever `i ≤ j`. -/
theorem dyck1_four_blocks (i j : Nat) (hij : i ≤ j) :
    dyckAs j ++ dyckBs i ++ dyckAs i ++ dyckBs j ∈ Dyck1 := by
  change dyckRun 0 (dyckAs j ++ dyckBs i ++ dyckAs i ++ dyckBs j) = some 0
  calc
    dyckRun 0 (dyckAs j ++ dyckBs i ++ dyckAs i ++ dyckBs j) =
        dyckRun j (dyckBs i ++ dyckAs i ++ dyckBs j) := by
          rw [dyckRun_append, dyckRun_as]
          simp
    _ = dyckRun (j - i) (dyckAs i ++ dyckBs j) := by
          rw [dyckRun_append, dyckRun_bs_le j i hij]
          simp
    _ = dyckRun ((j - i) + i) (dyckBs j) := by
          rw [dyckRun_append, dyckRun_as]
          simp
    _ = dyckRun j (dyckBs j) := by
          rw [Nat.sub_add_cancel hij]
    _ = some 0 := by
          simpa using dyckRun_bs_le j j (le_rfl)

/-- If `i < j`, the word `a^i b^j a^j b^i` underflows in its second block. -/
theorem dyck1_four_blocks_underflow (i j : Nat) (hij : i < j) :
    dyckAs i ++ dyckBs j ++ dyckAs j ++ dyckBs i ∉ Dyck1 := by
  change dyckRun 0 (dyckAs i ++ dyckBs j ++ dyckAs j ++ dyckBs i) ≠ some 0
  have hPrefix : dyckRun 0 (dyckAs i ++ dyckBs j) = none := by
    rw [dyckRun_append, dyckRun_as, dyckRun_bs_gt i j hij]
    simp
  have hAll :
      dyckRun 0 ((dyckAs i ++ dyckBs j) ++ (dyckAs j ++ dyckBs i)) = none := by
    rw [dyckRun_append, hPrefix]
    simp
  simpa only [List.append_assoc] using hAll

/-- The manuscript obstruction factor `b^n a^n`. -/
def dyckFactor (n : Nat) : Word DyckLetter :=
  dyckBs n ++ dyckAs n

/-- Distinct factor indices give distinct words. -/
theorem dyckFactor_injective : Function.Injective dyckFactor := by
  intro i j hEq
  have hLen := congrArg List.length hEq
  simp [dyckFactor, dyckAs, dyckBs] at hLen
  omega

/-- Every positive-index obstruction factor is a legal nonempty internal fragment. -/
theorem dyckFactor_internal (n : Nat) (hn : 1 ≤ n) :
    Internal (dyckFactor n) := by
  intro hNil
  have hLen := congrArg List.length hNil
  simp [dyckFactor, dyckAs, dyckBs] at hLen
  omega

/-- A larger `a^j, b^j` wrapper is a common context for `b^i a^i`. -/
theorem dyckFactor_in_context (i j : Nat) (hij : i ≤ j) :
    InDistribution Dyck1 (dyckFactor i) (dyckAs j) (dyckBs j) := by
  simpa [dyckFactor, List.append_assoc] using dyck1_four_blocks i j hij

/-- For `i < j`, the smaller wrapper separates the two factor distributions. -/
theorem dyckFactor_not_sameDistribution (i j : Nat) (hij : i < j) :
    ¬ SameDistribution Dyck1 (dyckFactor i) (dyckFactor j) := by
  intro hSame
  have hi :
      InDistribution Dyck1 (dyckFactor i) (dyckAs i) (dyckBs i) :=
    dyckFactor_in_context i i (le_rfl)
  have hj :
      ¬ InDistribution Dyck1 (dyckFactor j) (dyckAs i) (dyckBs i) := by
    simpa [dyckFactor, List.append_assoc] using
      dyck1_four_blocks_underflow i j hij
  exact hj ((hSame (dyckAs i) (dyckBs i)).mp hi)

/-- The infinite manuscript family `Xi = {b^i a^i | i >= 1}`. -/
def DyckXi : Set (Word DyckLetter) :=
  Set.range (fun n : Nat => dyckFactor (n + 1))

/-- `DyckXi` is infinite. -/
theorem dyckXi_infinite : DyckXi.Infinite := by
  apply Set.infinite_range_of_injective
  intro i j hEq
  have hSucc : i + 1 = j + 1 := dyckFactor_injective hEq
  omega

/-- Every member of `DyckXi` is nonempty. -/
theorem dyckXi_internal :
    ∀ x : Word DyckLetter, x ∈ DyckXi → Internal x := by
  intro x hx
  rcases hx with ⟨n, rfl⟩
  exact dyckFactor_internal (n + 1) (by omega)

/--
Every distinct pair in `DyckXi` shares a context but has unequal
two-sided distributions, exactly as in the manuscript proof.
-/
theorem dyckXi_separates :
    ∀ x : Word DyckLetter, x ∈ DyckXi →
      ∀ y : Word DyckLetter, y ∈ DyckXi → x ≠ y →
        ShareContext Dyck1 x y ∧ ¬ SameDistribution Dyck1 x y := by
  intro x hx y hy hxy
  rcases hx with ⟨i, rfl⟩
  rcases hy with ⟨j, rfl⟩
  have hij : i ≠ j := by
    intro h
    subst j
    exact hxy rfl
  constructor
  · let k := max (i + 1) (j + 1)
    refine ⟨dyckAs k, dyckBs k, ?_, ?_⟩
    · exact dyckFactor_in_context (i + 1) k (Nat.le_max_left _ _)
    · exact dyckFactor_in_context (j + 1) k (Nat.le_max_right _ _)
  · rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact dyckFactor_not_sameDistribution (i + 1) (j + 1) (by omega)
    · intro hSame
      exact dyckFactor_not_sameDistribution (j + 1) (i + 1) (by omega)
        (sameDistribution_symm hSame)

/-- Manuscript Corollary `cor:dyck-not-rs`: `D_1` is outside every finite-monoid slice. -/
theorem corollary_dyck_not_rs_v47 :
    ¬ RecognizablySubstitutableAt.{0, v} Dyck1 := by
  exact finite_monoid_obstruction_v47
    Dyck1 DyckXi dyckXi_infinite dyckXi_internal dyckXi_separates

end FixedHCFGv44
end LeanCfgProject
