import LeanCfgProject.TCS1.DeltaStarTyping

/-!
# TCS #1 v78: fixed-h proof kernel for Delta-star

This module develops the parser-side invariants needed for the fixed-h_star
part of the nonlinear Delta-star proposition.  The typing itself is defined
in DeltaStarTyping.lean; here we connect it to exact balance and parser
entry-height information.

The final goal of this module is the paper statement that DeltaStar.Language
is substitutable under DeltaStar.starTyping.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

open Symbol

/-- Signed a/b balance. -/
def balance : Word Symbol → Int
  | [] => 0
  | a :: w => 1 + balance w
  | b :: w => -1 + balance w

@[simp] theorem balance_nil :
    balance ([] : Word Symbol) = 0 := by
  rfl

@[simp] theorem balance_cons_a
    (w : Word Symbol) :
    balance (a :: w) = 1 + balance w := by
  rfl

@[simp] theorem balance_cons_b
    (w : Word Symbol) :
    balance (b :: w) = -1 + balance w := by
  rfl

@[simp] theorem balance_append
    (u v : Word Symbol) :
    balance (u ++ v) = balance u + balance v := by
  induction u with
  | nil =>
      simp
  | cons s u ih =>
      cases s <;> simp [ih, add_assoc]

@[simp] theorem balance_replicate_a
    (n : Nat) :
    balance (List.replicate n a) = (n : Int) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.replicate_succ]
      simp [ih]
      omega

@[simp] theorem balance_replicate_b
    (n : Nat) :
    balance (List.replicate n b) = -(n : Int) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.replicate_succ]
      simp [ih]

/-- Numerical height represented by a parser mode. -/
def modeHeight : Mode → Int
  | .zero => 0
  | .rising n => (n : Int) + 1
  | .falling n => (n : Int) + 1

theorem modeHeight_nonneg
    (q : Mode) :
    0 ≤ modeHeight q := by
  cases q <;> simp [modeHeight] <;> omega

/-- One successful parser step changes height by the symbol balance. -/
theorem step_height
    {q r : Mode} {s : Symbol}
    (hstep : step q s = some r) :
    modeHeight r =
      modeHeight q + balance [s] := by
  cases q with
  | zero =>
      cases s with
      | a =>
          simp [step] at hstep
          subst r
          simp [modeHeight]
      | b =>
          simp [step] at hstep
  | rising n =>
      cases s with
      | a =>
          simp [step] at hstep
          subst r
          simp [modeHeight]
      | b =>
          cases n with
          | zero =>
              simp [step] at hstep
              subst r
              simp [modeHeight]
          | succ n =>
              simp [step] at hstep
              subst r
              simp [modeHeight]
  | falling n =>
      cases s with
      | a =>
          simp [step] at hstep
      | b =>
          cases n with
          | zero =>
              simp [step] at hstep
              subst r
              simp [modeHeight]
          | succ n =>
              simp [step] at hstep
              subst r
              simp [modeHeight]

/-- Peel the first successful step from a successful nonempty scan. -/
theorem scan_cons_success
    {q r : Mode} {s : Symbol}
    {w : Word Symbol}
    (hscan : scan q (s :: w) = some r) :
    ∃ q' : Mode,
      step q s = some q' ∧
      scan q' w = some r := by
  simp only [scan] at hscan
  cases hs : step q s with
  | none =>
      simp [hs] at hscan
  | some q' =>
      refine ⟨q', rfl, ?_⟩
      simpa [hs] using hscan

/-- Successful scanning realizes exact signed balance as height change. -/
theorem scan_height
    {q r : Mode} {w : Word Symbol}
    (hscan : scan q w = some r) :
    modeHeight r =
      modeHeight q + balance w := by
  induction w generalizing q with
  | nil =>
      simp [scan] at hscan
      subst r
      simp
  | cons s w ih =>
      obtain ⟨q', hstep, htail⟩ :=
        scan_cons_success hscan
      have h₁ := ih htail
      have h₂ := step_height hstep
      cases s <;> simp at h₂ ⊢ <;> omega

/-- Every accepted Delta-star word has total balance zero. -/
theorem balance_mem_zero
    {w : Word Symbol}
    (hw : w ∈ Language) :
    balance w = 0 := by
  have hh :=
    scan_height
      (q := Mode.zero)
      (r := Mode.zero)
      (w := w)
      hw
  simp [modeHeight] at hh
  omega

/-- A shared accepting context forces the two factors to have equal balance. -/
theorem balance_eq_of_sharedContext
    {x y : Word Symbol}
    (hshared : HaveSharedContext Language x y) :
    balance x = balance y := by
  rcases hshared with ⟨u, v, hx, hy⟩
  have hx0 := balance_mem_zero hx
  have hy0 := balance_mem_zero hy
  simp only [balance_append] at hx0 hy0
  omega

/--
If a b-step is immediately followed by a successful a-step, the entry height
before that b must have been exactly one.
-/
theorem step_b_then_a_entry_height_one
    {q p r : Mode}
    (hb : step q b = some p)
    (ha : step p a = some r) :
    modeHeight q = 1 := by
  cases q with
  | zero =>
      simp [step] at hb
  | rising n =>
      cases n with
      | zero =>
          simp [step] at hb
          subst p
          simp [modeHeight]
      | succ n =>
          simp [step] at hb
          subst p
          simp [step] at ha
  | falling n =>
      cases n with
      | zero =>
          simp [step] at hb
          subst p
          simp [modeHeight]
      | succ n =>
          simp [step] at hb
          subst p
          simp [step] at ha

/--
A successful scan of a factor containing an internal ba transition determines
the parser entry height uniquely.
-/
theorem entry_height_unique_of_containsBA
    {w : Word Symbol}
    {q₁ q₂ r₁ r₂ : Mode}
    (hba : containsBA w = true)
    (h₁ : scan q₁ w = some r₁)
    (h₂ : scan q₂ w = some r₂) :
    modeHeight q₁ = modeHeight q₂ := by
  induction w generalizing q₁ q₂ r₁ r₂ with
  | nil =>
      simp [containsBA] at hba
  | cons s w ih =>
      cases w with
      | nil =>
          simp [containsBA] at hba
      | cons t rest =>
          obtain ⟨p₁, hs₁, ht₁⟩ :=
            scan_cons_success h₁
          obtain ⟨p₂, hs₂, ht₂⟩ :=
            scan_cons_success h₂
          cases s with
          | a =>
              cases t with
              | a =>
                  have hba' :
                      containsBA (a :: rest) = true := by
                    simpa [containsBA] using hba
                  have hp :=
                    ih hba' ht₁ ht₂
                  have hh₁ := step_height hs₁
                  have hh₂ := step_height hs₂
                  simp at hh₁ hh₂
                  omega
              | b =>
                  have hba' :
                      containsBA (b :: rest) = true := by
                    simpa [containsBA] using hba
                  have hp :=
                    ih hba' ht₁ ht₂
                  have hh₁ := step_height hs₁
                  have hh₂ := step_height hs₂
                  simp at hh₁ hh₂
                  omega
          | b =>
              cases t with
              | a =>
                  obtain ⟨z₁, ha₁, _⟩ :=
                    scan_cons_success ht₁
                  obtain ⟨z₂, ha₂, _⟩ :=
                    scan_cons_success ht₂
                  have hq₁ :=
                    step_b_then_a_entry_height_one
                      hs₁ ha₁
                  have hq₂ :=
                    step_b_then_a_entry_height_one
                      hs₂ ha₂
                  omega
              | b =>
                  have hba' :
                      containsBA (b :: rest) = true := by
                    simpa [containsBA] using hba
                  have hp :=
                    ih hba' ht₁ ht₂
                  have hh₁ := step_height hs₁
                  have hh₂ := step_height hs₂
                  simp at hh₁ hh₂
                  omega

/-- Once a b has occurred and no ba occurs, the remaining suffix is all b's. -/
theorem suffix_all_b_of_noBA
    (w : Word Symbol)
    (hba : containsBA (b :: w) = false) :
    w = List.replicate w.length b := by
  induction w with
  | nil =>
      rfl
  | cons s w ih =>
      cases s with
      | a =>
          simp [containsBA] at hba
      | b =>
          have htail :
              containsBA (b :: w) = false := by
            simpa [containsBA] using hba
          have hw := ih htail
          rw [hw]
          simp [List.replicate_succ]

/-- A word with no internal ba factor has the canonical a* b* shape. -/
theorem noBA_shape
    (w : Word Symbol)
    (hba : containsBA w = false) :
    ∃ p q : Nat,
      w =
        List.replicate p a ++
          List.replicate q b := by
  induction w with
  | nil =>
      exact ⟨0, 0, by simp⟩
  | cons s w ih =>
      cases s with
      | a =>
          have htail :
              containsBA w = false := by
            cases w with
            | nil =>
                rfl
            | cons t rest =>
                cases t <;>
                  simpa [containsBA] using hba
          obtain ⟨p, q, hpq⟩ := ih htail
          refine ⟨p + 1, q, ?_⟩
          rw [hpq]
          simp [List.replicate_succ, List.append_assoc,
            Nat.add_comm]
      | b =>
          have hw := suffix_all_b_of_noBA w hba
          refine ⟨0, w.length + 1, ?_⟩
          rw [hw]
          simp [List.replicate_succ, Nat.add_comm]

/-- Nonempty no-ba words split into pure-a, pure-b, or mixed a+ b+ cases. -/
theorem noBA_nonempty_shape_cases
    {w : Word Symbol}
    (hne : w ≠ [])
    (hba : containsBA w = false) :
    (∃ p : Nat,
        0 < p ∧
        w = List.replicate p a) ∨
    (∃ q : Nat,
        0 < q ∧
        w = List.replicate q b) ∨
    (∃ p q : Nat,
        0 < p ∧ 0 < q ∧
        w =
          List.replicate p a ++
            List.replicate q b) := by
  obtain ⟨p, q, hpq⟩ := noBA_shape w hba
  by_cases hp0 : p = 0
  · subst p
    by_cases hq0 : q = 0
    · subst q
      simp at hpq
      exact False.elim (hne hpq)
    · right
      left
      refine ⟨q, Nat.pos_of_ne_zero hq0, ?_⟩
      simpa using hpq
  · by_cases hq0 : q = 0
    · subst q
      left
      refine ⟨p, Nat.pos_of_ne_zero hp0, ?_⟩
      simpa using hpq
    · right
      right
      exact
        ⟨p, q,
          Nat.pos_of_ne_zero hp0,
          Nat.pos_of_ne_zero hq0,
          hpq⟩

end DeltaStar
end TCS1
end LeanCfgProject
