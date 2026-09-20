import LeanCfgProject.TCS1.LinearSeparatorTyping

/-!
# TCS #1 v77: distribution arithmetic for the separator language

This module formalizes the arithmetic core of the revised Section 8.1 proof.
For a one-center factor a^i z b^j, membership after a pure-power context
(a^m,b^n) is characterized exactly by the two boundary exponents.

This is the Lean form of the manuscript's balance/parity calculation:
the e-branch depends only on the exponent difference, while the c/d branch
adds the parity condition on the left exponent.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol

/-- A possibly unbalanced one-center word a^i z b^j. -/
def lpmOneCenter
    (i : Nat) (z : LpmSymbol) (j : Nat) :
    Word LpmSymbol :=
  List.replicate i a ++ [z] ++ List.replicate j b

@[simp] theorem lpmOneCenter_balanced
    (n : Nat) (z : LpmSymbol) :
    lpmOneCenter n z n = lpmCore n z := by
  rfl

/--
A one-center word belongs to L_{±,e} exactly when its two exponents agree
and the center/parity condition is accepted.
-/
theorem lpmOneCenter_mem_iff
    (i j : Nat) (z : LpmSymbol) :
    lpmOneCenter i z j ∈ LpmLanguage ↔
      i = j ∧ LpmAccepted i z := by
  constructor
  · rintro ⟨n, z', hword, hacc⟩
    have ha :=
      congrArg (List.count a) hword
    have hb :=
      congrArg (List.count b) hword
    have hc :=
      congrArg (List.count c) hword
    have hd :=
      congrArg (List.count d) hword
    have he :=
      congrArg (List.count e) hword
    cases z <;> cases z' <;>
      simp_all [lpmOneCenter, lpmCore, LpmAccepted] <;>
      omega
  · rintro ⟨hij, hacc⟩
    subst j
    simpa [lpmOneCenter, lpmCore] using
      (lpmCore_mem_iff i z).2 hacc

/--
Adding a pure-a context on the left and a pure-b context on the right just
adds to the two exponents.
-/
theorem lpm_power_context_word
    (m n i j : Nat) (z : LpmSymbol) :
    List.replicate m a ++
        lpmOneCenter i z j ++
        List.replicate n b =
      lpmOneCenter (m + i) z (j + n) := by
  unfold lpmOneCenter
  rw [List.replicate_add m i a]
  rw [List.replicate_add j n b]
  simp [List.append_assoc]


