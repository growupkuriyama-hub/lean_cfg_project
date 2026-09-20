import LeanCfgProject.TCS1.LinearSeparatorDistribution

/-!
# TCS #1 v77: pure-power context formulas for L_{±,e}

For center-containing factors, Section 8.1 reduces every admissible context
to a pair (a^m,b^n).  This module records the exact arithmetic membership
conditions for such contexts.  The separate context-shape lemma will justify
that no other contexts occur.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol

theorem lpm_power_context_c_mem_iff
    (m n i j : Nat) :
    List.replicate m a ++
        lpmOneCenter i c j ++
        List.replicate n b ∈ LpmLanguage ↔
      m + i = j + n ∧ (m + i) % 2 = 0 := by
  rw [lpm_power_context_word]
  exact lpmOneCenter_c_mem_iff (m + i) (j + n)

theorem lpm_power_context_d_mem_iff
    (m n i j : Nat) :
    List.replicate m a ++
        lpmOneCenter i d j ++
        List.replicate n b ∈ LpmLanguage ↔
      m + i = j + n ∧ (m + i) % 2 = 1 := by
  rw [lpm_power_context_word]
  exact lpmOneCenter_d_mem_iff (m + i) (j + n)

theorem lpm_power_context_e_mem_iff
    (m n i j : Nat) :
    List.replicate m a ++
        lpmOneCenter i e j ++
        List.replicate n b ∈ LpmLanguage ↔
      m + i = j + n := by
  rw [lpm_power_context_word]
  exact lpmOneCenter_e_mem_iff (m + i) (j + n)

/-- Balance equality is exactly what is needed to transfer e-branch pure contexts. -/
theorem lpm_e_power_context_transfer
    {i j i' j' m n : Nat}
    (hbal : i + j' = i' + j) :
    (List.replicate m a ++
          lpmOneCenter i e j ++
          List.replicate n b ∈ LpmLanguage ↔
      List.replicate m a ++
          lpmOneCenter i' e j' ++
          List.replicate n b ∈ LpmLanguage) := by
  rw [lpm_power_context_e_mem_iff, lpm_power_context_e_mem_iff]
  omega


end TCS1
end LeanCfgProject
