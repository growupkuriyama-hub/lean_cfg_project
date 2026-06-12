import LeanCfgProject.ObservedResidualConcept.ObservationCounterexample
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open CExSym
open Parity

lemma parityWord_length_one_odd
    (w : Word CExSym)
    (hw : w.length = 1) :
    parityHom.h w = odd := by
  cases w with
  | nil =>
      simp at hw
  | cons x xs =>
      cases xs with
      | nil =>
          simp [parityHom, parityWord, parityLetter, Parity.mul]
      | cons y ys =>
          simp at hw

lemma parity_context_values_of_eq_pair
    (letter t1 t2 : CExSym)
    (hneq : letter ≠ t2)
    (l r : Word CExSym)
    (heq : l ++ [letter] ++ r = [t1, t2]) :
    parityHom.h l = even ∧ parityHom.h r = odd := by
  have hlen := congrArg List.length heq
  simp [List.length_append] at hlen
  have hsum : l.length + r.length = 1 := by omega
  have hl_cases : l.length = 0 ∨ l.length = 1 := by omega
  rcases hl_cases with hl0 | hl1
  · cases l with
    | nil =>
        have hr1 : r.length = 1 := by simpa using hsum
        constructor
        · rfl
        · exact parityWord_length_one_odd r hr1
    | cons x xs =>
        simp at hl0
  · cases l with
    | nil =>
        simp at hl1
    | cons x xs =>
        cases xs with
        | cons y ys =>
            simp at hl1
        | nil =>
            have hr0 : r.length = 0 := by omega
            cases r with
            | nil =>
                exfalso
                apply hneq
                have heq' : [x, letter] = [t1, t2] := by
                  simpa using heq
                injection heq' with hx htail
                injection htail
            | cons y ys =>
                simp at hr0

theorem even_odd_context_for_a :
    (even, odd) ∈
      HTypedContextTypes parityHom counterexampleLanguage [a] := by
  refine ⟨[], [b], ?_, ?_⟩
  · rfl
  · left
    rfl

theorem even_odd_context_for_c :
    (even, odd) ∈
      HTypedContextTypes parityHom counterexampleLanguage [c] := by
  refine ⟨[], [d], ?_, ?_⟩
  · rfl
  · right
    rfl

lemma parity_context_values_for_a
    (l r : Word CExSym)
    (hmem : l ++ [a] ++ r ∈ counterexampleLanguage) :
    parityHom.h l = even ∧ parityHom.h r = odd := by
  rcases hmem with hAB | hCD
  · exact parity_context_values_of_eq_pair a a b (by decide) l r hAB
  · exact parity_context_values_of_eq_pair a c d (by decide) l r hCD

lemma parity_context_values_for_c
    (l r : Word CExSym)
    (hmem : l ++ [c] ++ r ∈ counterexampleLanguage) :
    parityHom.h l = even ∧ parityHom.h r = odd := by
  rcases hmem with hAB | hCD
  · exact parity_context_values_of_eq_pair c a b (by decide) l r hAB
  · exact parity_context_values_of_eq_pair c c d (by decide) l r hCD

lemma context_type_for_a_is_even_odd
    {mn : Parity × Parity}
    (hctx :
      mn ∈ HTypedContextTypes parityHom counterexampleLanguage [a]) :
    mn = (even, odd) := by
  rcases hctx with ⟨l, r, hmn, hmem⟩
  have hp := parity_context_values_for_a l r hmem
  calc
    mn = (parityHom.h l, parityHom.h r) := hmn
    _ = (even, odd) := by rw [hp.1, hp.2]

lemma context_type_for_c_is_even_odd
    {mn : Parity × Parity}
    (hctx :
      mn ∈ HTypedContextTypes parityHom counterexampleLanguage [c]) :
    mn = (even, odd) := by
  rcases hctx with ⟨l, r, hmn, hmem⟩
  have hp := parity_context_values_for_c l r hmem
  calc
    mn = (parityHom.h l, parityHom.h r) := hmn
    _ = (even, odd) := by rw [hp.1, hp.2]

theorem htyped_context_a_eq_c :
    HTypedContextTypes parityHom counterexampleLanguage [a] =
      HTypedContextTypes parityHom counterexampleLanguage [c] := by
  apply Set.Subset.antisymm
  · intro mn hmn
    have hpair := context_type_for_a_is_even_odd hmn
    rw [hpair]
    exact even_odd_context_for_c
  · intro mn hmn
    have hpair := context_type_for_c_is_even_odd hmn
    rw [hpair]
    exact even_odd_context_for_a

theorem same_observation_a_c :
    SameHTypedObservation
      parityHom counterexampleLanguage [a] [c] := by
  constructor
  · rfl
  · exact htyped_context_a_eq_c

theorem naive_observation_not_concat_compatible :
    ∃ u v s t : Word CExSym,
      SameHTypedObservation parityHom counterexampleLanguage u v ∧
      SameHTypedObservation parityHom counterexampleLanguage s t ∧
      ¬ SameHTypedObservation
          parityHom counterexampleLanguage (u ++ s) (v ++ t) := by
  exact observation_concat_obstruction_from_a_c same_observation_a_c

end LeanCfgProject
