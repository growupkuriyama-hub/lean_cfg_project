import Mathlib.Tactic
import LeanCfgProject.ObservedResidualConcept.LanguageQuotient
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG

universe u

inductive CExSym where
  | a
  | b
  | c
  | d
deriving DecidableEq, Fintype, Repr

inductive Parity where
  | even
  | odd
deriving DecidableEq, Fintype, Repr

namespace Parity

def mul : Parity → Parity → Parity
  | even, x => x
  | odd, even => odd
  | odd, odd => even

instance : Monoid Parity where
  one := even
  mul := mul
  mul_assoc := by
    intro x y z
    cases x <;> cases y <;> cases z <;> rfl
  one_mul := by
    intro x
    cases x <;> rfl
  mul_one := by
    intro x
    cases x <;> rfl

end Parity

open CExSym
open Parity

def parityLetter (_ : CExSym) : Parity :=
  odd

def parityWord : Word CExSym → Parity
  | [] => 1
  | x :: xs => parityLetter x * parityWord xs

theorem parityWord_append
    (u v : Word CExSym) :
    parityWord (u ++ v) = parityWord u * parityWord v := by
  induction u with
  | nil =>
      simp [parityWord]
  | cons x xs ih =>
      simp [parityWord, ih, mul_assoc]

def parityHom : FixedFiniteMonoidHom CExSym Parity where
  h := parityWord
  map_empty := rfl
  map_append := parityWord_append

def counterexampleLanguage : Language CExSym :=
  { w | w = [a, b] ∨ w = [c, d] }

theorem even_even_context_for_ab :
    (even, even) ∈
      HTypedContextTypes parityHom counterexampleLanguage [a, b] := by
  refine ⟨[], [], ?_, ?_⟩
  · rfl
  · left
    rfl

lemma no_context_for_cb
    (l r : Word CExSym) :
    ¬ (l ++ [c, b] ++ r ∈ counterexampleLanguage) := by
  intro hmem
  rcases hmem with hab | hcd
  · have hlen := congrArg List.length hab
    simp at hlen
    have hl0 : l.length = 0 := by omega
    have hr0 : r.length = 0 := by omega
    cases l with
    | nil =>
        cases r with
        | nil =>
            simp at hab
        | cons rh rt =>
            simp at hr0
    | cons lh lt =>
        simp at hl0
  · have hlen := congrArg List.length hcd
    simp at hlen
    have hl0 : l.length = 0 := by omega
    have hr0 : r.length = 0 := by omega
    cases l with
    | nil =>
        cases r with
        | nil =>
            simp at hcd
        | cons rh rt =>
            simp at hr0
    | cons lh lt =>
        simp at hl0

theorem even_even_not_context_for_cb :
    (even, even) ∉
      HTypedContextTypes parityHom counterexampleLanguage [c, b] := by
  intro hctx
  rcases hctx with ⟨l, r, hpair, hmem⟩
  exact no_context_for_cb l r hmem

theorem not_same_observation_ab_cb :
    ¬ SameHTypedObservation
        parityHom counterexampleLanguage [a, b] [c, b] := by
  intro hobs
  have hleft :
      (even, even) ∈
        HTypedContextTypes parityHom counterexampleLanguage [a, b] :=
    even_even_context_for_ab
  have hright :
      (even, even) ∈
        HTypedContextTypes parityHom counterexampleLanguage [c, b] := by
    simpa [hobs.2] using hleft
  exact even_even_not_context_for_cb hright

theorem same_observation_b_b :
    SameHTypedObservation
      parityHom counterexampleLanguage [b] [b] := by
  exact sameHTypedObservation_refl parityHom counterexampleLanguage [b]

theorem observation_concat_obstruction_from_a_c
    (hac :
      SameHTypedObservation
        parityHom counterexampleLanguage [a] [c]) :
    ∃ u v s t : Word CExSym,
      SameHTypedObservation parityHom counterexampleLanguage u v ∧
      SameHTypedObservation parityHom counterexampleLanguage s t ∧
      ¬ SameHTypedObservation
          parityHom counterexampleLanguage (u ++ s) (v ++ t) := by
  refine ⟨[a], [c], [b], [b], hac, same_observation_b_b, ?_⟩
  simpa using not_same_observation_ab_cb

end LeanCfgProject
