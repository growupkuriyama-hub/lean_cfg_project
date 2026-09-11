import Mathlib.Data.List.Chain
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.LinearBounds

namespace LeanCfgProject
namespace FixedHCFG

universe u

/-!
The list-theoretic core of Lemma 7.3 in the TCS manuscript.

A strict linear derivation has a unique nonterminal spine.  At this level we
represent the spine simply by a list whose adjacent states satisfy a one-step
relation.  If the same state occurs twice, the intervening cycle may be
spliced out: the prefix ending at the first occurrence and the suffix starting
at the second occurrence fit because the two endpoint states are equal.

This is deliberately a statement about validity and spine length, not equality
of terminal yields.  In the manuscript the deleted strict-linear segment
carries terminal material, so the resulting derivation generally has a
different (shorter) yield.
-/

/--
Lemma 7.3, relational spine form: a repeated state can be deleted from a valid
strict-linear spine, together with all states between its two occurrences.
-/
theorem lemma_7_3_delete_cycle
    {W : Type u} {step : W → W → Prop}
    (pre middle post : List W) (x : W)
    (hchain : List.IsChain step
      (pre ++ (x :: middle ++ (x :: post)))) :
    List.IsChain step (pre ++ (x :: post)) := by
  have hFirst :
      List.IsChain step (pre ++ [x]) ∧
        List.IsChain step (x :: middle ++ (x :: post)) := by
    exact (List.isChain_split (R := step) (c := x)
      (l₁ := pre) (l₂ := middle ++ (x :: post))).mp hchain
  have hSecond :
      List.IsChain step (x :: middle ++ [x]) ∧
        List.IsChain step (x :: post) := by
    exact (List.isChain_cons_split (R := step) (a := x) (c := x)
      (l₁ := middle) (l₂ := post)).mp hFirst.2
  exact (List.isChain_split (R := step) (c := x)
    (l₁ := pre) (l₂ := post)).mpr ⟨hFirst.1, hSecond.2⟩

/-- Deleting the repeated-state segment strictly shortens the spine. -/
theorem lemma_7_3_delete_cycle_shorter
    {W : Type u} (pre middle post : List W) (x : W) :
    (pre ++ (x :: post)).length <
      (pre ++ (x :: middle ++ (x :: post))).length := by
  simp only [List.length_append, List.length_cons]
  omega

/-- The exact number of removed spine states is `middle.length + 1`. -/
theorem lemma_7_3_delete_cycle_length_eq
    {W : Type u} (pre middle post : List W) (x : W) :
    (pre ++ (x :: middle ++ (x :: post))).length =
      (pre ++ (x :: post)).length + middle.length + 1 := by
  simp only [List.length_append, List.length_cons]
  omega

/-- A simple spine over a finite retained-state space visits at most all states. -/
theorem simple_spine_length_le_card
    {W : Type u} [Fintype W]
    {spine : List W} (hSimple : spine.Nodup) :
    spine.length ≤ Fintype.card W := by
  exact hSimple.length_le_card

/-- Hence a nonempty simple spine has at most `|W|-1` transitions. -/
theorem simple_spine_transition_count_le
    {W : Type u} [Fintype W]
    {spine : List W} (hSimple : spine.Nodup) :
    spine.length - 1 ≤ Fintype.card W - 1 := by
  have h := simple_spine_length_le_card hSimple
  omega

/--
Arithmetic endpoint used in Lemma 7.5: if a terminal derivation contributes
one terminal at every non-base spine step and one terminal at the base, then a
simple spine yields a word of length at most `|W|`.
-/
theorem lemma_7_5_length_from_simple_spine
    {W : Type u} [Fintype W]
    {spine : List W} {yieldLength : Nat}
    (hSimple : spine.Nodup)
    (hLength : yieldLength = spine.length) :
    yieldLength ≤ Fintype.card W := by
  rw [hLength]
  exact simple_spine_length_le_card hSimple

/--
Arithmetic endpoint used in Lemma 7.6: if external context length is the
number of transitions of a simple nonempty spine, it is at most `|W|-1`.
-/
theorem lemma_7_6_context_length_from_simple_spine
    {W : Type u} [Fintype W]
    {spine : List W} {contextLength : Nat}
    (hSimple : spine.Nodup)
    (hLength : contextLength = spine.length - 1) :
    contextLength ≤ Fintype.card W - 1 := by
  rw [hLength]
  exact simple_spine_transition_count_le hSimple

end FixedHCFG
end LeanCfgProject
