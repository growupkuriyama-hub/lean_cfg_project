import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.LinearDerivation
import LeanCfgProject.FixedHCFGv44.CanonicalWitness

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v w

/-!
Section 7 bridge lemmas for the v44 proof.

The older generic strict-linear spine development already proves the two
cycle-deletion consequences needed by v44: a minimum terminal yield has length
at most the number of retained spine states, and a minimum reaching context
has total length at most one less than that number.  This file re-exports those
facts in the v44 namespace and isolates the distinct wrapper-state arithmetic.

The normalization theorem that turns the manuscript's linear SSBNF grammar
into the strict-linear spine/wrapper shape is intentionally a separate layer.
-/

/-- Reuse of the verified strict-linear yield bound (manuscript Lemma 7.5). -/
theorem section7_spine_yield_bound
    {W : Type v} {Sigma : Type u} [Fintype W]
    {G : FixedHCFG.StrictLinearGrammar W Sigma} {X : W} {z : List Sigma}
    (hmin : FixedHCFG.LinearYieldMinimal G X z) :
    z.length ≤ Fintype.card W := by
  exact FixedHCFG.lemma_7_5_minimal_yield_length_le hmin

/-- Reuse of the verified strict-linear context bound (manuscript Lemma 7.6). -/
theorem section7_spine_context_bound
    {W : Type v} {Sigma : Type u} [Fintype W]
    {G : FixedHCFG.StrictLinearGrammar W Sigma} {X : W}
    {l r : List Sigma}
    (hmin : FixedHCFG.LinearContextMinimal G X l r) :
    l.length + r.length ≤ Fintype.card W - 1 := by
  exact FixedHCFG.lemma_7_6_minimal_context_length_le hmin

/-- A retained v44 yield-typed state is encoded by its label and one monoid value. -/
noncomputable instance keptStateFintype
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype N] :
    Fintype (KeptState Obs terminal binary start) := by
  classical
  exact Fintype.ofFinite _

/--
The v44 yield-only refinement has at most `|N| |M|` retained non-start states.
This is the state-count improvement over the old two-sided typed construction.
-/
theorem kept_state_card_le
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype N] :
    Fintype.card (KeptState Obs terminal binary start) ≤
      Fintype.card N * Fintype.card Obs.M := by
  classical
  calc
    Fintype.card (KeptState Obs terminal binary start) ≤
        Fintype.card (N × Obs.M) := by
      apply Fintype.card_le_of_injective
        (fun X : KeptState Obs terminal binary start => typedNTKey X.1)
      intro X Y h
      apply Subtype.ext
      exact typedNTKey_injective h
    _ = Fintype.card N * Fintype.card Obs.M := by simp

/-- A binary typed copy is determined by its source production and two child types. -/
abbrev BinaryTypedRuleSlot
    {Sigma : Type u} (Obs : Observer Sigma) (P : Type w) :=
  P × Obs.M × Obs.M

/-- Hence each indexed binary-production family has the `|P||M|^2` envelope. -/
theorem binary_typed_rule_slot_card
    {Sigma : Type u} {P : Type w} [Fintype P]
    (Obs : Observer Sigma) :
    Fintype.card (BinaryTypedRuleSlot Obs P) =
      Fintype.card P * Fintype.card Obs.M ^ 2 := by
  simp [BinaryTypedRuleSlot, pow_two, mul_assoc]

/--
For a direct spine state, the canonical anchor has linear length once the
spine-yield and spine-context bounds are available.
-/
theorem direct_anchor_length_le_two_mul
    {Sigma : Type u} {n : Nat} (hn : 0 < n)
    {l r z : Word Sigma}
    (hctx : l.length + r.length ≤ n - 1)
    (hyield : z.length ≤ n) :
    (l ++ z ++ r).length ≤ 2 * n := by
  simp only [List.length_append]
  omega

/-- A direct terminal-rule witness also has length at most `2 n`. -/
theorem direct_terminal_observation_length_le_two_mul
    {Sigma : Type u} {n : Nat} (hn : 0 < n)
    {l r : Word Sigma} (a : Sigma)
    (hctx : l.length + r.length ≤ n - 1) :
    (l ++ [a] ++ r).length ≤ 2 * n := by
  simp only [List.length_append, List.length_singleton]
  omega

/--
The distinct wrapper-context case from the v44 appendix: the wrapper sees the
outer spine context plus completion of the non-wrapper child.  Thus
`(n-1)+n < 2n`.
-/
theorem wrapper_context_length_lt_two_mul
    {Sigma : Type u} {n : Nat} (hn : 0 < n)
    {l r completion : Word Sigma}
    (hctx : l.length + r.length ≤ n - 1)
    (hcompletion : completion.length ≤ n) :
    l.length + completion.length + r.length < 2 * n := by
  omega

/-- The same wrapper bound with completion placed on the right side. -/
theorem wrapper_right_context_length_lt_two_mul
    {Sigma : Type u} {n : Nat} (hn : 0 < n)
    {l r completion : Word Sigma}
    (hctx : l.length + r.length ≤ n - 1)
    (hcompletion : completion.length ≤ n) :
    l.length + (completion ++ r).length < 2 * n := by
  simp only [List.length_append]
  exact wrapper_context_length_lt_two_mul hn hctx hcompletion

/-- The same wrapper bound with completion placed on the left side. -/
theorem wrapper_left_context_length_lt_two_mul
    {Sigma : Type u} {n : Nat} (hn : 0 < n)
    {l r completion : Word Sigma}
    (hctx : l.length + r.length ≤ n - 1)
    (hcompletion : completion.length ≤ n) :
    (l ++ completion).length + r.length < 2 * n := by
  simp only [List.length_append]
  exact wrapper_context_length_lt_two_mul hn hctx hcompletion

/-- A wrapper anchor is still bounded by `2 n` because its own yield is one terminal. -/
theorem wrapper_anchor_length_le_two_mul
    {Sigma : Type u} {n : Nat}
    {l r z : Word Sigma}
    (hctx : l.length + r.length < 2 * n)
    (hyield : z.length = 1) :
    (l ++ z ++ r).length ≤ 2 * n := by
  simp only [List.length_append]
  omega

/--
A binary observation from a spine state has one non-wrapper child of yield
length at most `n` and one wrapper child of yield length one, hence total
length at most `2 n`.
-/
theorem direct_binary_observation_length_le_two_mul
    {Sigma : Type u} {n : Nat} (hn : 0 < n)
    {l r spineYield wrapperYield : Word Sigma}
    (hctx : l.length + r.length ≤ n - 1)
    (hspine : spineYield.length ≤ n)
    (hwrapper : wrapperYield.length = 1) :
    (l ++ spineYield ++ wrapperYield ++ r).length ≤ 2 * n := by
  simp only [List.length_append]
  omega

/-- The child order is irrelevant to the same binary-observation bound. -/
theorem direct_binary_observation_swapped_length_le_two_mul
    {Sigma : Type u} {n : Nat} (hn : 0 < n)
    {l r spineYield wrapperYield : Word Sigma}
    (hctx : l.length + r.length ≤ n - 1)
    (hspine : spineYield.length ≤ n)
    (hwrapper : wrapperYield.length = 1) :
    (l ++ wrapperYield ++ spineYield ++ r).length ≤ 2 * n := by
  simp only [List.length_append]
  omega

end FixedHCFGv44
end LeanCfgProject
