import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.ComplexityBounds

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
Theorem-facing finite bounds for Section 7 of the TCS manuscript.

The manuscript's typed linear grammar has at most one retained typed state for
each quadruple `(A,p,m,n)` and at most one retained typed rule for each source
production together with three monoid coordinates.  Its linear characteristic
sample contains at most one anchor per retained state, one witness per retained
non-start rule, and possibly epsilon.  The results below verify exactly those
finite counting envelopes and the length arithmetic used in Proposition 7.7.
-/

/-- A finite retained typed-state family embeds in `V × M^3`. -/
theorem linear_typed_state_card_le
    {V : Type u} {M : Type v} {W : Type w}
    [Fintype V] [Fintype M] [Fintype W]
    (encode : W → V × M × M × M)
    (hinj : Function.Injective encode) :
    Fintype.card W ≤ Fintype.card V * Fintype.card M ^ 3 := by
  calc
    Fintype.card W ≤ Fintype.card (V × M × M × M) :=
      Fintype.card_le_of_injective encode hinj
    _ = Fintype.card V * Fintype.card M ^ 3 := by
      simp [pow_three, mul_assoc]

/-- A finite realised typed-rule family embeds in `P × M^3`. -/
theorem linear_typed_rule_card_le
    {P : Type u} {M : Type v} {R : Type w}
    [Fintype P] [Fintype M] [Fintype R]
    (encode : R → P × M × M × M)
    (hinj : Function.Injective encode) :
    Fintype.card R ≤ Fintype.card P * Fintype.card M ^ 3 := by
  calc
    Fintype.card R ≤ Fintype.card (P × M × M × M) :=
      Fintype.card_le_of_injective encode hinj
    _ = Fintype.card P * Fintype.card M ^ 3 := by
      simp [pow_three, mul_assoc]

/--
Indices for the three families occurring in `CS_lin(H)`: an anchor, a rule
witness, or the optional epsilon slot.  Using an always-present epsilon slot is
a harmless one-element envelope and gives the manuscript's `+ 1` bound.
-/
abbrev LinearSampleIndex (W : Type u) (R : Type v) :=
  Sum W (Sum R (Fin 1))

/-- The witness-index family has exactly `|W| + |R| + 1` elements. -/
theorem linearSampleIndex_card
    {W : Type u} {R : Type v} [Fintype W] [Fintype R] :
    Fintype.card (LinearSampleIndex W R) =
      Fintype.card W + Fintype.card R + 1 := by
  simp [LinearSampleIndex, Nat.add_assoc]

/--
A concrete finite sample obtained as the image of the manuscript witness-index
family.  Duplicate words only make the actual sample smaller.
-/
noncomputable def linearSampleFinset
    {Sigma : Type u} {W : Type v} {R : Type w}
    [Fintype W] [Fintype R]
    (wordOf : LinearSampleIndex W R → Word Sigma) : Finset (Word Sigma) := by
  classical
  exact Finset.univ.image wordOf

/-- Proposition 7.7(iii): the linear characteristic sample has at most `|W|+|R|+1` words. -/
theorem linearSampleFinset_card_le
    {Sigma : Type u} {W : Type v} {R : Type w}
    [Fintype W] [Fintype R]
    (wordOf : LinearSampleIndex W R → Word Sigma) :
    (linearSampleFinset wordOf).card ≤
      Fintype.card W + Fintype.card R + 1 := by
  classical
  calc
    (linearSampleFinset wordOf).card ≤
        Fintype.card (LinearSampleIndex W R) := by
      simpa [linearSampleFinset] using
        (Finset.card_image_le (s := (Finset.univ : Finset (LinearSampleIndex W R)))
          (f := wordOf))
    _ = Fintype.card W + Fintype.card R + 1 := linearSampleIndex_card

/--
Lemma-7.5/7.6 arithmetic for an anchor `u omega(X) v`: a context of length at
most `|W|-1` plus a canonical yield of length at most `|W|` has total length at
most `2|W|`.
-/
theorem linear_anchor_length_le_two_states
    {Sigma : Type u} {stateCount : Nat}
    (u omega v : Word Sigma)
    (hctx : u.length + v.length ≤ stateCount - 1)
    (hyield : omega.length ≤ stateCount) :
    (u ++ omega ++ v).length ≤ 2 * stateCount := by
  simp only [List.length_append]
  omega

/--
The same Section-7 bound for a rule witness containing one explicit terminal
and one child canonical yield.
-/
theorem linear_rule_witness_length_le_two_states
    {Sigma : Type u} {stateCount : Nat}
    (u child v : Word Sigma) (a : Sigma)
    (hctx : u.length + v.length ≤ stateCount - 1)
    (hchild : child.length ≤ stateCount) :
    (u ++ [a] ++ child ++ v).length ≤ 2 * stateCount := by
  simp only [List.length_append, List.length_singleton]
  omega

/-- Mirror-image rule witness `u omega(Y) a v`. -/
theorem linear_rule_witness_right_length_le_two_states
    {Sigma : Type u} {stateCount : Nat}
    (u child v : Word Sigma) (a : Sigma)
    (hctx : u.length + v.length ≤ stateCount - 1)
    (hchild : child.length ≤ stateCount) :
    (u ++ child ++ [a] ++ v).length ≤ 2 * stateCount := by
  simp only [List.length_append, List.length_singleton]
  omega

/--
Proposition 7.7(iv) in witness-family form: if each witness constructor obeys
the `2|W|` bound, every actual sample word does too.
-/
theorem linearSampleFinset_word_length_le
    {Sigma : Type u} {W : Type v} {R : Type w}
    [Fintype W] [Fintype R]
    (wordOf : LinearSampleIndex W R → Word Sigma)
    (hLen : ∀ i, (wordOf i).length ≤ 2 * Fintype.card W)
    {z : Word Sigma} (hz : z ∈ linearSampleFinset wordOf) :
    z.length ≤ 2 * Fintype.card W := by
  classical
  simp only [linearSampleFinset, Finset.mem_image, Finset.mem_univ, true_and] at hz
  rcases hz with ⟨i, rfl⟩
  exact hLen i

/--
Consequently the total symbol count of the finite sample is bounded by the
product of the cardinality envelope and the maximum word-length envelope.
-/
theorem linearSampleFinset_total_length_le
    {Sigma : Type u} {W : Type v} {R : Type w}
    [Fintype W] [Fintype R]
    (wordOf : LinearSampleIndex W R → Word Sigma)
    (hLen : ∀ i, (wordOf i).length ≤ 2 * Fintype.card W) :
    (∑ z ∈ linearSampleFinset wordOf, z.length) ≤
      (Fintype.card W + Fintype.card R + 1) * (2 * Fintype.card W) := by
  classical
  let S := linearSampleFinset wordOf
  have hEach : ∀ z ∈ S, z.length ≤ 2 * Fintype.card W := by
    intro z hz
    exact linearSampleFinset_word_length_le wordOf hLen hz
  have hSum : (∑ z ∈ S, z.length) ≤ S.card * (2 * Fintype.card W) := by
    calc
      (∑ z ∈ S, z.length) ≤ ∑ _z ∈ S, (2 * Fintype.card W) := by
        exact Finset.sum_le_sum fun z hz => hEach z hz
      _ = S.card * (2 * Fintype.card W) := by simp
  exact hSum.trans
    (Nat.mul_le_mul_right (2 * Fintype.card W)
      (linearSampleFinset_card_le wordOf))

end FixedHCFG
end LeanCfgProject
