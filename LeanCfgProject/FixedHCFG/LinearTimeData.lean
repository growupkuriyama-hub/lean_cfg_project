import LeanCfgProject.FixedHCFG.LinearBounds
import LeanCfgProject.FixedHCFG.LinearReconstruction

namespace LeanCfgProject
namespace FixedHCFG

universe u v w x y

/-!
Theorem-facing polynomial time-and-data envelope for Section 7.4.

The manuscript's Theorem 7.9 combines two independent ingredients:

* Lemma 7.8: once the linear characteristic sample is exposed, the learner
  exactly reconstructs the target language;
* Proposition 7.7 together with Theorem 6.1: for fixed `h`, the characteristic
  sample has polynomial total length in the target presentation size and the
  current hypothesis is constructible in polynomial time in the observed data.

This file packages those already verified components without pretending to be
an executable cost-semantics verification of the learner implementation.
-/

/--
A concrete polynomial envelope for the total symbol count of the linear
characteristic sample.  For fixed observer monoid size `m`, this is a quadratic
polynomial in the source state/rule counts `v,p`.
-/
def linearDataEnvelope (v p m : Nat) : Nat :=
  ((v + p) * m ^ 3 + 1) * (2 * (v * m ^ 3))

/--
Proposition 7.7(i)--(iv), combined into one total-data bound.

`W` is the retained typed-state family and `R` the realised typed-rule family.
The two injections are exactly the manuscript counting maps into `V × M^3`
and `P × M^3`.  `wordOf` indexes anchors, rule witnesses, and the optional
empty-word slot.
-/
theorem linear_characteristic_sample_total_length_poly
    {Sigma : Type u} {V : Type v} {P : Type w}
    {W : Type x} {R : Type y}
    [Fintype V] [Fintype P] [Fintype W] [Fintype R]
    (Obs : Observer Sigma)
    (stateEncode : W → V × Obs.M × Obs.M × Obs.M)
    (ruleEncode : R → P × Obs.M × Obs.M × Obs.M)
    (hStateInj : Function.Injective stateEncode)
    (hRuleInj : Function.Injective ruleEncode)
    (wordOf : LinearSampleIndex W R → Word Sigma)
    (hLen : ∀ i, (wordOf i).length ≤ 2 * Fintype.card W) :
    (∑ z ∈ linearSampleFinset wordOf, z.length) ≤
      linearDataEnvelope (Fintype.card V) (Fintype.card P)
        (Fintype.card Obs.M) := by
  have hBase := linearSampleFinset_total_length_le wordOf hLen
  have hW : Fintype.card W ≤
      Fintype.card V * Fintype.card Obs.M ^ 3 :=
    linear_typed_state_card_le stateEncode hStateInj
  have hR : Fintype.card R ≤
      Fintype.card P * Fintype.card Obs.M ^ 3 :=
    linear_typed_rule_card_le ruleEncode hRuleInj
  have hCount :
      Fintype.card W + Fintype.card R + 1 ≤
        (Fintype.card V + Fintype.card P) * Fintype.card Obs.M ^ 3 + 1 := by
    calc
      Fintype.card W + Fintype.card R + 1 ≤
          Fintype.card V * Fintype.card Obs.M ^ 3 +
            Fintype.card P * Fintype.card Obs.M ^ 3 + 1 :=
        Nat.add_le_add (Nat.add_le_add hW hR) le_rfl
      _ = (Fintype.card V + Fintype.card P) *
          Fintype.card Obs.M ^ 3 + 1 := by ring
  have hWord :
      2 * Fintype.card W ≤
        2 * (Fintype.card V * Fintype.card Obs.M ^ 3) :=
    Nat.mul_le_mul_left 2 hW
  have hProduct := Nat.mul_le_mul hCount hWord
  exact hBase.trans (by
    simpa [linearDataEnvelope] using hProduct)

/--
Theorem 7.9 in a theorem-facing interface.

The exact characteristic sample is represented by the finite image
`linearSampleFinset wordOf`.  The first assumption identifies this concrete
finite set with the reconstruction basis's observation language `B.CS`; the
second says that the observed positive sample contains it.  The conclusion
packages exact reconstruction, the polynomial data envelope, and the degree-5
Section-6 construction-time envelope.
-/
theorem theorem_7_9_time_and_data_envelope
    {Sigma : Type u} {V : Type v} {P : Type w}
    {W : Type x} {R : Type y}
    [DecidableEq Sigma]
    [Fintype V] [Fintype P] [Fintype W] [Fintype R]
    (Obs : Observer Sigma)
    (B : LinearReconstructionBasis Obs W)
    (stateEncode : W → V × Obs.M × Obs.M × Obs.M)
    (ruleEncode : R → P × Obs.M × Obs.M × Obs.M)
    (hStateInj : Function.Injective stateEncode)
    (hRuleInj : Function.Injective ruleEncode)
    (wordOf : LinearSampleIndex W R → Word Sigma)
    (hLen : ∀ i, (wordOf i).length ≤ 2 * Fintype.card W)
    (hCSrepr : ∀ z : Word Sigma,
      z ∈ B.CS ↔ z ∈ linearSampleFinset wordOf)
    (K : Language Sigma)
    (hSampleK : ∀ z : Word Sigma,
      z ∈ linearSampleFinset wordOf → z ∈ K)
    (hKL : K ⊆ LinearBasisLanguage B)
    (hSub : HSubstitutable Obs (LinearBasisLanguage B))
    {N learnerV ell k c : Nat}
    (hN : 1 ≤ N)
    (hLearnerV : learnerV ≤ c * N ^ 2)
    (hEll : ell ≤ N)
    (hKCount : k ≤ N + 1) :
    (∀ z : Word Sigma,
      StartDerives Obs K z ↔ LinearBasisLanguage B z) ∧
    (∑ z ∈ linearSampleFinset wordOf, z.length) ≤
      linearDataEnvelope (Fintype.card V) (Fintype.card P)
        (Fintype.card Obs.M) ∧
    section6CostEnvelope N learnerV ell k ≤
      (2 * c ^ 2 + c + 3) * N ^ 5 := by
  have hCSK : B.CS ⊆ K := by
    intro z hz
    exact hSampleK z ((hCSrepr z).mp hz)
  constructor
  · intro z
    exact lemma_7_8_exact_reconstruction B K hCSK hKL hSub z
  constructor
  · exact linear_characteristic_sample_total_length_poly
      Obs stateEncode ruleEncode hStateInj hRuleInj wordOf hLen
  · exact section6CostEnvelope_degree_five
      hN hLearnerV hEll hKCount

end FixedHCFG
end LeanCfgProject
