import LeanCfgProject.FixedHCFG.LinearBasisExtraction
import LeanCfgProject.FixedHCFG.LinearTimeData

namespace LeanCfgProject
namespace FixedHCFG

universe u v w x

/-!
Actual-grammar specialization of the Section-7 polynomial time-and-data theorem.

`LinearTimeData` packages the counting and Section-6 cost arithmetic for an
abstract reconstruction basis.  This file removes that remaining abstraction:
the basis is the one extracted from the actual reduced typed SSLNF grammar
`H = trim(fullTypedLinearGrammar Obs G)`.

The only finite presentation data still supplied externally are an indexing
`R` of the realised typed rules and a finite witness enumeration `wordOf` of
`CS_lin(H)`.  These are isolated here so that the next bridge can construct
them directly from the realised rule slots.
-/

/--
Theorem 7.9 specialized to the actual reduced typed linear grammar `H`.

The state-counting map is no longer an assumption: it is the canonical
coordinate map `(A,p,m,n)` and its injectivity is proved internally.  Exact
reconstruction is therefore stated directly against `L(H)`, while the data and
construction-time bounds are inherited from the verified Section-7 and
Section-6 envelopes.
-/
theorem theorem_7_9_actual_typed_linear_envelope
    {N : Type v} {Sigma : Type u} {P : Type w} {R : Type x}
    [LinearOrder Sigma] [WellFoundedLT Sigma] [DecidableEq Sigma]
    [Fintype N] [Fintype P] [Fintype R]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    [Fintype (ActualLinearState Obs G)]
    (ruleEncode : R → P × Obs.M × Obs.M × Obs.M)
    (hRuleInj : Function.Injective ruleEncode)
    (wordOf : LinearSampleIndex (ActualLinearState Obs G) R → Word Sigma)
    (hLen : ∀ i,
      (wordOf i).length ≤ 2 * Fintype.card (ActualLinearState Obs G))
    (hCSrepr : ∀ z : Word Sigma,
      z ∈ ActualLinearCS Obs G ↔ z ∈ linearSampleFinset wordOf)
    (K : Language Sigma)
    (hSampleK : ∀ z : Word Sigma,
      z ∈ linearSampleFinset wordOf → z ∈ K)
    (hKL : K ⊆ StrictLinearLanguage (ActualLinearGrammar Obs G))
    (hSub : HSubstitutable Obs
      (StrictLinearLanguage (ActualLinearGrammar Obs G)))
    {sampleN learnerV ell k c : Nat}
    (hN : 1 ≤ sampleN)
    (hLearnerV : learnerV ≤ c * sampleN ^ 2)
    (hEll : ell ≤ sampleN)
    (hKCount : k ≤ sampleN + 1) :
    (∀ z : Word Sigma,
      StartDerives Obs K z ↔
        StrictLinearLanguage (ActualLinearGrammar Obs G) z) ∧
    (∑ z ∈ linearSampleFinset wordOf, z.length) ≤
      linearDataEnvelope (Fintype.card N) (Fintype.card P)
        (Fintype.card Obs.M) ∧
    section6CostEnvelope sampleN learnerV ell k ≤
      (2 * c ^ 2 + c + 3) * sampleN ^ 5 := by
  let B := actualLinearReconstructionBasis Obs G
  let stateEncode : ActualLinearState Obs G →
      N × Obs.M × Obs.M × Obs.M :=
    fun X => encodeTypedNT Obs X.1
  have hStateInj : Function.Injective stateEncode := by
    intro X Y hXY
    apply Subtype.ext
    exact encodeTypedNT_injective Obs hXY
  have hLang : LinearBasisLanguage B =
      StrictLinearLanguage (ActualLinearGrammar Obs G) := by
    exact actualBasisLanguage_eq Obs G
  have hCSreprB : ∀ z : Word Sigma,
      z ∈ B.CS ↔ z ∈ linearSampleFinset wordOf := by
    intro z
    simpa [B, actualLinearReconstructionBasis] using hCSrepr z
  have hKLB : K ⊆ LinearBasisLanguage B := by
    intro z hz
    rw [hLang]
    exact hKL hz
  have hSubB : HSubstitutable Obs (LinearBasisLanguage B) := by
    rw [hLang]
    exact hSub
  have hAll := theorem_7_9_time_and_data_envelope
    Obs B stateEncode ruleEncode hStateInj hRuleInj wordOf hLen hCSreprB
      K hSampleK hKLB hSubB hN hLearnerV hEll hKCount
  rcases hAll with ⟨hExact, hData, hCost⟩
  refine ⟨?_, hData, hCost⟩
  intro z
  have hz := hExact z
  rw [hLang] at hz
  exact hz

end FixedHCFG
end LeanCfgProject
