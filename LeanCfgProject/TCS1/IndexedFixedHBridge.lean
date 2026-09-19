import LeanCfgProject.TCS1.IndexedNormalizationLanguage
import LeanCfgProject.TCS1.FixedWindowCharacteristicDataFacade
import LeanCfgProject.TCS1.ConcreteConservativeLearner
import LeanCfgProject.TCS1.TrivialTargetEndpoints

/-!
# TCS #1: qualitative indexed fixed-h reconstruction and Gold learning

The fixed-window development is a quantitative specialization.  The main
qualitative theorem of the paper is more general: for an arbitrary fixed finite
monoid homomorphism h, a finite canonical witness sample suffices for exact
reconstruction.

This module connects that theorem directly to a finite indexed source CFG.
No fixed-window hypothesis, source thickness parameter, or normalization-size
bound is needed.  The source grammar is normalized semantically, the generic
fixed-h canonical sample is taken on the resulting reduced start-separated
grammar, and exact reconstruction is transported back to the original source
language.  The same sample then feeds the concrete conservative Gold learner.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w q

section IndexedFixedHBridge

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable {M : Type q}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]
variable [Monoid M] [Fintype M]

/-- Generic fixed-h canonical sample of the actual normalized indexed grammar. -/
noncomputable def indexedFixedHCanonicalSample
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ []) :
    Finset (Word α) := by
  classical
  let start :
      ProductiveUnitFreeState
        (indexedFiniteFrontEndGrammar G) :=
    indexedProductiveUnitFreeState_of_nonempty
      G A hprod
  let Nf :=
    ReducedUnitFreeState
      (indexedFiniteFrontEndGrammar G) start
  letI : Fintype Nf := Fintype.ofFinite _
  exact
    fixedWindowMinimalCanonicalSample
      H
      (reducedSSBNFTerminalRule
        (indexedFiniteFrontEndGrammar G) start)
      (reducedSSBNFBinaryRule
        (indexedFiniteFrontEndGrammar G) start)
      (reducedSSBNFStartRule
        (indexedFiniteFrontEndGrammar G) start)
      ([] ∈ LeastClosedLanguage G.toMixedRules A)

/--
Exact source-language reconstruction for an arbitrary fixed finite-monoid
typing.  This is the qualitative source-CFG form of the main reconstruction
theorem, with Appendix-A normalization discharged internally.
-/
theorem indexedFixedHCanonicalSample_characteristic
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules A)) :
    BatchLanguage H
        (indexedFixedHCanonicalSample H G A hprod)
      =
    LeastClosedLanguage G.toMixedRules A := by
  classical
  let start :
      ProductiveUnitFreeState
        (indexedFiniteFrontEndGrammar G) :=
    indexedProductiveUnitFreeState_of_nonempty
      G A hprod
  let Nf :=
    ReducedUnitFreeState
      (indexedFiniteFrontEndGrammar G) start
  letI : Fintype Nf := Fintype.ofFinite _

  have hlang :
      UntypedStartLanguage
        (reducedSSBNFTerminalRule
          (indexedFiniteFrontEndGrammar G) start)
        (reducedSSBNFBinaryRule
          (indexedFiniteFrontEndGrammar G) start)
        (reducedSSBNFStartRule
          (indexedFiniteFrontEndGrammar G) start)
        ([] ∈ LeastClosedLanguage G.toMixedRules A)
        =
      LeastClosedLanguage G.toMixedRules A := by
    simpa [start] using
      indexedReducedSSBNF_untypedStartLanguage_eq_source
        G A hprod

  have hsub' :
      FixedHSubstitutable H
        (UntypedStartLanguage
          (reducedSSBNFTerminalRule
            (indexedFiniteFrontEndGrammar G) start)
          (reducedSSBNFBinaryRule
            (indexedFiniteFrontEndGrammar G) start)
          (reducedSSBNFStartRule
            (indexedFiniteFrontEndGrammar G) start)
          ([] ∈ LeastClosedLanguage G.toMixedRules A)) := by
    rw [hlang]
    exact hsub

  have hchar :=
    fixedWindowMinimalCanonicalSample_characteristic_untyped
      H
      (reducedSSBNFTerminalRule
        (indexedFiniteFrontEndGrammar G) start)
      (reducedSSBNFBinaryRule
        (indexedFiniteFrontEndGrammar G) start)
      (reducedSSBNFStartRule
        (indexedFiniteFrontEndGrammar G) start)
      ([] ∈ LeastClosedLanguage G.toMixedRules A)
      hsub'

  rw [hlang] at hchar
  simpa [indexedFixedHCanonicalSample, Nf, start] using hchar

/--
Concrete conservative Gold identification for the arbitrary fixed-h source
theorem.  The only text assumptions are positivity and coverage.
-/
theorem indexedFixedH_concreteGold_identification
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules A))
    (datum : Nat → Word α)
    (hpositive :
      ∀ n,
        datum n ∈ LeastClosedLanguage G.toMixedRules A)
    (hcoverage :
      ∀ word,
        word ∈ LeastClosedLanguage G.toMixedRules A →
        ∃ n,
          word ∈ concreteAccumulatedSample datum n) :
    let R :=
      concreteAccumulatedConservativeRun
        H
        (LeastClosedLanguage G.toMixedRules A)
        datum hpositive
    ∃ n₀,
      (R.lang (R.hyp n₀) =
          LeastClosedLanguage G.toMixedRules A ∧
        ∀ j, R.hyp (n₀ + j) = R.hyp n₀)
      ∨
      (∃ n,
        n₀ ≤ n ∧
        R.hyp (n + 1) ≠ R.hyp n ∧
        R.lang (R.hyp (n + 1)) =
          LeastClosedLanguage G.toMixedRules A ∧
        ∀ j,
          R.hyp ((n + 1) + j) =
            R.hyp (n + 1)) := by
  exact
    concreteConservative_gold_identification
      H
      (LeastClosedLanguage G.toMixedRules A)
      (indexedFixedHCanonicalSample H G A hprod)
      (indexedFixedHCanonicalSample_characteristic
        H G A hprod hsub)
      hsub
      datum hpositive hcoverage

end IndexedFixedHBridge

end TCS1
end LeanCfgProject
