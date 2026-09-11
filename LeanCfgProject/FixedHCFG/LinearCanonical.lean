import LeanCfgProject.FixedHCFG.LinearTrimmed
import LeanCfgProject.FixedHCFG.LinearShortlex

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Canonical shortlex witnesses on the reduced strict-linear grammar.

This file closes the bridge between the generic spine arguments and the actual
canonical choices used in Section 7: `omega(X)` is the shortlex-least terminal
yield of a retained state and `chi(X)` is the lexicographic-shortlex least
reachable context pair.
-/

/-- Terminal yields of a retained state in the trimmed strict-linear grammar. -/
def TrimLinearYieldSet
    {W : Type v} {Sigma : Type u}
    (G : StrictLinearGrammar W Sigma) (X : StrictLinearKeptState G) :
    Set (Word Sigma) :=
  {z | LinearDerives (trimStrictLinearGrammar G) X z}

/-- Every retained state has a terminal yield after trimming. -/
theorem trimLinearYieldSet_nonempty
    {W : Type v} {Sigma : Type u}
    (G : StrictLinearGrammar W Sigma) (X : StrictLinearKeptState G) :
    (TrimLinearYieldSet G X).Nonempty := by
  exact trim_kept_productive X

/-- Section-7 canonical yield `omega(X)`. -/
noncomputable def trimLinearOmega
    {W : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (G : StrictLinearGrammar W Sigma) (X : StrictLinearKeptState G) :
    Word Sigma :=
  (wordShortlex_wf (Sigma := Sigma)).min
    (TrimLinearYieldSet G X) (trimLinearYieldSet_nonempty G X)

/-- The canonical yield is genuinely derivable. -/
theorem trimLinearOmega_spec
    {W : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (G : StrictLinearGrammar W Sigma) (X : StrictLinearKeptState G) :
    LinearDerives (trimStrictLinearGrammar G) X (trimLinearOmega G X) := by
  exact (wordShortlex_wf (Sigma := Sigma)).min_mem
    (TrimLinearYieldSet G X) (trimLinearYieldSet_nonempty G X)

/-- No derivable yield is shortlex-smaller than `omega(X)`. -/
theorem trimLinearOmega_minimal
    {W : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (G : StrictLinearGrammar W Sigma) (X : StrictLinearKeptState G)
    {z : Word Sigma}
    (hz : LinearDerives (trimStrictLinearGrammar G) X z) :
    ¬ WordShortlex z (trimLinearOmega G X) := by
  simpa [trimLinearOmega, TrimLinearYieldSet] using
    ((wordShortlex_wf (Sigma := Sigma)).not_lt_min
      (TrimLinearYieldSet G X) hz)

/-- The canonical yield satisfies the exact shortlex-minimality predicate of Lemma 7.5. -/
theorem trimLinearOmega_shortlexMinimal
    {W : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (G : StrictLinearGrammar W Sigma) (X : StrictLinearKeptState G) :
    LinearYieldShortlexMinimal (trimStrictLinearGrammar G) X
      (trimLinearOmega G X) := by
  refine ⟨trimLinearOmega_spec G X, ?_⟩
  intro z hz
  exact trimLinearOmega_minimal G X hz

/-- Lemma 7.5 for the actual canonical yield of the reduced linear grammar. -/
theorem trimLinearOmega_length_le
    {W : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (G : StrictLinearGrammar W Sigma)
    [Fintype (StrictLinearKeptState G)]
    (X : StrictLinearKeptState G) :
    (trimLinearOmega G X).length ≤ Fintype.card (StrictLinearKeptState G) := by
  exact lemma_7_5_shortlex_yield_length_le
    (trimLinearOmega_shortlexMinimal G X)

/-- Reachable context pairs of a retained state in the trimmed grammar. -/
def TrimLinearContextSet
    {W : Type v} {Sigma : Type u}
    (G : StrictLinearGrammar W Sigma) (X : StrictLinearKeptState G) :
    Set (Word Sigma × Word Sigma) :=
  {c | LinearOccurs (trimStrictLinearGrammar G) X c.1 c.2}

/-- Every retained state has a reachable context after trimming. -/
theorem trimLinearContextSet_nonempty
    {W : Type v} {Sigma : Type u}
    (G : StrictLinearGrammar W Sigma) (X : StrictLinearKeptState G) :
    (TrimLinearContextSet G X).Nonempty := by
  rcases trim_kept_reachable X with ⟨l, r, h⟩
  exact ⟨(l, r), h⟩

/-- Section-7 canonical context pair `chi(X)`. -/
noncomputable def trimLinearChi
    {W : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (G : StrictLinearGrammar W Sigma) (X : StrictLinearKeptState G) :
    Word Sigma × Word Sigma :=
  (contextShortlex_wf (Sigma := Sigma)).min
    (TrimLinearContextSet G X) (trimLinearContextSet_nonempty G X)

noncomputable def trimLinearLeftCtx
    {W : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (G : StrictLinearGrammar W Sigma) (X : StrictLinearKeptState G) : Word Sigma :=
  (trimLinearChi G X).1

noncomputable def trimLinearRightCtx
    {W : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (G : StrictLinearGrammar W Sigma) (X : StrictLinearKeptState G) : Word Sigma :=
  (trimLinearChi G X).2

/-- The canonical context is genuinely reachable. -/
theorem trimLinearChi_spec
    {W : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (G : StrictLinearGrammar W Sigma) (X : StrictLinearKeptState G) :
    LinearOccurs (trimStrictLinearGrammar G) X
      (trimLinearLeftCtx G X) (trimLinearRightCtx G X) := by
  exact (contextShortlex_wf (Sigma := Sigma)).min_mem
    (TrimLinearContextSet G X) (trimLinearContextSet_nonempty G X)

/-- No reachable context is smaller than `chi(X)` in the manuscript's pair order. -/
theorem trimLinearChi_minimal
    {W : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (G : StrictLinearGrammar W Sigma) (X : StrictLinearKeptState G)
    {l r : Word Sigma}
    (h : LinearOccurs (trimStrictLinearGrammar G) X l r) :
    ¬ ContextShortlex (l, r)
      (trimLinearLeftCtx G X, trimLinearRightCtx G X) := by
  simpa [trimLinearLeftCtx, trimLinearRightCtx, trimLinearChi,
    TrimLinearContextSet] using
    ((contextShortlex_wf (Sigma := Sigma)).not_lt_min
      (TrimLinearContextSet G X) h)

/-- The canonical context satisfies the exact shortlex-minimality predicate of Lemma 7.6. -/
theorem trimLinearChi_shortlexMinimal
    {W : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (G : StrictLinearGrammar W Sigma) (X : StrictLinearKeptState G) :
    LinearContextShortlexMinimal (trimStrictLinearGrammar G) X
      (trimLinearLeftCtx G X) (trimLinearRightCtx G X) := by
  refine ⟨trimLinearChi_spec G X, ?_⟩
  intro l r h
  exact trimLinearChi_minimal G X h

/-- Lemma 7.6 for the actual canonical context pair of the reduced linear grammar. -/
theorem trimLinearChi_length_le
    {W : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (G : StrictLinearGrammar W Sigma)
    [Fintype (StrictLinearKeptState G)]
    (X : StrictLinearKeptState G) :
    (trimLinearLeftCtx G X).length + (trimLinearRightCtx G X).length ≤
      Fintype.card (StrictLinearKeptState G) - 1 := by
  exact lemma_7_6_shortlex_context_length_le
    (trimLinearChi_shortlexMinimal G X)

end FixedHCFG
end LeanCfgProject
