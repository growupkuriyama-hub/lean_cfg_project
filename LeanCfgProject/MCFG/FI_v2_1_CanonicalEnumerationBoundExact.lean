import LeanCfgProject.MCFG.FI_v2_1_CanonicalEnumerationBoundInterface

/-!
# FI v2.1 Lean experiment: exact canonical packages with enumeration bounds

This sixtieth layer combines exact canonical learner grammar packages, rule-list
counting summaries, and enumeration-bound certificates.

No nontrivial arithmetic estimate is proved here.  The layer merely says that
an exact package may also carry a bound certificate, and all semantic exactness
and finite-rule-list facts are inherited unchanged.  This keeps the later
complexity interface separate from the semantic reconstruction interface.
-/

namespace FIv21

universe u v w

noncomputable section

section CanonicalEnumerationBoundExact

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Exact canonical learner grammar package equipped with explicit enumeration
bounds. -/
structure CanonicalLearnerGrammarExactWithEnumerationBounds
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : CanonicalLearnerGrammarPackage G obs K) where
  exactWithCounts : CanonicalLearnerGrammarExactWithCounts P
  bounds : CanonicalEnumerationBounds P

namespace CanonicalLearnerGrammarExactWithEnumerationBounds

/-- Any exact package with counts can be equipped with the tautological exact
bounds. -/
def ofExactWithCounts
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithCounts P) :
    CanonicalLearnerGrammarExactWithEnumerationBounds P :=
  { exactWithCounts := C
    bounds := CanonicalEnumerationBounds.exactForPackage P }

/-- Any exact canonical package can be equipped with rule counts and the
corresponding tautological enumeration bounds. -/
def ofExactPackage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactForGrammar P) :
    CanonicalLearnerGrammarExactWithEnumerationBounds P :=
  ofExactWithCounts
    (CanonicalLearnerGrammarExactWithCounts.ofExactPackage C)

/-- Forget to the exact-with-counts certificate. -/
def toExactWithCounts
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithEnumerationBounds P) :
    CanonicalLearnerGrammarExactWithCounts P :=
  C.exactWithCounts

/-- Exact equality of package-level approximate distributions and target
named-context distributions. -/
theorem approxDistribution_exact
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithEnumerationBounds P)
    {d : Nat} (x : Tuple α d) :
    P.ApproxDistribution x = NamedDistribution G.StringLanguage x := by
  exact C.exactWithCounts.approxDistribution_exact x

/-- Learner-side generation of a sampled word. -/
theorem sample_word_generated_by_learner
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithEnumerationBounds P)
    (w : Word α) (hw : w ∈ K) :
    w ∈ P.wordLanguage := by
  exact C.exactWithCounts.sample_word_generated_by_learner w hw

/-- Target-side start derivation witness for a sampled word. -/
theorem sample_word_start_derives
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithEnumerationBounds P)
    (w : Word α) (hw : w ∈ K) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact C.exactWithCounts.sample_word_start_derives w hw

/-- Rule-list coverage inherited from the exact-with-counts certificate. -/
theorem refinedRuleLists_coverAll
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithEnumerationBounds P) :
    P.finiteRefinedGrammar.CoversAllOrdinaryRuleRefinements := by
  exact C.exactWithCounts.refinedRuleLists_coverAll

/-- Rule-list plan support inherited from the exact-with-counts certificate. -/
theorem refinedRuleLists_supportedByPlan
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithEnumerationBounds P) :
    P.finiteRefinedGrammar.AllRulesSupportedByPlan P.ruleEnumerationPlan := by
  exact C.exactWithCounts.refinedRuleLists_supportedByPlan

/-- Total refined-rule count is below the supplied total enumeration bound. -/
theorem refinedRuleCount_le_bound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithEnumerationBounds P) :
    P.refinedRuleCount ≤ C.bounds.totalBound := by
  exact C.bounds.refinedRuleCount_le

/-- Terminal refined-rule count is below the supplied terminal bound. -/
theorem refinedTerminalRuleCount_le_bound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithEnumerationBounds P) :
    P.refinedTerminalRuleCount ≤ C.bounds.terminalBound := by
  exact C.bounds.refinedTerminalRuleCount_le

/-- Binary refined-rule count is below the supplied binary bound. -/
theorem refinedBinaryRuleCount_le_bound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithEnumerationBounds P) :
    P.refinedBinaryRuleCount ≤ C.bounds.binaryBound := by
  exact C.bounds.refinedBinaryRuleCount_le

/-- Start refined-rule count is below the supplied start bound. -/
theorem refinedStartRuleCount_le_bound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithEnumerationBounds P) :
    P.refinedStartRuleCount ≤ C.bounds.startBound := by
  exact C.bounds.refinedStartRuleCount_le

/-- Ordinary base-rule count is below the supplied ordinary-rule bound. -/
theorem ordinaryRuleCount_le_bound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithEnumerationBounds P) :
    P.ordinaryRuleCount ≤ C.bounds.ordinaryBound := by
  exact C.bounds.ordinaryRuleCount_le

/-- Output-type count at arity `d` is below the supplied bound. -/
theorem outputTypeCount_le_bound
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {P : CanonicalLearnerGrammarPackage G obs K}
    (C : CanonicalLearnerGrammarExactWithEnumerationBounds P)
    (d : Nat) :
    P.planOutputTypeCount d ≤ C.bounds.outputTypeBound d := by
  exact C.bounds.outputTypeCount_le d

end CanonicalLearnerGrammarExactWithEnumerationBounds

end CanonicalEnumerationBoundExact

end

end FIv21
