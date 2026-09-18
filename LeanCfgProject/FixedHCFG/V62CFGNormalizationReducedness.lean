import LeanCfgProject.FixedHCFG.V62CFGNormalizationBinaryThicknessTransfer

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Reducedness bridge for the first executable normalization stages

The manuscript starts Proposition `thick-ssbnf-normal` from a reduced CFG.
For the thickness argument, the relevant part of reducedness is productivity.

This file propagates that information through fresh-start separation and
terminal isolation, proves elementary RHS-length bounds for both stages, and
then instantiates the executable binarization thickness theorem.  Thus the
first three normalization stages are connected by one quantitative theorem,
rather than by independent local estimates.
-/

/-- Fresh-start separation preserves productivity of every nonterminal. -/
theorem v62_fresh_start_all_productive
    {T : Type*} {g : ContextFreeGrammar T}
    (hAll : V62CFGAllProductive g) :
    V62CFGAllProductive (v62FreshStartGrammar g) := by
  intro A
  cases A with
  | none =>
      rcases hAll g.initial with ⟨w, hw⟩
      refine ⟨w, ?_⟩
      unfold V62CFGDerivesWordFrom at hw ⊢
      have hSome :=
        v62_fresh_start_preserves_old_word_derivation hw
      exact (v62_fresh_start_produces g).single.trans hSome
  | some B =>
      rcases hAll B with ⟨w, hw⟩
      exact ⟨w, v62_fresh_start_preserves_old_word_derivation hw⟩

/-- Fresh-start separation changes a uniform RHS-length bound only by the new unit rule. -/
theorem v62_fresh_start_rhs_length_bound
    {T : Type*} {g : ContextFreeGrammar T} {rhsBound : Nat}
    (hBound : ∀ r ∈ g.rules, r.output.length ≤ rhsBound) :
    ∀ q ∈ (v62FreshStartGrammar g).rules,
      q.output.length ≤ max rhsBound 1 := by
  classical
  intro q hq
  change q ∈ g.rules.image v62LiftCFGRule ∪ {v62FreshStartRule g} at hq
  rw [Finset.mem_union] at hq
  rcases hq with hOld | hFresh
  · rcases Finset.mem_image.mp hOld with ⟨r, hr, hqr⟩
    subst q
    have h := (hBound r hr).trans (Nat.le_max_left rhsBound 1)
    simpa [v62LiftCFGRule] using h
  · have hEq : q = v62FreshStartRule g := by simpa using hFresh
    subst q
    simpa [v62FreshStartRule] using (Nat.le_max_right rhsBound 1)

/-- Terminal isolation preserves RHS length exactly on transformed old rules. -/
@[simp] theorem v62_isolate_output_length
    {T N : Type*} (u : List (Symbol T N)) :
    (v62IsolateOutput u).length = u.length := by
  by_cases h : 2 ≤ u.length
  · simp [v62IsolateOutput, h]
  · simp [v62IsolateOutput, h]

/--
If all old nonterminals are productive, then every nonterminal that actually
occurs on an isolated RHS is productive.  Phantom helper names outside the
finite rule set need not be productive and are intentionally excluded.
-/
theorem v62_terminal_isolation_rhs_nonterminals_productive
    {T : Type} {g : ContextFreeGrammar T}
    (hAll : V62CFGAllProductive g) :
    V62CFGRHSNonterminalsProductive
      (v62TerminalIsolationGrammar g) := by
  classical
  intro q hq A hA
  change q ∈ g.rules.image v62IsolateRule ∪
    (v62GrammarTerminals g).image v62TerminalHelperRule at hq
  rw [Finset.mem_union] at hq
  rcases hq with hOld | hHelper
  · rcases Finset.mem_image.mp hOld with ⟨r, hr, hqr⟩
    subst q
    change Symbol.nonterminal A ∈ v62IsolateOutput r.output at hA
    have hproj :
        v62ProjectIsolatedSymbol g (Symbol.nonterminal A) ∈ r.output := by
      rw [← v62_project_isolated_output g r.output]
      exact List.mem_map_of_mem (v62ProjectIsolatedSymbol g) hA
    cases A with
    | inl B =>
        rcases hAll B with ⟨w, hw⟩
        exact ⟨w, v62_terminal_isolation_preserves_old_word_derivation hw⟩
    | inr a =>
        have haOld : Symbol.terminal a ∈ r.output := by
          simpa [v62ProjectIsolatedSymbol] using hproj
        have ha : a ∈ v62GrammarTerminals g :=
          v62_terminal_mem_grammarTerminals_of_rule hr haOld
        refine ⟨[a], ?_⟩
        unfold V62CFGDerivesWordFrom
        exact (v62_terminal_helper_produces g ha).single
  · rcases Finset.mem_image.mp hHelper with ⟨a, ha, hqa⟩
    subst q
    simp [v62TerminalHelperRule] at hA

/-- Terminal isolation changes a uniform RHS bound only by one-letter helper rules. -/
theorem v62_terminal_isolation_rhs_length_bound
    {T : Type} {g : ContextFreeGrammar T} {rhsBound : Nat}
    (hBound : ∀ r ∈ g.rules, r.output.length ≤ rhsBound) :
    ∀ q ∈ (v62TerminalIsolationGrammar g).rules,
      q.output.length ≤ max rhsBound 1 := by
  classical
  intro q hq
  change q ∈ g.rules.image v62IsolateRule ∪
    (v62GrammarTerminals g).image v62TerminalHelperRule at hq
  rw [Finset.mem_union] at hq
  rcases hq with hOld | hHelper
  · rcases Finset.mem_image.mp hOld with ⟨r, hr, hqr⟩
    subst q
    have h := (hBound r hr).trans (Nat.le_max_left rhsBound 1)
    simpa [v62IsolateRule] using h
  · rcases Finset.mem_image.mp hHelper with ⟨a, ha, hqa⟩
    subst q
    simpa [v62TerminalHelperRule] using (Nat.le_max_right rhsBound 1)

/--
Quantitative composition of fresh-start separation, terminal isolation, and
long-rule binarization.

Starting from thickness `tau`, all-productivity, and old RHS bound
`rhsBound`, the binary-stage thickness is bounded explicitly by

`(tau+1) + max rhsBound 1 * max (tau+1) 1`.

This is the executable counterpart of the appendix estimate
`tau_B <= c₁ n (tau_R+1)` before nullable elimination.
-/
theorem v62_first_three_normalization_stages_thickness
    {T : Type} {g : ContextFreeGrammar T}
    {tau rhsBound : Nat}
    (hTau : V62CFGThicknessBound g tau)
    (hAll : V62CFGAllProductive g)
    (hBound : ∀ r ∈ g.rules, r.output.length ≤ rhsBound) :
    V62CFGThicknessBound
      (v62BinarizedGrammar
        (v62TerminalIsolationGrammar (v62FreshStartGrammar g)))
      (V62CFGBinarizationThicknessEnvelope
        (tau + 1) (max rhsBound 1)) := by
  have hTauFresh :
      V62CFGThicknessBound (v62FreshStartGrammar g) tau :=
    v62_fresh_start_preserves_thickness_bound hTau
  have hAllFresh :
      V62CFGAllProductive (v62FreshStartGrammar g) :=
    v62_fresh_start_all_productive hAll
  have hBoundFresh :
      ∀ r ∈ (v62FreshStartGrammar g).rules,
        r.output.length ≤ max rhsBound 1 :=
    v62_fresh_start_rhs_length_bound hBound
  have hTauIso :
      V62CFGThicknessBound
        (v62TerminalIsolationGrammar (v62FreshStartGrammar g))
        (tau + 1) :=
    v62_terminal_isolation_preserves_thickness_bound hTauFresh
  have hRHSProdIso :
      V62CFGRHSNonterminalsProductive
        (v62TerminalIsolationGrammar (v62FreshStartGrammar g)) :=
    v62_terminal_isolation_rhs_nonterminals_productive hAllFresh
  have hBoundIsoRaw :
      ∀ r ∈
          (v62TerminalIsolationGrammar (v62FreshStartGrammar g)).rules,
        r.output.length ≤ max (max rhsBound 1) 1 :=
    v62_terminal_isolation_rhs_length_bound hBoundFresh
  have hBoundIso :
      ∀ r ∈
          (v62TerminalIsolationGrammar (v62FreshStartGrammar g)).rules,
        r.output.length ≤ max rhsBound 1 := by
    intro r hr
    simpa [max_assoc] using hBoundIsoRaw r hr
  exact v62_binarization_preserves_thickness_bound
    hTauIso hRHSProdIso hBoundIso

end FixedHCFG
end LeanCfgProject
