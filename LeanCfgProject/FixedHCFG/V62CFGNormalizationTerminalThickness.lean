import LeanCfgProject.FixedHCFG.V62CFGNormalizationTerminalForward

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Thickness control for v62 terminal isolation

The manuscript uses `bar tau = tau_R + 1` before the later binarization and
nullable-elimination estimates.  Terminal isolation fits exactly inside that
budget: an embedded old nonterminal keeps an old short witness, while every
productive helper nonterminal `T_a` has the one-letter witness `a`.

Because the executable construction creates helper rules only for terminals
that actually occur in the finite rule set, we also prove that productivity of
a helper forces membership in that helper set.
-/

/-- Projection leaves terminal words unchanged. -/
@[simp] theorem v62_project_isolated_terminal_word
    {T : Type} (g : ContextFreeGrammar T) (w : List T) :
    (w.map (@Symbol.terminal T (Sum g.NT T))).map
        (v62ProjectIsolatedSymbol g) =
      w.map (@Symbol.terminal T g.NT) := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [v62ProjectIsolatedSymbol, ih]

/-- Productivity of an embedded old nonterminal projects back to the old grammar. -/
theorem v62_terminal_isolation_old_productive
    {T : Type} {g : ContextFreeGrammar T} {A : g.NT}
    (hProd : V62CFGProductive
      (v62TerminalIsolationGrammar g) (Sum.inl A)) :
    V62CFGProductive g A := by
  rcases hProd with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  unfold V62CFGDerivesWordFrom at hw ⊢
  have hp := v62_project_terminal_isolation_derives hw
  change g.Derives
    [Symbol.nonterminal A]
    ((w.map (@Symbol.terminal T (Sum g.NT T))).map
      (v62ProjectIsolatedSymbol g)) at hp
  rw [v62_project_isolated_terminal_word g w] at hp
  exact hp

/-- A productive helper nonterminal must have been created from an occurring terminal. -/
theorem v62_productive_helper_mem_grammarTerminals
    {T : Type} {g : ContextFreeGrammar T} {a : T}
    (hProd : V62CFGProductive
      (v62TerminalIsolationGrammar g) (Sum.inr a)) :
    a ∈ v62GrammarTerminals g := by
  classical
  rcases hProd with ⟨w, hw⟩
  unfold V62CFGDerivesWordFrom at hw
  have hneq :
      [Symbol.nonterminal (Sum.inr a)] ≠
        w.map (@Symbol.terminal T (Sum g.NT T)) := by
    intro heq
    have hm : Symbol.nonterminal (Sum.inr a) ∈
        w.map (@Symbol.terminal T (Sum g.NT T)) := by
      rw [← heq]
      simp
    simpa using hm
  rcases hw.eq_or_head with heq | ⟨v, hstep, hrest⟩
  · exact (hneq heq).elim
  · rcases hstep.exists_nonterminal_input_mem with ⟨r, hr, hin⟩
    have hinput : r.input = Sum.inr a := by
      simpa using hin
    change r ∈ g.rules.image v62IsolateRule ∪
      (v62GrammarTerminals g).image v62TerminalHelperRule at hr
    rw [Finset.mem_union] at hr
    rcases hr with hOld | hHelper
    · rcases Finset.mem_image.mp hOld with ⟨q, hq, hqr⟩
      subst r
      simp [v62IsolateRule] at hinput
    · rcases Finset.mem_image.mp hHelper with ⟨b, hb, hbr⟩
      subst r
      have hba : b = a := by
        simpa [v62TerminalHelperRule] using hinput
      simpa [hba] using hb

/--
Terminal isolation increases the thickness upper bound by at most one.  This is
the executable counterpart of the manuscript's use of `tau_R + 1` before the
remaining normalization stages.
-/
theorem v62_terminal_isolation_preserves_thickness_bound
    {T : Type} {g : ContextFreeGrammar T} {tau : Nat}
    (hTau : V62CFGThicknessBound g tau) :
    V62CFGThicknessBound (v62TerminalIsolationGrammar g) (tau + 1) := by
  intro A hProd
  cases A with
  | inl B =>
      have hOldProd : V62CFGProductive g B :=
        v62_terminal_isolation_old_productive hProd
      rcases hTau B hOldProd with ⟨w, hw, hlen⟩
      refine ⟨w,
        v62_terminal_isolation_preserves_old_word_derivation hw, ?_⟩
      omega
  | inr a =>
      have ha : a ∈ v62GrammarTerminals g :=
        v62_productive_helper_mem_grammarTerminals hProd
      refine ⟨[a], ?_, ?_⟩
      · unfold V62CFGDerivesWordFrom
        exact (v62_terminal_helper_produces g ha).single
      · simp

end FixedHCFG
end LeanCfgProject
