import LeanCfgProject.FixedHCFG.V62CFGNormalizationBinaryThickness

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Installed helper positions for executable v62 binarization

The executable binary grammar uses an intentionally large helper type
`ContextFreeRule × Nat`.  Most of those formal helper names are unreachable
and unproductive.  For thickness we only need productive helpers.

This file proves that any productive helper actually occurs at a genuine
position of the chain generated from an installed old production.  It also
recovers the complete remaining helper subchain, which is what lets the
sentential short-witness bound be transported back to that helper.
-/

/--
A member of a generated tail chain remembers a genuine chain position.  From
that position onward, the restarted tail chain is contained in the original
tail list.
-/
theorem v62_binarize_tail_member_recovers_position
    {T N : Type*} {r : ContextFreeRule T N} {i : Nat}
    {u : List (Symbol T N)}
    {q : ContextFreeRule T
      (Sum N (ContextFreeRule T N × Nat))}
    (hu : r.output.drop (i + 1) = u)
    (hq : q ∈ v62BinarizeTailRules r i u) :
    ∃ k : Nat,
      q.input = Sum.inr (r, k) ∧
      2 ≤ (r.output.drop (k + 1)).length ∧
      ∀ q',
        q' ∈ v62BinarizeTailRules r k
            (r.output.drop (k + 1)) →
          q' ∈ v62BinarizeTailRules r i u := by
  induction u generalizing i q with
  | nil =>
      simp [v62BinarizeTailRules] at hq
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [v62BinarizeTailRules] at hq
      | cons y ys =>
          cases ys with
          | nil =>
              simp [v62BinarizeTailRules] at hq
              subst q
              refine ⟨i, rfl, ?_, ?_⟩
              · rw [hu]
                simp
              · intro q' hq'
                simpa [hu] using hq'
          | cons z zs =>
              simp only [v62BinarizeTailRules, List.mem_cons] at hq
              have hnext :
                  r.output.drop ((i + 1) + 1) = y :: z :: zs := by
                calc
                  r.output.drop ((i + 1) + 1) =
                      (r.output.drop (i + 1)).drop 1 := by
                    simp [List.drop_drop]
                  _ = (x :: y :: z :: zs).drop 1 := by rw [hu]
                  _ = y :: z :: zs := by rfl
              rcases hq with hfirst | hrest
              · subst q
                refine ⟨i, rfl, ?_, ?_⟩
                · rw [hu]
                  simp
                · intro q' hq'
                  simpa [hu] using hq'
              · rcases ih hnext hrest with
                  ⟨k, hkinput, hklen, hksub⟩
                refine ⟨k, hkinput, hklen, ?_⟩
                intro q' hq'
                simp only [v62BinarizeTailRules, List.mem_cons]
                exact Or.inr (hksub q' hq')

/--
If a transformed production has a helper as its input, that helper belongs to
the same old production and to a suffix of length at least two.  The complete
remaining helper chain is part of the transformed rule list for that old rule.
-/
theorem v62_binarize_rules_for_helper_recovers
    {T N : Type*}
    {r₀ r : ContextFreeRule T N} {i : Nat}
    {q : ContextFreeRule T
      (Sum N (ContextFreeRule T N × Nat))}
    (hq : q ∈ v62BinarizeRulesFor r₀)
    (hinput : q.input = Sum.inr (r, i)) :
    r₀ = r ∧
      2 ≤ (r.output.drop (i + 1)).length ∧
      ∀ q',
        q' ∈ v62BinarizeTailRules r i
            (r.output.drop (i + 1)) →
          q' ∈ v62BinarizeRulesFor r₀ := by
  cases h0 : r₀.output with
  | nil =>
      simp [v62BinarizeRulesFor, h0] at hq
      subst q
      simp at hinput
  | cons x xs =>
      cases xs with
      | nil =>
          simp [v62BinarizeRulesFor, h0] at hq
          subst q
          simp at hinput
      | cons y ys =>
          cases ys with
          | nil =>
              simp [v62BinarizeRulesFor, h0] at hq
              subst q
              simp at hinput
          | cons z zs =>
              simp only [v62BinarizeRulesFor, h0, List.mem_cons] at hq
              rcases hq with hfirst | htail
              · subst q
                simp at hinput
              · have hbase :
                    r₀.output.drop (0 + 1) = y :: z :: zs := by
                  simpa [h0]
                rcases v62_binarize_tail_member_recovers_position
                    hbase htail with
                  ⟨k, hkinput, hklen, hksub⟩
                have hsum :
                    Sum.inr (r₀, k) = Sum.inr (r, i) :=
                  hkinput.symm.trans hinput
                have hp : (r₀, k) = (r, i) :=
                  Sum.inr.inj hsum
                have hr : r₀ = r := congrArg Prod.fst hp
                have hi : k = i := congrArg Prod.snd hp
                subst r
                subst i
                refine ⟨rfl, hklen, ?_⟩
                intro q' hq'
                simp only [v62BinarizeRulesFor, h0, List.mem_cons]
                exact Or.inr (hksub q' hq')

/--
A productive binary helper is necessarily one of the installed helper
positions of some old production.  All rules of its remaining chain are
therefore present in the binary grammar.
-/
theorem v62_productive_binarized_helper_data
    {T : Type} {g : ContextFreeGrammar T}
    {r : ContextFreeRule T g.NT} {i : Nat}
    (hProd : V62CFGProductive
      (v62BinarizedGrammar g) (Sum.inr (r, i))) :
    r ∈ g.rules ∧
      2 ≤ (r.output.drop (i + 1)).length ∧
      ∀ q,
        q ∈ v62BinarizeTailRules r i
            (r.output.drop (i + 1)) →
          q ∈ (v62BinarizedGrammar g).rules := by
  classical
  rcases hProd with ⟨w, hw⟩
  unfold V62CFGDerivesWordFrom at hw
  have hneq :
      [Symbol.nonterminal (Sum.inr (r, i))] ≠
        w.map (@Symbol.terminal T
          (Sum g.NT (ContextFreeRule T g.NT × Nat))) := by
    intro heq
    have hm : Symbol.nonterminal (Sum.inr (r, i)) ∈
        w.map (@Symbol.terminal T
          (Sum g.NT (ContextFreeRule T g.NT × Nat))) := by
      rw [← heq]
      simp
    simpa using hm
  rcases hw.eq_or_head with heq | ⟨v, hstep, hrest⟩
  · exact (hneq heq).elim
  · rcases hstep.exists_nonterminal_input_mem with ⟨q, hq, hin⟩
    have hinput : q.input = Sum.inr (r, i) := by
      simpa using hin
    change q ∈ g.rules.biUnion
      (fun s => (v62BinarizeRulesFor s).toFinset) at hq
    rcases Finset.mem_biUnion.mp hq with ⟨r₀, hr₀, hqr⟩
    have hlist : q ∈ v62BinarizeRulesFor r₀ := by
      simpa only [List.mem_toFinset] using hqr
    rcases v62_binarize_rules_for_helper_recovers
        hlist hinput with
      ⟨hrEq, hlen, hsub⟩
    subst r₀
    refine ⟨hr₀, hlen, ?_⟩
    intro q' hq'
    exact v62_binarized_rule_mem hr₀ (hsub q' hq')

end FixedHCFG
end LeanCfgProject
