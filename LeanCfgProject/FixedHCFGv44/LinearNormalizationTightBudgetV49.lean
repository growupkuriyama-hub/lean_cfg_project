import LeanCfgProject.FixedHCFGv44.LinearNormalizationActiveStatesV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Tight polynomial state budget for the explicit v49 linear normalization.

`LinearNormalizationActiveStatesV49` used the deliberately coarse finite set of
*all* spine programs up to a global length bound.  That is ideal for proving
finiteness but its cardinality can be exponential.  Here we enumerate only the
stage labels that are actually introduced by each prepared production.  Their
number is exactly the manuscript's fresh-state count, so the resulting support
has the polynomial `normalizationNonterminalBudget` cardinality envelope.
-/

/--
Stage labels appearing after successively consuming the outer spine operation.
For a program of length `k`, exactly `k-1` stage labels are introduced; the
last continuation is the old center state (context rule) or terminal endpoint.
-/
def properStageLabelsV49
    {N : Type v} {Sigma : Type u}
    (r : PreparedLinearRule N Sigma) :
    List (LinearSpineOp Sigma) → List (LinearNormNT N Sigma)
  | [] => []
  | [_] => []
  | _ :: op :: rest =>
      LinearNormNT.stage r (op :: rest) ::
        properStageLabelsV49 r (op :: rest)

/-- Exact number of proper stage labels in a spine program. -/
theorem properStageLabelsV49_length
    {N : Type v} {Sigma : Type u}
    (r : PreparedLinearRule N Sigma) (ops : List (LinearSpineOp Sigma)) :
    (properStageLabelsV49 r ops).length = ops.length - 1 := by
  induction ops with
  | nil => simp [properStageLabelsV49]
  | cons op ops ih =>
      cases ops with
      | nil => simp [properStageLabelsV49]
      | cons op' rest =>
          simp [properStageLabelsV49, ih]

/--
Fresh normalized labels contributed by one prepared rule.  Context rules use
only proper stage states.  A terminal-only rule with at least one wrapper step
also uses its final `terminalEnd` state.
-/
def preparedFreshLabelsV49
    {N : Type v} {Sigma : Type u} :
    PreparedLinearRule N Sigma → List (LinearNormNT N Sigma)
  | .context A body h =>
      properStageLabelsV49 (.context A body h) body.spineOps
  | .terminal A body =>
      match body.spineOps with
      | [] => []
      | _ :: _ =>
          properStageLabelsV49 (.terminal A body) body.spineOps ++
            [LinearNormNT.terminalEnd (.terminal A body)]

/-- The explicit fresh-label list has exactly the manuscript fresh-state count. -/
theorem preparedFreshLabelsV49_length
    {N : Type v} {Sigma : Type u}
    (r : PreparedLinearRule N Sigma) :
    (preparedFreshLabelsV49 r).length = r.freshStateCount := by
  cases r with
  | context A body h =>
      change
        (properStageLabelsV49 (PreparedLinearRule.context A body h)
          body.spineOps).length = body.freshChainCount
      rw [properStageLabelsV49_length]
      have hEq := body.freshChainCount_add_one_eq_spineSteps h
      omega
  | terminal A body =>
      have hEq := body.spineOps_length_eq_freshChainCount
      cases hOps : body.spineOps with
      | nil =>
          rw [hOps] at hEq
          simp only [List.length_nil] at hEq
          simp [preparedFreshLabelsV49, hOps, PreparedLinearRule.freshStateCount,
            hEq]
      | cons op rest =>
          rw [hOps] at hEq
          simp only [List.length_cons] at hEq
          simp [preparedFreshLabelsV49, hOps, properStageLabelsV49_length,
            PreparedLinearRule.freshStateCount]
          omega

/-- Production-local fresh labels concatenated over the prepared grammar. -/
def normalizationFreshLabelsV49
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) :
    List (LinearNormNT N Sigma) :=
  rules.flatMap preparedFreshLabelsV49

/-- The concatenated fresh-label list realizes the global fresh-state count. -/
theorem normalizationFreshLabelsV49_length
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) :
    (normalizationFreshLabelsV49 rules).length =
      normalizationFreshStateCount rules := by
  induction rules with
  | nil => simp [normalizationFreshLabelsV49, normalizationFreshStateCount]
  | cons r rs ih =>
      simp [normalizationFreshLabelsV49, normalizationFreshStateCount,
        preparedFreshLabelsV49_length]

/-- All old source labels, embedded in the normalized nonterminal type. -/
noncomputable def linearNormOldLabelsV49
    {N : Type v} {Sigma : Type u} [Fintype N] :
    Finset (LinearNormNT N Sigma) := by
  classical
  exact (Finset.univ : Finset N).image (fun A => LinearNormNT.old A)

/-- All globally shared terminal wrappers. -/
noncomputable def linearNormWrapperLabelsV49
    {N : Type v} {Sigma : Type u} [Fintype Sigma] :
    Finset (LinearNormNT N Sigma) := by
  classical
  exact (Finset.univ : Finset Sigma).image (fun a => LinearNormNT.wrap a)

/-- Exactly the production-local fresh labels, quotienting possible duplicates. -/
noncomputable def linearNormFreshLabelsFinsetV49
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) :
    Finset (LinearNormNT N Sigma) := by
  classical
  exact (normalizationFreshLabelsV49 rules).toFinset

/-- Tight finite support for normalized labels. -/
noncomputable def linearNormTightLabelsV49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma)) :
    Finset (LinearNormNT N Sigma) := by
  classical
  exact linearNormOldLabelsV49 ∪ linearNormWrapperLabelsV49 ∪
    linearNormFreshLabelsFinsetV49 rules

/-- The fresh-label support is bounded by the summed fresh-state count. -/
theorem linearNormFreshLabelsFinsetV49_card_le
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) :
    (linearNormFreshLabelsFinsetV49 rules).card ≤
      normalizationFreshStateCount rules := by
  classical
  unfold linearNormFreshLabelsFinsetV49
  have h := List.toFinset_card_le (normalizationFreshLabelsV49 rules)
  simpa [normalizationFreshLabelsV49_length] using h

/--
The tight normalized label support fits exactly inside the manuscript's
nonterminal budget `|N| + |Sigma| + freshStates`.
-/
theorem linearNormTightLabelsV49_card_le_budget
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma)) :
    (linearNormTightLabelsV49 rules).card ≤
      normalizationNonterminalBudget rules := by
  classical
  have hOld : (linearNormOldLabelsV49 (N := N) (Sigma := Sigma)).card ≤
      Fintype.card N := by
    unfold linearNormOldLabelsV49
    exact Finset.card_image_le
  have hWrap : (linearNormWrapperLabelsV49 (N := N) (Sigma := Sigma)).card ≤
      Fintype.card Sigma := by
    unfold linearNormWrapperLabelsV49
    exact Finset.card_image_le
  have hFresh := linearNormFreshLabelsFinsetV49_card_le rules
  have hFirst := Finset.card_union_le
    (linearNormOldLabelsV49 (N := N) (Sigma := Sigma))
    (linearNormWrapperLabelsV49 (N := N) (Sigma := Sigma))
  have hSecond := Finset.card_union_le
    (linearNormOldLabelsV49 (N := N) (Sigma := Sigma) ∪
      linearNormWrapperLabelsV49 (N := N) (Sigma := Sigma))
    (linearNormFreshLabelsFinsetV49 rules)
  unfold linearNormTightLabelsV49 normalizationNonterminalBudget
  omega

end FixedHCFGv44
end LeanCfgProject
