import LeanCfgProject.FixedHCFGv44.LinearPreprocessingPreparedBridgeV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
A construction-friendly finite-list contract for the preparation boundary.

`PreparedRuleListExact` says that list membership is literally equivalent to
`PreparedRuleMatchesUnit` for every proof-carrying `PreparedLinearRule`.  That
is convenient semantically, but stronger than a concrete enumerator needs.
For construction it is enough that every listed prepared rule is sound, every
unit-free context rule is represented, and every unit-free terminal rule is
represented by some (necessarily nonempty) terminal body.
-/

/-- Soundness plus context/terminal coverage of a finite prepared rule list. -/
def PreparedRuleListAdequate
    {N : Type v} {Sigma : Type u}
    (sourceRules : List (SourceLinearRule N Sigma))
    (prepared : List (PreparedLinearRule N Sigma)) : Prop :=
  (∀ p, p ∈ prepared → PreparedRuleMatchesUnit sourceRules p) ∧
    (∀ {A B : N} {u v : Word Sigma},
      UnitElimLinearRule sourceRules
          (SourceLinearRule.context A u B v) →
        ∃ hnonunit : u ≠ [] ∨ v ≠ [],
          PreparedLinearRule.context A
            { left := u, center := B, right := v } hnonunit ∈ prepared) ∧
    (∀ {A : N} {w : Word Sigma},
      UnitElimLinearRule sourceRules
          (SourceLinearRule.terminal A w) →
        ∃ body : NonemptyTerminalBody Sigma,
          body.word = w ∧
            PreparedLinearRule.terminal A body ∈ prepared)

/-- Literal exactness implies the weaker construction-oriented adequacy contract. -/
theorem preparedRuleListExact_implies_adequate
    {N : Type v} {Sigma : Type u}
    {sourceRules : List (SourceLinearRule N Sigma)}
    {prepared : List (PreparedLinearRule N Sigma)}
    (hExact : PreparedRuleListExact sourceRules prepared) :
    PreparedRuleListAdequate sourceRules prepared := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact (hExact p).1 hp
  · intro A B u v hRule
    cases hRule with
    | @context A D B u v reach hsrc hnonunit =>
        let body : LinearContextBody N Sigma :=
          { left := u, center := B, right := v }
        have hBody : body.Nonunit := by
          simpa [body, LinearContextBody.Nonunit] using hnonunit
        refine ⟨hBody, ?_⟩
        apply (hExact (PreparedLinearRule.context A body hBody)).2
        change UnitElimLinearRule sourceRules
          (SourceLinearRule.context A u B v)
        exact UnitElimLinearRule.context reach hsrc hnonunit
  · intro A w hRule
    have hne : w ≠ [] := unitElim_terminal_rule_nonempty hRule
    rcases exists_nonemptyTerminalBody_of_ne_nil w hne with ⟨body, hword⟩
    refine ⟨body, hword, ?_⟩
    apply (hExact (PreparedLinearRule.terminal A body)).2
    simpa [PreparedRuleMatchesUnit, hword] using hRule

/-- Every unit-free derivation is represented by an adequate prepared rule list. -/
theorem unitElim_to_prepared_of_adequate
    {N : Type v} {Sigma : Type u}
    {sourceRules : List (SourceLinearRule N Sigma)}
    {prepared : List (PreparedLinearRule N Sigma)}
    (hAdeq : PreparedRuleListAdequate sourceRules prepared)
    {A : N} {w : Word Sigma}
    (d : UnitElimLinearDerives sourceRules A w) :
    PreparedLinearDerives prepared A w := by
  induction d with
  | @terminal A w hrule =>
      rcases hAdeq.2.2 hrule with ⟨body, hword, hmem⟩
      have hd : PreparedLinearDerives prepared A body.word :=
        PreparedLinearDerives.terminal hmem
      simpa [hword] using hd
  | @context A B u v z hrule center ih =>
      rcases hAdeq.2.1 hrule with ⟨hnonunit, hmem⟩
      let body : LinearContextBody N Sigma :=
        { left := u, center := B, right := v }
      have hd : PreparedLinearDerives prepared A
          (body.left ++ z ++ body.right) :=
        PreparedLinearDerives.context hmem ih
      simpa [body] using hd

/-- Every prepared derivation of an adequate list expands to the unit-free grammar. -/
theorem prepared_to_unitElim_of_adequate
    {N : Type v} {Sigma : Type u}
    {sourceRules : List (SourceLinearRule N Sigma)}
    {prepared : List (PreparedLinearRule N Sigma)}
    (hAdeq : PreparedRuleListAdequate sourceRules prepared)
    {A : N} {w : Word Sigma}
    (d : PreparedLinearDerives prepared A w) :
    UnitElimLinearDerives sourceRules A w := by
  induction d with
  | @terminal A body hmem =>
      have hmatch := hAdeq.1 (PreparedLinearRule.terminal A body) hmem
      exact UnitElimLinearDerives.terminal hmatch
  | @context A body h z hmem center ih =>
      have hmatch := hAdeq.1 (PreparedLinearRule.context A body h) hmem
      exact UnitElimLinearDerives.context hmatch ih

/-- Exact nonterminal-language equivalence under the adequate-list contract. -/
theorem prepared_unitElim_language_iff_of_adequate
    {N : Type v} {Sigma : Type u}
    {sourceRules : List (SourceLinearRule N Sigma)}
    {prepared : List (PreparedLinearRule N Sigma)}
    (hAdeq : PreparedRuleListAdequate sourceRules prepared)
    (A : N) (w : Word Sigma) :
    PreparedLinearDerives prepared A w ↔
      UnitElimLinearDerives sourceRules A w := by
  constructor
  · exact prepared_to_unitElim_of_adequate hAdeq
  · exact unitElim_to_prepared_of_adequate hAdeq

/--
An adequate prepared list has exactly the original source linear language at
the separated start interface.
-/
theorem prepared_separated_language_eq_source_of_adequate_v49
    {N : Type v} {Sigma : Type u}
    {sourceRules : List (SourceLinearRule N Sigma)}
    {prepared : List (PreparedLinearRule N Sigma)}
    (S : N)
    (hAdeq : PreparedRuleListAdequate sourceRules prepared) :
    PreparedLinearLanguage prepared
        (SourceSeparatedStart S) (SourceNullable sourceRules S) =
      SourceLinearLanguage sourceRules S := by
  ext w
  constructor
  · intro h
    cases h with
    | epsilon hNullable =>
        exact hNullable
    | @nonempty A w hStart hDeriv =>
        have hAS : A = S := by
          simpa [SourceSeparatedStart] using hStart
        subst A
        exact epsilonElim_to_source
          (unitElim_to_epsilonElim
            (prepared_to_unitElim_of_adequate hAdeq hDeriv))
  · intro h
    by_cases hw : w = []
    · subst w
      exact PreparedLinearStartDerives.epsilon h
    · have hEps : EpsilonElimLinearDerives sourceRules S w :=
        source_nonempty_to_epsilonElim h hw
      have hUnit : UnitElimLinearDerives sourceRules S w :=
        epsilonElim_to_unitElim hEps
      exact PreparedLinearStartDerives.nonempty
        (A := S) (by rfl)
        (unitElim_to_prepared_of_adequate hAdeq hUnit)

end FixedHCFGv44
end LeanCfgProject