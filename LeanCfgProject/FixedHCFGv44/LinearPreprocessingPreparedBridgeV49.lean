import LeanCfgProject.FixedHCFGv44.LinearPreprocessingUnitV49
import LeanCfgProject.FixedHCFGv44.LinearNormalizationPreparedSemanticsV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Semantic bridge from the source-side epsilon/unit preprocessing to the
`PreparedLinearRule` representation consumed by the explicit Appendix A
single-spine normalization.

The only still-separate issue after this file is finite enumeration: given the
finite source grammar and a finite nonterminal type, construct a concrete list
of prepared rules whose membership is exactly `PreparedRuleMatchesUnit`.
Once such a list is supplied, the theorems below identify its prepared start
language with the original source linear-CFG language.
-/

/-- A prepared production denotes exactly one surviving unit-free source rule. -/
def PreparedRuleMatchesUnit
    {N : Type v} {Sigma : Type u}
    (sourceRules : List (SourceLinearRule N Sigma)) :
    PreparedLinearRule N Sigma → Prop
  | .context A body _ =>
      UnitElimLinearRule sourceRules
        (SourceLinearRule.context A body.left body.center body.right)
  | .terminal A body =>
      UnitElimLinearRule sourceRules
        (SourceLinearRule.terminal A body.word)

/-- A concrete prepared rule list is exact when it enumerates precisely the unit-free rules. -/
def PreparedRuleListExact
    {N : Type v} {Sigma : Type u}
    (sourceRules : List (SourceLinearRule N Sigma))
    (prepared : List (PreparedLinearRule N Sigma)) : Prop :=
  ∀ p, p ∈ prepared ↔ PreparedRuleMatchesUnit sourceRules p

/-- Every terminal rule surviving unit elimination has a nonempty terminal word. -/
theorem unitElim_terminal_rule_nonempty
    {N : Type v} {Sigma : Type u}
    {sourceRules : List (SourceLinearRule N Sigma)}
    {A : N} {w : Word Sigma}
    (h : UnitElimLinearRule sourceRules
      (SourceLinearRule.terminal A w)) :
    w ≠ [] := by
  cases h with
  | @terminal A B w reach hsrc =>
      cases hsrc with
      | terminal hmem hne => exact hne
      | omitNullable hmem hnullable hne => exact hne

/-- Every nonempty word admits the `initial ++ [finalSymbol]` representation used downstream. -/
theorem exists_nonemptyTerminalBody_of_ne_nil
    {Sigma : Type u} (w : Word Sigma) (hne : w ≠ []) :
    ∃ body : NonemptyTerminalBody Sigma, body.word = w := by
  induction w with
  | nil =>
      exact (hne rfl).elim
  | cons a t ih =>
      by_cases ht : t = []
      · subst t
        refine ⟨{ initial := [], finalSymbol := a }, ?_⟩
        simp [NonemptyTerminalBody.word]
      · rcases ih ht with ⟨body, hbody⟩
        refine ⟨{ initial := a :: body.initial,
          finalSymbol := body.finalSymbol }, ?_⟩
        simp [NonemptyTerminalBody.word, hbody]

/--
Every derivation after unit elimination is represented by any exact prepared
rule list.
-/
theorem unitElim_to_prepared_of_exact
    {N : Type v} {Sigma : Type u}
    {sourceRules : List (SourceLinearRule N Sigma)}
    {prepared : List (PreparedLinearRule N Sigma)}
    (hExact : PreparedRuleListExact sourceRules prepared)
    {A : N} {w : Word Sigma}
    (d : UnitElimLinearDerives sourceRules A w) :
    PreparedLinearDerives prepared A w := by
  induction d with
  | @terminal A w hrule =>
      have hne : w ≠ [] := unitElim_terminal_rule_nonempty hrule
      rcases exists_nonemptyTerminalBody_of_ne_nil w hne with
        ⟨body, hword⟩
      have hmem : PreparedLinearRule.terminal A body ∈ prepared := by
        apply (hExact (PreparedLinearRule.terminal A body)).2
        simpa [PreparedRuleMatchesUnit, hword] using hrule
      have hd : PreparedLinearDerives prepared A body.word :=
        PreparedLinearDerives.terminal hmem
      simpa [hword] using hd
  | @context A B u v z hrule center ih =>
      cases hrule with
      | @context A D B u v reach hsrc hnonunit =>
          let body : LinearContextBody N Sigma :=
            { left := u, center := B, right := v }
          have hmem : PreparedLinearRule.context A body hnonunit ∈ prepared := by
            apply (hExact (PreparedLinearRule.context A body hnonunit)).2
            change UnitElimLinearRule sourceRules
              (SourceLinearRule.context A u B v)
            exact UnitElimLinearRule.context reach hsrc hnonunit
          have hd : PreparedLinearDerives prepared A
              (body.left ++ z ++ body.right) :=
            PreparedLinearDerives.context hmem ih
          simpa [body] using hd

/-- Every derivation of an exact prepared list expands back to the unit-free source grammar. -/
theorem prepared_to_unitElim_of_exact
    {N : Type v} {Sigma : Type u}
    {sourceRules : List (SourceLinearRule N Sigma)}
    {prepared : List (PreparedLinearRule N Sigma)}
    (hExact : PreparedRuleListExact sourceRules prepared)
    {A : N} {w : Word Sigma}
    (d : PreparedLinearDerives prepared A w) :
    UnitElimLinearDerives sourceRules A w := by
  induction d with
  | @terminal A body hmem =>
      have hmatch : UnitElimLinearRule sourceRules
          (SourceLinearRule.terminal A body.word) := by
        exact (hExact (PreparedLinearRule.terminal A body)).1 hmem
      exact UnitElimLinearDerives.terminal hmatch
  | @context A body h z hmem center ih =>
      have hmatch : UnitElimLinearRule sourceRules
          (SourceLinearRule.context A body.left body.center body.right) := by
        exact (hExact (PreparedLinearRule.context A body h)).1 hmem
      exact UnitElimLinearDerives.context hmatch ih

/-- Exact nonterminal-language equivalence across the preparation boundary. -/
theorem prepared_unitElim_language_iff_of_exact
    {N : Type v} {Sigma : Type u}
    {sourceRules : List (SourceLinearRule N Sigma)}
    {prepared : List (PreparedLinearRule N Sigma)}
    (hExact : PreparedRuleListExact sourceRules prepared)
    (A : N) (w : Word Sigma) :
    PreparedLinearDerives prepared A w ↔
      UnitElimLinearDerives sourceRules A w := by
  constructor
  · exact prepared_to_unitElim_of_exact hExact
  · exact unitElim_to_prepared_of_exact hExact

/-- Separated start language after both epsilon and unit elimination. -/
def UnitSeparatedLinearLanguage
    {N : Type v} {Sigma : Type u}
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) : Language Sigma :=
  fun w =>
    (w = [] ∧ SourceNullable sourceRules S) ∨
      (w ≠ [] ∧ UnitElimLinearDerives sourceRules S w)

/-- Epsilon plus unit elimination preserves the original source start language exactly. -/
theorem unit_separated_language_eq_source_v49
    {N : Type v} {Sigma : Type u}
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) :
    UnitSeparatedLinearLanguage sourceRules S =
      SourceLinearLanguage sourceRules S := by
  ext w
  constructor
  · intro h
    rcases h with hEps | hNonempty
    · rcases hEps with ⟨rfl, hNullable⟩
      exact hNullable
    · exact epsilonElim_to_source
        (unitElim_to_epsilonElim hNonempty.2)
  · intro h
    by_cases hw : w = []
    · subst w
      exact Or.inl ⟨rfl, h⟩
    · have hEps : EpsilonElimLinearDerives sourceRules S w :=
        source_nonempty_to_epsilonElim h hw
      exact Or.inr ⟨hw, epsilonElim_to_unitElim hEps⟩

/--
Any exact finite prepared enumeration has exactly the original source linear
language at the separated start interface.
-/
theorem prepared_separated_language_eq_source_of_exact_v49
    {N : Type v} {Sigma : Type u}
    {sourceRules : List (SourceLinearRule N Sigma)}
    {prepared : List (PreparedLinearRule N Sigma)}
    (S : N)
    (hExact : PreparedRuleListExact sourceRules prepared) :
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
        have hAS : A = S := hStart
        subst A
        exact epsilonElim_to_source
          (unitElim_to_epsilonElim
            (prepared_to_unitElim_of_exact hExact hDeriv))
  · intro h
    by_cases hw : w = []
    · subst w
      exact PreparedLinearStartDerives.epsilon h
    · have hEps : EpsilonElimLinearDerives sourceRules S w :=
        source_nonempty_to_epsilonElim h hw
      have hUnit : UnitElimLinearDerives sourceRules S w :=
        epsilonElim_to_unitElim hEps
      exact PreparedLinearStartDerives.nonempty rfl
        (unitElim_to_prepared_of_exact hExact hUnit)

end FixedHCFGv44
end LeanCfgProject