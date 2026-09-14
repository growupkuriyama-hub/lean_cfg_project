import LeanCfgProject.FixedHCFGv44.LinearPreprocessingPreparedAdequacyV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Concrete finite enumeration of the prepared grammar used by Appendix A.

The preceding adequacy layer isolates the semantic contract needed at the
preparation boundary.  Here, assuming a finite nonterminal type, we actually
build a finite list satisfying that contract.  Unit elimination never creates
new terminal blocks: it only copies an epsilon-eliminated source rule backward
along the finite unit closure.  Hence it is enough to range over every possible
new left-hand side and every original source production.
-/

/-- Canonical terminal-body representation of a nonempty word beginning with `a`. -/
def terminalBodyOfCons {Sigma : Type u} (a : Sigma) :
    List Sigma → NonemptyTerminalBody Sigma
  | [] => { initial := [], finalSymbol := a }
  | b :: t =>
      let tail := terminalBodyOfCons b t
      { initial := a :: tail.initial, finalSymbol := tail.finalSymbol }

/-- The canonical body for `a :: t` spells exactly that word. -/
theorem terminalBodyOfCons_word
    {Sigma : Type u} (a : Sigma) (t : List Sigma) :
    (terminalBodyOfCons a t).word = a :: t := by
  induction t generalizing a with
  | nil =>
      simp [terminalBodyOfCons, NonemptyTerminalBody.word]
  | cons b t ih =>
      simpa [terminalBodyOfCons, NonemptyTerminalBody.word] using
        congrArg (List.cons a) (ih b)

/-- Canonical body attached to an arbitrary word together with a nonemptiness proof. -/
def nonemptyTerminalBodyOf
    {Sigma : Type u} (w : Word Sigma) (hne : w ≠ []) :
    NonemptyTerminalBody Sigma :=
  match w with
  | [] => False.elim (hne rfl)
  | a :: t => terminalBodyOfCons a t

/-- The canonical nonempty body spells the input word. -/
theorem nonemptyTerminalBodyOf_word
    {Sigma : Type u} (w : Word Sigma) (hne : w ≠ []) :
    (nonemptyTerminalBodyOf w hne).word = w := by
  cases w with
  | nil => exact (hne rfl).elim
  | cons a t =>
      simpa [nonemptyTerminalBodyOf] using terminalBodyOfCons_word a t

/--
Prepared rules contributed by one original source rule when `A` is chosen as
the copied left-hand side after unit closure.
-/
noncomputable def preparedRulesFromSourceAt
    {N : Type v} {Sigma : Type u}
    (sourceRules : List (SourceLinearRule N Sigma))
    (A : N) : SourceLinearRule N Sigma → List (PreparedLinearRule N Sigma)
  | .context B u C v => by
      classical
      by_cases hreach : LinearUnitReach sourceRules A B
      · let contextPart : List (PreparedLinearRule N Sigma) :=
          if hnonunit : u ≠ [] ∨ v ≠ [] then
            [PreparedLinearRule.context A
              { left := u, center := C, right := v } hnonunit]
          else []
        let terminalPart : List (PreparedLinearRule N Sigma) :=
          if hnullable : SourceNullable sourceRules C then
            if hne : u ++ v ≠ [] then
              [PreparedLinearRule.terminal A
                (nonemptyTerminalBodyOf (u ++ v) hne)]
            else []
          else []
        exact contextPart ++ terminalPart
      · exact []
  | .terminal B w => by
      classical
      by_cases hreach : LinearUnitReach sourceRules A B
      · exact if hne : w ≠ [] then
          [PreparedLinearRule.terminal A (nonemptyTerminalBodyOf w hne)]
        else []
      · exact []

/-- Explicit finite prepared-rule list obtained from the finite source grammar. -/
noncomputable def enumeratePreparedLinearRules
    {N : Type v} {Sigma : Type u} [Fintype N]
    (sourceRules : List (SourceLinearRule N Sigma)) :
    List (PreparedLinearRule N Sigma) := by
  classical
  exact Finset.univ.toList.flatMap fun A =>
    sourceRules.flatMap (preparedRulesFromSourceAt sourceRules A)

/-- Every enumerated prepared production is a genuine unit-elimination production. -/
theorem enumeratePreparedLinearRules_sound
    {N : Type v} {Sigma : Type u} [Fintype N]
    (sourceRules : List (SourceLinearRule N Sigma))
    {p : PreparedLinearRule N Sigma}
    (hp : p ∈ enumeratePreparedLinearRules sourceRules) :
    PreparedRuleMatchesUnit sourceRules p := by
  classical
  simp only [enumeratePreparedLinearRules, List.mem_flatMap] at hp
  rcases hp with ⟨A, hA, hp⟩
  rcases hp with ⟨r, hr, hp⟩
  cases r with
  | context B u C v =>
      simp only [preparedRulesFromSourceAt] at hp
      split at hp
      next hreach =>
        simp only [List.mem_append] at hp
        rcases hp with hpCtx | hpTerm
        · split at hpCtx
          next hnonunit =>
            simp only [List.mem_singleton] at hpCtx
            subst p
            change UnitElimLinearRule sourceRules
              (SourceLinearRule.context A u C v)
            exact UnitElimLinearRule.context hreach
              (EpsilonElimLinearRule.context hr) hnonunit
          next hnonunit => simp at hpCtx
        · split at hpTerm
          next hnullable =>
            split at hpTerm
            next hne =>
              simp only [List.mem_singleton] at hpTerm
              subst p
              change UnitElimLinearRule sourceRules
                (SourceLinearRule.terminal A
                  (nonemptyTerminalBodyOf (u ++ v) hne).word)
              rw [nonemptyTerminalBodyOf_word]
              exact UnitElimLinearRule.terminal hreach
                (EpsilonElimLinearRule.omitNullable hr hnullable hne)
            next hne => simp at hpTerm
          next hnullable => simp at hpTerm
      next hreach => simp at hp
  | terminal B w =>
      simp only [preparedRulesFromSourceAt] at hp
      split at hp
      next hreach =>
        split at hp
        next hne =>
          simp only [List.mem_singleton] at hp
          subst p
          change UnitElimLinearRule sourceRules
            (SourceLinearRule.terminal A (nonemptyTerminalBodyOf w hne).word)
          rw [nonemptyTerminalBodyOf_word]
          exact UnitElimLinearRule.terminal hreach
            (EpsilonElimLinearRule.terminal hr hne)
        next hne => simp at hp
      next hreach => simp at hp

/-- Every unit-free context production is present in the explicit enumeration. -/
theorem enumeratePreparedLinearRules_context_complete
    {N : Type v} {Sigma : Type u} [Fintype N]
    (sourceRules : List (SourceLinearRule N Sigma))
    {A C : N} {u v : Word Sigma}
    (hRule : UnitElimLinearRule sourceRules
      (SourceLinearRule.context A u C v)) :
    ∃ hnonunit : u ≠ [] ∨ v ≠ [],
      PreparedLinearRule.context A
        { left := u, center := C, right := v } hnonunit ∈
          enumeratePreparedLinearRules sourceRules := by
  classical
  cases hRule with
  | @context A B C u v reach hsrc hnonunit =>
      cases hsrc with
      | context hr =>
          refine ⟨hnonunit, ?_⟩
          simp only [enumeratePreparedLinearRules, List.mem_flatMap]
          refine ⟨A, by simp, ?_⟩
          refine ⟨SourceLinearRule.context B u C v, hr, ?_⟩
          simp [preparedRulesFromSourceAt, reach, hnonunit]

/-- Every unit-free terminal production is present in the explicit enumeration. -/
theorem enumeratePreparedLinearRules_terminal_complete
    {N : Type v} {Sigma : Type u} [Fintype N]
    (sourceRules : List (SourceLinearRule N Sigma))
    {A : N} {w : Word Sigma}
    (hRule : UnitElimLinearRule sourceRules
      (SourceLinearRule.terminal A w)) :
    ∃ body : NonemptyTerminalBody Sigma,
      body.word = w ∧
        PreparedLinearRule.terminal A body ∈
          enumeratePreparedLinearRules sourceRules := by
  classical
  cases hRule with
  | @terminal A B w reach hsrc =>
      cases hsrc with
      | terminal hr hne =>
          refine ⟨nonemptyTerminalBodyOf w hne,
            nonemptyTerminalBodyOf_word w hne, ?_⟩
          simp only [enumeratePreparedLinearRules, List.mem_flatMap]
          refine ⟨A, by simp, ?_⟩
          refine ⟨SourceLinearRule.terminal B w, hr, ?_⟩
          simp [preparedRulesFromSourceAt, reach, hne]
      | @omitNullable B C u v hr hnullable hne =>
          refine ⟨nonemptyTerminalBodyOf (u ++ v) hne,
            nonemptyTerminalBodyOf_word (u ++ v) hne, ?_⟩
          simp only [enumeratePreparedLinearRules, List.mem_flatMap]
          refine ⟨A, by simp, ?_⟩
          refine ⟨SourceLinearRule.context B u C v, hr, ?_⟩
          simp [preparedRulesFromSourceAt, reach, hnullable, hne]

/-- The concrete finite enumeration satisfies the preparation adequacy contract. -/
theorem enumeratePreparedLinearRules_adequate_v49
    {N : Type v} {Sigma : Type u} [Fintype N]
    (sourceRules : List (SourceLinearRule N Sigma)) :
    PreparedRuleListAdequate sourceRules
      (enumeratePreparedLinearRules sourceRules) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact enumeratePreparedLinearRules_sound sourceRules hp
  · intro A B u v hRule
    exact enumeratePreparedLinearRules_context_complete sourceRules hRule
  · intro A w hRule
    exact enumeratePreparedLinearRules_terminal_complete sourceRules hRule

/--
The explicitly enumerated prepared grammar has exactly the original source
linear-CFG language at the separated start interface.
-/
theorem enumerated_prepared_language_eq_source_v49
    {N : Type v} {Sigma : Type u} [Fintype N]
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) :
    PreparedLinearLanguage (enumeratePreparedLinearRules sourceRules)
        (SourceSeparatedStart S) (SourceNullable sourceRules S) =
      SourceLinearLanguage sourceRules S := by
  exact prepared_separated_language_eq_source_of_adequate_v49 S
    (enumeratePreparedLinearRules_adequate_v49 sourceRules)

end FixedHCFGv44
end LeanCfgProject
