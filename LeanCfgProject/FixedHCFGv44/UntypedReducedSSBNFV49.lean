import LeanCfgProject.FixedHCFGv44.UntypedTrimmingV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Reification of reachable/productive trimming as an actual terminal/binary
SSBNF presentation.

`UntypedTrimmingV49` gives the semantic kept-derivation relation.  This file
restricts the original terminal, binary, and separated start rules to retained
states and proves that the resulting ordinary `UntypedDerives` grammar has
exactly the same start language.  The final contracts state directly that
every state mentioned by a retained production/start rule is productive and
reachable in the original presentation.
-/

/-- Terminal rules retained by reachable/productive trimming. -/
def TrimmedTerminalRules
    {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) : TerminalRules N Sigma :=
  fun A a => terminal A a ∧ UntypedKept terminal binary start A

/-- Binary rules retained by reachable/productive trimming. -/
def TrimmedBinaryRules
    {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) : BinaryRules N :=
  fun A B C =>
    binary A B C ∧
      UntypedKept terminal binary start A ∧
      UntypedKept terminal binary start B ∧
      UntypedKept terminal binary start C

/-- Separated start rules retained by reachable/productive trimming. -/
def TrimmedStartRules
    {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) : StartRules N :=
  fun A => start A ∧ UntypedKept terminal binary start A

/-- A semantic kept derivation is a derivation of the explicitly restricted grammar. -/
theorem untyped_kept_to_trimmed_rules
    {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    {A : N} {w : Word Sigma}
    (d : UntypedKeptDerives terminal binary start A w) :
    UntypedDerives
      (TrimmedTerminalRules terminal binary start)
      (TrimmedBinaryRules terminal binary start) A w := by
  induction d with
  | terminal hrule hkeep =>
      exact UntypedDerives.terminal ⟨hrule, hkeep⟩
  | @binary A B C x y hrule hkeep left right ihLeft ihRight =>
      have hB : UntypedKept terminal binary start B :=
        untyped_kept_root_is_kept terminal binary start left
      have hC : UntypedKept terminal binary start C :=
        untyped_kept_root_is_kept terminal binary start right
      exact UntypedDerives.binary
        ⟨hrule, hkeep, hB, hC⟩ ihLeft ihRight

/-- Every derivation of the restricted grammar is a semantic kept derivation. -/
theorem trimmed_rules_to_untyped_kept
    {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    {A : N} {w : Word Sigma}
    (d : UntypedDerives
      (TrimmedTerminalRules terminal binary start)
      (TrimmedBinaryRules terminal binary start) A w) :
    UntypedKeptDerives terminal binary start A w := by
  induction d with
  | terminal hrule =>
      exact UntypedKeptDerives.terminal hrule.1 hrule.2
  | binary hrule left right ihLeft ihRight =>
      exact UntypedKeptDerives.binary hrule.1 hrule.2.1 ihLeft ihRight

/-- Start language of the explicitly restricted reduced SSBNF grammar. -/
def ReducedUntypedStartLanguage
    {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) : Language Sigma :=
  GenericUntypedStartLanguage
    (TrimmedTerminalRules terminal binary start)
    (TrimmedBinaryRules terminal binary start)
    (TrimmedStartRules terminal binary start)
    epsilonStart

/-- The restricted-rule grammar realizes exactly the semantic trimmed language. -/
theorem reduced_untyped_language_eq_semantic_trim
    {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    ReducedUntypedStartLanguage terminal binary start epsilonStart =
      TrimmedUntypedStartLanguage terminal binary start epsilonStart := by
  ext w
  constructor
  · intro h
    cases h with
    | epsilon hEps =>
        exact Or.inl ⟨rfl, hEps⟩
    | @nonempty A w hStart hDeriv =>
        exact Or.inr ⟨A, hStart.1,
          trimmed_rules_to_untyped_kept terminal binary start hDeriv⟩
  · intro h
    rcases h with hEps | hNonempty
    · rcases hEps with ⟨rfl, hEps⟩
      exact UntypedStartDerives.epsilon hEps
    · rcases hNonempty with ⟨A, hStart, hDeriv⟩
      have hKeep : UntypedKept terminal binary start A :=
        untyped_kept_root_is_kept terminal binary start hDeriv
      exact UntypedStartDerives.nonempty
        ⟨hStart, hKeep⟩
        (untyped_kept_to_trimmed_rules terminal binary start hDeriv)

/-- The explicitly reduced grammar preserves the original start language exactly. -/
theorem reduced_untyped_language_eq_original
    {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    ReducedUntypedStartLanguage terminal binary start epsilonStart =
      GenericUntypedStartLanguage terminal binary start epsilonStart := by
  calc
    ReducedUntypedStartLanguage terminal binary start epsilonStart =
        TrimmedUntypedStartLanguage terminal binary start epsilonStart :=
      reduced_untyped_language_eq_semantic_trim
        terminal binary start epsilonStart
    _ = GenericUntypedStartLanguage terminal binary start epsilonStart :=
      untyped_trimming_language_eq terminal binary start epsilonStart

/-- Every retained terminal-rule left-hand side is productive and reachable. -/
theorem trimmed_terminal_lhs_kept
    {N : Type v} {Sigma : Type u}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N} {A : N} {a : Sigma}
    (h : TrimmedTerminalRules terminal binary start A a) :
    UntypedKept terminal binary start A :=
  h.2

/-- Every state occurring in a retained binary production is productive and reachable. -/
theorem trimmed_binary_states_kept
    {N : Type v} {Sigma : Type u}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N} {A B C : N}
    (h : TrimmedBinaryRules terminal binary start A B C) :
    UntypedKept terminal binary start A ∧
      UntypedKept terminal binary start B ∧
      UntypedKept terminal binary start C :=
  h.2

/-- Every retained start target is productive and reachable. -/
theorem trimmed_start_target_kept
    {N : Type v} {Sigma : Type u}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N} {A : N}
    (h : TrimmedStartRules terminal binary start A) :
    UntypedKept terminal binary start A :=
  h.2

/-- Compact reducedness contract for the explicitly restricted grammar. -/
theorem reduced_untyped_rule_contract_v49
    {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) :
    (∀ ⦃A : N⦄ ⦃a : Sigma⦄,
        TrimmedTerminalRules terminal binary start A a →
          UntypedKept terminal binary start A) ∧
      (∀ ⦃A B C : N⦄,
        TrimmedBinaryRules terminal binary start A B C →
          UntypedKept terminal binary start A ∧
          UntypedKept terminal binary start B ∧
          UntypedKept terminal binary start C) ∧
      (∀ ⦃A : N⦄,
        TrimmedStartRules terminal binary start A →
          UntypedKept terminal binary start A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A a h
    exact trimmed_terminal_lhs_kept
      (terminal := terminal) (binary := binary) (start := start) h
  · intro A B C h
    exact trimmed_binary_states_kept
      (terminal := terminal) (binary := binary) (start := start) h
  · intro A h
    exact trimmed_start_target_kept
      (terminal := terminal) (binary := binary) (start := start) h

end FixedHCFGv44
end LeanCfgProject
