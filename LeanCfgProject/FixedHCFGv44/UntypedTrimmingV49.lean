import LeanCfgProject.FixedHCFGv44.YieldTypedCore

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Generic reachable/productive trimming for the untyped SSBNF semantics used by
TCS v49.

This is the untyped analogue of `YieldTypedTrimmed`.  It is factored out so
Appendix A can perform its final useless-symbol deletion on the explicit
single-spine SSBNF grammar without changing the generated start language.
-/

/-- An untyped state occurs in a successful start tree with terminal context `(u,v)`. -/
inductive UntypedOccurs {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma)
    (binary : BinaryRules N) (start : StartRules N) :
    N → Word Sigma → Word Sigma → Prop
  | start {A : N}
      (hrule : start A) :
      UntypedOccurs terminal binary start A [] []
  | left {A B C : N} {u v y : Word Sigma}
      (parent : UntypedOccurs terminal binary start A u v)
      (hrule : binary A B C)
      (rightDeriv : UntypedDerives terminal binary C y) :
      UntypedOccurs terminal binary start B u (y ++ v)
  | right {A B C : N} {u v x : Word Sigma}
      (parent : UntypedOccurs terminal binary start A u v)
      (hrule : binary A B C)
      (leftDeriv : UntypedDerives terminal binary B x) :
      UntypedOccurs terminal binary start C (u ++ x) v

/-- Productivity in an untyped SSBNF grammar. -/
def UntypedProductive {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (A : N) : Prop :=
  ∃ w : Word Sigma, UntypedDerives terminal binary A w

/-- Reachability from the separated start interface. -/
def UntypedReachable {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (A : N) : Prop :=
  ∃ u v : Word Sigma, UntypedOccurs terminal binary start A u v

/-- States retained by ordinary reachable/productive trimming. -/
def UntypedKept {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (A : N) : Prop :=
  UntypedProductive terminal binary A ∧
    UntypedReachable terminal binary start A

/-- Derivations all of whose participating states survive trimming. -/
inductive UntypedKeptDerives {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) :
    N → Word Sigma → Prop
  | terminal {A : N} {a : Sigma}
      (hrule : terminal A a)
      (hkeep : UntypedKept terminal binary start A) :
      UntypedKeptDerives terminal binary start A [a]
  | binary {A B C : N} {x y : Word Sigma}
      (hrule : binary A B C)
      (hkeep : UntypedKept terminal binary start A)
      (left : UntypedKeptDerives terminal binary start B x)
      (right : UntypedKeptDerives terminal binary start C y) :
      UntypedKeptDerives terminal binary start A (x ++ y)

/-- A trimmed derivation is an ordinary derivation. -/
theorem untyped_kept_to_full
    {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    {A : N} {w : Word Sigma}
    (d : UntypedKeptDerives terminal binary start A w) :
    UntypedDerives terminal binary A w := by
  induction d with
  | terminal hrule hkeep =>
      exact UntypedDerives.terminal hrule
  | binary hrule hkeep left right ihLeft ihRight =>
      exact UntypedDerives.binary hrule ihLeft ihRight

/-- The root of every trimmed derivation is retained. -/
theorem untyped_kept_root_is_kept
    {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    {A : N} {w : Word Sigma}
    (d : UntypedKeptDerives terminal binary start A w) :
    UntypedKept terminal binary start A := by
  cases d with
  | terminal hrule hkeep => exact hkeep
  | binary hrule hkeep left right => exact hkeep

/-- Every successful subtree survives reachable/productive trimming. -/
theorem successful_untyped_derivation_survives
    {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    {A : N} {u v w : Word Sigma}
    (hocc : UntypedOccurs terminal binary start A u v)
    (d : UntypedDerives terminal binary A w) :
    UntypedKeptDerives terminal binary start A w := by
  induction d generalizing u v with
  | @terminal A a hrule =>
      have hkeep : UntypedKept terminal binary start A := by
        constructor
        · exact ⟨[a], UntypedDerives.terminal hrule⟩
        · exact ⟨u, v, hocc⟩
      exact UntypedKeptDerives.terminal hrule hkeep
  | @binary A B C x y hrule left right ihLeft ihRight =>
      have hoccLeft : UntypedOccurs terminal binary start B u (y ++ v) :=
        UntypedOccurs.left hocc hrule right
      have hoccRight : UntypedOccurs terminal binary start C (u ++ x) v :=
        UntypedOccurs.right hocc hrule left
      have hleft := ihLeft hoccLeft
      have hright := ihRight hoccRight
      have hkeep : UntypedKept terminal binary start A := by
        constructor
        · exact ⟨x ++ y, UntypedDerives.binary hrule left right⟩
        · exact ⟨u, v, hocc⟩
      exact UntypedKeptDerives.binary hrule hkeep hleft hright

/-- Start language after reachable/productive trimming. -/
def TrimmedUntypedStartLanguage {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) : Language Sigma :=
  fun w =>
    (w = [] ∧ epsilonStart) ∨
      ∃ A : N, start A ∧
        UntypedKeptDerives terminal binary start A w

/-- Ordinary SSBNF start language in set-valued form. -/
def GenericUntypedStartLanguage {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) : Language Sigma :=
  fun w => UntypedStartDerives terminal binary start epsilonStart w

/-- Reachable/productive trimming preserves the SSBNF start language exactly. -/
theorem untyped_trimming_language_iff
    {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (w : Word Sigma) :
    TrimmedUntypedStartLanguage terminal binary start epsilonStart w ↔
      GenericUntypedStartLanguage terminal binary start epsilonStart w := by
  constructor
  · intro h
    rcases h with hEps | hNonempty
    · exact UntypedStartDerives.epsilon hEps.2
    · rcases hNonempty with ⟨A, hStart, hDeriv⟩
      exact UntypedStartDerives.nonempty hStart
        (untyped_kept_to_full terminal binary start hDeriv)
  · intro h
    cases h with
    | epsilon hEps =>
        exact Or.inl ⟨rfl, hEps⟩
    | @nonempty A w hStart hDeriv =>
        have hOcc : UntypedOccurs terminal binary start A [] [] :=
          UntypedOccurs.start hStart
        have hKept := successful_untyped_derivation_survives
          terminal binary start hOcc hDeriv
        exact Or.inr ⟨A, hStart, hKept⟩

/-- Language-valued form of untyped trimming preservation. -/
theorem untyped_trimming_language_eq
    {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    TrimmedUntypedStartLanguage terminal binary start epsilonStart =
      GenericUntypedStartLanguage terminal binary start epsilonStart := by
  ext w
  exact untyped_trimming_language_iff
    terminal binary start epsilonStart w

end FixedHCFGv44
end LeanCfgProject
