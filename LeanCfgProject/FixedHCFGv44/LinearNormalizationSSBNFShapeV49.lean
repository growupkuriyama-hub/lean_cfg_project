import LeanCfgProject.FixedHCFGv44.LinearNormalizationSSBNFExactV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Structural SSBNF package for the explicit Appendix A normalization.

The previous layer proves exact language preservation.  Here we record the
specific single-spine shape required by Proposition `prop:linear-normal` and
bridge the custom start presentation to the generic `UntypedStartDerives`
SSBNF semantics already used by the fixed-h development.
-/

/-- Wrapper symbols are exactly the shared `W_a` states. -/
def IsLinearNormWrapper
    {N : Type v} {Sigma : Type u} : LinearNormNT N Sigma → Prop
  | .wrap _ => True
  | _ => False

/-- Every non-wrapper state is a possible continuing/spine state. -/
def IsLinearNormSpine
    {N : Type v} {Sigma : Type u} : LinearNormNT N Sigma → Prop
  | .wrap _ => False
  | _ => True

/-- An `entry` state is never a wrapper and is therefore a spine state. -/
theorem linearNorm_entry_is_spine
    {N : Type v} {Sigma : Type u}
    (r : PreparedLinearRule N Sigma)
    (ops : List (LinearSpineOp Sigma)) :
    IsLinearNormSpine (LinearNormNT.entry r ops) := by
  cases ops with
  | nil =>
      cases r <;> simp [LinearNormNT.entry, LinearNormNT.ruleCore,
        IsLinearNormSpine]
  | cons op rest =>
      simp [LinearNormNT.entry, IsLinearNormSpine]

/-- Old symbols are spine symbols. -/
theorem linearNorm_old_is_spine
    {N : Type v} {Sigma : Type u} (A : N) :
    IsLinearNormSpine (LinearNormNT.old (Sigma := Sigma) A) := by
  trivial

/-- Terminal-chain endpoints are spine symbols, not wrappers. -/
theorem linearNorm_terminalEnd_is_spine
    {N : Type v} {Sigma : Type u}
    (r : PreparedLinearRule N Sigma) :
    IsLinearNormSpine (LinearNormNT.terminalEnd r) := by
  trivial

/--
Every binary production has exactly one wrapper child and one non-wrapper
continuing child.  The disjunction records whether the wrapper occurs on the
left or on the right.
-/
theorem linearNormBinary_single_spine_shape
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {X Y Z : LinearNormNT N Sigma}
    (h : LinearNormBinary rules X Y Z) :
    (IsLinearNormWrapper Y ∧ IsLinearNormSpine Z) ∨
      (IsLinearNormSpine Y ∧ IsLinearNormWrapper Z) := by
  cases h with
  | contextRootLeft hrule hops =>
      exact Or.inl ⟨trivial, linearNorm_entry_is_spine _ _⟩
  | contextRootRight hrule hops =>
      exact Or.inr ⟨linearNorm_entry_is_spine _ _, trivial⟩
  | terminalRootLeft hrule hops =>
      exact Or.inl ⟨trivial, linearNorm_entry_is_spine _ _⟩
  | stageLeft hrule =>
      exact Or.inl ⟨trivial, linearNorm_entry_is_spine _ _⟩
  | stageRight hrule =>
      exact Or.inr ⟨linearNorm_entry_is_spine _ _, trivial⟩

/-- A wrapper terminal rule can only be `W_a -> a`. -/
theorem linearNorm_wrapper_terminal_unique
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {a b : Sigma}
    (h : LinearNormTerminal rules (.wrap a) b) : b = a := by
  cases h
  rfl

/-- No binary production can have a wrapper as its left-hand side. -/
theorem linearNorm_wrapper_never_binary_lhs
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {a : Sigma} {Y Z : LinearNormNT N Sigma} :
    ¬ LinearNormBinary rules (.wrap a) Y Z := by
  intro h
  cases h

/-- Separated start rules point only to old, hence non-wrapper, symbols. -/
def LinearNormStartRules
    {N : Type v} {Sigma : Type u}
    (start : N → Prop) : StartRules (LinearNormNT N Sigma)
  | .old A => start A
  | _ => False

/-- The custom explicit start semantics is exactly the generic SSBNF semantics. -/
theorem explicitLinearNormStart_iff_untypedStart
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop)
    (w : Word Sigma) :
    ExplicitLinearNormStartDerives rules start epsilonStart w ↔
      UntypedStartDerives
        (LinearNormTerminal rules)
        (LinearNormBinary rules)
        (LinearNormStartRules start)
        epsilonStart w := by
  constructor
  · intro d
    cases d with
    | epsilon h =>
        exact UntypedStartDerives.epsilon h
    | @nonempty A w hrule hder =>
        exact UntypedStartDerives.nonempty hrule hder
  · intro d
    cases d with
    | epsilon h =>
        exact ExplicitLinearNormStartDerives.epsilon h
    | @nonempty X w hrule hder =>
        cases X with
        | old A =>
            exact ExplicitLinearNormStartDerives.nonempty hrule hder
        | wrap a =>
            contradiction
        | stage r ops =>
            contradiction
        | terminalEnd r =>
            contradiction

/-- Language of the explicit normalization written purely with generic SSBNF semantics. -/
def ReifiedLinearSpineSSBNFLanguage
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop) : Language Sigma :=
  fun w =>
    UntypedStartDerives
      (LinearNormTerminal rules)
      (LinearNormBinary rules)
      (LinearNormStartRules start)
      epsilonStart w

/--
The reified generic SSBNF grammar has exactly the prepared grammar's language.
This is the manuscript-facing endpoint of the post-preprocessing
wrapper-chain construction.
-/
theorem linearNormalization_reifiedSSBNF_language_eq_v49
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop) :
    ReifiedLinearSpineSSBNFLanguage rules start epsilonStart =
      PreparedLinearLanguage rules start epsilonStart := by
  ext w
  rw [← linearNormalization_explicitSSBNF_language_eq_v49
    rules start epsilonStart]
  exact (explicitLinearNormStart_iff_untypedStart
    rules start epsilonStart w).symm

end FixedHCFGv44
end LeanCfgProject
