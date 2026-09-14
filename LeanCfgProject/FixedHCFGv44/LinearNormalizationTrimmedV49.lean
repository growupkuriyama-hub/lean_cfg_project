import LeanCfgProject.FixedHCFGv44.LinearNormalizationPostPreprocessingV49
import LeanCfgProject.FixedHCFGv44.UntypedReducedSSBNFV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Final reachable/productive trimming of the explicit Appendix A normalization.

The post-preprocessing construction already gives an exact single-spine SSBNF.
Here we apply the generic untyped trimming/reification layer and obtain an
actual restricted terminal/binary/start-rule presentation whose participating
states are all productive and reachable.  Trimming only removes rules, so the
single-spine/wrapper contracts are inherited verbatim.
-/

/-- Retained terminal rules of the explicit normalized grammar. -/
def TrimmedLinearNormTerminal
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) : TerminalRules (LinearNormNT N Sigma) Sigma :=
  TrimmedTerminalRules
    (LinearNormTerminal rules)
    (LinearNormBinary rules)
    (LinearNormStartRules start)

/-- Retained binary rules of the explicit normalized grammar. -/
def TrimmedLinearNormBinary
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) : BinaryRules (LinearNormNT N Sigma) :=
  TrimmedBinaryRules
    (LinearNormTerminal rules)
    (LinearNormBinary rules)
    (LinearNormStartRules start)

/-- Retained separated start rules of the explicit normalized grammar. -/
def TrimmedLinearNormStart
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) : StartRules (LinearNormNT N Sigma) :=
  TrimmedStartRules
    (LinearNormTerminal rules)
    (LinearNormBinary rules)
    (LinearNormStartRules start)

/-- Start language of the final reduced single-spine SSBNF presentation. -/
def ReducedLinearSpineSSBNFLanguage
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop) : Language Sigma :=
  GenericUntypedStartLanguage
    (TrimmedLinearNormTerminal rules start)
    (TrimmedLinearNormBinary rules start)
    (TrimmedLinearNormStart rules start)
    epsilonStart

/-- Final trimming preserves exactly the prepared grammar's language. -/
theorem linearNormalization_trimmed_language_eq_v49
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop) :
    ReducedLinearSpineSSBNFLanguage rules start epsilonStart =
      PreparedLinearLanguage rules start epsilonStart := by
  calc
    ReducedLinearSpineSSBNFLanguage rules start epsilonStart =
        GenericUntypedStartLanguage
          (LinearNormTerminal rules)
          (LinearNormBinary rules)
          (LinearNormStartRules start)
          epsilonStart :=
      reduced_untyped_language_eq_original
        (LinearNormTerminal rules)
        (LinearNormBinary rules)
        (LinearNormStartRules start)
        epsilonStart
    _ = ReifiedLinearSpineSSBNFLanguage rules start epsilonStart := rfl
    _ = PreparedLinearLanguage rules start epsilonStart :=
      linearNormalization_reifiedSSBNF_language_eq_v49
        rules start epsilonStart

/-- Every retained binary rule still has exactly one wrapper child. -/
theorem trimmedLinearNormBinary_single_spine_shape
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {start : N → Prop}
    {X Y Z : LinearNormNT N Sigma}
    (h : TrimmedLinearNormBinary rules start X Y Z) :
    LinearNormSingleSpineRule Y Z := by
  exact linearNormBinary_single_spine_shape h.1

/-- Retained wrapper terminal rules are still uniquely `W_a -> a`. -/
theorem trimmedLinearNorm_wrapper_terminal_unique
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {start : N → Prop} {a b : Sigma}
    (h : TrimmedLinearNormTerminal rules start (.wrap a) b) :
    b = a := by
  exact linearNorm_wrapper_terminal_unique h.1

/-- A wrapper can never become the left-hand side of a retained binary rule. -/
theorem trimmedLinearNorm_wrapper_never_binary_lhs
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {start : N → Prop} {a : Sigma}
    {Y Z : LinearNormNT N Sigma} :
    ¬ TrimmedLinearNormBinary rules start (.wrap a) Y Z := by
  intro h
  exact linearNorm_wrapper_never_binary_lhs h.1

/-- Every state in a retained binary rule is productive and reachable. -/
theorem trimmedLinearNorm_binary_states_reduced
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {start : N → Prop}
    {X Y Z : LinearNormNT N Sigma}
    (h : TrimmedLinearNormBinary rules start X Y Z) :
    UntypedKept
        (LinearNormTerminal rules)
        (LinearNormBinary rules)
        (LinearNormStartRules start) X ∧
      UntypedKept
        (LinearNormTerminal rules)
        (LinearNormBinary rules)
        (LinearNormStartRules start) Y ∧
      UntypedKept
        (LinearNormTerminal rules)
        (LinearNormBinary rules)
        (LinearNormStartRules start) Z := by
  exact h.2

/-- Every left-hand side of a retained terminal rule is productive and reachable. -/
theorem trimmedLinearNorm_terminal_lhs_reduced
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {start : N → Prop}
    {X : LinearNormNT N Sigma} {a : Sigma}
    (h : TrimmedLinearNormTerminal rules start X a) :
    UntypedKept
      (LinearNormTerminal rules)
      (LinearNormBinary rules)
      (LinearNormStartRules start) X := by
  exact h.2

/-- Every retained start target is productive and reachable. -/
theorem trimmedLinearNorm_start_target_reduced
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {start : N → Prop}
    {X : LinearNormNT N Sigma}
    (h : TrimmedLinearNormStart rules start X) :
    UntypedKept
      (LinearNormTerminal rules)
      (LinearNormBinary rules)
      (LinearNormStartRules start) X := by
  exact h.2

/--
Manuscript-facing final-trimming contract for the post-preprocessing half of
`prop:linear-normal`: exact language preservation, reduced participating
states, and preservation of the single-spine/wrapper shape.
-/
theorem linearNormalization_final_trimming_v49
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop) :
    ReducedLinearSpineSSBNFLanguage rules start epsilonStart =
        PreparedLinearLanguage rules start epsilonStart ∧
      (∀ ⦃X Y Z : LinearNormNT N Sigma⦄,
        TrimmedLinearNormBinary rules start X Y Z →
          LinearNormSingleSpineRule Y Z) ∧
      (∀ ⦃X Y Z : LinearNormNT N Sigma⦄,
        TrimmedLinearNormBinary rules start X Y Z →
          UntypedKept
              (LinearNormTerminal rules)
              (LinearNormBinary rules)
              (LinearNormStartRules start) X ∧
            UntypedKept
              (LinearNormTerminal rules)
              (LinearNormBinary rules)
              (LinearNormStartRules start) Y ∧
            UntypedKept
              (LinearNormTerminal rules)
              (LinearNormBinary rules)
              (LinearNormStartRules start) Z) := by
  refine ⟨linearNormalization_trimmed_language_eq_v49
      rules start epsilonStart, ?_, ?_⟩
  · intro X Y Z h
    exact trimmedLinearNormBinary_single_spine_shape h
  · intro X Y Z h
    exact trimmedLinearNorm_binary_states_reduced h

end FixedHCFGv44
end LeanCfgProject
