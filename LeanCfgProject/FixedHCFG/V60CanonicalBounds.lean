import LeanCfgProject.FixedHCFG.V60CanonicalChoices

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Length consequences of the exact v60 canonical choices.

These are the bridge lemmas needed by the fixed-window and linear-spine data
bounds: shortlex minimality implies shortest yield length, while the v60
context order implies minimum total context length.
-/

/-- `omega(X)` is no longer than any other terminal yield of `X`. -/
theorem v60CanonicalOmega_length_le
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start)
    {w : Word Sigma}
    (hw : V60YieldTypedDerives Obs terminal binary X.1 w) :
    (v60CanonicalOmega X).length ≤ w.length := by
  by_contra hle
  have hlt : w.length < (v60CanonicalOmega X).length :=
    Nat.lt_of_not_ge hle
  have hShort : V60WordShortlex w (v60CanonicalOmega X) :=
    List.Shortlex.of_length_lt hlt
  exact v60CanonicalOmega_minimal X hw hShort

/-- `chi(X)` minimizes total terminal context length among successful occurrences. -/
theorem v60CanonicalChi_total_length_le
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start)
    {u v : Word Sigma}
    (hOcc : V60TypedOccurs Obs terminal binary start X.1 u v) :
    (v60CanonicalLeftCtx X).length + (v60CanonicalRightCtx X).length ≤
      u.length + v.length := by
  by_contra hle
  have hlt :
      u.length + v.length <
        (v60CanonicalLeftCtx X).length + (v60CanonicalRightCtx X).length :=
    Nat.lt_of_not_ge hle
  have hMem : (u, v) ∈ V60TypedContextSet X := hOcc
  have hNot := v60CanonicalChi_minimal X hMem
  apply hNot
  have hOrder : V60ContextOrder (u, v) (v60CanonicalChi X) := by
    exact Prod.Lex.left _ _ hlt
  exact hOrder

end FixedHCFG
end LeanCfgProject
