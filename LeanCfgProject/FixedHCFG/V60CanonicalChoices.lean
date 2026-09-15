import Mathlib.Data.List.Shortlex
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60Extraction

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Canonical choices from Section 4 of the v60 manuscript.

`omega(X)` is the shortlex-least terminal yield.  `chi(X)=(u_X,v_X)` first
minimizes `|u|+|v|`, then breaks ties by shortlex on `u`, then by shortlex on
`v`.  In particular this context order is intentionally not the older plain
lexicographic order on context pairs.
-/

/-- The manuscript's shortlex order on terminal words. -/
abbrev V60WordShortlex {Sigma : Type u} [LT Sigma] :
    Word Sigma → Word Sigma → Prop :=
  List.Shortlex (fun a b : Sigma => a < b)

/-- Shortlex on terminal words is well founded. -/
theorem v60WordShortlex_wf
    {Sigma : Type u} [LT Sigma] [WellFoundedLT Sigma] :
    WellFounded (V60WordShortlex (Sigma := Sigma)) :=
  List.Shortlex.wf wellFounded_lt

/-- Terminal yields of a retained v60 state. -/
def V60TypedYieldSet
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) : Set (Word Sigma) :=
  {w | V60YieldTypedDerives Obs terminal binary X.1 w}

/-- Every retained state has at least one terminal yield. -/
theorem v60TypedYieldSet_nonempty
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) :
    (V60TypedYieldSet X).Nonempty := by
  exact X.property.1

/-- The exact v60 shortlex-least canonical yield `omega(X)`. -/
noncomputable def v60CanonicalOmega
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) : Word Sigma :=
  (v60WordShortlex_wf (Sigma := Sigma)).min
    (V60TypedYieldSet X) (v60TypedYieldSet_nonempty X)

/-- The canonical yield is genuinely derivable. -/
theorem v60CanonicalOmega_spec
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) :
    V60YieldTypedDerives Obs terminal binary X.1 (v60CanonicalOmega X) := by
  exact (v60WordShortlex_wf (Sigma := Sigma)).min_mem
    (V60TypedYieldSet X) (v60TypedYieldSet_nonempty X)

/-- No terminal yield of `X` is strictly shortlex-smaller than `omega(X)`. -/
theorem v60CanonicalOmega_minimal
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start)
    {w : Word Sigma}
    (hw : V60YieldTypedDerives Obs terminal binary X.1 w) :
    ¬ V60WordShortlex w (v60CanonicalOmega X) := by
  simpa [v60CanonicalOmega, V60TypedYieldSet] using
    ((v60WordShortlex_wf (Sigma := Sigma)).not_lt_min
      (V60TypedYieldSet X) hw)

/-- Canonical yields of non-start states are nonempty. -/
theorem v60CanonicalOmega_nonempty
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) :
    v60CanonicalOmega X ≠ [] := by
  exact v60_yield_typed_derivation_nonempty Obs terminal binary
    (v60CanonicalOmega_spec X)

/-- The canonical yield has exactly the yield type written on `X`. -/
theorem v60CanonicalOmega_type
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) :
    Obs.value (v60CanonicalOmega X) = X.1.yieldType := by
  exact v60_yield_typed_invariant Obs terminal binary
    (v60CanonicalOmega_spec X)

/-- Successful terminal contexts of a retained state. -/
def V60TypedContextSet
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) :
    Set (Word Sigma × Word Sigma) :=
  {c | V60TypedOccurs Obs terminal binary start X.1 c.1 c.2}

/-- Every retained state has at least one successful terminal context. -/
theorem v60TypedContextSet_nonempty
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) :
    (V60TypedContextSet X).Nonempty := by
  rcases X.property.2 with ⟨u, v, hOcc⟩
  exact ⟨(u, v), hOcc⟩

/-- Tie-break order on contexts: first left shortlex, then right shortlex. -/
abbrev V60ContextTie {Sigma : Type u} [LT Sigma] :
    (Word Sigma × Word Sigma) → (Word Sigma × Word Sigma) → Prop :=
  Prod.Lex (V60WordShortlex (Sigma := Sigma))
    (V60WordShortlex (Sigma := Sigma))

/-- The key used by v60: total context length, then the two shortlex components. -/
def V60ContextKey {Sigma : Type u}
    (c : Word Sigma × Word Sigma) :
    Nat × (Word Sigma × Word Sigma) :=
  (c.1.length + c.2.length, c)

/-- Exact order defining `chi`: total length first, then left/right shortlex. -/
abbrev V60ContextOrder {Sigma : Type u} [LT Sigma] :
    (Word Sigma × Word Sigma) → (Word Sigma × Word Sigma) → Prop :=
  (Prod.Lex ((· < ·) : Nat → Nat → Prop)
    (V60ContextTie (Sigma := Sigma))).onFun V60ContextKey

/-- The exact v60 context order is well founded. -/
theorem v60ContextOrder_wf
    {Sigma : Type u} [LT Sigma] [WellFoundedLT Sigma] :
    WellFounded (V60ContextOrder (Sigma := Sigma)) := by
  have hNat : WellFounded ((· < ·) : Nat → Nat → Prop) := wellFounded_lt
  have hTie : WellFounded (V60ContextTie (Sigma := Sigma)) :=
    (v60WordShortlex_wf (Sigma := Sigma)).prod_lex
      (v60WordShortlex_wf (Sigma := Sigma))
  exact (hNat.prod_lex hTie).onFun

/-- The v60 canonical context `chi(X)`. -/
noncomputable def v60CanonicalChi
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) :
    Word Sigma × Word Sigma :=
  (v60ContextOrder_wf (Sigma := Sigma)).min
    (V60TypedContextSet X) (v60TypedContextSet_nonempty X)

noncomputable def v60CanonicalLeftCtx
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) : Word Sigma :=
  (v60CanonicalChi X).1

noncomputable def v60CanonicalRightCtx
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) : Word Sigma :=
  (v60CanonicalChi X).2

/-- The canonical pair is a genuine successful occurrence. -/
theorem v60CanonicalChi_spec
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) :
    V60TypedOccurs Obs terminal binary start X.1
      (v60CanonicalLeftCtx X) (v60CanonicalRightCtx X) := by
  exact (v60ContextOrder_wf (Sigma := Sigma)).min_mem
    (V60TypedContextSet X) (v60TypedContextSet_nonempty X)

/-- No successful context is smaller than the v60 canonical context. -/
theorem v60CanonicalChi_minimal
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start)
    {c : Word Sigma × Word Sigma}
    (hc : c ∈ V60TypedContextSet X) :
    ¬ V60ContextOrder c (v60CanonicalChi X) := by
  simpa [v60CanonicalChi] using
    ((v60ContextOrder_wf (Sigma := Sigma)).not_lt_min
      (V60TypedContextSet X) hc)

/-- A direct start state has canonical context exactly `([],[])`. -/
theorem v60CanonicalChi_start_empty
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (X : V60KeptState Obs terminal binary start)
    (hStart : V60KeptStart X) :
    v60CanonicalLeftCtx X = [] ∧ v60CanonicalRightCtx X = [] := by
  have hEmpty : ([], []) ∈ V60TypedContextSet X := by
    exact v60_kept_start_occurs_empty Obs terminal binary start X hStart
  have hNot :
      ¬ V60ContextOrder ([], []) (v60CanonicalChi X) :=
    v60CanonicalChi_minimal X hEmpty
  have hsum :
      (v60CanonicalChi X).1.length + (v60CanonicalChi X).2.length = 0 := by
    by_contra hne
    have hpos :
        0 < (v60CanonicalChi X).1.length + (v60CanonicalChi X).2.length :=
      Nat.pos_of_ne_zero hne
    apply hNot
    exact Prod.Lex.left _ _ hpos
  have hleftLen : (v60CanonicalChi X).1.length = 0 := by omega
  have hrightLen : (v60CanonicalChi X).2.length = 0 := by omega
  constructor
  · exact List.length_eq_zero_iff.mp hleftLen
  · exact List.length_eq_zero_iff.mp hrightLen

end FixedHCFG
end LeanCfgProject
