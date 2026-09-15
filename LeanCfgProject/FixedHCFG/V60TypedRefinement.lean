import LeanCfgProject.FixedHCFG.V60Kernel

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Exact yield-only typed refinement from Section 4 of the v60 TCS manuscript.

The refined non-start symbol is only `A_mu`.  No left/right context type is
stored.  This is deliberately separate from the older two-sided typed
formalization so that the v60 proof can be checked against the manuscript
literally.
-/

/-- Untyped SSBNF terminal productions `A -> a`. -/
abbrev V60TerminalRules (N : Type v) (Sigma : Type u) := N → Sigma → Prop

/-- Untyped SSBNF binary productions `A -> BC`. -/
abbrev V60BinaryRules (N : Type v) := N → N → N → Prop

/-- Untyped SSBNF start productions `S0 -> A`. -/
abbrev V60StartRules (N : Type v) := N → Prop

/-- A v60 refined non-start symbol `A_mu`. -/
structure V60TypedNT (N : Type v) {Sigma : Type u} (Obs : Observer Sigma) where
  label : N
  yieldType : Obs.M

/-- Non-start derivations in the underlying SSBNF grammar. -/
inductive V60UntypedDerives {N : Type v} {Sigma : Type u}
    (terminal : V60TerminalRules N Sigma) (binary : V60BinaryRules N) :
    N → Word Sigma → Prop
  | terminal {A : N} {a : Sigma}
      (hrule : terminal A a) :
      V60UntypedDerives terminal binary A [a]
  | binary {A B C : N} {x y : Word Sigma}
      (hrule : binary A B C)
      (left : V60UntypedDerives terminal binary B x)
      (right : V60UntypedDerives terminal binary C y) :
      V60UntypedDerives terminal binary A (x ++ y)

/--
Derivations in the full yield-only refinement.

The constructors are exactly the manuscript rules
`A_{h(a)} -> a` and `A_{mu nu} -> B_mu C_nu`.
-/
inductive V60YieldTypedDerives {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma) (binary : V60BinaryRules N) :
    V60TypedNT N Obs → Word Sigma → Prop
  | terminal {A : N} {a : Sigma} {p : Obs.M}
      (hrule : terminal A a)
      (htype : Obs.value [a] = p) :
      V60YieldTypedDerives Obs terminal binary
        { label := A, yieldType := p } [a]
  | binary {A B C : N} {p q r : Obs.M} {x y : Word Sigma}
      (hrule : binary A B C)
      (hproduct : Obs.mul q r = p)
      (left : V60YieldTypedDerives Obs terminal binary
        { label := B, yieldType := q } x)
      (right : V60YieldTypedDerives Obs terminal binary
        { label := C, yieldType := r } y) :
      V60YieldTypedDerives Obs terminal binary
        { label := A, yieldType := p } (x ++ y)

/-- Proposition 4.x, yield invariant: a typed root records exactly the `h`-type of its yield. -/
theorem v60_yield_typed_invariant
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma) (binary : V60BinaryRules N)
    {X : V60TypedNT N Obs} {w : Word Sigma}
    (d : V60YieldTypedDerives Obs terminal binary X w) :
    Obs.value w = X.yieldType := by
  induction d with
  | terminal hrule htype =>
      exact htype
  | binary hrule hproduct left right ihLeft ihRight =>
      calc
        Obs.value (_ ++ _) = Obs.mul (Obs.value _) (Obs.value _) :=
          Obs.value_append _ _
        _ = Obs.mul _ _ := by rw [ihLeft, ihRight]
        _ = _ := hproduct

/-- Every untyped SSBNF derivation lifts to the full yield-only refinement. -/
theorem v60_untyped_derivation_lifts
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma) (binary : V60BinaryRules N)
    {A : N} {w : Word Sigma}
    (d : V60UntypedDerives terminal binary A w) :
    V60YieldTypedDerives Obs terminal binary
      { label := A, yieldType := Obs.value w } w := by
  induction d with
  | terminal hrule =>
      exact V60YieldTypedDerives.terminal hrule rfl
  | @binary A B C x y hrule left right ihLeft ihRight =>
      exact V60YieldTypedDerives.binary hrule
        (Obs.value_append x y).symm ihLeft ihRight

/-- Erasing a yield annotation maps every typed derivation back to the SSBNF derivation. -/
theorem v60_yield_typed_derivation_erases
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma) (binary : V60BinaryRules N)
    {X : V60TypedNT N Obs} {w : Word Sigma}
    (d : V60YieldTypedDerives Obs terminal binary X w) :
    V60UntypedDerives terminal binary X.label w := by
  induction d with
  | terminal hrule htype =>
      exact V60UntypedDerives.terminal hrule
  | binary hrule hproduct left right ihLeft ihRight =>
      exact V60UntypedDerives.binary hrule ihLeft ihRight

private theorem v60_append_ne_nil_of_left_ne
    {Alpha : Type u} {x y : List Alpha} (hx : x ≠ []) : x ++ y ≠ [] := by
  cases x with
  | nil => exact (hx rfl).elim
  | cons a xs => simp

/-- Every non-start SSBNF derivation has a nonempty terminal yield. -/
theorem v60_untyped_derivation_nonempty
    {N : Type v} {Sigma : Type u}
    (terminal : V60TerminalRules N Sigma) (binary : V60BinaryRules N)
    {A : N} {w : Word Sigma}
    (d : V60UntypedDerives terminal binary A w) :
    w ≠ [] := by
  induction d with
  | terminal hrule => simp
  | binary hrule left right ihLeft ihRight =>
      exact v60_append_ne_nil_of_left_ne ihLeft

/-- Hence every yield of a refined non-start symbol lies in `Sigma+`. -/
theorem v60_yield_typed_derivation_nonempty
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma) (binary : V60BinaryRules N)
    {X : V60TypedNT N Obs} {w : Word Sigma}
    (d : V60YieldTypedDerives Obs terminal binary X w) :
    w ≠ [] := by
  exact v60_untyped_derivation_nonempty terminal binary
    (v60_yield_typed_derivation_erases Obs terminal binary d)

/-- Language of the underlying SSBNF presentation, including the isolated epsilon start rule. -/
def V60UntypedStartLanguage
    {N : Type v} {Sigma : Type u}
    (terminal : V60TerminalRules N Sigma) (binary : V60BinaryRules N)
    (start : V60StartRules N) (epsilonStart : Prop) : Language Sigma :=
  fun w =>
    (w = [] ∧ epsilonStart) ∨
      ∃ A : N, start A ∧ V60UntypedDerives terminal binary A w

/-- Language of the full, before-trimming, yield-only refinement. -/
def V60FullTypedStartLanguage
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma) (binary : V60BinaryRules N)
    (start : V60StartRules N) (epsilonStart : Prop) : Language Sigma :=
  fun w =>
    (w = [] ∧ epsilonStart) ∨
      ∃ (A : N) (p : Obs.M),
        start A ∧
          V60YieldTypedDerives Obs terminal binary
            { label := A, yieldType := p } w

/-- Proposition `typed-core`, language part, before trim: full typing preserves the language exactly. -/
theorem v60_full_typed_language_iff_untyped
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma) (binary : V60BinaryRules N)
    (start : V60StartRules N) (epsilonStart : Prop)
    (w : Word Sigma) :
    V60FullTypedStartLanguage Obs terminal binary start epsilonStart w ↔
      V60UntypedStartLanguage terminal binary start epsilonStart w := by
  constructor
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨A, p, hStart, hDeriv⟩
      exact Or.inr ⟨A, hStart,
        v60_yield_typed_derivation_erases Obs terminal binary hDeriv⟩
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨A, hStart, hDeriv⟩
      exact Or.inr ⟨A, Obs.value w, hStart,
        v60_untyped_derivation_lifts Obs terminal binary hDeriv⟩

end FixedHCFG
end LeanCfgProject
