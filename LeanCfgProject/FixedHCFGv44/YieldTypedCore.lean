import LeanCfgProject.FixedHCFGv44.Observer

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-- A non-start typed copy `A_mu` in the v44 yield-only refinement. -/
structure TypedNT (N : Type v) {Sigma : Type u} (Obs : Observer Sigma) where
  label : N
  yieldType : Obs.M

/-- Untyped terminal productions `A -> a`. -/
abbrev TerminalRules (N : Type v) (Sigma : Type u) := N → Sigma → Prop

/-- Untyped binary productions `A -> B C`. -/
abbrev BinaryRules (N : Type v) := N → N → N → Prop

/-- Start productions `S0 -> A`; the optional epsilon rule is separate. -/
abbrev StartRules (N : Type v) := N → Prop

/-- Ordinary terminal derivations in the non-start part of an SSBNF grammar. -/
inductive UntypedDerives {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N) :
    N → Word Sigma → Prop
  | terminal {A : N} {a : Sigma}
      (hrule : terminal A a) :
      UntypedDerives terminal binary A [a]
  | binary {A B C : N} {x y : Word Sigma}
      (hrule : binary A B C)
      (left : UntypedDerives terminal binary B x)
      (right : UntypedDerives terminal binary C y) :
      UntypedDerives terminal binary A (x ++ y)

/--
Terminal derivations in the full v44 yield-only refinement.

The binary constructor is exactly `A_{mu*nu} -> B_mu C_nu`; unlike the
pre-revision formalization, no left/right outer-context types occur here.
-/
inductive TypedDerives {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N) :
    TypedNT N Obs → Word Sigma → Prop
  | terminal {A : N} {a : Sigma}
      (hrule : terminal A a) :
      TypedDerives Obs terminal binary
        { label := A, yieldType := obsValue Obs [a] } [a]
  | binary {A B C : N} {mu nu : Obs.M} {x y : Word Sigma}
      (hrule : binary A B C)
      (left : TypedDerives Obs terminal binary
        { label := B, yieldType := mu } x)
      (right : TypedDerives Obs terminal binary
        { label := C, yieldType := nu } y) :
      TypedDerives Obs terminal binary
        { label := A, yieldType := Obs.mul mu nu } (x ++ y)

/-- Every untyped non-start derivation lifts to its unique yield type. -/
theorem full_yield_typed_lift
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    {A : N} {w : Word Sigma}
    (d : UntypedDerives terminal binary A w) :
    TypedDerives Obs terminal binary
      { label := A, yieldType := obsValue Obs w } w := by
  induction d with
  | terminal hrule =>
      exact TypedDerives.terminal hrule
  | @binary A B C x y hrule left right ihLeft ihRight =>
      have h := TypedDerives.binary (Obs := Obs)
        (terminal := terminal) (binary := binary)
        hrule ihLeft ihRight
      simpa only [obsValue_append] using h

/-- Erasing the yield index gives an ordinary derivation. -/
theorem erase_typed_derivation
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    {X : TypedNT N Obs} {w : Word Sigma}
    (d : TypedDerives Obs terminal binary X w) :
    UntypedDerives terminal binary X.label w := by
  induction d with
  | terminal hrule =>
      exact UntypedDerives.terminal hrule
  | binary hrule left right ihLeft ihRight =>
      exact UntypedDerives.binary hrule ihLeft ihRight

/-- v44 Proposition 4.1 yield invariant for the full refinement. -/
theorem typed_yield_invariant
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    {X : TypedNT N Obs} {w : Word Sigma}
    (d : TypedDerives Obs terminal binary X w) :
    obsValue Obs w = X.yieldType := by
  induction d with
  | terminal hrule =>
      rfl
  | binary hrule left right ihLeft ihRight =>
      calc
        obsValue Obs (_ ++ _) = Obs.mul (obsValue Obs _) (obsValue Obs _) :=
          obsValue_append Obs _ _
        _ = Obs.mul _ _ := by rw [ihLeft, ihRight]

/-- Start derivations of the original SSBNF grammar. -/
inductive UntypedStartDerives {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) : Word Sigma → Prop
  | epsilon (h : epsilonStart) :
      UntypedStartDerives terminal binary start epsilonStart []
  | nonempty {A : N} {w : Word Sigma}
      (hrule : start A)
      (hder : UntypedDerives terminal binary A w) :
      UntypedStartDerives terminal binary start epsilonStart w

/-- Start derivations of the full yield-typed refinement. -/
inductive TypedStartDerives {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) : Word Sigma → Prop
  | epsilon (h : epsilonStart) :
      TypedStartDerives Obs terminal binary start epsilonStart []
  | nonempty {A : N} {mu : Obs.M} {w : Word Sigma}
      (hrule : start A)
      (hder : TypedDerives Obs terminal binary
        { label := A, yieldType := mu } w) :
      TypedStartDerives Obs terminal binary start epsilonStart w

/-- Every original successful start derivation lifts to the full refinement. -/
theorem lift_start_derivation
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    {w : Word Sigma}
    (d : UntypedStartDerives terminal binary start epsilonStart w) :
    TypedStartDerives Obs terminal binary start epsilonStart w := by
  cases d with
  | epsilon h =>
      exact TypedStartDerives.epsilon h
  | @nonempty A w hrule hder =>
      exact TypedStartDerives.nonempty hrule
        (full_yield_typed_lift Obs terminal binary hder)

/-- Every full-refinement start derivation erases to an original derivation. -/
theorem erase_start_derivation
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    {w : Word Sigma}
    (d : TypedStartDerives Obs terminal binary start epsilonStart w) :
    UntypedStartDerives terminal binary start epsilonStart w := by
  cases d with
  | epsilon h =>
      exact UntypedStartDerives.epsilon h
  | @nonempty A mu w hrule hder =>
      exact UntypedStartDerives.nonempty hrule
        (erase_typed_derivation Obs terminal binary hder)

/-- Language equivalence between an SSBNF grammar and its full yield refinement. -/
theorem full_refinement_language_iff
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (w : Word Sigma) :
    TypedStartDerives Obs terminal binary start epsilonStart w ↔
      UntypedStartDerives terminal binary start epsilonStart w := by
  constructor
  · exact erase_start_derivation Obs terminal binary start epsilonStart
  · exact lift_start_derivation Obs terminal binary start epsilonStart

end FixedHCFGv44
end LeanCfgProject
