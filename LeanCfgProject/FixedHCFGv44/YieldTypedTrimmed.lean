import LeanCfgProject.FixedHCFGv44.YieldTypedCore

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-- A typed state occurs in a successful full-refinement start tree with terminal context `(u,v)`. -/
inductive TypedOccurs {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma)
    (binary : BinaryRules N) (start : StartRules N) :
    TypedNT N Obs → Word Sigma → Word Sigma → Prop
  | start {A : N} {mu : Obs.M}
      (hrule : start A) :
      TypedOccurs Obs terminal binary start
        { label := A, yieldType := mu } [] []
  | left {A B C : N} {mu nu : Obs.M}
      {u v y : Word Sigma}
      (parent : TypedOccurs Obs terminal binary start
        { label := A, yieldType := Obs.mul mu nu } u v)
      (hrule : binary A B C)
      (rightDeriv : TypedDerives Obs terminal binary
        { label := C, yieldType := nu } y) :
      TypedOccurs Obs terminal binary start
        { label := B, yieldType := mu } u (y ++ v)
  | right {A B C : N} {mu nu : Obs.M}
      {u v x : Word Sigma}
      (parent : TypedOccurs Obs terminal binary start
        { label := A, yieldType := Obs.mul mu nu } u v)
      (hrule : binary A B C)
      (leftDeriv : TypedDerives Obs terminal binary
        { label := B, yieldType := mu } x) :
      TypedOccurs Obs terminal binary start
        { label := C, yieldType := nu } (u ++ x) v

/-- Productivity in the full yield-typed refinement. -/
def TypedProductive {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (X : TypedNT N Obs) : Prop :=
  ∃ w : Word Sigma, TypedDerives Obs terminal binary X w

/-- Reachability from the typed start interface. -/
def TypedReachable {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    (X : TypedNT N Obs) : Prop :=
  ∃ u v : Word Sigma, TypedOccurs Obs terminal binary start X u v

/-- The states retained by ordinary reachable/productive reduction. -/
def TypedKept {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    (X : TypedNT N Obs) : Prop :=
  TypedProductive Obs terminal binary X ∧
    TypedReachable Obs terminal binary start X

/-- Derivations whose participating typed states survive reduction. -/
inductive KeptDerives {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) :
    TypedNT N Obs → Word Sigma → Prop
  | terminal {A : N} {a : Sigma}
      (hrule : terminal A a)
      (hkeep : TypedKept Obs terminal binary start
        { label := A, yieldType := obsValue Obs [a] }) :
      KeptDerives Obs terminal binary start
        { label := A, yieldType := obsValue Obs [a] } [a]
  | binary {A B C : N} {mu nu : Obs.M} {x y : Word Sigma}
      (hrule : binary A B C)
      (hkeep : TypedKept Obs terminal binary start
        { label := A, yieldType := Obs.mul mu nu })
      (left : KeptDerives Obs terminal binary start
        { label := B, yieldType := mu } x)
      (right : KeptDerives Obs terminal binary start
        { label := C, yieldType := nu } y) :
      KeptDerives Obs terminal binary start
        { label := A, yieldType := Obs.mul mu nu } (x ++ y)

/-- A reduced derivation is also a derivation of the full refinement. -/
theorem kept_to_full
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    {X : TypedNT N Obs} {w : Word Sigma}
    (d : KeptDerives Obs terminal binary start X w) :
    TypedDerives Obs terminal binary X w := by
  induction d with
  | terminal hrule hkeep =>
      exact TypedDerives.terminal hrule
  | binary hrule hkeep left right ihLeft ihRight =>
      exact TypedDerives.binary hrule ihLeft ihRight

/-- Every successful full-refinement subtree survives reachable/productive reduction. -/
theorem successful_derivation_survives
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    {X : TypedNT N Obs} {u v w : Word Sigma}
    (hocc : TypedOccurs Obs terminal binary start X u v)
    (d : TypedDerives Obs terminal binary X w) :
    KeptDerives Obs terminal binary start X w := by
  induction d generalizing u v with
  | @terminal A a hrule =>
      have hkeep : TypedKept Obs terminal binary start
          { label := A, yieldType := obsValue Obs [a] } := by
        constructor
        · exact ⟨[a], TypedDerives.terminal hrule⟩
        · exact ⟨u, v, hocc⟩
      exact KeptDerives.terminal hrule hkeep
  | @binary A B C mu nu x y hrule left right ihLeft ihRight =>
      have hoccLeft : TypedOccurs Obs terminal binary start
          { label := B, yieldType := mu } u (y ++ v) :=
        TypedOccurs.left hocc hrule right
      have hoccRight : TypedOccurs Obs terminal binary start
          { label := C, yieldType := nu } (u ++ x) v :=
        TypedOccurs.right hocc hrule left
      have hleft := ihLeft hoccLeft
      have hright := ihRight hoccRight
      have hkeep : TypedKept Obs terminal binary start
          { label := A, yieldType := Obs.mul mu nu } := by
        constructor
        · exact ⟨x ++ y, TypedDerives.binary hrule left right⟩
        · exact ⟨u, v, hocc⟩
      exact KeptDerives.binary hrule hkeep hleft hright

/-- Start language of the reduced yield-typed refinement. -/
def TrimmedTypedStartLanguage {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) : Language Sigma :=
  fun w =>
    (w = [] ∧ epsilonStart) ∨
      ∃ (A : N) (mu : Obs.M),
        start A ∧
          KeptDerives Obs terminal binary start
            { label := A, yieldType := mu } w

/-- Start language of the original SSBNF presentation. -/
def UntypedStartLanguage {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) : Language Sigma :=
  fun w =>
    (w = [] ∧ epsilonStart) ∨
      ∃ A : N, start A ∧ UntypedDerives terminal binary A w

/--
v44 Proposition 4.1, language part: reducing the full yield-only refinement
preserves exactly the language of the original SSBNF grammar.
-/
theorem typed_refinement_language_iff
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (w : Word Sigma) :
    TrimmedTypedStartLanguage Obs terminal binary start epsilonStart w ↔
      UntypedStartLanguage terminal binary start epsilonStart w := by
  constructor
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨A, mu, hStart, hDeriv⟩
      exact Or.inr ⟨A, hStart,
        erase_typed_derivation Obs terminal binary
          (kept_to_full Obs terminal binary start hDeriv)⟩
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨A, hStart, hDeriv⟩
      let mu : Obs.M := obsValue Obs w
      have hTyped : TypedDerives Obs terminal binary
          { label := A, yieldType := mu } w := by
        simpa [mu] using full_yield_typed_lift Obs terminal binary hDeriv
      have hOcc : TypedOccurs Obs terminal binary start
          { label := A, yieldType := mu } [] [] :=
        TypedOccurs.start (mu := mu) hStart
      have hKept := successful_derivation_survives
        Obs terminal binary start hOcc hTyped
      exact Or.inr ⟨A, mu, hStart, hKept⟩

/-- The yield invariant also holds in the reduced typed grammar. -/
theorem kept_yield_invariant
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    {X : TypedNT N Obs} {w : Word Sigma}
    (d : KeptDerives Obs terminal binary start X w) :
    obsValue Obs w = X.yieldType := by
  exact typed_yield_invariant Obs terminal binary
    (kept_to_full Obs terminal binary start d)

end FixedHCFGv44
end LeanCfgProject
