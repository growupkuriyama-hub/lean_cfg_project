import LeanCfgProject.FixedHCFG.TypedRefinement

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-- Productivity of a typed state in the full refinement. -/
def TypedProductive {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (X : TypedNT N Obs) : Prop :=
  ∃ w : Word Sigma, TypedDerives Obs terminal binary X w

/-- Reachability of a typed state from the typed start interface. -/
def TypedReachable {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    (X : TypedNT N Obs) : Prop :=
  ∃ u v : Word Sigma, TypedOccurs Obs terminal binary start X u v

/-- The state predicate retained by ordinary reachable/productive trimming. -/
def TypedKept {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    (X : TypedNT N Obs) : Prop :=
  TypedProductive Obs terminal binary X ∧
    TypedReachable Obs terminal binary start X

/--
Derivations in the trimmed typed refinement.  A rule instance is retained only
when its participating typed states are retained; recursively, every state in
the derivation tree is therefore reachable and productive.
-/
inductive KeptDerives {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) :
    TypedNT N Obs → Word Sigma → Prop
  | terminal {A : N} {a : Sigma} {p m n : Obs.M}
      (hrule : terminal A a)
      (htype : Obs.value [a] = p)
      (hkeep : TypedKept Obs terminal binary start
        { label := A, yieldType := p, leftType := m, rightType := n }) :
      KeptDerives Obs terminal binary start
        { label := A, yieldType := p, leftType := m, rightType := n } [a]
  | binary {A B C : N} {p m n q r : Obs.M} {x y : Word Sigma}
      (hrule : binary A B C)
      (hproduct : Obs.mul q r = p)
      (hkeep : TypedKept Obs terminal binary start
        { label := A, yieldType := p, leftType := m, rightType := n })
      (left : KeptDerives Obs terminal binary start
        { label := B,
          yieldType := q,
          leftType := m,
          rightType := Obs.mul r n } x)
      (right : KeptDerives Obs terminal binary start
        { label := C,
          yieldType := r,
          leftType := Obs.mul m q,
          rightType := n } y) :
      KeptDerives Obs terminal binary start
        { label := A, yieldType := p, leftType := m, rightType := n } (x ++ y)

/-- Forgetting annotations in a full typed derivation gives an untyped derivation. -/
theorem typed_derivation_erases
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    {X : TypedNT N Obs} {w : Word Sigma}
    (d : TypedDerives Obs terminal binary X w) :
    UntypedDerives terminal binary X.label w := by
  induction d with
  | terminal hrule htype =>
      exact UntypedDerives.terminal hrule
  | binary hrule hproduct left right ihLeft ihRight =>
      exact UntypedDerives.binary hrule ihLeft ihRight

/-- A trimmed derivation is, in particular, a full typed derivation. -/
theorem kept_derivation_to_full
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    {X : TypedNT N Obs} {w : Word Sigma}
    (d : KeptDerives Obs terminal binary start X w) :
    TypedDerives Obs terminal binary X w := by
  induction d with
  | terminal hrule htype hkeep =>
      exact TypedDerives.terminal hrule htype
  | binary hrule hproduct hkeep left right ihLeft ihRight =>
      exact TypedDerives.binary hrule hproduct ihLeft ihRight

/-- Forgetting annotations in a trimmed typed derivation gives an untyped derivation. -/
theorem kept_derivation_erases
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    {X : TypedNT N Obs} {w : Word Sigma}
    (d : KeptDerives Obs terminal binary start X w) :
    UntypedDerives terminal binary X.label w := by
  exact typed_derivation_erases Obs terminal binary
    (kept_derivation_to_full Obs terminal binary start d)

/--
Every typed derivation that occurs inside a successful start derivation survives
reachable/productive trimming.  This is the local survival fact used in the
reverse inclusion of Lemma 4.5(iii).
-/
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
  | @terminal A a p m n hrule htype =>
      have hkeep : TypedKept Obs terminal binary start
          { label := A, yieldType := p, leftType := m, rightType := n } := by
        constructor
        · exact ⟨[a], TypedDerives.terminal hrule htype⟩
        · exact ⟨u, v, hocc⟩
      exact KeptDerives.terminal hrule htype hkeep
  | @binary A B C p m n q r x y hrule hproduct left right ihLeft ihRight =>
      have hoccLeft : TypedOccurs Obs terminal binary start
          { label := B,
            yieldType := q,
            leftType := m,
            rightType := Obs.mul r n } u (y ++ v) :=
        TypedOccurs.left hocc hrule hproduct right
      have hoccRight : TypedOccurs Obs terminal binary start
          { label := C,
            yieldType := r,
            leftType := Obs.mul m q,
            rightType := n } (u ++ x) v :=
        TypedOccurs.right hocc hrule hproduct left
      have hleft := ihLeft hoccLeft
      have hright := ihRight hoccRight
      have hkeep : TypedKept Obs terminal binary start
          { label := A, yieldType := p, leftType := m, rightType := n } := by
        constructor
        · exact ⟨x ++ y, TypedDerives.binary hrule hproduct left right⟩
        · exact ⟨u, v, hocc⟩
      exact KeptDerives.binary hrule hproduct hkeep hleft hright

/-- Untyped start language of the SSBNF presentation. -/
def UntypedStartLanguage {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) : Language Sigma :=
  fun w =>
    (w = [] ∧ epsilonStart) ∨
      ∃ A : N, start A ∧ UntypedDerives terminal binary A w

/-- Start language of the reachable/productive trimmed typed refinement. -/
def TrimmedTypedStartLanguage {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) : Language Sigma :=
  fun w =>
    (w = [] ∧ epsilonStart) ∨
      ∃ (A : N) (p : Obs.M),
        start A ∧
          KeptDerives Obs terminal binary start
            { label := A,
              yieldType := p,
              leftType := Obs.one,
              rightType := Obs.one } w

/--
Lemma 4.5(iii): reachable/productive trimming of the full typed refinement
preserves exactly the language of the original start-separated grammar.
-/
theorem lemma_4_5_iii_trimmed_language
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
    · rcases hNonempty with ⟨A, p, hStart, hDeriv⟩
      exact Or.inr ⟨A, hStart,
        kept_derivation_erases Obs terminal binary start hDeriv⟩
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨A, hStart, hDeriv⟩
      let p : Obs.M := Obs.value w
      have hTyped : TypedDerives Obs terminal binary
          { label := A,
            yieldType := p,
            leftType := Obs.one,
            rightType := Obs.one } w := by
        simpa [p] using
          (lemma_4_4_full_typing Obs terminal binary hDeriv Obs.one Obs.one)
      have hOcc : TypedOccurs Obs terminal binary start
          { label := A,
            yieldType := p,
            leftType := Obs.one,
            rightType := Obs.one } [] [] :=
        TypedOccurs.start (p := p) hStart
      have hKept := successful_derivation_survives
        Obs terminal binary start hOcc hTyped
      exact Or.inr ⟨A, p, hStart, hKept⟩

end FixedHCFG
end LeanCfgProject
