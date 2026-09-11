import LeanCfgProject.FixedHCFG.Observer

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-- A non-start typed copy `A_p^{m,n}` from Section 4 of the TCS manuscript. -/
structure TypedNT (N : Type v) {Sigma : Type u} (Obs : Observer Sigma) where
  label : N
  yieldType : Obs.M
  leftType : Obs.M
  rightType : Obs.M

/-- Untyped terminal productions `A → a`. -/
abbrev TerminalRules (N : Type v) (Sigma : Type u) := N → Sigma → Prop

/-- Untyped binary productions `A → BC`. -/
abbrev BinaryRules (N : Type v) := N → N → N → Prop

/-- Start productions `S₀ → A` (the epsilon start rule is handled separately). -/
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
Terminal derivations in the full two-sided typed refinement.

The binary constructor is exactly the paper rule
`A_p^{m,n} → B_q^{m,rn} C_r^{mq,n}` with `qr = p`.
Any trimmed typed refinement uses a subset of these rule instances, so the
invariants proved below apply to trimmed derivations as well.
-/
inductive TypedDerives {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N) :
    TypedNT N Obs → Word Sigma → Prop
  | terminal {A : N} {a : Sigma} {p m n : Obs.M}
      (hrule : terminal A a)
      (htype : Obs.value [a] = p) :
      TypedDerives Obs terminal binary
        { label := A, yieldType := p, leftType := m, rightType := n } [a]
  | binary {A B C : N} {p m n q r : Obs.M} {x y : Word Sigma}
      (hrule : binary A B C)
      (hproduct : Obs.mul q r = p)
      (left : TypedDerives Obs terminal binary
        { label := B,
          yieldType := q,
          leftType := m,
          rightType := Obs.mul r n } x)
      (right : TypedDerives Obs terminal binary
        { label := C,
          yieldType := r,
          leftType := Obs.mul m q,
          rightType := n } y) :
      TypedDerives Obs terminal binary
        { label := A, yieldType := p, leftType := m, rightType := n } (x ++ y)

/--
Lemma 4.4 (full typing derivability): every untyped nonempty derivation lifts
into every external frame, with yield component fixed by `h`.
-/
theorem lemma_4_4_full_typing
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    {A : N} {w : Word Sigma}
    (d : UntypedDerives terminal binary A w) :
    ∀ m n : Obs.M,
      TypedDerives Obs terminal binary
        { label := A,
          yieldType := Obs.value w,
          leftType := m,
          rightType := n } w := by
  induction d with
  | terminal hrule =>
      intro m n
      exact TypedDerives.terminal hrule rfl
  | @binary A B C x y hrule left right ihLeft ihRight =>
      intro m n
      exact TypedDerives.binary hrule
        (Obs.value_append x y).symm
        (ihLeft m (Obs.mul (Obs.value y) n))
        (ihRight (Obs.mul m (Obs.value x)) n)

/-- Lemma 4.5(i): a typed derivation has the yield type written on its root. -/
theorem lemma_4_5_i_yield_type
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    {X : TypedNT N Obs} {w : Word Sigma}
    (d : TypedDerives Obs terminal binary X w) :
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

/--
A typed nonterminal occurrence inside a successful start derivation.

The two descent rules follow one branch of a parse tree.  The sibling branch is
required to have a terminal derivation; its yield becomes part of the outer
terminal context of the selected child.
-/
inductive TypedOccurs {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma)
    (binary : BinaryRules N) (start : StartRules N) :
    TypedNT N Obs → Word Sigma → Word Sigma → Prop
  | start {A : N} {p : Obs.M}
      (hrule : start A) :
      TypedOccurs Obs terminal binary start
        { label := A,
          yieldType := p,
          leftType := Obs.one,
          rightType := Obs.one } [] []
  | left {A B C : N} {p m n q r : Obs.M}
      {u v y : Word Sigma}
      (parent : TypedOccurs Obs terminal binary start
        { label := A, yieldType := p, leftType := m, rightType := n } u v)
      (hrule : binary A B C)
      (hproduct : Obs.mul q r = p)
      (rightDeriv : TypedDerives Obs terminal binary
        { label := C,
          yieldType := r,
          leftType := Obs.mul m q,
          rightType := n } y) :
      TypedOccurs Obs terminal binary start
        { label := B,
          yieldType := q,
          leftType := m,
          rightType := Obs.mul r n } u (y ++ v)
  | right {A B C : N} {p m n q r : Obs.M}
      {u v x : Word Sigma}
      (parent : TypedOccurs Obs terminal binary start
        { label := A, yieldType := p, leftType := m, rightType := n } u v)
      (hrule : binary A B C)
      (hproduct : Obs.mul q r = p)
      (leftDeriv : TypedDerives Obs terminal binary
        { label := B,
          yieldType := q,
          leftType := m,
          rightType := Obs.mul r n } x) :
      TypedOccurs Obs terminal binary start
        { label := C,
          yieldType := r,
          leftType := Obs.mul m q,
          rightType := n } (u ++ x) v

/--
Lemma 4.5(ii): the terminal context around a reachable typed occurrence has
exactly the left and right `h`-types recorded on that occurrence.
-/
theorem lemma_4_5_ii_context_type
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma)
    (binary : BinaryRules N) (start : StartRules N)
    {X : TypedNT N Obs} {u v : Word Sigma}
    (hocc : TypedOccurs Obs terminal binary start X u v) :
    Obs.value u = X.leftType ∧ Obs.value v = X.rightType := by
  induction hocc with
  | start hrule =>
      constructor <;> exact Obs.value_nil
  | left parent hrule hproduct rightDeriv ih =>
      rcases ih with ⟨hu, hv⟩
      have hy := lemma_4_5_i_yield_type Obs terminal binary rightDeriv
      constructor
      · exact hu
      · calc
          Obs.value (_ ++ _) = Obs.mul (Obs.value _) (Obs.value _) :=
            Obs.value_append _ _
          _ = Obs.mul _ _ := by rw [hy, hv]
  | right parent hrule hproduct leftDeriv ih =>
      rcases ih with ⟨hu, hv⟩
      have hx := lemma_4_5_i_yield_type Obs terminal binary leftDeriv
      constructor
      · calc
          Obs.value (_ ++ _) = Obs.mul (Obs.value _) (Obs.value _) :=
            Obs.value_append _ _
          _ = Obs.mul _ _ := by rw [hu, hx]
      · exact hv

end FixedHCFG
end LeanCfgProject
