import LeanCfgProject.FixedHCFG.LinearShortlex

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
The actual fixed-h typed linear refinement used in Section 7.

Unlike the generic spine files, this file remembers the source SSLNF
production index and the monoid equations.  It is the bridge from the paper's
reduced SSLNF presentation to the strict-linear grammar on which Lemmas
7.3--7.6 were verified.
-/

/-- The three non-start right-hand-side shapes of SSLNF. -/
inductive LinearRHS (N : Type v) (Sigma : Type u) where
  | terminal (a : Sigma)
  | left (a : Sigma) (child : N)
  | right (child : N) (a : Sigma)

/--
An indexed SSLNF presentation.  `P` is the finite type of non-start
productions; keeping it explicit makes the Proposition-7.7 rule count exact.
-/
structure IndexedSSLNF (N : Type v) (Sigma : Type u) (P : Type w) where
  lhs : P → N
  rhs : P → LinearRHS N Sigma
  startState : N → Prop
  hasEpsilon : Prop

/-- The full fixed-h typed linear refinement before reachable/productive trimming. -/
def fullTypedLinearGrammar
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :
    StrictLinearGrammar (TypedNT N Obs) Sigma where
  leftRule := fun X a Y =>
    (∃ r : P, G.lhs r = X.label ∧ G.rhs r = LinearRHS.left a Y.label) ∧
      X.yieldType = Obs.mul (Obs.value [a]) Y.yieldType ∧
      Y.leftType = Obs.mul X.leftType (Obs.value [a]) ∧
      Y.rightType = X.rightType
  rightRule := fun X Y a =>
    (∃ r : P, G.lhs r = X.label ∧ G.rhs r = LinearRHS.right Y.label a) ∧
      X.yieldType = Obs.mul Y.yieldType (Obs.value [a]) ∧
      Y.leftType = X.leftType ∧
      Y.rightType = Obs.mul (Obs.value [a]) X.rightType
  terminalRule := fun X a =>
    (∃ r : P, G.lhs r = X.label ∧ G.rhs r = LinearRHS.terminal a) ∧
      Obs.value [a] = X.yieldType
  startState := fun X =>
    G.startState X.label ∧ X.leftType = Obs.one ∧ X.rightType = Obs.one
  hasEpsilon := G.hasEpsilon

/-- Yield typing is preserved by every derivation in the full linear refinement. -/
theorem linearTyped_yield_type
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    {X : TypedNT N Obs} {sp : List (TypedNT N Obs)} {z : Word Sigma}
    (d : LinearDerivesSpine (fullTypedLinearGrammar Obs G) X sp z) :
    Obs.value z = X.yieldType := by
  induction d with
  | @terminal X a hrule =>
      exact hrule.2
  | @left X Y a sp z hrule child ih =>
      have hEq := hrule.2.1
      calc
        Obs.value (a :: z) = Obs.value ([a] ++ z) := by rfl
        _ = Obs.mul (Obs.value [a]) (Obs.value z) := Obs.value_append [a] z
        _ = Obs.mul (Obs.value [a]) Y.yieldType := by rw [ih]
        _ = X.yieldType := hEq.symm
  | @right X Y a sp z hrule child ih =>
      have hEq := hrule.2.1
      calc
        Obs.value (z ++ [a]) = Obs.mul (Obs.value z) (Obs.value [a]) :=
          Obs.value_append z [a]
        _ = Obs.mul Y.yieldType (Obs.value [a]) := by rw [ih]
        _ = X.yieldType := hEq.symm

/-- Ordinary derivability version of the linear yield-type invariant. -/
theorem linearTyped_yield_type_of_derives
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    {X : TypedNT N Obs} {z : Word Sigma}
    (d : LinearDerives (fullTypedLinearGrammar Obs G) X z) :
    Obs.value z = X.yieldType := by
  rcases d with ⟨sp, hd⟩
  exact linearTyped_yield_type Obs G hd

/-- The two outer h-types are preserved along every typed linear occurrence spine. -/
theorem linearTyped_context_type
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    {X : TypedNT N Obs} {sp : List (TypedNT N Obs)} {l r : Word Sigma}
    (d : LinearOccursSpine (fullTypedLinearGrammar Obs G) X sp l r) :
    Obs.value l = X.leftType ∧ Obs.value r = X.rightType := by
  induction d with
  | @start X hstart =>
      exact ⟨by simpa [hstart.2.1] using Obs.value_nil,
        by simpa [hstart.2.2] using Obs.value_nil⟩
  | @left X Y a sp l r parent hrule ih =>
      constructor
      · calc
          Obs.value (l ++ [a]) = Obs.mul (Obs.value l) (Obs.value [a]) :=
            Obs.value_append l [a]
          _ = Obs.mul X.leftType (Obs.value [a]) := by rw [ih.1]
          _ = Y.leftType := hrule.2.2.1.symm
      · calc
          Obs.value r = X.rightType := ih.2
          _ = Y.rightType := hrule.2.2.2.symm
  | @right X Y a sp l r parent hrule ih =>
      constructor
      · calc
          Obs.value l = X.leftType := ih.1
          _ = Y.leftType := hrule.2.2.1.symm
      · calc
          Obs.value ([a] ++ r) = Obs.mul (Obs.value [a]) (Obs.value r) :=
            Obs.value_append [a] r
          _ = Obs.mul (Obs.value [a]) X.rightType := by rw [ih.2]
          _ = Y.rightType := hrule.2.2.2.symm

/-- Ordinary occurrence version of the two-sided context invariant. -/
theorem linearTyped_context_type_of_occurs
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    {X : TypedNT N Obs} {l r : Word Sigma}
    (d : LinearOccurs (fullTypedLinearGrammar Obs G) X l r) :
    Obs.value l = X.leftType ∧ Obs.value r = X.rightType := by
  rcases d with ⟨sp, hd⟩
  exact linearTyped_context_type Obs G hd

/-- A typed state is retained exactly when it is both productive and reachable. -/
def LinearTypedKept
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (X : TypedNT N Obs) : Prop :=
  (∃ z : Word Sigma, LinearDerives (fullTypedLinearGrammar Obs G) X z) ∧
    (∃ l r : Word Sigma, LinearOccurs (fullTypedLinearGrammar Obs G) X l r)

/-- Retained typed state family `W` of Section 7. -/
abbrev LinearKeptState
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :=
  {X : TypedNT N Obs // LinearTypedKept Obs G X}

/-- Explicit encoding of a typed nonterminal by its untyped label and three monoid coordinates. -/
def encodeTypedNT
    {N : Type v} {Sigma : Type u} (Obs : Observer Sigma) :
    TypedNT N Obs → N × Obs.M × Obs.M × Obs.M :=
  fun X => (X.label, X.yieldType, X.leftType, X.rightType)

/-- The coordinate encoding is injective. -/
theorem encodeTypedNT_injective
    {N : Type v} {Sigma : Type u} (Obs : Observer Sigma) :
    Function.Injective (encodeTypedNT (N := N) Obs) := by
  intro X Y h
  cases X with
  | mk xl xp xm xn =>
      cases Y with
      | mk yl yp ym yn =>
          simp only [encodeTypedNT, Prod.mk.injEq] at h
          rcases h with ⟨hl, hp, hm, hn⟩
          subst yl
          subst yp
          subst ym
          subst yn
          rfl

/-- Proposition 7.7(i), with the manuscript's constant made explicit. -/
theorem proposition_7_7_i_state_bound
    {N : Type v} {Sigma : Type u} {P : Type w}
    [Fintype N]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    [Fintype (LinearKeptState Obs G)] :
    Fintype.card (LinearKeptState Obs G) ≤
      Fintype.card N * Fintype.card Obs.M ^ 3 := by
  apply linear_typed_state_card_le
    (fun X : LinearKeptState Obs G => encodeTypedNT Obs X.1)
  intro X Y h
  apply Subtype.ext
  exact encodeTypedNT_injective Obs h

/--
A uniform `P × M^3` slot family for typed linear rules.  For `A -> aB` and
`A -> Ba`, the three monoid coordinates are `(q,m,n)` and the parent yield
coordinate `p` is *determined* as `h(a)q` or `qh(a)`.  For a terminal rule the
first slot can be fixed to `1`, so this is still a valid common envelope.
-/
abbrev LinearTypedRuleSlot
    {Sigma : Type u} (Obs : Observer Sigma) (P : Type w) :=
  P × Obs.M × Obs.M × Obs.M

/-- The rule-slot family has exactly the `|P||M|^3` size used in Proposition 7.7(ii). -/
theorem linearTypedRuleSlot_card
    {Sigma : Type u} {P : Type w} [Fintype P]
    (Obs : Observer Sigma) :
    Fintype.card (LinearTypedRuleSlot Obs P) =
      Fintype.card P * Fintype.card Obs.M ^ 3 := by
  simp [LinearTypedRuleSlot, pow_three, mul_assoc]

end FixedHCFG
end LeanCfgProject
