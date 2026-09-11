import LeanCfgProject.FixedHCFG.LinearDerivation

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Reachable/productive trimming for strict-linear grammars.

Because a strict-linear derivation has only one nonterminal child, every state
on a successful derivation below a reachable state is again reachable and
productive.  Dually, every state on a successful occurrence spine above a
productive target is again productive.  This makes the linear trimming bridge
considerably simpler than the branching CFG case.
-/

/-- A strict-linear state survives trimming iff it is productive and reachable. -/
def StrictLinearKept
    {W : Type v} {Sigma : Type u}
    (G : StrictLinearGrammar W Sigma) (X : W) : Prop :=
  (∃ z : Word Sigma, LinearDerives G X z) ∧
    (∃ l r : Word Sigma, LinearOccurs G X l r)

/-- Retained state type of a reduced strict-linear grammar. -/
abbrev StrictLinearKeptState
    {W : Type v} {Sigma : Type u}
    (G : StrictLinearGrammar W Sigma) :=
  {X : W // StrictLinearKept G X}

/-- Restrict all non-start rules and start states to retained states. -/
def trimStrictLinearGrammar
    {W : Type v} {Sigma : Type u}
    (G : StrictLinearGrammar W Sigma) :
    StrictLinearGrammar (StrictLinearKeptState G) Sigma where
  leftRule := fun X a Y => G.leftRule X.1 a Y.1
  rightRule := fun X Y a => G.rightRule X.1 Y.1 a
  terminalRule := fun X a => G.terminalRule X.1 a
  startState := fun X => G.startState X.1
  hasEpsilon := G.hasEpsilon

/--
A successful derivation below a reachable state lifts wholly into the trimmed
grammar.  Reachability of the unique child is obtained by one occurrence step.
-/
theorem lift_linear_derivation_to_trim
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma}
    {X : W} {sp : List W} {z : Word Sigma}
    (d : LinearDerivesSpine G X sp z)
    (hReach : ∃ l r : Word Sigma, LinearOccurs G X l r) :
    LinearDerives (trimStrictLinearGrammar G)
      (⟨X, ⟨⟨z, ⟨sp, d⟩⟩, hReach⟩⟩ : StrictLinearKeptState G) z := by
  induction d with
  | @terminal X a hrule =>
      exact ⟨[_], LinearDerivesSpine.terminal hrule⟩
  | @left X Y a sp z hrule child ih =>
      rcases hReach with ⟨l, r, osp, hocc⟩
      have hReachY : ∃ l' r' : Word Sigma, LinearOccurs G Y l' r' := by
        exact ⟨l ++ [a], r, osp.concat Y,
          LinearOccursSpine.left hocc hrule⟩
      have hChild := ih hReachY
      rcases hChild with ⟨spK, dK⟩
      exact ⟨_ :: spK, LinearDerivesSpine.left hrule dK⟩
  | @right X Y a sp z hrule child ih =>
      rcases hReach with ⟨l, r, osp, hocc⟩
      have hReachY : ∃ l' r' : Word Sigma, LinearOccurs G Y l' r' := by
        exact ⟨l, [a] ++ r, osp.concat Y,
          LinearOccursSpine.right hocc hrule⟩
      have hChild := ih hReachY
      rcases hChild with ⟨spK, dK⟩
      exact ⟨_ :: spK, LinearDerivesSpine.right hrule dK⟩

/--
A successful occurrence spine to a productive target lifts wholly into the
trimmed grammar.  Productivity is propagated upward by wrapping the child's
terminal derivation with the unique linear rule.
-/
theorem lift_linear_occurrence_to_trim
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma}
    {X : W} {sp : List W} {l r : Word Sigma}
    (d : LinearOccursSpine G X sp l r)
    (hProd : ∃ z : Word Sigma, LinearDerives G X z) :
    LinearOccurs (trimStrictLinearGrammar G)
      (⟨X, ⟨hProd, ⟨l, r, ⟨sp, d⟩⟩⟩⟩ : StrictLinearKeptState G) l r := by
  induction d with
  | @start X hstart =>
      exact ⟨[_], LinearOccursSpine.start hstart⟩
  | @left X Y a sp l r parent hrule ih =>
      rcases hProd with ⟨z, dsp, dY⟩
      have hProdX : ∃ z' : Word Sigma, LinearDerives G X z' := by
        exact ⟨a :: z, X :: dsp,
          LinearDerivesSpine.left hrule dY⟩
      have hParent := ih hProdX
      rcases hParent with ⟨ospK, hoccK⟩
      exact ⟨ospK.concat _, LinearOccursSpine.left hoccK hrule⟩
  | @right X Y a sp l r parent hrule ih =>
      rcases hProd with ⟨z, dsp, dY⟩
      have hProdX : ∃ z' : Word Sigma, LinearDerives G X z' := by
        exact ⟨z ++ [a], X :: dsp,
          LinearDerivesSpine.right hrule dY⟩
      have hParent := ih hProdX
      rcases hParent with ⟨ospK, hoccK⟩
      exact ⟨ospK.concat _, LinearOccursSpine.right hoccK hrule⟩

/-- Every retained state remains productive after restriction to retained states. -/
theorem trim_kept_productive
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma}
    (X : StrictLinearKeptState G) :
    ∃ z : Word Sigma, LinearDerives (trimStrictLinearGrammar G) X z := by
  rcases X.property.1 with ⟨z, sp, d⟩
  refine ⟨z, ?_⟩
  simpa using lift_linear_derivation_to_trim d X.property.2

/-- Every retained state remains reachable after restriction to retained states. -/
theorem trim_kept_reachable
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma}
    (X : StrictLinearKeptState G) :
    ∃ l r : Word Sigma, LinearOccurs (trimStrictLinearGrammar G) X l r := by
  rcases X.property.2 with ⟨l, r, sp, d⟩
  refine ⟨l, r, ?_⟩
  simpa using lift_linear_occurrence_to_trim d X.property.1

/-- The restricted grammar is reduced in the theorem-facing sense. -/
theorem trimStrictLinearGrammar_reduced
    {W : Type v} {Sigma : Type u}
    {G : StrictLinearGrammar W Sigma} :
    ∀ X : StrictLinearKeptState G,
      (∃ z : Word Sigma, LinearDerives (trimStrictLinearGrammar G) X z) ∧
      (∃ l r : Word Sigma, LinearOccurs (trimStrictLinearGrammar G) X l r) := by
  intro X
  exact ⟨trim_kept_productive X, trim_kept_reachable X⟩

end FixedHCFG
end LeanCfgProject
