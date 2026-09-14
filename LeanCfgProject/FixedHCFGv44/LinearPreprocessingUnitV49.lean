import LeanCfgProject.FixedHCFGv44.LinearPreprocessingEpsilonV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Non-start unit-rule elimination for the source-side linear preprocessing in
Appendix A of TCS v49.

The input relation is the epsilon-eliminated grammar.  Unit closure is finite
reachability conceptually; this file proves the semantic part independently of
its later finite enumeration.  A surviving non-unit production of `B` is
copied to every `A` that reaches `B` by unit rules.  This is exactly the
standard construction described in Appendix A.
-/

/-- Unit edge `A -> B` in the epsilon-eliminated grammar. -/
def EpsilonElimUnitEdge
    {N : Type v} {Sigma : Type u}
    (rules : List (SourceLinearRule N Sigma)) (A B : N) : Prop :=
  EpsilonElimLinearRule rules
    (SourceLinearRule.context A [] B [])

/-- Reflexive/transitive unit closure. -/
inductive LinearUnitReach
    {N : Type v} {Sigma : Type u}
    (rules : List (SourceLinearRule N Sigma)) : N → N → Prop
  | refl (A : N) : LinearUnitReach rules A A
  | step {A B C : N}
      (edge : EpsilonElimUnitEdge rules A B)
      (tail : LinearUnitReach rules B C) :
      LinearUnitReach rules A C

/-- Unit reachability is transitive. -/
theorem linearUnitReach_trans
    {N : Type v} {Sigma : Type u}
    {rules : List (SourceLinearRule N Sigma)}
    {A B C : N}
    (hAB : LinearUnitReach rules A B)
    (hBC : LinearUnitReach rules B C) :
    LinearUnitReach rules A C := by
  induction hAB with
  | refl A => exact hBC
  | step edge tail ih =>
      exact LinearUnitReach.step edge (ih hBC)

/-- A single unit edge belongs to the unit closure. -/
theorem linearUnitReach_of_edge
    {N : Type v} {Sigma : Type u}
    {rules : List (SourceLinearRule N Sigma)}
    {A B : N}
    (h : EpsilonElimUnitEdge rules A B) :
    LinearUnitReach rules A B :=
  LinearUnitReach.step h (LinearUnitReach.refl B)

/-- Non-unit rules produced by unit-closure copying. -/
inductive UnitElimLinearRule
    {N : Type v} {Sigma : Type u}
    (rules : List (SourceLinearRule N Sigma)) :
    SourceLinearRule N Sigma → Prop
  | context
      {A B C : N} {u v : Word Sigma}
      (reach : LinearUnitReach rules A B)
      (hrule : EpsilonElimLinearRule rules
        (SourceLinearRule.context B u C v))
      (nonunit : u ≠ [] ∨ v ≠ []) :
      UnitElimLinearRule rules
        (SourceLinearRule.context A u C v)
  | terminal
      {A B : N} {w : Word Sigma}
      (reach : LinearUnitReach rules A B)
      (hrule : EpsilonElimLinearRule rules
        (SourceLinearRule.terminal B w)) :
      UnitElimLinearRule rules
        (SourceLinearRule.terminal A w)

/-- Recursive semantics of the unit-free linear grammar. -/
inductive UnitElimLinearDerives
    {N : Type v} {Sigma : Type u}
    (rules : List (SourceLinearRule N Sigma)) : N → Word Sigma → Prop
  | context
      {A B : N} {u v z : Word Sigma}
      (hrule : UnitElimLinearRule rules
        (SourceLinearRule.context A u B v))
      (center : UnitElimLinearDerives rules B z) :
      UnitElimLinearDerives rules A (u ++ z ++ v)
  | terminal
      {A : N} {w : Word Sigma}
      (hrule : UnitElimLinearRule rules
        (SourceLinearRule.terminal A w)) :
      UnitElimLinearDerives rules A w

/-- Unit-eliminated derivations can be relabelled backwards along unit closure. -/
theorem unitElimDerives_lift_reach
    {N : Type v} {Sigma : Type u}
    {rules : List (SourceLinearRule N Sigma)}
    {A B : N} {w : Word Sigma}
    (reach : LinearUnitReach rules A B)
    (d : UnitElimLinearDerives rules B w) :
    UnitElimLinearDerives rules A w := by
  cases d with
  | @context B C u v z hrule center =>
      cases hrule with
      | @context _ D _ _ _ reachBD hsrc hnonunit =>
          exact UnitElimLinearDerives.context
            (UnitElimLinearRule.context
              (linearUnitReach_trans reach reachBD) hsrc hnonunit)
            center
  | @terminal B w hrule =>
      cases hrule with
      | @terminal _ D _ reachBD hsrc =>
          exact UnitElimLinearDerives.terminal
            (UnitElimLinearRule.terminal
              (linearUnitReach_trans reach reachBD) hsrc)

/-- Epsilon-eliminated derivations can be expanded backwards along unit closure. -/
theorem epsilonElimDerives_lift_unitReach
    {N : Type v} {Sigma : Type u}
    {rules : List (SourceLinearRule N Sigma)}
    {A B : N} {w : Word Sigma}
    (reach : LinearUnitReach rules A B)
    (d : EpsilonElimLinearDerives rules B w) :
    EpsilonElimLinearDerives rules A w := by
  induction reach with
  | refl A => exact d
  | @step A B C edge tail ih =>
      have hB : EpsilonElimLinearDerives rules B w := ih d
      have hA : EpsilonElimLinearDerives rules A ([] ++ w ++ []) :=
        EpsilonElimLinearDerives.context edge hB
      simpa using hA

/-- Every epsilon-free derivation survives unit elimination. -/
theorem epsilonElim_to_unitElim
    {N : Type v} {Sigma : Type u}
    {rules : List (SourceLinearRule N Sigma)}
    {A : N} {w : Word Sigma}
    (d : EpsilonElimLinearDerives rules A w) :
    UnitElimLinearDerives rules A w := by
  induction d with
  | @terminal A w hrule =>
      exact UnitElimLinearDerives.terminal
        (UnitElimLinearRule.terminal
          (LinearUnitReach.refl A) hrule)
  | @context A B u v z hrule center ih =>
      by_cases hnonunit : u ≠ [] ∨ v ≠ []
      · exact UnitElimLinearDerives.context
          (UnitElimLinearRule.context
            (LinearUnitReach.refl A) hrule hnonunit)
          ih
      · push_neg at hnonunit
        rcases hnonunit with ⟨hu, hv⟩
        subst u
        subst v
        have hreach : LinearUnitReach rules A B :=
          linearUnitReach_of_edge hrule
        simpa using unitElimDerives_lift_reach hreach ih

/-- Every unit-free derivation expands back to the epsilon-eliminated grammar. -/
theorem unitElim_to_epsilonElim
    {N : Type v} {Sigma : Type u}
    {rules : List (SourceLinearRule N Sigma)}
    {A : N} {w : Word Sigma}
    (d : UnitElimLinearDerives rules A w) :
    EpsilonElimLinearDerives rules A w := by
  induction d with
  | @terminal A w hrule =>
      cases hrule with
      | @terminal A B w reach hsrc =>
          have hB : EpsilonElimLinearDerives rules B w :=
            EpsilonElimLinearDerives.terminal hsrc
          exact epsilonElimDerives_lift_unitReach reach hB
  | @context A C u v z hrule center ih =>
      cases hrule with
      | @context A B C u v reach hsrc hnonunit =>
          have hB : EpsilonElimLinearDerives rules B (u ++ z ++ v) :=
            EpsilonElimLinearDerives.context hsrc ih
          exact epsilonElimDerives_lift_unitReach reach hB

/-- Exact nonterminal-language preservation by unit elimination. -/
theorem unit_elimination_language_iff
    {N : Type v} {Sigma : Type u}
    (rules : List (SourceLinearRule N Sigma))
    (A : N) (w : Word Sigma) :
    UnitElimLinearDerives rules A w ↔
      EpsilonElimLinearDerives rules A w := by
  constructor
  · exact unitElim_to_epsilonElim
  · exact epsilonElim_to_unitElim

/-- Unit-eliminated derivations remain nonempty. -/
theorem unitElimLinearDerives_nonempty
    {N : Type v} {Sigma : Type u}
    {rules : List (SourceLinearRule N Sigma)}
    {A : N} {w : Word Sigma}
    (d : UnitElimLinearDerives rules A w) : w ≠ [] := by
  exact epsilonElimLinearDerives_nonempty
    (unitElim_to_epsilonElim d)

end FixedHCFGv44
end LeanCfgProject
