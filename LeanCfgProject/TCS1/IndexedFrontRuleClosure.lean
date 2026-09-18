import LeanCfgProject.TCS1.IndexedClosedFrontSupport

/-!
# TCS #1 v66: finite indexed front-end rule closure

This module discharges the remaining closure obligation for the finite
front-end support.  The key source-rule fact is that any isolated structural
right-hand side of length at least three comes from an actual indexed source
production with exactly that mixed right-hand side.  This makes the suffix
child of a long source rule an actual occurrence suffix.

Together with suffix-tail closure from IndexedClosedFrontSupport, this proves
that the linear support is closed under every unit and binary rule of the
front-end BinaryNullableGrammar.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section IndexedFrontRuleClosure

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}

/-- Any source-RHS drop beginning at a valid occurrence is supported. -/
theorem indexedClosedFrontSupport_drop_mem
    [Fintype N] [Fintype α] [Fintype P]
    [DecidableEq N] [DecidableEq α]
    (G : IndexedMixedCFG N α P)
    (p : P)
    (i : Nat)
    (hi : i < (G.rhs p).length) :
    BinarizedState.suffix ((G.rhs p).drop i) ∈
      indexedClosedFrontSupport G := by
  let o : ProductionOccurrence G :=
    ⟨p, ⟨i, hi⟩⟩
  simpa [o, occurrenceSuffix] using
    indexedClosedFrontSupport_suffix_mem G o

/--
A length-at-least-three structural RHS of the terminal-isolated sequence
grammar is literally the right-hand side of some indexed source production.
-/
theorem indexed_isolatedStructural_long_has_source
    [Fintype P]
    (G : IndexedMixedCFG N α P)
    (X B C D : MixedSymbol N α)
    (rest : List (MixedSymbol N α))
    (h :
      (isolatedSequenceGrammar G.toMixedRules).structural
        X (B :: C :: D :: rest)) :
    ∃ p : P,
      G.rhs p = B :: C :: D :: rest := by
  change
    IsolatedRule G.toMixedRules X
      ((B :: C :: D :: rest).map Sum.inl) at h
  cases h with
  | @original A rhs hR =>
      rcases hR with ⟨p, hLhs, hRhs⟩
      refine ⟨p, ?_⟩
      subst rhs
      simp_all [isolateRhs,
        map_isolateSymbol_true_eq_map_inl]
  | wrapper a =>
      simp_all

end IndexedFrontRuleClosure

end TCS1
end LeanCfgProject
