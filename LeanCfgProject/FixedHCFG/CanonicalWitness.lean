import LeanCfgProject.FixedHCFG.TypedRefinement

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/--
Canonical yield/context witness package for a reachable productive typed state.

The paper chooses these witnesses by shortlex.  Lemma 4.6 uses only the facts
that `omega` is a terminal yield of the state and `(u,v)` is a terminal context
of that occurrence, so we isolate exactly those proof-relevant facts here.
-/
structure CanonicalWitness {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma)
    (binary : BinaryRules N) (start : StartRules N)
    (X : TypedNT N Obs) where
  omega : Word Sigma
  leftCtx : Word Sigma
  rightCtx : Word Sigma
  yieldDeriv : TypedDerives Obs terminal binary X omega
  occurrence : TypedOccurs Obs terminal binary start X leftCtx rightCtx

/--
Lemma 4.6: canonical witnesses carry exactly the three monoid types written on
`X = A_p^{m,n}`.
-/
theorem lemma_4_6_canonical_witness_types
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma)
    (binary : BinaryRules N) (start : StartRules N)
    {X : TypedNT N Obs}
    (cw : CanonicalWitness Obs terminal binary start X) :
    Obs.value cw.leftCtx = X.leftType ∧
      Obs.value cw.omega = X.yieldType ∧
      Obs.value cw.rightCtx = X.rightType := by
  have hy := lemma_4_5_i_yield_type Obs terminal binary cw.yieldDeriv
  have hc := lemma_4_5_ii_context_type Obs terminal binary start cw.occurrence
  exact ⟨hc.1, hy, hc.2⟩

end FixedHCFG
end LeanCfgProject
