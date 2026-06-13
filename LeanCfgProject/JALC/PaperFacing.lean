import LeanCfgProject.JALC.Transport
import LeanCfgProject.JALC.Bracketing
import LeanCfgProject.JALC.ProductiveFirst

namespace LeanCfgProject
namespace JALC
namespace PaperFacing

/-
Paper-facing Lean checks for the JALC paper.

This module gathers the theorem-facing checks that are currently relevant to
the paper text.  The imported modules contain the actual constructions and
proofs; this file gives stable names for the results that should be cited in
the formalization report and in the Lean artifact section of the paper.
-/

universe u v


/-- Paper-facing name for the yield-type invariant of typed derivations. -/
theorem checked_yield_type_invariant
    {Sigma : Type u} {M : Type v} [Monoid M]
    {Obs : WordObserver Sigma M}
    {p : M} {w : List Sigma}
    (d : TypedDeriv Obs p w) :
    Obs.h w = p :=
  TypedDeriv.yield_type_invariant d


/--
Paper-facing name for the context-type invariant of two-sided frame transport.

This result is checked over an arbitrary monoid.
-/
theorem checked_context_type_invariant
    {Sigma : Type u} {M : Type v} [Monoid M]
    {Obs : WordObserver Sigma M}
    {p m n : M} {u v : List Sigma}
    (d : TypedCtx Obs p m n u v) :
    Obs.h u = m ∧ Obs.h v = n :=
  TypedCtx.context_type_invariant d


/--
Paper-facing name for the arithmetic kernel of the bracketing non-rigidity
witness.
-/
theorem checked_bracketing_nonrigidity_kernel :
    ((0, 1, 0) ∈ Bracketing.G1states ∧
      (0, 1, 0) ∉ Bracketing.G2states) ∧
    ((0, 0, 1) ∈ Bracketing.G2states ∧
      (0, 0, 1) ∉ Bracketing.G1states) :=
  Bracketing.bracketing_nonrigidity_arithmetic_kernel


/--
Paper-facing name for the finite productive-first trimming witness.

The wrong-frame copy is reachable in the displayed full path and productive in
the full toy model, but it is not kept after productive-first reachability is
computed in the modeled finite example.
-/
theorem checked_productive_first_counterexample_kernel :
    ProductiveFirst.displayedFullReachable ProductiveFirst.spuriousY ∧
    ProductiveFirst.fullProductiveCopy ProductiveFirst.spuriousY ∧
    ¬ ProductiveFirst.productiveFirstReachable ProductiveFirst.spuriousY :=
  ProductiveFirst.productive_first_counterexample_kernel


/--
Paper-facing name for the statement that the intended Y copy is kept while the
wrong-frame Y copy is not kept in the finite productive-first witness.
-/
theorem checked_productive_first_keeps_intended_not_spurious :
    ProductiveFirst.productiveFirstReachable ProductiveFirst.intendedY ∧
    ¬ ProductiveFirst.productiveFirstReachable ProductiveFirst.spuriousY :=
  ProductiveFirst.productive_first_keeps_intended_not_spurious


/--
Combined paper-facing summary theorem.

This theorem packages the two finite example checks.  The transport invariants
remain separately quantified theorems above.
-/
theorem checked_finite_example_kernels :
    (((0, 1, 0) ∈ Bracketing.G1states ∧
        (0, 1, 0) ∉ Bracketing.G2states) ∧
      ((0, 0, 1) ∈ Bracketing.G2states ∧
        (0, 0, 1) ∉ Bracketing.G1states)) ∧
    (ProductiveFirst.displayedFullReachable ProductiveFirst.spuriousY ∧
      ProductiveFirst.fullProductiveCopy ProductiveFirst.spuriousY ∧
      ¬ ProductiveFirst.productiveFirstReachable ProductiveFirst.spuriousY) := by
  exact ⟨checked_bracketing_nonrigidity_kernel,
    checked_productive_first_counterexample_kernel⟩

end PaperFacing
end JALC
end LeanCfgProject
