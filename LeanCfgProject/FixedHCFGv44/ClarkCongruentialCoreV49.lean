import LeanCfgProject.FixedHCFGv44.CanonicalWitness
import LeanCfgProject.FixedHCFGv44.WitnessEndToEnd

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Core of TCS v49 Proposition `prop:clark-congruential-comparison`.

Clark's congruential condition asks that the terminal language generated from
each nonterminal lie inside one syntactic congruence class of the target
language.  In the v49 proof this is obtained on the reduced yield-typed
non-start states: two yields of the same `A_mu` have the same observer value,
and the canonical reaching context of that retained typed state is common to
both yields.  Fixed-h substitutability then gives equality of their full
two-sided distributions.

This file formalizes exactly that substantive typed-state argument.  The
finite-initial-set packaging and the strict Dyck witness are kept separate so
that no stronger Clark-family theorem is claimed before those pieces are
formalized.
-/

/-- Every non-start yield-typed derivation has a nonempty terminal yield. -/
theorem typedDerives_internal_v49
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    {X : TypedNT N Obs} {w : Word Sigma}
    (d : TypedDerives Obs terminal binary X w) :
    Internal w := by
  induction d with
  | terminal hrule =>
      simp [Internal]
  | @binary A B C mu nu x y hrule left right ihLeft ihRight =>
      intro hNil
      have hx : x = [] := (List.append_eq_nil.mp hNil).1
      exact ihLeft hx

/--
The canonical reaching context of a retained typed state is shared by every
two terminal yields of that state in the original SSBNF target language.
-/
theorem typedYields_share_canonical_context_v49
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (X : KeptState Obs terminal binary start)
    {x y : Word Sigma}
    (dx : TypedDerives Obs terminal binary X.1 x)
    (dy : TypedDerives Obs terminal binary X.1 y) :
    ShareContext
      (UntypedStartLanguage terminal binary start epsilonStart) x y := by
  let u := canonicalLeftCtx X
  let v := canonicalRightCtx X
  have hOcc : TypedOccurs Obs terminal binary start X.1 u v := by
    simpa [u, v] using canonicalChi_spec X
  refine ⟨u, v, ?_, ?_⟩
  · change UntypedStartLanguage terminal binary start epsilonStart
      (u ++ x ++ v)
    exact (typed_refinement_language_iff
      Obs terminal binary start epsilonStart (u ++ x ++ v)).mp
        (typedOccurs_plug_trimmed
          Obs terminal binary start epsilonStart hOcc dx)
  · change UntypedStartLanguage terminal binary start epsilonStart
      (u ++ y ++ v)
    exact (typed_refinement_language_iff
      Obs terminal binary start epsilonStart (u ++ y ++ v)).mp
        (typedOccurs_plug_trimmed
          Obs terminal binary start epsilonStart hOcc dy)

/--
Substantive inclusion lemma behind v49 Proposition
`prop:clark-congruential-comparison`: all yields of one retained yield-typed
non-start state are syntactically congruent for the target language.

`SameDistribution L x y` is exactly equality of all two-sided contexts, i.e.
the language's syntactic congruence `x ≡_L y` used in the manuscript.
-/
theorem typedNonterminal_yields_syntactically_congruent_v49
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart))
    (X : KeptState Obs terminal binary start)
    {x y : Word Sigma}
    (dx : TypedDerives Obs terminal binary X.1 x)
    (dy : TypedDerives Obs terminal binary X.1 y) :
    SameDistribution
      (UntypedStartLanguage terminal binary start epsilonStart) x y := by
  have hx : Internal x :=
    typedDerives_internal_v49 Obs terminal binary dx
  have hy : Internal y :=
    typedDerives_internal_v49 Obs terminal binary dy
  have hType : obsValue Obs x = obsValue Obs y := by
    calc
      obsValue Obs x = X.1.yieldType :=
        typed_yield_invariant Obs terminal binary dx
      _ = obsValue Obs y :=
        (typed_yield_invariant Obs terminal binary dy).symm
  have hShare :
      ShareContext
        (UntypedStartLanguage terminal binary start epsilonStart) x y :=
    typedYields_share_canonical_context_v49
      Obs terminal binary start epsilonStart X dx dy
  exact hSub x y hx hy hType hShare

end FixedHCFGv44
end LeanCfgProject
