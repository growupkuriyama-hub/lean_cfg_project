import LeanCfgProject.FixedHCFG.V60ContextSpine

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Manuscript-facing arithmetic envelope for Section `fixed-window-thick`.

The specialized derivation-tree argument of Lemma `window-typed-yield`
supplies a short candidate yield.  The finite dependency-spine argument of
Lemma `window-context` is formalized in `V60ContextSpine` and is used below to
construct the required short successful context automatically.  Thus the only
remaining fixed-window-specific input is the yield candidate itself.
-/

/-- The displayed bound `B_{k,l}(G)` with `r = k+l`. -/
def V60WindowYieldBound (r N tau : Nat) : Nat :=
  if r = 0 then tau else r + (2 * r - 1) * N * tau

/-- A short typed candidate yield gives the same bound for canonical `omega`. -/
theorem v60_window_canonical_yield_bound
    {N0 : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N0 Sigma}
    {binary : V60BinaryRules N0} {start : V60StartRules N0}
    (r N tau : Nat)
    (hCandidate : ∀ X : V60KeptState Obs terminal binary start,
      ∃ w : Word Sigma,
        V60YieldTypedDerives Obs terminal binary X.1 w ∧
          w.length ≤ V60WindowYieldBound r N tau) :
    ∀ X : V60KeptState Obs terminal binary start,
      (v60CanonicalOmega X).length ≤ V60WindowYieldBound r N tau := by
  intro X
  exact v60CanonicalOmega_length_le_of_exists X
    (V60WindowYieldBound r N tau) (hCandidate X)

/-- A short reachable context gives the manuscript bound for canonical `chi`. -/
theorem v60_window_canonical_context_bound
    {N0 : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N0 Sigma}
    {binary : V60BinaryRules N0} {start : V60StartRules N0}
    (r N tau Nt : Nat)
    (hCandidate : ∀ X : V60KeptState Obs terminal binary start,
      ∃ u v : Word Sigma,
        V60TypedOccurs Obs terminal binary start X.1 u v ∧
          u.length + v.length ≤ Nt * V60WindowYieldBound r N tau) :
    ∀ X : V60KeptState Obs terminal binary start,
      (v60CanonicalLeftCtx X).length +
        (v60CanonicalRightCtx X).length ≤
          Nt * V60WindowYieldBound r N tau := by
  intro X
  exact v60CanonicalChi_total_length_le_of_exists X
    (Nt * V60WindowYieldBound r N tau) (hCandidate X)

/--
The finite typed dependency graph turns the yield bound into the short-context
candidate required by manuscript Lemma `window-context`.
-/
theorem v60_window_context_candidate_from_yields
    {N0 : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    [Finite N0]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N0 Sigma)
    (binary : V60BinaryRules N0) (start : V60StartRules N0)
    (r N tau : Nat)
    (hYieldCandidate : ∀ X : V60KeptState Obs terminal binary start,
      ∃ w : Word Sigma,
        V60YieldTypedDerives Obs terminal binary X.1 w ∧
          w.length ≤ V60WindowYieldBound r N tau) :
    ∀ X : V60KeptState Obs terminal binary start,
      ∃ u v : Word Sigma,
        V60TypedOccurs Obs terminal binary start X.1 u v ∧
          u.length + v.length ≤
            Fintype.card (V60KeptState Obs terminal binary start) *
              V60WindowYieldBound r N tau := by
  have hOmega := v60_window_canonical_yield_bound
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
    r N tau hYieldCandidate
  intro X
  exact v60_exists_short_context_of_canonical_yield_bound
    Obs terminal binary start (V60WindowYieldBound r N tau) hOmega X

/--
Consequently the canonical v60 context satisfies the manuscript `N_t B` bound
without a separate context-existence assumption.
-/
theorem v60_window_canonical_context_bound_from_yields
    {N0 : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    [Finite N0]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N0 Sigma)
    (binary : V60BinaryRules N0) (start : V60StartRules N0)
    (r N tau : Nat)
    (hYieldCandidate : ∀ X : V60KeptState Obs terminal binary start,
      ∃ w : Word Sigma,
        V60YieldTypedDerives Obs terminal binary X.1 w ∧
          w.length ≤ V60WindowYieldBound r N tau) :
    ∀ X : V60KeptState Obs terminal binary start,
      (v60CanonicalLeftCtx X).length +
        (v60CanonicalRightCtx X).length ≤
          Fintype.card (V60KeptState Obs terminal binary start) *
            V60WindowYieldBound r N tau := by
  intro X
  exact v60CanonicalChi_total_length_le_of_exists X
    (Fintype.card (V60KeptState Obs terminal binary start) *
      V60WindowYieldBound r N tau)
    (v60_window_context_candidate_from_yields
      Obs terminal binary start r N tau hYieldCandidate X)

/--
The second conclusion of manuscript Lemma `window-context`: once its two
combinatorial candidate bounds are available, every exact canonical witness has
length at most `(N_t+2) B_{k,l}(G)+1`.
-/
theorem v60_window_witness_length_bound
    {N0 : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N0 Sigma}
    {binary : V60BinaryRules N0} {start : V60StartRules N0}
    (epsilonStart : Prop)
    (r N tau Nt : Nat)
    (hYieldCandidate : ∀ X : V60KeptState Obs terminal binary start,
      ∃ w : Word Sigma,
        V60YieldTypedDerives Obs terminal binary X.1 w ∧
          w.length ≤ V60WindowYieldBound r N tau)
    (hContextCandidate : ∀ X : V60KeptState Obs terminal binary start,
      ∃ u v : Word Sigma,
        V60TypedOccurs Obs terminal binary start X.1 u v ∧
          u.length + v.length ≤ Nt * V60WindowYieldBound r N tau)
    {z : Word Sigma}
    (hz : V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart z) :
    z.length ≤
      (Nt + 2) * V60WindowYieldBound r N tau + 1 := by
  let B := V60WindowYieldBound r N tau
  have hOmega : ∀ X : V60KeptState Obs terminal binary start,
      (v60CanonicalOmega X).length ≤ B := by
    intro X
    exact v60CanonicalOmega_length_le_of_exists X B (hYieldCandidate X)
  have hCtx : ∀ X : V60KeptState Obs terminal binary start,
      (v60CanonicalLeftCtx X).length +
        (v60CanonicalRightCtx X).length ≤ Nt * B := by
    intro X
    exact v60CanonicalChi_total_length_le_of_exists X (Nt * B)
      (hContextCandidate X)
  have h := v60CanonicalWitnessSet_word_length_le
    epsilonStart B (Nt * B) hOmega hCtx hz
  dsimp [B] at h ⊢
  simpa [Nat.add_mul] using h

/--
Exact-v60 form of the witness-length conclusion of `window-context`: the
short-context hypothesis has been eliminated.  The only remaining specialized
premise is the candidate-yield statement of `window-typed-yield`.
-/
theorem v60_window_witness_length_bound_from_yields
    {N0 : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    [Finite N0]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N0 Sigma)
    (binary : V60BinaryRules N0) (start : V60StartRules N0)
    (epsilonStart : Prop)
    (r N tau : Nat)
    (hYieldCandidate : ∀ X : V60KeptState Obs terminal binary start,
      ∃ w : Word Sigma,
        V60YieldTypedDerives Obs terminal binary X.1 w ∧
          w.length ≤ V60WindowYieldBound r N tau)
    {z : Word Sigma}
    (hz : V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart z) :
    z.length ≤
      (Fintype.card (V60KeptState Obs terminal binary start) + 2) *
        V60WindowYieldBound r N tau + 1 := by
  let B := V60WindowYieldBound r N tau
  let Nt := Fintype.card (V60KeptState Obs terminal binary start)
  have hOmega : ∀ X : V60KeptState Obs terminal binary start,
      (v60CanonicalOmega X).length ≤ B := by
    intro X
    exact v60CanonicalOmega_length_le_of_exists X B (hYieldCandidate X)
  have hContextCandidate : ∀ X : V60KeptState Obs terminal binary start,
      ∃ u v : Word Sigma,
        V60TypedOccurs Obs terminal binary start X.1 u v ∧
          u.length + v.length ≤ Nt * B := by
    intro X
    simpa [Nt, B] using
      (v60_window_context_candidate_from_yields
        Obs terminal binary start r N tau hYieldCandidate X)
  have hCtx : ∀ X : V60KeptState Obs terminal binary start,
      (v60CanonicalLeftCtx X).length +
        (v60CanonicalRightCtx X).length ≤ Nt * B := by
    intro X
    exact v60CanonicalChi_total_length_le_of_exists X (Nt * B)
      (hContextCandidate X)
  have h := v60CanonicalWitnessSet_word_length_le
    epsilonStart B (Nt * B) hOmega hCtx hz
  dsimp [Nt, B] at h ⊢
  simpa [Nat.add_mul] using h

end FixedHCFG
end LeanCfgProject
