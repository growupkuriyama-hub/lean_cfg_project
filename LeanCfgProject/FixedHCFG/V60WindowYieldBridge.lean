import LeanCfgProject.FixedHCFG.V60WindowEnvelope

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
A manuscript-facing bridge isolating the one genuinely fixed-window-specific
combinatorial argument in Lemma `window-typed-yield`.

For `r = k+l > 0`, the paper shortens an ordinary SSBNF derivation while
preserving its first `k` and last `l` terminals.  Once that untyped
boundary-preserving compression statement is available, the results below lift
it automatically to the yield-only typed refinement and then feed the result
into the already formalized finite dependency-spine/context argument.

The endpoint `r = 0` is separated exactly as in the manuscript: it needs only a
thickness witness for each productive base nonterminal plus the fact that all
nonempty words have the same observer type.
-/

/-- The last `l` symbols, written without committing to a particular API name. -/
def v60WindowSuffix {Sigma : Type u} (l : Nat) (w : Word Sigma) : Word Sigma :=
  w.drop (w.length - l)

/-- Equality of the fixed left and right windows. -/
def V60WindowBoundaryEq {Sigma : Type u}
    (k l : Nat) (x y : Word Sigma) : Prop :=
  x.take k = y.take k ∧
    v60WindowSuffix l x = v60WindowSuffix l y

/--
The only observer property used after the marked-leaf compression: sufficiently
long words with the same fixed windows have the same `h_{k,l}` value.
-/
def V60WindowObserverCompatible {Sigma : Type u}
    (Obs : Observer Sigma) (k l : Nat) : Prop :=
  ∀ x y : Word Sigma,
    k + l ≤ x.length →
    k + l ≤ y.length →
    V60WindowBoundaryEq k l x y →
    Obs.value x = Obs.value y

/--
Untyped form of the marked-leaf/cycle-deletion conclusion of manuscript Lemma
`window-typed-yield`.  This is now the sole nontrivial combinatorial premise in
the positive-window bridge.
-/
def V60WindowUntypedCompression
    {N0 : Type v} {Sigma : Type u}
    (terminal : V60TerminalRules N0 Sigma)
    (binary : V60BinaryRules N0)
    (k l N tau : Nat) : Prop :=
  ∀ (A : N0) (w : Word Sigma),
    V60UntypedDerives terminal binary A w →
    k + l ≤ w.length →
    ∃ z : Word Sigma,
      V60UntypedDerives terminal binary A z ∧
      k + l ≤ z.length ∧
      V60WindowBoundaryEq k l w z ∧
      z.length ≤ V60WindowYieldBound (k + l) N tau

/-- A thickness-style shortest-yield hypothesis on the base SSBNF grammar. -/
def V60BaseThicknessBound
    {N0 : Type v} {Sigma : Type u}
    (terminal : V60TerminalRules N0 Sigma)
    (binary : V60BinaryRules N0)
    (tau : Nat) : Prop :=
  ∀ A : N0,
    (∃ w : Word Sigma, V60UntypedDerives terminal binary A w) →
      ∃ z : Word Sigma,
        V60UntypedDerives terminal binary A z ∧ z.length ≤ tau

/-- Endpoint property of `h_{0,0}` under the paper's nonempty-factor convention. -/
def V60NonemptyObserverTrivial {Sigma : Type u}
    (Obs : Observer Sigma) : Prop :=
  ∀ x y : Word Sigma,
    x ≠ [] → y ≠ [] → Obs.value x = Obs.value y

/--
Positive-window part of Lemma `window-typed-yield`: boundary-preserving
compression of the underlying SSBNF derivation lifts to the exact v60 typed
copy `A_mu`.
-/
theorem v60_window_typed_yield_candidate_of_boundary_compression
    {N0 : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N0 Sigma)
    (binary : V60BinaryRules N0) (start : V60StartRules N0)
    (k l N tau : Nat)
    (hr : k + l ≠ 0)
    (hObserver : V60WindowObserverCompatible Obs k l)
    (hCompress : V60WindowUntypedCompression terminal binary k l N tau) :
    ∀ X : V60KeptState Obs terminal binary start,
      ∃ z : Word Sigma,
        V60YieldTypedDerives Obs terminal binary X.1 z ∧
          z.length ≤ V60WindowYieldBound (k + l) N tau := by
  rintro ⟨⟨A, p⟩, hKeep⟩
  rcases hKeep.1 with ⟨w, d⟩
  by_cases hShort : w.length < k + l
  · refine ⟨w, d, ?_⟩
    have hB : k + l ≤ V60WindowYieldBound (k + l) N tau := by
      unfold V60WindowYieldBound
      rw [if_neg hr]
      omega
    exact le_trans (Nat.le_of_lt hShort) hB
  · have hLong : k + l ≤ w.length := Nat.le_of_not_gt hShort
    have dUntyped : V60UntypedDerives terminal binary A w :=
      v60_yield_typed_derivation_erases Obs terminal binary d
    obtain ⟨z, dz, hzLong, hBoundary, hzBound⟩ :=
      hCompress A w dUntyped hLong
    have hTypeOld : Obs.value w = p :=
      v60_yield_typed_invariant Obs terminal binary d
    have hWindowEq : Obs.value w = Obs.value z :=
      hObserver w z hLong hzLong hBoundary
    have hTypeNew : Obs.value z = p := hWindowEq.symm.trans hTypeOld
    have dzTyped := v60_untyped_derivation_lifts Obs terminal binary dz
    refine ⟨z, ?_, hzBound⟩
    simpa [hTypeNew] using dzTyped

/--
Endpoint `r=0` part of Lemma `window-typed-yield`: the unique nonempty type
inherits the base nonterminal's thickness bound.
-/
theorem v60_window_zero_typed_yield_candidate
    {N0 : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N0 Sigma)
    (binary : V60BinaryRules N0) (start : V60StartRules N0)
    (N tau : Nat)
    (hObserver : V60NonemptyObserverTrivial Obs)
    (hThickness : V60BaseThicknessBound terminal binary tau) :
    ∀ X : V60KeptState Obs terminal binary start,
      ∃ z : Word Sigma,
        V60YieldTypedDerives Obs terminal binary X.1 z ∧
          z.length ≤ V60WindowYieldBound 0 N tau := by
  rintro ⟨⟨A, p⟩, hKeep⟩
  rcases hKeep.1 with ⟨w, d⟩
  have dUntyped : V60UntypedDerives terminal binary A w :=
    v60_yield_typed_derivation_erases Obs terminal binary d
  obtain ⟨z, dz, hzBound⟩ := hThickness A ⟨w, dUntyped⟩
  have hwNonempty : w ≠ [] :=
    v60_yield_typed_derivation_nonempty Obs terminal binary d
  have hzNonempty : z ≠ [] :=
    v60_untyped_derivation_nonempty terminal binary dz
  have hTypeOld : Obs.value w = p :=
    v60_yield_typed_invariant Obs terminal binary d
  have hTypeNew : Obs.value z = p :=
    (hObserver z w hzNonempty hwNonempty).trans hTypeOld
  have dzTyped := v60_untyped_derivation_lifts Obs terminal binary dz
  refine ⟨z, ?_, ?_⟩
  · simpa [hTypeNew] using dzTyped
  · simpa [V60WindowYieldBound] using hzBound

/--
Positive-window witness bound with the context hypothesis completely removed.
The remaining premise is exactly the untyped marked-leaf compression statement.
-/
theorem v60_window_witness_bound_of_boundary_compression
    {N0 : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    [Finite N0]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N0 Sigma)
    (binary : V60BinaryRules N0) (start : V60StartRules N0)
    (epsilonStart : Prop)
    (k l N tau : Nat)
    (hr : k + l ≠ 0)
    (hObserver : V60WindowObserverCompatible Obs k l)
    (hCompress : V60WindowUntypedCompression terminal binary k l N tau)
    {z : Word Sigma}
    (hz : V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart z) :
    z.length ≤
      (Fintype.card (V60KeptState Obs terminal binary start) + 2) *
        V60WindowYieldBound (k + l) N tau + 1 := by
  apply v60_window_witness_length_bound_from_yields
    Obs terminal binary start epsilonStart (k + l) N tau
  · exact v60_window_typed_yield_candidate_of_boundary_compression
      Obs terminal binary start k l N tau hr hObserver hCompress
  · exact hz

/-- The corresponding exact-v60 witness bound at the endpoint `(k,l)=(0,0)`. -/
theorem v60_window_zero_witness_bound
    {N0 : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    [Finite N0]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N0 Sigma)
    (binary : V60BinaryRules N0) (start : V60StartRules N0)
    (epsilonStart : Prop)
    (N tau : Nat)
    (hObserver : V60NonemptyObserverTrivial Obs)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {z : Word Sigma}
    (hz : V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart z) :
    z.length ≤
      (Fintype.card (V60KeptState Obs terminal binary start) + 2) * tau + 1 := by
  have hYield := v60_window_zero_typed_yield_candidate
    Obs terminal binary start N tau hObserver hThickness
  have h := v60_window_witness_length_bound_from_yields
    Obs terminal binary start epsilonStart 0 N tau hYield hz
  simpa [V60WindowYieldBound] using h

end FixedHCFG
end LeanCfgProject
