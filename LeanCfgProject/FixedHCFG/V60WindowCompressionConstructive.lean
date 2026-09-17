import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60WindowCompression
import LeanCfgProject.FixedHCFG.V60AlignedMarkedPruning

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Constructive closure of the positive-window part of manuscript Lemma
`window-typed-yield`.

Earlier layers reduced the fixed-window argument to an abstract untyped
boundary-preserving compression premise (and, equivalently, to a family of
skeleton certificates).  The aligned marked-support pruning theorem now builds
the required short same-root derivation directly from the base thickness
hypothesis.  Thus no external `hCert` assumption remains in the positive-window
endpoint.
-/

/--
The manuscript's marked-leaf pruning construction supplies the full untyped
positive-window compression from the base SSBNF thickness bound alone.
-/
theorem v60_window_untyped_compression_from_thickness
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N)
    (k l tau : Nat)
    (hr : k + l ≠ 0)
    (hThickness : V60BaseThicknessBound terminal binary tau) :
    V60WindowUntypedCompression terminal binary
      k l (Fintype.card N) tau := by
  intro A w d hLong
  obtain ⟨t, ht⟩ := V60DerivationTree.exists_tree_of_untyped_derives d
  have hLongLeaves :
      k + l ≤ V60DerivationTree.leafCount t := by
    rw [← V60DerivationTree.yield_length_eq_leafCount t, ht]
    exact hLong
  obtain ⟨shape, hSupport, hBlocks⟩ :=
    V60AlignedMarkedSupport.boundary_support_block_count
      k l t hLongLeaves hr
  have hLeaves :
      V60MarkedSupportShape.markedLeaves shape = k + l := by
    rw [V60AlignedMarkedSupport.markedLeaves_eq_markCount hSupport]
    exact v60BoundaryMarks_count k l _
  obtain ⟨t', hMarked, hBound⟩ :=
    V60AlignedMarkedSupport.prune_marked_bound
      tau hThickness hSupport
  let z : Word Sigma := V60DerivationTree.yield t'
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · exact V60DerivationTree.toUntypedDerives t'
  · have hzLong :=
      V60MarkedWordReplacement.boundary_target_length
        k l (V60DerivationTree.leafCount t) hMarked
    simpa [z] using hzLong
  · have hBoundary :=
      V60MarkedWordReplacement.boundary_eq_of_boundary_marks
        k l (V60DerivationTree.leafCount t) hMarked
    simpa [z, ht] using hBoundary
  · have hConcrete :
        z.length ≤
          k + l + (2 * (k + l) - 1) * Fintype.card N * tau := by
      dsimp [z]
      simpa [hLeaves, hBlocks] using hBound
    unfold V60WindowYieldBound
    rw [if_neg hr]
    exact hConcrete

/--
Exact constructive positive-window form of manuscript Lemma
`window-typed-yield`: every productive kept typed state has a same-type yield
within the displayed `B_{k,l}(G)` bound, assuming only base thickness.
-/
theorem v60_window_typed_yield_candidate_from_thickness
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (k l tau : Nat)
    (hr : k + l ≠ 0)
    (hObserver : V60WindowObserverCompatible Obs k l)
    (hThickness : V60BaseThicknessBound terminal binary tau) :
    ∀ X : V60KeptState Obs terminal binary start,
      ∃ z : Word Sigma,
        V60YieldTypedDerives Obs terminal binary X.1 z ∧
          z.length ≤
            V60WindowYieldBound (k + l) (Fintype.card N) tau := by
  exact v60_window_typed_yield_candidate_of_boundary_compression
    Obs terminal binary start k l (Fintype.card N) tau hr hObserver
    (v60_window_untyped_compression_from_thickness
      terminal binary k l tau hr hThickness)

/--
Constructive positive-window form of the context half of manuscript Lemma
`window-context`.  The finite dependency-spine argument now consumes the
constructive typed-yield theorem directly, so no context-existence premise is
left either.
-/
theorem v60_window_canonical_context_bound_from_thickness
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (k l tau : Nat)
    (hr : k + l ≠ 0)
    (hObserver : V60WindowObserverCompatible Obs k l)
    (hThickness : V60BaseThicknessBound terminal binary tau) :
    ∀ X : V60KeptState Obs terminal binary start,
      (v60CanonicalLeftCtx X).length +
        (v60CanonicalRightCtx X).length ≤
          Fintype.card (V60KeptState Obs terminal binary start) *
            V60WindowYieldBound (k + l) (Fintype.card N) tau := by
  exact v60_window_canonical_context_bound_from_yields
    Obs terminal binary start
    (k + l) (Fintype.card N) tau
    (v60_window_typed_yield_candidate_from_thickness
      Obs terminal binary start k l tau hr hObserver hThickness)

/--
Manuscript-facing positive-window canonical-witness bound with the previous
structural certificate premise eliminated.  The only grammar-side hypothesis
is the base thickness bound used in the paper.
-/
theorem v60_window_witness_bound_from_thickness
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop)
    (k l tau : Nat)
    (hr : k + l ≠ 0)
    (hObserver : V60WindowObserverCompatible Obs k l)
    (hThickness : V60BaseThicknessBound terminal binary tau)
    {z : Word Sigma}
    (hz : V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart z) :
    z.length ≤
      (Fintype.card (V60KeptState Obs terminal binary start) + 2) *
        V60WindowYieldBound (k + l) (Fintype.card N) tau + 1 := by
  exact v60_window_witness_length_bound_from_yields
    Obs terminal binary start epsilonStart
    (k + l) (Fintype.card N) tau
    (v60_window_typed_yield_candidate_from_thickness
      Obs terminal binary start k l tau hr hObserver hThickness)
    hz

end FixedHCFG
end LeanCfgProject
