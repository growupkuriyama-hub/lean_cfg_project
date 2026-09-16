import LeanCfgProject.FixedHCFG.V60MarkedSkeleton

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Bridge from the concrete marked-skeleton count to the manuscript's positive
fixed-window yield bound.

`V60WindowYieldBridge` deliberately left the boundary-preserving compression as
one proposition.  The derivation-tree and marked-skeleton files now expose the
internal certificate produced by that proof: a boundary-preserving replacement
whose marked skeleton has exactly `k+l` leaves and whose non-boundary terminal
material is bounded by `tau` per retained nonterminal vertex.

The results below discharge all remaining arithmetic from such a certificate.
Consequently the only missing positive-window ingredient is the structural
construction of these certificates from an arbitrary SSBNF derivation tree.
-/

/--
Certificate supplied by the marked-leaf/cycle-deletion construction.

The raw length estimate separates the `k+l` marked boundary terminals from the
short replacement material charged at most `tau` for every retained
nonterminal vertex of the simple marked skeleton.
-/
def V60SkeletonCompressionCertificate
    {N : Type v} {Sigma : Type u}
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N)
    (k l tau : Nat) (A : N) (w : Word Sigma) : Prop :=
  ∃ (s : V60MarkedSkeleton N) (z : Word Sigma),
    V60MarkedSkeleton.markedLeaves s = k + l ∧
    V60UntypedDerives terminal binary A z ∧
    k + l ≤ z.length ∧
    V60WindowBoundaryEq k l w z ∧
    z.length ≤ k + l + V60MarkedSkeleton.nodeCount s * tau

/--
The marked-skeleton count converts the raw replacement estimate into exactly
`r + (2r-1) N tau`, with `r = k+l` and `N = |N|`.
-/
theorem v60_skeleton_candidate_length_le_window_bound
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    (k l tau : Nat)
    (hr : k + l ≠ 0)
    (s : V60MarkedSkeleton N) (z : Word Sigma)
    (hLeaves : V60MarkedSkeleton.markedLeaves s = k + l)
    (hRaw : z.length ≤
      k + l + V60MarkedSkeleton.nodeCount s * tau) :
    z.length ≤ V60WindowYieldBound (k + l) (Fintype.card N) tau := by
  have hNodes : V60MarkedSkeleton.nodeCount s ≤
      (2 * (k + l) - 1) * Fintype.card N := by
    simpa [hLeaves] using
      (V60MarkedSkeleton.nodeCount_le_manuscript_bound s)
  have hScaled : V60MarkedSkeleton.nodeCount s * tau ≤
      ((2 * (k + l) - 1) * Fintype.card N) * tau :=
    Nat.mul_le_mul_right tau hNodes
  have hExpanded :
      k + l + V60MarkedSkeleton.nodeCount s * tau ≤
        k + l + ((2 * (k + l) - 1) * Fintype.card N) * tau :=
    Nat.add_le_add_left hScaled (k + l)
  unfold V60WindowYieldBound
  rw [if_neg hr]
  exact le_trans hRaw hExpanded

/--
A family of marked-skeleton certificates is enough to discharge the abstract
`V60WindowUntypedCompression` premise used by the typed-yield bridge.
-/
theorem v60_window_untyped_compression_of_skeleton_certificates
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N)
    (k l tau : Nat)
    (hr : k + l ≠ 0)
    (hCert : ∀ (A : N) (w : Word Sigma),
      V60UntypedDerives terminal binary A w →
      k + l ≤ w.length →
      V60SkeletonCompressionCertificate terminal binary k l tau A w) :
    V60WindowUntypedCompression terminal binary
      k l (Fintype.card N) tau := by
  intro A w d hLong
  obtain ⟨s, z, hLeaves, dz, hzLong, hBoundary, hRaw⟩ :=
    hCert A w d hLong
  refine ⟨z, dz, hzLong, hBoundary, ?_⟩
  exact v60_skeleton_candidate_length_le_window_bound
    k l tau hr s z hLeaves hRaw

/--
Manuscript-facing positive-window endpoint: once the structural tree proof
produces marked-skeleton certificates, the exact canonical characteristic
witnesses satisfy the displayed `(N_t+2) B_{k,l}(G)+1` bound.
-/
theorem v60_window_witness_bound_of_skeleton_certificates
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
    (hCert : ∀ (A : N) (w : Word Sigma),
      V60UntypedDerives terminal binary A w →
      k + l ≤ w.length →
      V60SkeletonCompressionCertificate terminal binary k l tau A w)
    {z : Word Sigma}
    (hz : V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart z) :
    z.length ≤
      (Fintype.card (V60KeptState Obs terminal binary start) + 2) *
        V60WindowYieldBound (k + l) (Fintype.card N) tau + 1 := by
  exact v60_window_witness_bound_of_boundary_compression
    Obs terminal binary start epsilonStart
    k l (Fintype.card N) tau hr hObserver
    (v60_window_untyped_compression_of_skeleton_certificates
      terminal binary k l tau hr hCert)
    hz

end FixedHCFG
end LeanCfgProject
