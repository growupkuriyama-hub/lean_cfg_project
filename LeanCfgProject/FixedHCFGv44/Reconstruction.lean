import LeanCfgProject.FixedHCFGv44.Soundness

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/--
Abstract interface for the canonical positive witnesses used by the v44
completeness proof.  Unlike the pre-revision basis, only yield types remain.
-/
structure ReconstructionBasis {Sigma : Type u} (Obs : Observer Sigma)
    (W : Type v) where
  terminal : W → Sigma → Prop
  binary : W → W → W → Prop
  startState : W → Prop
  hasEpsilon : Prop

  omega : W → Word Sigma
  leftCtx : W → Word Sigma
  rightCtx : W → Word Sigma
  yieldType : W → Obs.M

  CS : Language Sigma

  omega_type : ∀ X : W, obsValue Obs (omega X) = yieldType X
  omega_internal : ∀ X : W, Internal (omega X)

  terminal_type : ∀ {X : W} {a : Sigma},
    terminal X a → obsValue Obs [a] = yieldType X
  binary_yield_type : ∀ {X Y Z : W},
    binary X Y Z → Obs.mul (yieldType Y) (yieldType Z) = yieldType X

  anchor_mem : ∀ X : W,
    leftCtx X ++ omega X ++ rightCtx X ∈ CS
  terminal_observation_mem : ∀ {X : W} {a : Sigma},
    terminal X a → leftCtx X ++ [a] ++ rightCtx X ∈ CS
  binary_observation_mem : ∀ {X Y Z : W},
    binary X Y Z →
      leftCtx X ++ omega Y ++ omega Z ++ rightCtx X ∈ CS

  start_context : ∀ {X : W}, startState X →
    leftCtx X = [] ∧ rightCtx X = []
  epsilon_mem : hasEpsilon → ([] : Word Sigma) ∈ CS

/-- Terminal derivations represented by a reconstruction basis. -/
inductive BasisDerives {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W) :
    W → Word Sigma → Prop
  | terminal {X : W} {a : Sigma}
      (hrule : B.terminal X a) :
      BasisDerives B X [a]
  | binary {X Y Z : W} {x y : Word Sigma}
      (hrule : B.binary X Y Z)
      (left : BasisDerives B Y x)
      (right : BasisDerives B Z y) :
      BasisDerives B X (x ++ y)

/-- Language represented by the typed witness basis. -/
def BasisLanguage {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W) : Language Sigma :=
  fun w =>
    (w = [] ∧ B.hasEpsilon) ∨
      ∃ X : W, B.startState X ∧ BasisDerives B X w

/-- A nonempty word remains nonempty after appending anything to its right. -/
theorem internal_append_left {Sigma : Type u} {x y : Word Sigma}
    (hx : Internal x) : Internal (x ++ y) := by
  cases x with
  | nil => exact (hx rfl).elim
  | cons a xs => simp [Internal]

/-- The canonical anchor is visible in every sample containing the witness set. -/
theorem anchor_visible
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    (X : W) :
    Visible K { x := B.omega X, u := B.leftCtx X, v := B.rightCtx X } := by
  exact hCSK (B.anchor_mem X)

/-- A terminal rule witness exposes its one-letter factor. -/
theorem terminal_observation_visible
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X : W} {a : Sigma} (hrule : B.terminal X a) :
    Visible K { x := [a], u := B.leftCtx X, v := B.rightCtx X } := by
  exact hCSK (B.terminal_observation_mem hrule)

/-- A binary rule witness exposes the concatenated canonical child yields. -/
theorem binary_parent_visible
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X Y Z : W} (hrule : B.binary X Y Z) :
    Visible K
      { x := B.omega Y ++ B.omega Z,
        u := B.leftCtx X, v := B.rightCtx X } := by
  have hmem := hCSK (B.binary_observation_mem hrule)
  simpa [Visible, List.append_assoc] using hmem

/-- The binary witness exposes the left child in its rule-local context. -/
theorem binary_left_visible
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X Y Z : W} (hrule : B.binary X Y Z) :
    Visible K
      { x := B.omega Y,
        u := B.leftCtx X,
        v := B.omega Z ++ B.rightCtx X } := by
  have hmem := hCSK (B.binary_observation_mem hrule)
  simpa [Visible, List.append_assoc] using hmem

/-- The binary witness exposes the right child in its rule-local context. -/
theorem binary_right_visible
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X Y Z : W} (hrule : B.binary X Y Z) :
    Visible K
      { x := B.omega Z,
        u := B.leftCtx X ++ B.omega Y,
        v := B.rightCtx X } := by
  have hmem := hCSK (B.binary_observation_mem hrule)
  simpa [Visible, List.append_assoc] using hmem

/--
The induction claim of v44 completeness: every basis derivation can be
simulated from the canonical learner nonterminal of its root state.
-/
theorem completeness_claim
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X : W} {w : Word Sigma}
    (d : BasisDerives B X w) :
    Derives Obs K
      { x := B.omega X, u := B.leftCtx X, v := B.rightCtx X } w := by
  induction d with
  | @terminal X a hrule =>
      have hAnchor := anchor_visible B hCSK X
      have hTerm := terminal_observation_visible B hCSK hrule
      have hTerminalDeriv :
          Derives Obs K
            { x := [a], u := B.leftCtx X, v := B.rightCtx X } [a] :=
        Derives.terminal (Obs := Obs) (K := K)
          a (B.leftCtx X) (B.rightCtx X) hTerm
      have htype : obsValue Obs (B.omega X) = obsValue Obs [a] :=
        (B.omega_type X).trans (B.terminal_type hrule).symm
      exact Derives.typedSubstitution (Obs := Obs) (K := K)
        (x := B.omega X) (x' := [a])
        (u := B.leftCtx X) (v := B.rightCtx X) (w := [a])
        (B.omega_internal X) (by simp [Internal])
        hAnchor hTerm htype hTerminalDeriv
  | @binary X Y Z x y hrule left right ihLeft ihRight =>
      have hAnchorX := anchor_visible B hCSK X
      have hParent := binary_parent_visible B hCSK hrule
      have hLeftLocal := binary_left_visible B hCSK hrule
      have hRightLocal := binary_right_visible B hCSK hrule
      have hAnchorY := anchor_visible B hCSK Y
      have hAnchorZ := anchor_visible B hCSK Z
      have hLeftDeriv : Derives Obs K
          { x := B.omega Y,
            u := B.leftCtx X,
            v := B.omega Z ++ B.rightCtx X } x :=
        Derives.contextTransport (Obs := Obs) (K := K)
          (x := B.omega Y)
          (u := B.leftCtx X) (v := B.omega Z ++ B.rightCtx X)
          (u' := B.leftCtx Y) (v' := B.rightCtx Y) (w := x)
          (B.omega_internal Y) hLeftLocal hAnchorY ihLeft
      have hRightDeriv : Derives Obs K
          { x := B.omega Z,
            u := B.leftCtx X ++ B.omega Y,
            v := B.rightCtx X } y :=
        Derives.contextTransport (Obs := Obs) (K := K)
          (x := B.omega Z)
          (u := B.leftCtx X ++ B.omega Y) (v := B.rightCtx X)
          (u' := B.leftCtx Z) (v' := B.rightCtx Z) (w := y)
          (B.omega_internal Z) hRightLocal hAnchorZ ihRight
      have hSplit : Derives Obs K
          { x := B.omega Y ++ B.omega Z,
            u := B.leftCtx X,
            v := B.rightCtx X } (x ++ y) :=
        Derives.split (Obs := Obs) (K := K)
          (x := B.omega Y) (y := B.omega Z)
          (u := B.leftCtx X) (v := B.rightCtx X)
          (w₁ := x) (w₂ := y)
          (B.omega_internal Y) (B.omega_internal Z)
          hParent hLeftLocal hRightLocal hLeftDeriv hRightDeriv
      have hConcatType :
          obsValue Obs (B.omega Y ++ B.omega Z) = B.yieldType X := by
        calc
          obsValue Obs (B.omega Y ++ B.omega Z) =
              Obs.mul (obsValue Obs (B.omega Y)) (obsValue Obs (B.omega Z)) :=
            obsValue_append Obs (B.omega Y) (B.omega Z)
          _ = Obs.mul (B.yieldType Y) (B.yieldType Z) := by
            rw [B.omega_type Y, B.omega_type Z]
          _ = B.yieldType X := B.binary_yield_type hrule
      have htype :
          obsValue Obs (B.omega X) =
            obsValue Obs (B.omega Y ++ B.omega Z) :=
        (B.omega_type X).trans hConcatType.symm
      have hConcatInternal : Internal (B.omega Y ++ B.omega Z) :=
        internal_append_left (B.omega_internal Y)
      exact Derives.typedSubstitution (Obs := Obs) (K := K)
        (x := B.omega X) (x' := B.omega Y ++ B.omega Z)
        (u := B.leftCtx X) (v := B.rightCtx X) (w := x ++ y)
        (B.omega_internal X) hConcatInternal
        hAnchorX hParent htype hSplit

/--
v44 completeness from finite witnesses.  Finiteness and `K ⊆ L` are not
needed for this combinatorial inclusion; only `CS ⊆ K` is used.
-/
theorem theorem_completeness
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    (K : Language Sigma)
    (hCSK : B.CS ⊆ K) :
    BasisLanguage B ⊆ HypLanguage Obs K := by
  intro w hw
  rcases hw with hEps | hNonempty
  · rcases hEps with ⟨rfl, hHasEps⟩
    exact StartDerives.epsilon (Obs := Obs) (K := K)
      (hCSK (B.epsilon_mem hHasEps))
  · rcases hNonempty with ⟨X, hStart, hDeriv⟩
    have hClaim := completeness_claim B hCSK hDeriv
    rcases B.start_context hStart with ⟨hLeft, hRight⟩
    have hOmegaMem : B.omega X ∈ K := by
      have hAnchor := hCSK (B.anchor_mem X)
      simpa [hLeft, hRight] using hAnchor
    have hRootDeriv :
        Derives Obs K { x := B.omega X, u := [], v := [] } w := by
      simpa [hLeft, hRight] using hClaim
    exact StartDerives.sample (Obs := Obs) (K := K)
      (x := B.omega X) (w := w)
      (B.omega_internal X) hOmegaMem hRootDeriv

/-- v44 exact finite-sample reconstruction at the witness-basis interface. -/
theorem theorem_exact_reconstruction
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    (K : Language Sigma)
    (hCSK : B.CS ⊆ K)
    (hKL : K ⊆ BasisLanguage B)
    (hSub : HSubstitutable Obs (BasisLanguage B)) :
    HypLanguage Obs K = BasisLanguage B := by
  apply Set.Subset.antisymm
  · exact theorem_soundness Obs K (BasisLanguage B) hKL hSub
  · exact theorem_completeness B K hCSK

end FixedHCFGv44
end LeanCfgProject
