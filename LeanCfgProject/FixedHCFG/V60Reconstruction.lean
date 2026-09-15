import LeanCfgProject.FixedHCFG.V60Kernel

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Yield-only reconstruction basis matching the v60 TCS manuscript.

Unlike the older `ReconstructionBasis`, this structure has no left/right
monoid-type annotations.  Its typed state carries only the yield type; the
outer contexts are concrete terminal words chosen for the witness set.
-/

structure V60ReconstructionBasis {Sigma : Type u} (Obs : Observer Sigma)
    (W : Type v) where
  terminal : W → Sigma → Prop
  binary : W → W → W → Prop
  startState : W → Prop
  hasEpsilon : Prop

  omega : W → Word Sigma
  leftCtx : W → Word Sigma
  rightCtx : W → Word Sigma
  yieldType : W → Obs.M

  witnessSet : Language Sigma

  omega_nonempty : ∀ X : W, omega X ≠ []
  omega_type : ∀ X : W, Obs.value (omega X) = yieldType X
  terminal_type : ∀ {X : W} {a : Sigma},
    terminal X a → Obs.value [a] = yieldType X
  binary_yield_type : ∀ {X Y Z : W},
    binary X Y Z → Obs.mul (yieldType Y) (yieldType Z) = yieldType X

  anchor_mem : ∀ X : W,
    leftCtx X ++ omega X ++ rightCtx X ∈ witnessSet
  terminal_observation_mem : ∀ {X : W} {a : Sigma},
    terminal X a → leftCtx X ++ [a] ++ rightCtx X ∈ witnessSet
  binary_observation_mem : ∀ {X Y Z : W},
    binary X Y Z →
      leftCtx X ++ omega Y ++ omega Z ++ rightCtx X ∈ witnessSet

  start_context : ∀ {X : W}, startState X →
    leftCtx X = [] ∧ rightCtx X = []
  epsilon_mem : hasEpsilon → ([] : Word Sigma) ∈ witnessSet

/-- Terminal derivations in the trimmed yield-only typed target grammar. -/
inductive V60BasisDerives {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W) :
    W → Word Sigma → Prop
  | terminal {X : W} {a : Sigma}
      (hrule : B.terminal X a) :
      V60BasisDerives B X [a]
  | binary {X Y Z : W} {x y : Word Sigma}
      (hrule : B.binary X Y Z)
      (left : V60BasisDerives B Y x)
      (right : V60BasisDerives B Z y) :
      V60BasisDerives B X (x ++ y)

/-- Language of the trimmed yield-only typed target grammar. -/
def V60BasisLanguage {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W) :
    Language Sigma :=
  fun w =>
    (w = [] ∧ B.hasEpsilon) ∨
      ∃ X : W, B.startState X ∧ V60BasisDerives B X w

private theorem append_ne_nil_left
    {Alpha : Type u} {x y : List Alpha} (hx : x ≠ []) : x ++ y ≠ [] := by
  intro hnil
  cases x with
  | nil => exact hx rfl
  | cons a as => simp at hnil

/-- Canonical anchor visibility in the exact v60 learner. -/
theorem v60_anchor_visible
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W)
    {K : Language Sigma} (hWK : B.witnessSet ⊆ K)
    (X : W) :
    VisibleV60 K
      { x := B.omega X, u := B.leftCtx X, v := B.rightCtx X } := by
  exact ⟨B.omega_nonempty X, hWK (B.anchor_mem X)⟩

/-- A terminal-rule witness exposes `[a:u_X,v_X]`. -/
theorem v60_terminal_observation_visible
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W)
    {K : Language Sigma} (hWK : B.witnessSet ⊆ K)
    {X : W} {a : Sigma} (hrule : B.terminal X a) :
    VisibleV60 K
      { x := [a], u := B.leftCtx X, v := B.rightCtx X } := by
  exact ⟨by simp, hWK (B.terminal_observation_mem hrule)⟩

/-- The binary-rule witness exposes the parent concatenation. -/
theorem v60_binary_parent_visible
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W)
    {K : Language Sigma} (hWK : B.witnessSet ⊆ K)
    {X Y Z : W} (hrule : B.binary X Y Z) :
    VisibleV60 K
      { x := B.omega Y ++ B.omega Z,
        u := B.leftCtx X,
        v := B.rightCtx X } := by
  constructor
  · exact append_ne_nil_left (B.omega_nonempty Y)
  · have hmem := hWK (B.binary_observation_mem hrule)
    simpa [List.append_assoc] using hmem

/-- The same binary witness exposes the left-child split configuration. -/
theorem v60_binary_left_visible
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W)
    {K : Language Sigma} (hWK : B.witnessSet ⊆ K)
    {X Y Z : W} (hrule : B.binary X Y Z) :
    VisibleV60 K
      { x := B.omega Y,
        u := B.leftCtx X,
        v := B.omega Z ++ B.rightCtx X } := by
  constructor
  · exact B.omega_nonempty Y
  · have hmem := hWK (B.binary_observation_mem hrule)
    simpa [List.append_assoc] using hmem

/-- The same binary witness exposes the right-child split configuration. -/
theorem v60_binary_right_visible
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W)
    {K : Language Sigma} (hWK : B.witnessSet ⊆ K)
    {X Y Z : W} (hrule : B.binary X Y Z) :
    VisibleV60 K
      { x := B.omega Z,
        u := B.leftCtx X ++ B.omega Y,
        v := B.rightCtx X } := by
  constructor
  · exact B.omega_nonempty Z
  · have hmem := hWK (B.binary_observation_mem hrule)
    simpa [List.append_assoc] using hmem

/-- R2 transports a derived yield between observed contexts of the same factor. -/
theorem v60_context_transport
    {Sigma : Type u} {Obs : Observer Sigma}
    {K : Language Sigma}
    {x u v u' v' w : Word Sigma}
    (hsrc : VisibleV60 K { x := x, u := u, v := v })
    (hdst : VisibleV60 K { x := x, u := u', v := v' })
    (hder : V60Derives Obs K { x := x, u := u', v := v' } w) :
    V60Derives Obs K { x := x, u := u, v := v } w := by
  exact V60Derives.contextTransport x u v u' v' w hsrc hdst hder

/-- R3 transports a derived yield between equal `h`-types in one context. -/
theorem v60_typed_substitution
    {Sigma : Type u} {Obs : Observer Sigma}
    {K : Language Sigma}
    {x x' u v w : Word Sigma}
    (hsrc : VisibleV60 K { x := x, u := u, v := v })
    (hdst : VisibleV60 K { x := x', u := u, v := v })
    (htype : Obs.value x = Obs.value x')
    (hder : V60Derives Obs K { x := x', u := u, v := v } w) :
    V60Derives Obs K { x := x, u := u, v := v } w := by
  exact V60Derives.typedSubstitution x x' u v w hsrc hdst htype hder

/--
The induction claim of v60 completeness.  A target derivation rooted at `X`
is simulated from the learner anchor `[omega(X):u_X,v_X]`.
-/
theorem v60_completeness_claim
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W)
    {K : Language Sigma} (hWK : B.witnessSet ⊆ K)
    {X : W} {w : Word Sigma}
    (d : V60BasisDerives B X w) :
    V60Derives Obs K
      { x := B.omega X, u := B.leftCtx X, v := B.rightCtx X } w := by
  induction d with
  | @terminal X a hrule =>
      have hAnchor := v60_anchor_visible B hWK X
      have hTerm := v60_terminal_observation_visible B hWK hrule
      have hTerminalDeriv : V60Derives Obs K
          { x := [a], u := B.leftCtx X, v := B.rightCtx X } [a] :=
        V60Derives.terminal a (B.leftCtx X) (B.rightCtx X) hTerm
      have htype : Obs.value (B.omega X) = Obs.value [a] :=
        (B.omega_type X).trans (B.terminal_type hrule).symm
      exact v60_typed_substitution hAnchor hTerm htype hTerminalDeriv
  | @binary X Y Z x y hrule left right ihLeft ihRight =>
      have hAnchorX := v60_anchor_visible B hWK X
      have hParent := v60_binary_parent_visible B hWK hrule
      have hLeftLocal := v60_binary_left_visible B hWK hrule
      have hRightLocal := v60_binary_right_visible B hWK hrule
      have hAnchorY := v60_anchor_visible B hWK Y
      have hAnchorZ := v60_anchor_visible B hWK Z
      have hLeftDeriv : V60Derives Obs K
          { x := B.omega Y,
            u := B.leftCtx X,
            v := B.omega Z ++ B.rightCtx X } x :=
        v60_context_transport hLeftLocal hAnchorY ihLeft
      have hRightDeriv : V60Derives Obs K
          { x := B.omega Z,
            u := B.leftCtx X ++ B.omega Y,
            v := B.rightCtx X } y :=
        v60_context_transport hRightLocal hAnchorZ ihRight
      have hSplit : V60Derives Obs K
          { x := B.omega Y ++ B.omega Z,
            u := B.leftCtx X,
            v := B.rightCtx X } (x ++ y) := by
        exact V60Derives.split
          (B.omega Y) (B.omega Z)
          (B.leftCtx X) (B.rightCtx X) x y
          hParent hLeftLocal hRightLocal hLeftDeriv hRightDeriv
      have hConcatType :
          Obs.value (B.omega Y ++ B.omega Z) = B.yieldType X := by
        calc
          Obs.value (B.omega Y ++ B.omega Z) =
              Obs.mul (Obs.value (B.omega Y)) (Obs.value (B.omega Z)) :=
            Obs.value_append (B.omega Y) (B.omega Z)
          _ = Obs.mul (B.yieldType Y) (B.yieldType Z) := by
            rw [B.omega_type Y, B.omega_type Z]
          _ = B.yieldType X := B.binary_yield_type hrule
      have htype :
          Obs.value (B.omega X) =
            Obs.value (B.omega Y ++ B.omega Z) :=
        (B.omega_type X).trans hConcatType.symm
      exact v60_typed_substitution hAnchorX hParent htype hSplit

/-- v60 completeness: the witness set suffices to reconstruct every target word. -/
theorem v60_completeness
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W)
    (K : Language Sigma)
    (hWK : B.witnessSet ⊆ K)
    {w : Word Sigma}
    (hw : V60BasisLanguage B w) :
    V60StartDerives Obs K w := by
  rcases hw with hEps | hNonempty
  · rcases hEps with ⟨rfl, hHasEps⟩
    exact V60StartDerives.epsilon (hWK (B.epsilon_mem hHasEps))
  · rcases hNonempty with ⟨X, hStart, hDeriv⟩
    have hClaim := v60_completeness_claim B hWK hDeriv
    rcases B.start_context hStart with ⟨hLeft, hRight⟩
    have hOmegaMem : B.omega X ∈ K := by
      have hAnchor := hWK (B.anchor_mem X)
      simpa [hLeft, hRight] using hAnchor
    have hRootDeriv :
        V60Derives Obs K { x := B.omega X, u := [], v := [] } w := by
      simpa [hLeft, hRight] using hClaim
    exact V60StartDerives.sample (B.omega X) w
      (B.omega_nonempty X) hOmegaMem hRootDeriv

/--
Exact reconstruction in the v60 nonempty-factor convention.
-/
theorem v60_exact_reconstruction
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : V60ReconstructionBasis Obs W)
    (K : Language Sigma)
    (hWK : B.witnessSet ⊆ K)
    (hKL : K ⊆ V60BasisLanguage B)
    (hSub : HSubstitutableV60 Obs (V60BasisLanguage B))
    (w : Word Sigma) :
    V60StartDerives Obs K w ↔ V60BasisLanguage B w := by
  constructor
  · intro hLearn
    exact v60_start_soundness Obs K (V60BasisLanguage B) hKL hSub hLearn
  · intro hTarget
    exact v60_completeness B K hWK hTarget

end FixedHCFG
end LeanCfgProject
