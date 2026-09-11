import LeanCfgProject.FixedHCFG.CanonicalWitness
import LeanCfgProject.FixedHCFG.Soundness

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/--
Abstract finite typed reconstruction basis from Sections 4.3--4.4.

This packages exactly the data used by the reconstruction proof: canonical
terminal yields `omega`, canonical two-sided contexts, typed rule equations,
start states, and the observation set `CS`.  The fields `anchor_mem`,
`terminal_observation_mem`, and `binary_observation_mem` are the proof-facing
content of Lemmas 4.7--4.8 / Theorem 4.12.
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
  leftType : W → Obs.M
  rightType : W → Obs.M

  CS : Language Sigma

  omega_type : ∀ X : W, Obs.value (omega X) = yieldType X
  left_context_type : ∀ X : W, Obs.value (leftCtx X) = leftType X
  right_context_type : ∀ X : W, Obs.value (rightCtx X) = rightType X

  terminal_type : ∀ {X : W} {a : Sigma},
    terminal X a → Obs.value [a] = yieldType X
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

/-- Terminal derivations of the trimmed typed basis after forgetting annotations. -/
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

/-- Language represented by the typed reconstruction basis. -/
def BasisLanguage {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W) :
    Language Sigma :=
  fun w =>
    (w = [] ∧ B.hasEpsilon) ∨
      ∃ X : W, B.startState X ∧ BasisDerives B X w

/-- The canonical anchor for a basis state is visible in every sample containing `CS`. -/
theorem anchor_visible
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    (X : W) :
    Visible K
      { x := B.omega X, u := B.leftCtx X, v := B.rightCtx X } := by
  exact hCSK (B.anchor_mem X)

/-- The terminal rule observation for `X → a` is visible in the learner. -/
theorem terminal_observation_visible
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X : W} {a : Sigma} (hrule : B.terminal X a) :
    Visible K
      { x := [a], u := B.leftCtx X, v := B.rightCtx X } := by
  exact hCSK (B.terminal_observation_mem hrule)

/-- The binary rule observation exposes the parent concatenation. -/
theorem binary_parent_visible
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X Y Z : W} (hrule : B.binary X Y Z) :
    Visible K
      { x := B.omega Y ++ B.omega Z,
        u := B.leftCtx X,
        v := B.rightCtx X } := by
  have hmem := hCSK (B.binary_observation_mem hrule)
  simpa [Visible, List.append_assoc] using hmem

/-- The same binary observation exposes the left child local configuration. -/
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

/-- The same binary observation exposes the right child local configuration. -/
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
Terminal part of Lemma 5.2 in the form actually needed for reconstruction.

For an arbitrary realized terminal rule `X → a`, the observation set exposes
both the anchor `[omega(X):u_X,v_X]` and `[a:u_X,v_X]`, and the latter has the
Rule-(4) terminal production.  This formulation does not assume
`omega(X) = [a]`.
-/
theorem lemma_5_2_terminal_local_realization
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X : W} {a : Sigma} (hrule : B.terminal X a) :
    Visible K
      { x := B.omega X, u := B.leftCtx X, v := B.rightCtx X } ∧
    Visible K
      { x := [a], u := B.leftCtx X, v := B.rightCtx X } ∧
    Derives Obs K
      { x := [a], u := B.leftCtx X, v := B.rightCtx X } [a] := by
  have hAnchor := anchor_visible B hCSK X
  have hTerm := terminal_observation_visible B hCSK hrule
  exact ⟨hAnchor, hTerm, Derives.terminal a (B.leftCtx X) (B.rightCtx X) hTerm⟩

/-- Lemma 5.2(ii): all four local configurations of a realized binary rule are visible. -/
theorem lemma_5_2_binary_local_realization
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X Y Z : W} (hrule : B.binary X Y Z) :
    Visible K
      { x := B.omega X, u := B.leftCtx X, v := B.rightCtx X } ∧
    Visible K
      { x := B.omega Y ++ B.omega Z,
        u := B.leftCtx X, v := B.rightCtx X } ∧
    Visible K
      { x := B.omega Y,
        u := B.leftCtx X, v := B.omega Z ++ B.rightCtx X } ∧
    Visible K
      { x := B.omega Z,
        u := B.leftCtx X ++ B.omega Y, v := B.rightCtx X } := by
  exact ⟨anchor_visible B hCSK X,
    binary_parent_visible B hCSK hrule,
    binary_left_visible B hCSK hrule,
    binary_right_visible B hCSK hrule⟩

/-- Lemma 5.3, continuation form: Rule (2) transports a derivation across outer contexts. -/
theorem lemma_5_3_transport
    {Sigma : Type u} {Obs : Observer Sigma}
    {K : Language Sigma}
    {x u v u' v' w : Word Sigma}
    (hsrc : Visible K { x := x, u := u, v := v })
    (hdst : Visible K { x := x, u := u', v := v' })
    (hder : Derives Obs K { x := x, u := u', v := v' } w) :
    Derives Obs K { x := x, u := u, v := v } w := by
  exact Derives.contextTransport x u v u' v' w hsrc hdst hder

/-- Lemma 5.4, continuation form: Rule (3) substitutes equal `h`-types in one context. -/
theorem lemma_5_4_substitution
    {Sigma : Type u} {Obs : Observer Sigma}
    {K : Language Sigma}
    {x x' u v w : Word Sigma}
    (hsrc : Visible K { x := x, u := u, v := v })
    (hdst : Visible K { x := x', u := u, v := v })
    (htype : Obs.value x = Obs.value x')
    (hder : Derives Obs K { x := x', u := u, v := v } w) :
    Derives Obs K { x := x, u := u, v := v } w := by
  exact Derives.typedSubstitution x x' u v w hsrc hdst htype hder

/--
The induction claim in Theorem 5.5: every basis derivation can be simulated
from the canonical learner nonterminal of its root state.
-/
theorem theorem_5_5_claim
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X : W} {w : Word Sigma}
    (d : BasisDerives B X w) :
    Derives Obs K
      { x := B.omega X, u := B.leftCtx X, v := B.rightCtx X } w := by
  induction d with
  | @terminal X a hrule =>
      have hlocal := lemma_5_2_terminal_local_realization B hCSK hrule
      rcases hlocal with ⟨hAnchor, hTerm, hTerminalDeriv⟩
      have htype : Obs.value (B.omega X) = Obs.value [a] := by
        exact (B.omega_type X).trans (B.terminal_type hrule).symm
      exact lemma_5_4_substitution hAnchor hTerm htype hTerminalDeriv
  | @binary X Y Z x y hrule left right ihLeft ihRight =>
      have hlocal := lemma_5_2_binary_local_realization B hCSK hrule
      rcases hlocal with ⟨hAnchorX, hParent, hLeftLocal, hRightLocal⟩
      have hAnchorY := anchor_visible B hCSK Y
      have hAnchorZ := anchor_visible B hCSK Z
      have hLeftDeriv : Derives Obs K
          { x := B.omega Y,
            u := B.leftCtx X,
            v := B.omega Z ++ B.rightCtx X } x :=
        lemma_5_3_transport hLeftLocal hAnchorY ihLeft
      have hRightDeriv : Derives Obs K
          { x := B.omega Z,
            u := B.leftCtx X ++ B.omega Y,
            v := B.rightCtx X } y :=
        lemma_5_3_transport hRightLocal hAnchorZ ihRight
      have hSplit : Derives Obs K
          { x := B.omega Y ++ B.omega Z,
            u := B.leftCtx X,
            v := B.rightCtx X } (x ++ y) := by
        exact Derives.split
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
      exact lemma_5_4_substitution hAnchorX hParent htype hSplit

/--
Theorem 5.5 (completeness), at the reconstruction-basis interface.

The paper assumes `K` finite and `K ⊆ L`; neither condition is needed for this
inclusion.  Only exposure of the characteristic sample, `CS ⊆ K`, is used.
-/
theorem theorem_5_5_completeness
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    (K : Language Sigma)
    (hCSK : B.CS ⊆ K)
    {w : Word Sigma}
    (hw : BasisLanguage B w) :
    StartDerives Obs K w := by
  rcases hw with hEps | hNonempty
  · rcases hEps with ⟨rfl, hHasEps⟩
    exact StartDerives.epsilon (hCSK (B.epsilon_mem hHasEps))
  · rcases hNonempty with ⟨X, hStart, hDeriv⟩
    have hClaim := theorem_5_5_claim B hCSK hDeriv
    rcases B.start_context hStart with ⟨hLeft, hRight⟩
    have hOmegaMem : B.omega X ∈ K := by
      have hAnchor := hCSK (B.anchor_mem X)
      simpa [hLeft, hRight] using hAnchor
    have hRootDeriv :
        Derives Obs K { x := B.omega X, u := [], v := [] } w := by
      simpa [hLeft, hRight] using hClaim
    exact StartDerives.sample (B.omega X) w hOmegaMem hRootDeriv

/--
Theorem 5.7 at the reconstruction-basis interface: completeness (Theorem 5.5)
and soundness (Theorem 5.6) give exact reconstruction.
-/
theorem theorem_5_7_exact_reconstruction
    {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : ReconstructionBasis Obs W)
    (K : Language Sigma)
    (hCSK : B.CS ⊆ K)
    (hKL : K ⊆ BasisLanguage B)
    (hSub : HSubstitutable Obs (BasisLanguage B))
    (w : Word Sigma) :
    StartDerives Obs K w ↔ BasisLanguage B w := by
  constructor
  · intro hLearn
    exact theorem_5_6_soundness Obs K (BasisLanguage B) hKL hSub hLearn
  · intro hTarget
    exact theorem_5_5_completeness B K hCSK hTarget

end FixedHCFG
end LeanCfgProject
