import LeanCfgProject.FixedHCFG.Soundness
import LeanCfgProject.FixedHCFG.LinearDerivation

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Theorem-facing reconstruction basis for Section 7.

This is the strict-linear analogue of `ReconstructionBasis`.  It packages
exactly the canonical anchors and rule-evidence words used by `CS_lin(H)` and
proves the core of manuscript Lemma 7.8 directly with learner Rules (1)--(5).
-/

structure LinearReconstructionBasis {Sigma : Type u}
    (Obs : Observer Sigma) (W : Type v) where
  terminal : W → Sigma → Prop
  leftRule : W → Sigma → W → Prop
  rightRule : W → W → Sigma → Prop
  startState : W → Prop
  hasEpsilon : Prop

  omega : W → Word Sigma
  leftCtx : W → Word Sigma
  rightCtx : W → Word Sigma
  yieldType : W → Obs.M

  CS : Language Sigma

  omega_type : ∀ X : W, Obs.value (omega X) = yieldType X
  terminal_type : ∀ {X : W} {a : Sigma},
    terminal X a → Obs.value [a] = yieldType X
  left_rule_type : ∀ {X Y : W} {a : Sigma},
    leftRule X a Y →
      Obs.mul (Obs.value [a]) (yieldType Y) = yieldType X
  right_rule_type : ∀ {X Y : W} {a : Sigma},
    rightRule X Y a →
      Obs.mul (yieldType Y) (Obs.value [a]) = yieldType X

  anchor_mem : ∀ X : W,
    leftCtx X ++ omega X ++ rightCtx X ∈ CS
  terminal_observation_mem : ∀ {X : W} {a : Sigma},
    terminal X a → leftCtx X ++ [a] ++ rightCtx X ∈ CS
  left_observation_mem : ∀ {X Y : W} {a : Sigma},
    leftRule X a Y →
      leftCtx X ++ [a] ++ omega Y ++ rightCtx X ∈ CS
  right_observation_mem : ∀ {X Y : W} {a : Sigma},
    rightRule X Y a →
      leftCtx X ++ omega Y ++ [a] ++ rightCtx X ∈ CS

  start_context : ∀ {X : W}, startState X →
    leftCtx X = [] ∧ rightCtx X = []
  epsilon_mem : hasEpsilon → ([] : Word Sigma) ∈ CS

/-- Strict-linear target derivations represented by a reconstruction basis. -/
inductive LinearBasisDerives {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : LinearReconstructionBasis Obs W) :
    W → Word Sigma → Prop
  | terminal {X : W} {a : Sigma}
      (hrule : B.terminal X a) :
      LinearBasisDerives B X [a]
  | left {X Y : W} {a : Sigma} {w : Word Sigma}
      (hrule : B.leftRule X a Y)
      (child : LinearBasisDerives B Y w) :
      LinearBasisDerives B X ([a] ++ w)
  | right {X Y : W} {a : Sigma} {w : Word Sigma}
      (hrule : B.rightRule X Y a)
      (child : LinearBasisDerives B Y w) :
      LinearBasisDerives B X (w ++ [a])

/-- Language represented by the strict-linear reconstruction basis. -/
def LinearBasisLanguage {Sigma : Type u} {W : Type v}
    {Obs : Observer Sigma} (B : LinearReconstructionBasis Obs W) :
    Language Sigma :=
  fun w =>
    (w = [] ∧ B.hasEpsilon) ∨
      ∃ X : W, B.startState X ∧ LinearBasisDerives B X w

/-- Canonical anchor visibility. -/
theorem linear_anchor_visible
    {Sigma : Type u} {W : Type v} {Obs : Observer Sigma}
    (B : LinearReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K) (X : W) :
    Visible K { x := B.omega X, u := B.leftCtx X, v := B.rightCtx X } := by
  exact hCSK (B.anchor_mem X)

/-- Terminal-rule evidence visibility. -/
theorem linear_terminal_visible
    {Sigma : Type u} {W : Type v} {Obs : Observer Sigma}
    (B : LinearReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X : W} {a : Sigma} (hrule : B.terminal X a) :
    Visible K { x := [a], u := B.leftCtx X, v := B.rightCtx X } := by
  exact hCSK (B.terminal_observation_mem hrule)

/-- `X -> aY`: the whole rule witness is visible as one learner nonterminal. -/
theorem linear_left_parent_visible
    {Sigma : Type u} {W : Type v} {Obs : Observer Sigma}
    (B : LinearReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X Y : W} {a : Sigma} (hrule : B.leftRule X a Y) :
    Visible K
      { x := [a] ++ B.omega Y, u := B.leftCtx X, v := B.rightCtx X } := by
  have h := hCSK (B.left_observation_mem hrule)
  simpa [Visible, List.append_assoc] using h

/-- `X -> aY`: the explicit terminal factor is visible locally. -/
theorem linear_left_terminal_visible
    {Sigma : Type u} {W : Type v} {Obs : Observer Sigma}
    (B : LinearReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X Y : W} {a : Sigma} (hrule : B.leftRule X a Y) :
    Visible K
      { x := [a], u := B.leftCtx X,
        v := B.omega Y ++ B.rightCtx X } := by
  have h := hCSK (B.left_observation_mem hrule)
  simpa [Visible, List.append_assoc] using h

/-- `X -> aY`: the child canonical yield is visible in its rule-local context. -/
theorem linear_left_child_visible
    {Sigma : Type u} {W : Type v} {Obs : Observer Sigma}
    (B : LinearReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X Y : W} {a : Sigma} (hrule : B.leftRule X a Y) :
    Visible K
      { x := B.omega Y, u := B.leftCtx X ++ [a], v := B.rightCtx X } := by
  have h := hCSK (B.left_observation_mem hrule)
  simpa [Visible, List.append_assoc] using h

/-- `X -> Ya`: the whole rule witness is visible. -/
theorem linear_right_parent_visible
    {Sigma : Type u} {W : Type v} {Obs : Observer Sigma}
    (B : LinearReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X Y : W} {a : Sigma} (hrule : B.rightRule X Y a) :
    Visible K
      { x := B.omega Y ++ [a], u := B.leftCtx X, v := B.rightCtx X } := by
  have h := hCSK (B.right_observation_mem hrule)
  simpa [Visible, List.append_assoc] using h

/-- `X -> Ya`: the child canonical yield is visible in its rule-local context. -/
theorem linear_right_child_visible
    {Sigma : Type u} {W : Type v} {Obs : Observer Sigma}
    (B : LinearReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X Y : W} {a : Sigma} (hrule : B.rightRule X Y a) :
    Visible K
      { x := B.omega Y, u := B.leftCtx X,
        v := [a] ++ B.rightCtx X } := by
  have h := hCSK (B.right_observation_mem hrule)
  simpa [Visible, List.append_assoc] using h

/-- `X -> Ya`: the explicit terminal factor is visible locally. -/
theorem linear_right_terminal_visible
    {Sigma : Type u} {W : Type v} {Obs : Observer Sigma}
    (B : LinearReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X Y : W} {a : Sigma} (hrule : B.rightRule X Y a) :
    Visible K
      { x := [a], u := B.leftCtx X ++ B.omega Y, v := B.rightCtx X } := by
  have h := hCSK (B.right_observation_mem hrule)
  simpa [Visible, List.append_assoc] using h

/--
Core completeness induction for Lemma 7.8: every strict-linear target
spine is simulated from its canonical learner nonterminal.
-/
theorem lemma_7_8_completeness_claim
    {Sigma : Type u} {W : Type v} {Obs : Observer Sigma}
    (B : LinearReconstructionBasis Obs W)
    {K : Language Sigma} (hCSK : B.CS ⊆ K)
    {X : W} {w : Word Sigma}
    (d : LinearBasisDerives B X w) :
    Derives Obs K
      { x := B.omega X, u := B.leftCtx X, v := B.rightCtx X } w := by
  induction d with
  | @terminal X a hrule =>
      have hAnchor := linear_anchor_visible B hCSK X
      have hTerm := linear_terminal_visible B hCSK hrule
      have hTermDeriv : Derives Obs K
          { x := [a], u := B.leftCtx X, v := B.rightCtx X } [a] :=
        Derives.terminal a (B.leftCtx X) (B.rightCtx X) hTerm
      have htype : Obs.value (B.omega X) = Obs.value [a] :=
        (B.omega_type X).trans (B.terminal_type hrule).symm
      exact Derives.typedSubstitution
        (B.omega X) [a] (B.leftCtx X) (B.rightCtx X) [a]
        hAnchor hTerm htype hTermDeriv
  | @left X Y a w hrule child ih =>
      have hAnchorX := linear_anchor_visible B hCSK X
      have hAnchorY := linear_anchor_visible B hCSK Y
      have hParent := linear_left_parent_visible B hCSK hrule
      have hTerm := linear_left_terminal_visible B hCSK hrule
      have hChildLocal := linear_left_child_visible B hCSK hrule
      have hChildDeriv : Derives Obs K
          { x := B.omega Y, u := B.leftCtx X ++ [a], v := B.rightCtx X } w :=
        Derives.contextTransport
          (B.omega Y) (B.leftCtx X ++ [a]) (B.rightCtx X)
          (B.leftCtx Y) (B.rightCtx Y) w
          hChildLocal hAnchorY ih
      have hTermDeriv : Derives Obs K
          { x := [a], u := B.leftCtx X,
            v := B.omega Y ++ B.rightCtx X } [a] :=
        Derives.terminal a (B.leftCtx X)
          (B.omega Y ++ B.rightCtx X) hTerm
      have hSplit : Derives Obs K
          { x := [a] ++ B.omega Y,
            u := B.leftCtx X, v := B.rightCtx X } ([a] ++ w) := by
        exact Derives.split
          [a] (B.omega Y) (B.leftCtx X) (B.rightCtx X)
          [a] w hParent hTerm hChildLocal hTermDeriv hChildDeriv
      have hRuleType :
          Obs.value ([a] ++ B.omega Y) = B.yieldType X := by
        calc
          Obs.value ([a] ++ B.omega Y) =
              Obs.mul (Obs.value [a]) (Obs.value (B.omega Y)) :=
            Obs.value_append [a] (B.omega Y)
          _ = Obs.mul (Obs.value [a]) (B.yieldType Y) := by
            rw [B.omega_type Y]
          _ = B.yieldType X := B.left_rule_type hrule
      have htype :
          Obs.value (B.omega X) = Obs.value ([a] ++ B.omega Y) :=
        (B.omega_type X).trans hRuleType.symm
      exact Derives.typedSubstitution
        (B.omega X) ([a] ++ B.omega Y)
        (B.leftCtx X) (B.rightCtx X) ([a] ++ w)
        hAnchorX hParent htype hSplit
  | @right X Y a w hrule child ih =>
      have hAnchorX := linear_anchor_visible B hCSK X
      have hAnchorY := linear_anchor_visible B hCSK Y
      have hParent := linear_right_parent_visible B hCSK hrule
      have hChildLocal := linear_right_child_visible B hCSK hrule
      have hTerm := linear_right_terminal_visible B hCSK hrule
      have hChildDeriv : Derives Obs K
          { x := B.omega Y, u := B.leftCtx X,
            v := [a] ++ B.rightCtx X } w :=
        Derives.contextTransport
          (B.omega Y) (B.leftCtx X) ([a] ++ B.rightCtx X)
          (B.leftCtx Y) (B.rightCtx Y) w
          hChildLocal hAnchorY ih
      have hTermDeriv : Derives Obs K
          { x := [a], u := B.leftCtx X ++ B.omega Y,
            v := B.rightCtx X } [a] :=
        Derives.terminal a (B.leftCtx X ++ B.omega Y)
          (B.rightCtx X) hTerm
      have hSplit : Derives Obs K
          { x := B.omega Y ++ [a],
            u := B.leftCtx X, v := B.rightCtx X } (w ++ [a]) := by
        exact Derives.split
          (B.omega Y) [a] (B.leftCtx X) (B.rightCtx X)
          w [a] hParent hChildLocal hTerm hChildDeriv hTermDeriv
      have hRuleType :
          Obs.value (B.omega Y ++ [a]) = B.yieldType X := by
        calc
          Obs.value (B.omega Y ++ [a]) =
              Obs.mul (Obs.value (B.omega Y)) (Obs.value [a]) :=
            Obs.value_append (B.omega Y) [a]
          _ = Obs.mul (B.yieldType Y) (Obs.value [a]) := by
            rw [B.omega_type Y]
          _ = B.yieldType X := B.right_rule_type hrule
      have htype :
          Obs.value (B.omega X) = Obs.value (B.omega Y ++ [a]) :=
        (B.omega_type X).trans hRuleType.symm
      exact Derives.typedSubstitution
        (B.omega X) (B.omega Y ++ [a])
        (B.leftCtx X) (B.rightCtx X) (w ++ [a])
        hAnchorX hParent htype hSplit

/-- Completeness half of manuscript Lemma 7.8. -/
theorem lemma_7_8_completeness
    {Sigma : Type u} {W : Type v} {Obs : Observer Sigma}
    (B : LinearReconstructionBasis Obs W)
    (K : Language Sigma) (hCSK : B.CS ⊆ K)
    {w : Word Sigma} (hw : LinearBasisLanguage B w) :
    StartDerives Obs K w := by
  rcases hw with hEps | hNonempty
  · rcases hEps with ⟨rfl, hHasEps⟩
    exact StartDerives.epsilon (hCSK (B.epsilon_mem hHasEps))
  · rcases hNonempty with ⟨X, hStart, hDeriv⟩
    have hClaim := lemma_7_8_completeness_claim B hCSK hDeriv
    rcases B.start_context hStart with ⟨hLeft, hRight⟩
    have hOmegaMem : B.omega X ∈ K := by
      have hAnchor := hCSK (B.anchor_mem X)
      simpa [hLeft, hRight] using hAnchor
    have hRootDeriv :
        Derives Obs K { x := B.omega X, u := [], v := [] } w := by
      simpa [hLeft, hRight] using hClaim
    exact StartDerives.sample (B.omega X) w hOmegaMem hRootDeriv

/--
Manuscript Lemma 7.8 at the strict-linear reconstruction-basis interface.
Soundness is exactly Theorem 5.6; completeness is the spine simulation above.
-/
theorem lemma_7_8_exact_reconstruction
    {Sigma : Type u} {W : Type v} {Obs : Observer Sigma}
    (B : LinearReconstructionBasis Obs W)
    (K : Language Sigma)
    (hCSK : B.CS ⊆ K)
    (hKL : K ⊆ LinearBasisLanguage B)
    (hSub : HSubstitutable Obs (LinearBasisLanguage B))
    (w : Word Sigma) :
    StartDerives Obs K w ↔ LinearBasisLanguage B w := by
  constructor
  · intro hLearn
    exact theorem_5_6_soundness Obs K (LinearBasisLanguage B) hKL hSub hLearn
  · intro hTarget
    exact lemma_7_8_completeness B K hCSK hTarget

end FixedHCFG
end LeanCfgProject
