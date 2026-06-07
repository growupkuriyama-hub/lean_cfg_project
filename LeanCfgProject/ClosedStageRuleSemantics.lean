import LeanCfgProject.ClosedStageConceptStability

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/-
Closed-stage rule semantics.

This "attack" layer complements the concept-level stability theorems by proving
that, after a closed saturation stage, the raw later stages themselves satisfy
the terminal and binary rule inclusions.  It gives the algorithmic reading:

  once a stage is closed, every later stage is a rule-closed semantic solution,
  and hence its concept closure is the corresponding closed-stage concept
  semantics.

This is useful for the paper because it phrases closed-stage saturation as a
finite semantic model of the carrier terminal/binary rules.
-/

/--
At a closed carrier saturation stage, all terminal insertions are already
present in that stage.
-/
theorem carrier_terminalImage_subset_closedStage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N))
    (X : W) :
    CarrierTerminalImage q H profile R X ⊆
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X := by
  intro a ha
  exact hClosed X (Or.inr (Or.inl ha))

/--
After a closed carrier saturation stage, all later stages still contain all
terminal insertions.
-/
theorem carrier_terminalImage_subset_laterClosedStage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N k : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N))
    (X : W) :
    CarrierTerminalImage q H profile R X ⊆
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + k) X := by
  intro a ha
  have hN := carrier_terminalImage_subset_closedStage
    q H profile R N hClosed X ha
  have hEq :=
    carrierSaturationIter_eq_closed_stage_add
      q H profile R N k hClosed X
  simpa [hEq] using hN

/--
At a closed carrier saturation stage, binary carrier relations are closed under
multiplication at the raw saturation level.
-/
theorem carrier_binaryRel_mul_mem_closedStage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N))
    {X Y Z : W}
    (hbin : CarrierBinaryRel H profile R X Y Z)
    {b c : Q}
    (hb : b ∈ SaturationIter
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      N Y)
    (hc : c ∈ SaturationIter
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      N Z) :
    b * c ∈
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X := by
  exact hClosed X
    (Or.inr (Or.inr ⟨Y, Z, b, c, hbin, hb, hc, rfl⟩))

/--
After a closed carrier saturation stage, binary carrier relations are closed
under multiplication at every later raw saturation stage.
-/
theorem carrier_binaryRel_mul_mem_laterClosedStage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N k : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N))
    {X Y Z : W}
    (hbin : CarrierBinaryRel H profile R X Y Z)
    {b c : Q}
    (hb : b ∈ SaturationIter
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (N + k) Y)
    (hc : c ∈ SaturationIter
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (N + k) Z) :
    b * c ∈
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + k) X := by
  have eX :=
    carrierSaturationIter_eq_closed_stage_add
      q H profile R N k hClosed X
  have eY :=
    carrierSaturationIter_eq_closed_stage_add
      q H profile R N k hClosed Y
  have eZ :=
    carrierSaturationIter_eq_closed_stage_add
      q H profile R N k hClosed Z
  have hbN : b ∈ SaturationIter
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      N Y := by
    simpa [eY] using hb
  have hcN : c ∈ SaturationIter
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      N Z := by
    simpa [eZ] using hc
  have hN :
      b * c ∈
        SaturationIter
          (CarrierTerminalImage q H profile R)
          (CarrierBinaryRel H profile R)
          N X :=
    carrier_binaryRel_mul_mem_closedStage
      q H profile R N hClosed hbin hbN hcN
  simpa [eX] using hN

/--
Listed-rule version of raw binary closure at a closed stage.
-/
theorem carrier_binaryRule_mul_mem_closedStage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N))
    (br : CarrierBinaryRule profile)
    (hmem : List.Mem (CarrierTypedRule.binary br) R)
    {b c : Q}
    (hb : b ∈ SaturationIter
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      N br.Y)
    (hc : c ∈ SaturationIter
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      N br.Z) :
    b * c ∈
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N br.X := by
  exact carrier_binaryRel_mul_mem_closedStage
    q H profile R N hClosed ⟨br, hmem, rfl, rfl, rfl⟩ hb hc

/--
Listed-rule version of raw binary closure at every later stage after a closed
stage.
-/
theorem carrier_binaryRule_mul_mem_laterClosedStage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N k : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N))
    (br : CarrierBinaryRule profile)
    (hmem : List.Mem (CarrierTypedRule.binary br) R)
    {b c : Q}
    (hb : b ∈ SaturationIter
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (N + k) br.Y)
    (hc : c ∈ SaturationIter
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (N + k) br.Z) :
    b * c ∈
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + k) br.X := by
  exact carrier_binaryRel_mul_mem_laterClosedStage
    q H profile R N k hClosed ⟨br, hmem, rfl, rfl, rfl⟩ hb hc

/--
Terminal insertions are contained in the residual concept closure of a closed
stage.
-/
theorem carrier_terminalImage_subset_closedStageConcept
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N))
    (X : W) :
    CarrierTerminalImage q H profile R X ⊆
      CarrierClosedStageConceptSemantics S q H profile R N X := by
  intro a ha
  unfold CarrierClosedStageConceptSemantics
  exact subset_conceptClosure S
    (carrier_terminalImage_subset_closedStage
      q H profile R N hClosed X ha)

/--
Terminal insertions are contained in every later closed-stage concept semantics.
-/
theorem carrier_terminalImage_subset_laterClosedStageConcept
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N k : Nat)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N))
    (X : W) :
    CarrierTerminalImage q H profile R X ⊆
      CarrierClosedStageConceptSemantics S q H profile R (N + k) X := by
  intro a ha
  unfold CarrierClosedStageConceptSemantics
  exact subset_conceptClosure S
    (carrier_terminalImage_subset_laterClosedStage
      q H profile R N k hClosed X ha)

end LeanCfgProject
