import LeanCfgProject.ObservedResidualConcept.LocalStoppingCorrectness
import LeanCfgProject.ObservedResidualConcept.ClosedStageRuleSemantics
import LeanCfgProject.ObservedResidualConcept.LaterClosedStageClosure
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/-
Local stopping rule semantics.

This file packages the rule-semantics consequences of the checkable local
stopping condition

  SaturationIter (N+1) = SaturationIter N.

Once this equality is detected, the stopped stage and all later stages are
terminal-closed and binary-rule-closed.  Moreover, terminal insertions are
contained in the corresponding closed-stage concept semantics.
-/

/--
If the local stopping equality holds at stage `N`, then stage `N` contains all
carrier terminal insertions.
-/
theorem carrier_terminalImage_subset_stoppedStage_of_succ_eq
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat)
    (hStop : ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X)
    (X : W) :
    CarrierTerminalImage q H profile R X ⊆
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X := by
  have hClosed :=
    carrierSaturationStage_closed_of_succ_eq
      q H profile R N hStop
  exact carrier_terminalImage_subset_closedStage
    q H profile R N hClosed X

/--
If the local stopping equality holds at stage `N`, then every later stage
`N+k` contains all carrier terminal insertions.
-/
theorem carrier_terminalImage_subset_laterStoppedStage_of_succ_eq
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N k : Nat)
    (hStop : ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X)
    (X : W) :
    CarrierTerminalImage q H profile R X ⊆
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + k) X := by
  have hClosed :=
    carrierSaturationStage_closed_of_succ_eq
      q H profile R N hStop
  exact carrier_terminalImage_subset_laterClosedStage
    q H profile R N k hClosed X

/--
If the local stopping equality holds at stage `N`, then stage `N` is closed
under every carrier binary relation.
-/
theorem carrier_binaryRel_mul_mem_stoppedStage_of_succ_eq
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat)
    (hStop : ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X)
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
  have hClosed :=
    carrierSaturationStage_closed_of_succ_eq
      q H profile R N hStop
  exact carrier_binaryRel_mul_mem_closedStage
    q H profile R N hClosed hbin hb hc

/--
If the local stopping equality holds at stage `N`, then every later stage
`N+k` is closed under every carrier binary relation.
-/
theorem carrier_binaryRel_mul_mem_laterStoppedStage_of_succ_eq
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N k : Nat)
    (hStop : ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X)
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
  have hClosed :=
    carrierSaturationStage_closed_of_succ_eq
      q H profile R N hStop
  exact carrier_binaryRel_mul_mem_laterClosedStage
    q H profile R N k hClosed hbin hb hc

/--
Listed-rule version of binary closure at a locally stopped stage.
-/
theorem carrier_binaryRule_mul_mem_stoppedStage_of_succ_eq
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N : Nat)
    (hStop : ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X)
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
  exact carrier_binaryRel_mul_mem_stoppedStage_of_succ_eq
    q H profile R N hStop ⟨br, hmem, rfl, rfl, rfl⟩ hb hc

/--
Listed-rule version of binary closure at every later stage after local stopping.
-/
theorem carrier_binaryRule_mul_mem_laterStoppedStage_of_succ_eq
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N k : Nat)
    (hStop : ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X)
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
  exact carrier_binaryRel_mul_mem_laterStoppedStage_of_succ_eq
    q H profile R N k hStop ⟨br, hmem, rfl, rfl, rfl⟩ hb hc

/--
If the local stopping equality holds, then terminal insertions are contained in
the stopped-stage residual concept semantics.
-/
theorem carrier_terminalImage_subset_stoppedStageConcept_of_succ_eq
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
    (hStop : ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X)
    (X : W) :
    CarrierTerminalImage q H profile R X ⊆
      CarrierClosedStageConceptSemantics S q H profile R N X := by
  have hClosed :=
    carrierSaturationStage_closed_of_succ_eq
      q H profile R N hStop
  exact carrier_terminalImage_subset_closedStageConcept
    S q H profile R N hClosed X

/--
If the local stopping equality holds, then terminal insertions are contained in
every later stopped-stage residual concept semantics.
-/
theorem carrier_terminalImage_subset_laterStoppedStageConcept_of_succ_eq
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
    (hStop : ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X)
    (X : W) :
    CarrierTerminalImage q H profile R X ⊆
      CarrierClosedStageConceptSemantics S q H profile R (N + k) X := by
  have hClosed :=
    carrierSaturationStage_closed_of_succ_eq
      q H profile R N hStop
  exact carrier_terminalImage_subset_laterClosedStageConcept
    S q H profile R N k hClosed X

/--
If local stopping is detected at stage `N`, all later stages are closed.
-/
theorem carrierSaturationIter_closed_of_succ_eq_add
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (N k : Nat)
    (hStop : ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + 1) X =
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        N X) :
    IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (N + k)) := by
  have hClosed :=
    carrierSaturationStage_closed_of_succ_eq
      q H profile R N hStop
  exact carrierSaturationIter_closed_of_closed_add
    q H profile R N k hClosed

end LeanCfgProject
