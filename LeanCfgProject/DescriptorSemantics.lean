import LeanCfgProject.FullArchitecture_Test
import LeanCfgProject.ResidualConcept

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

def CarrierYieldSet
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (X : W) : Set (Word Sigma) :=
  { w | YieldFamily H profile R X w }

def CarrierStateSemantics
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v}
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (X : W) : Set Q :=
  StateSemantics q (CarrierYieldSet H profile R) X

theorem carrier_terminal_sound
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v}
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (tr : CarrierTerminalRule H profile)
    (hmem : List.Mem (CarrierTypedRule.terminal tr) R) :
    q [tr.a] ∈ CarrierStateSemantics q H profile R tr.X := by
  exact terminal_sound q
    (CarrierYieldSet H profile R)
    tr.X
    [tr.a]
    (YieldFamily.terminal tr hmem)

theorem carrier_binary_rule_hbin
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (br : CarrierBinaryRule profile)
    (hmem : List.Mem (CarrierTypedRule.binary br) R) :
    ∀ u v : Word Sigma,
      u ∈ CarrierYieldSet H profile R br.Y →
      v ∈ CarrierYieldSet H profile R br.Z →
      u ++ v ∈ CarrierYieldSet H profile R br.X := by
  intro u v hY hZ
  exact YieldFamily.binary br hmem hY hZ

theorem carrier_binary_sound
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (br : CarrierBinaryRule profile)
    (hmem : List.Mem (CarrierTypedRule.binary br) R) :
    SetMul
      (CarrierStateSemantics q H profile R br.Y)
      (CarrierStateSemantics q H profile R br.Z)
      ⊆
    CarrierStateSemantics q H profile R br.X := by
  exact binary_sound q q_mul
    (CarrierYieldSet H profile R)
    br.X br.Y br.Z
    (carrier_binary_rule_hbin H profile R br hmem)

theorem carrier_binary_sound_after_closure
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (br : CarrierBinaryRule profile)
    (hmem : List.Mem (CarrierTypedRule.binary br) R) :
    ConceptClosure S
      (SetMul
        (CarrierStateSemantics q H profile R br.Y)
        (CarrierStateSemantics q H profile R br.Z))
      ⊆
    ConceptClosure S
      (CarrierStateSemantics q H profile R br.X) := by
  exact binary_sound_after_closure S q q_mul
    (CarrierYieldSet H profile R)
    br.X br.Y br.Z
    (carrier_binary_rule_hbin H profile R br hmem)

theorem carrier_binary_sound_as_conceptProduct
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (br : CarrierBinaryRule profile)
    (hmem : List.Mem (CarrierTypedRule.binary br) R) :
    ConceptProduct S
      (CarrierStateSemantics q H profile R br.Y)
      (CarrierStateSemantics q H profile R br.Z)
      ⊆
    ConceptClosure S
      (CarrierStateSemantics q H profile R br.X) := by
  exact binary_sound_as_conceptProduct S q q_mul
    (CarrierYieldSet H profile R)
    br.X br.Y br.Z
    (carrier_binary_rule_hbin H profile R br hmem)

def CarrierStartLanguage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W) : Language Sigma :=
  { w | ∃ X : W, X ∈ S0 ∧ YieldFamily H profile R X w }

end LeanCfgProject
