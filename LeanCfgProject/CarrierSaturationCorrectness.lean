import LeanCfgProject.FiniteSaturation
import LeanCfgProject.DescriptorSemantics

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/-- Terminal insertions for the carrier grammar, after applying an observation `q`. -/
def CarrierTerminalImage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v}
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (X : W) : Set Q :=
  { a | ∃ tr : CarrierTerminalRule H profile,
      List.Mem (CarrierTypedRule.terminal tr) R ∧
      tr.X = X ∧
      a = q [tr.a] }

/-- Binary relation induced by carrier binary rules. -/
def CarrierBinaryRel
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (X Y Z : W) : Prop :=
  ∃ br : CarrierBinaryRule profile,
    List.Mem (CarrierTypedRule.binary br) R ∧
    br.X = X ∧ br.Y = Y ∧ br.Z = Z

/-- The set obtained after any finite number of saturation steps. -/
def CarrierSaturationImage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (X : W) : Set Q :=
  { a | ∃ n : Nat,
      a ∈ SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n X }

/-- Generic soundness of finite saturation against any closed target family. -/
theorem saturationIter_subset_of_closed
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (Target : State → Set Q)
    (hTerminal : ∀ X : State, Terminal X ⊆ Target X)
    (hBinary : ∀ X Y Z : State, ∀ b c : Q,
      Binary X Y Z → b ∈ Target Y → c ∈ Target Z → b * c ∈ Target X) :
    ∀ n : Nat, ∀ X : State,
      SaturationIter Terminal Binary n X ⊆ Target X := by
  intro n
  induction n with
  | zero =>
      intro X x hx
      simpa using hx
  | succ n ih =>
      intro X x hx
      rcases hx with hxPrev | hxRest
      · exact ih X x hxPrev
      · rcases hxRest with hxTerm | hxBin
        · exact hTerminal X x hxTerm
        · rcases hxBin with ⟨Y, Z, b, c, hbin, hb, hc, hxEq⟩
          rw [hxEq]
          exact hBinary X Y Z b c hbin (ih Y b hb) (ih Z c hc)

/-- Saturation is monotone in the iteration index. -/
theorem saturationIter_mono_of_le
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    {m n : Nat}
    (hmn : m ≤ n)
    (X : State) :
    SaturationIter Terminal Binary m X ⊆
      SaturationIter Terminal Binary n X := by
  intro x hx
  induction hmn with
  | refl =>
      exact hx
  | step hmn ih =>
      exact saturationIter_subset_succ Terminal Binary _ X ih

/-- Terminal images are sound for carrier state semantics. -/
theorem carrier_terminalImage_subset_stateSemantics
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v}
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (X : W) :
    CarrierTerminalImage q H profile R X ⊆
      CarrierStateSemantics q H profile R X := by
  intro a ha
  rcases ha with ⟨tr, hmem, hX, haEq⟩
  rw [haEq]
  simpa [hX] using carrier_terminal_sound q H profile R tr hmem

/-- Carrier state semantics is closed under the carrier binary relation. -/
theorem carrier_binaryRel_closed_stateSemantics
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile)) :
    ∀ X Y Z : W, ∀ b c : Q,
      CarrierBinaryRel H profile R X Y Z →
      b ∈ CarrierStateSemantics q H profile R Y →
      c ∈ CarrierStateSemantics q H profile R Z →
      b * c ∈ CarrierStateSemantics q H profile R X := by
  intro X Y Z b c hbin hb hc
  rcases hbin with ⟨br, hmem, hX, hY, hZ⟩
  have hb' : b ∈ CarrierStateSemantics q H profile R br.Y := by
    simpa [hY] using hb
  have hc' : c ∈ CarrierStateSemantics q H profile R br.Z := by
    simpa [hZ] using hc
  have hmul : b * c ∈
      SetMul
        (CarrierStateSemantics q H profile R br.Y)
        (CarrierStateSemantics q H profile R br.Z) := by
    exact ⟨b, hb', c, hc', rfl⟩
  have hs := carrier_binary_sound q q_mul H profile R br hmem hmul
  simpa [hX] using hs

/-- Every finite saturation stage is sound for carrier state semantics. -/
theorem carrier_saturationIter_subset_stateSemantics
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile)) :
    ∀ n : Nat, ∀ X : W,
      SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n X ⊆
      CarrierStateSemantics q H profile R X := by
  exact saturationIter_subset_of_closed
    (CarrierTerminalImage q H profile R)
    (CarrierBinaryRel H profile R)
    (CarrierStateSemantics q H profile R)
    (carrier_terminalImage_subset_stateSemantics q H profile R)
    (carrier_binaryRel_closed_stateSemantics q q_mul H profile R)

/-- Every carrier yield appears at some finite saturation stage. -/
theorem carrier_yield_mem_saturationIter_exists
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    {X : W}
    {w : Word Sigma}
    (hy : YieldFamily H profile R X w) :
    ∃ n : Nat,
      q w ∈ SaturationIter
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        n X := by
  induction hy with
  | terminal tr hmem =>
      refine ⟨1, ?_⟩
      apply terminal_mem_saturationIter_one
      exact ⟨tr, hmem, rfl, rfl⟩
  | binary br hmem hY hZ ihY ihZ =>
      rcases ihY with ⟨nY, hnY⟩
      rcases ihZ with ⟨nZ, hnZ⟩
      let n := Nat.max nY nZ
      have hnY' : q _ ∈ SaturationIter
          (CarrierTerminalImage q H profile R)
          (CarrierBinaryRel H profile R)
          n br.Y :=
        saturationIter_mono_of_le
          (CarrierTerminalImage q H profile R)
          (CarrierBinaryRel H profile R)
          (Nat.le_max_left nY nZ) br.Y hnY
      have hnZ' : q _ ∈ SaturationIter
          (CarrierTerminalImage q H profile R)
          (CarrierBinaryRel H profile R)
          n br.Z :=
        saturationIter_mono_of_le
          (CarrierTerminalImage q H profile R)
          (CarrierBinaryRel H profile R)
          (Nat.le_max_right nY nZ) br.Z hnZ
      refine ⟨n + 1, ?_⟩
      rw [q_mul]
      exact binary_mul_mem_saturationIter_succ
        (CarrierTerminalImage q H profile R)
        (CarrierBinaryRel H profile R)
        (⟨br, hmem, rfl, rfl, rfl⟩ : CarrierBinaryRel H profile R br.X br.Y br.Z)
        hnY' hnZ'

/-- The finite-stage saturation image equals the carrier state semantics. -/
theorem carrier_saturationImage_eq_stateSemantics
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (X : W) :
    CarrierSaturationImage q H profile R X =
      CarrierStateSemantics q H profile R X := by
  ext a
  constructor
  · intro ha
    rcases ha with ⟨n, hn⟩
    exact carrier_saturationIter_subset_stateSemantics
      q q_mul H profile R n X hn
  · intro ha
    rcases ha with ⟨w, hy, haEq⟩
    rw [haEq]
    exact carrier_yield_mem_saturationIter_exists
      q q_mul H profile R hy

end LeanCfgProject
