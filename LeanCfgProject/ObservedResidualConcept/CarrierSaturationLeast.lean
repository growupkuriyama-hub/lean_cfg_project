import LeanCfgProject.ObservedResidualConcept.CarrierSaturationCorrectness
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/--
Terminal insertions are contained in the finite-stage carrier saturation image.
This is the terminal half of saturation closure for `CarrierSaturationImage`.
-/
theorem carrier_terminal_mem_saturationImage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    {X : W}
    {a : Q}
    (ha : a ∈ CarrierTerminalImage q H profile R X) :
    a ∈ CarrierSaturationImage q H profile R X := by
  refine ⟨1, ?_⟩
  exact terminal_mem_saturationIter_one
    (CarrierTerminalImage q H profile R)
    (CarrierBinaryRel H profile R)
    ha

/--
Binary insertions are contained in the finite-stage carrier saturation image.
This is the binary half of saturation closure for `CarrierSaturationImage`.
-/
theorem carrier_binary_mul_mem_saturationImage
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    {X Y Z : W}
    {b c : Q}
    (hbin : CarrierBinaryRel H profile R X Y Z)
    (hb : b ∈ CarrierSaturationImage q H profile R Y)
    (hc : c ∈ CarrierSaturationImage q H profile R Z) :
    b * c ∈ CarrierSaturationImage q H profile R X := by
  rcases hb with ⟨nY, hbY⟩
  rcases hc with ⟨nZ, hcZ⟩
  let n := Nat.max nY nZ
  have hbY' : b ∈ SaturationIter
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      n Y :=
    saturationIter_mono_of_le
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (Nat.le_max_left nY nZ) Y hbY
  have hcZ' : c ∈ SaturationIter
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      n Z :=
    saturationIter_mono_of_le
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (Nat.le_max_right nY nZ) Z hcZ
  refine ⟨n + 1, ?_⟩
  exact binary_mul_mem_saturationIter_succ
    (CarrierTerminalImage q H profile R)
    (CarrierBinaryRel H profile R)
    hbin hbY' hcZ'

/--
The carrier saturation image is closed under the one-step saturation operator.
This upgrades the finite-stage union to an actual closed simultaneous solution.
-/
theorem carrierSaturationImage_isSaturationClosed
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile)) :
    IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (CarrierSaturationImage q H profile R) := by
  intro X x hx
  rcases hx with hxPrev | hxRest
  · exact hxPrev
  · rcases hxRest with hxTerm | hxBin
    · exact carrier_terminal_mem_saturationImage q H profile R hxTerm
    · rcases hxBin with ⟨Y, Z, b, c, hbin, hb, hc, hxEq⟩
      rw [hxEq]
      exact carrier_binary_mul_mem_saturationImage
        q H profile R hbin hb hc

/--
Leastness of the carrier saturation image: every closed family containing all
terminal insertions and closed under carrier binary products contains the
finite-stage carrier saturation image.
-/
theorem carrierSaturationImage_subset_of_closed
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (U : W → Set Q)
    (hTerminal : ∀ X : W,
      CarrierTerminalImage q H profile R X ⊆ U X)
    (hBinary : ∀ X Y Z : W, ∀ b c : Q,
      CarrierBinaryRel H profile R X Y Z →
      b ∈ U Y → c ∈ U Z → b * c ∈ U X)
    (X : W) :
    CarrierSaturationImage q H profile R X ⊆ U X := by
  intro a ha
  rcases ha with ⟨n, hn⟩
  exact saturationIter_subset_of_closed
    (CarrierTerminalImage q H profile R)
    (CarrierBinaryRel H profile R)
    U hTerminal hBinary n X hn

/--
Carrier state semantics is itself closed under the carrier saturation rules.
This is the closed-target side of the least-fixed-point picture.
-/
theorem carrierStateSemantics_isSaturationClosed
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile)) :
    IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      (CarrierStateSemantics q H profile R) := by
  intro X x hx
  rcases hx with hxPrev | hxRest
  · exact hxPrev
  · rcases hxRest with hxTerm | hxBin
    · exact carrier_terminalImage_subset_stateSemantics q H profile R X hxTerm
    · rcases hxBin with ⟨Y, Z, b, c, hbin, hb, hc, hxEq⟩
      rw [hxEq]
      exact carrier_binaryRel_closed_stateSemantics
        q q_mul H profile R X Y Z b c hbin hb hc

/--
Reformulation of saturation correctness as the least closed simultaneous
solution: the carrier saturation image is the least family closed under the
terminal and binary carrier rules.
-/
theorem carrierSaturationImage_least_closed_solution
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Mul Q]
    (q : Word Sigma → Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (U : W → Set Q)
    (hClosed : IsSaturationClosed
      (CarrierTerminalImage q H profile R)
      (CarrierBinaryRel H profile R)
      U)
    (X : W) :
    CarrierSaturationImage q H profile R X ⊆ U X := by
  apply carrierSaturationImage_subset_of_closed q H profile R U
  · intro Y y hy
    exact hClosed Y (Or.inr (Or.inl hy))
  · intro Y Z T b c hbin hb hc
    exact hClosed Y
      (Or.inr (Or.inr ⟨Z, T, b, c, hbin, hb, hc, rfl⟩))

end LeanCfgProject
