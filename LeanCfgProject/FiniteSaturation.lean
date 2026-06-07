import LeanCfgProject.StateSemantics

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u v

def SaturationStep
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (U : State → Set Q)
    (X : State) : Set Q :=
  { x |
      x ∈ U X ∨
      x ∈ Terminal X ∨
      ∃ Y Z : State, ∃ b c : Q,
        Binary X Y Z ∧ b ∈ U Y ∧ c ∈ U Z ∧ x = b * c }

def IsSaturationClosed
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (U : State → Set Q) : Prop :=
  ∀ X : State, SaturationStep Terminal Binary U X ⊆ U X

theorem saturationStep_inflationary
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (U : State → Set Q)
    (X : State) :
    U X ⊆ SaturationStep Terminal Binary U X := by
  intro x hx
  exact Or.inl hx

theorem terminal_subset_saturationStep
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (U : State → Set Q)
    (X : State) :
    Terminal X ⊆ SaturationStep Terminal Binary U X := by
  intro x hx
  exact Or.inr (Or.inl hx)

theorem binary_mul_mem_saturationStep
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (U : State → Set Q)
    {X Y Z : State}
    {b c : Q}
    (hbin : Binary X Y Z)
    (hb : b ∈ U Y)
    (hc : c ∈ U Z) :
    b * c ∈ SaturationStep Terminal Binary U X := by
  exact Or.inr (Or.inr ⟨Y, Z, b, c, hbin, hb, hc, rfl⟩)

theorem saturationStep_mono
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    {U V : State → Set Q}
    (hUV : ∀ X : State, U X ⊆ V X) :
    ∀ X : State,
      SaturationStep Terminal Binary U X ⊆
      SaturationStep Terminal Binary V X := by
  intro X x hx
  rcases hx with hxU | hxRest
  · exact Or.inl (hUV X hxU)
  · rcases hxRest with hxT | hxBin
    · exact Or.inr (Or.inl hxT)
    · rcases hxBin with ⟨Y, Z, b, c, hbin, hb, hc, hxEq⟩
      exact Or.inr (Or.inr
        ⟨Y, Z, b, c, hbin, hUV Y hb, hUV Z hc, hxEq⟩)

theorem terminal_mem_of_saturationClosed
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (U : State → Set Q)
    (hclosed : IsSaturationClosed Terminal Binary U)
    {X : State}
    {a : Q}
    (ha : a ∈ Terminal X) :
    a ∈ U X := by
  exact hclosed X (Or.inr (Or.inl ha))

theorem binary_mul_mem_of_saturationClosed
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (U : State → Set Q)
    (hclosed : IsSaturationClosed Terminal Binary U)
    {X Y Z : State}
    {b c : Q}
    (hbin : Binary X Y Z)
    (hb : b ∈ U Y)
    (hc : c ∈ U Z) :
    b * c ∈ U X := by
  exact hclosed X
    (binary_mul_mem_saturationStep Terminal Binary U hbin hb hc)

def SaturationIter
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop) :
    Nat → State → Set Q
  | 0 => fun _ => ∅
  | n + 1 => SaturationStep Terminal Binary
      (SaturationIter Terminal Binary n)

theorem saturationIter_zero_empty
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (X : State) :
    SaturationIter Terminal Binary 0 X = ∅ := by
  rfl

theorem saturationIter_succ_eq_step
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (n : Nat)
    (X : State) :
    SaturationIter Terminal Binary (n + 1) X =
      SaturationStep Terminal Binary
        (SaturationIter Terminal Binary n) X := by
  rfl

theorem saturationIter_subset_succ
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    (n : Nat)
    (X : State) :
    SaturationIter Terminal Binary n X ⊆
      SaturationIter Terminal Binary (n + 1) X := by
  intro x hx
  exact Or.inl hx

theorem terminal_mem_saturationIter_one
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    {X : State}
    {a : Q}
    (ha : a ∈ Terminal X) :
    a ∈ SaturationIter Terminal Binary 1 X := by
  exact Or.inr (Or.inl ha)

theorem binary_mul_mem_saturationIter_succ
    {State : Type u}
    {Q : Type v} [Mul Q]
    (Terminal : State → Set Q)
    (Binary : State → State → State → Prop)
    {n : Nat}
    {X Y Z : State}
    {b c : Q}
    (hbin : Binary X Y Z)
    (hb : b ∈ SaturationIter Terminal Binary n Y)
    (hc : c ∈ SaturationIter Terminal Binary n Z) :
    b * c ∈ SaturationIter Terminal Binary (n + 1) X := by
  exact binary_mul_mem_saturationStep
    Terminal Binary (SaturationIter Terminal Binary n) hbin hb hc

end LeanCfgProject
