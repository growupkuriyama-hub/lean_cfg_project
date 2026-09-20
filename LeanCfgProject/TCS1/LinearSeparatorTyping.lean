import LeanCfgProject.TCS1.LinearSeparatorExample

/-!
# TCS #1 v77: the four-element typing for L_{±,e}

This module formalizes the concrete monoid M_{±,e} from Section 8.1.
It is the identity adjoined to a three-element null semigroup:
1, kappa_cd, kappa_e, 0.

The associated homomorphism maps a,b to 1, c,d to kappa_cd, and e to
kappa_e.
-/

namespace LeanCfgProject
namespace TCS1

inductive LpmType where
  | one
  | cd
  | ee
  | zero
  deriving DecidableEq, Fintype, Repr

namespace LpmType

def mul : LpmType → LpmType → LpmType
  | one, y => y
  | x, one => x
  | _, _ => zero

instance : Monoid LpmType where
  one := one
  mul := mul
  one_mul x := by
    cases x <;> rfl
  mul_one x := by
    cases x <;> rfl
  mul_assoc x y z := by
    cases x <;> cases y <;> cases z <;> rfl

end LpmType

open LpmSymbol LpmType

def lpmLetterType : LpmSymbol → LpmType
  | a => 1
  | b => 1
  | c => cd
  | d => cd
  | e => ee

/-- The four-element monoid homomorphism h from equation (8.1). -/
def lpmTyping :
    FixedFiniteMonoidHom LpmSymbol LpmType where
  h w := (w.map lpmLetterType).prod
  map_nil := by simp
  map_append u v := by
    simp [List.map_append, List.prod_append]

@[simp] theorem lpmTyping_a :
    lpmTyping.h [a] = 1 := by
  rfl

@[simp] theorem lpmTyping_b :
    lpmTyping.h [b] = 1 := by
  rfl

@[simp] theorem lpmTyping_c :
    lpmTyping.h [c] = cd := by
  rfl

@[simp] theorem lpmTyping_d :
    lpmTyping.h [d] = cd := by
  rfl

@[simp] theorem lpmTyping_e :
    lpmTyping.h [e] = ee := by
  rfl

@[simp] theorem lpmTyping_replicate_a
    (n : Nat) :
    lpmTyping.h (List.replicate n a) = 1 := by
  simp [lpmTyping, lpmLetterType]

@[simp] theorem lpmTyping_replicate_b
    (n : Nat) :
    lpmTyping.h (List.replicate n b) = 1 := by
  simp [lpmTyping, lpmLetterType]

/-- The type of a canonical one-center word is exactly the type of its center. -/
@[simp] theorem lpmTyping_core
    (n : Nat) (z : LpmSymbol) :
    lpmTyping.h (lpmCore n z) =
      lpmLetterType z := by
  rw [lpmTyping.map_append]
  rw [lpmTyping.map_append]
  simp [lpmCore, lpmTyping, lpmLetterType]

@[simp] theorem lpmTyping_core_c
    (n : Nat) :
    lpmTyping.h (lpmCore n c) = cd := by
  simp

@[simp] theorem lpmTyping_core_d
    (n : Nat) :
    lpmTyping.h (lpmCore n d) = cd := by
  simp

@[simp] theorem lpmTyping_core_e
    (n : Nat) :
    lpmTyping.h (lpmCore n e) = ee := by
  simp

end TCS1
end LeanCfgProject
