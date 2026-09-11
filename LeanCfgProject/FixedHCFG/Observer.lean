import LeanCfgProject.JALC.Basic

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-- Words over the terminal alphabet. -/
abbrev Word (Sigma : Type u) := List Sigma

/--
A fixed finite-monoid observer for the TCS fixed-h development.

We reuse the finite explicit monoid package already present in the JALC
formalization and add the two laws saying that the observer on words is a
monoid homomorphism.  These are the laws used in the fixed-h paper.
-/
structure Observer (Sigma : Type u) extends JALC.FixedFiniteMonoidHom Sigma where
  map_nil : h [] = one
  map_append : ∀ x y : List Sigma, h (x ++ y) = mul (h x) (h y)

/-- The observed value of a word. -/
def Observer.value {Sigma : Type u} (Obs : Observer Sigma)
    (w : Word Sigma) : Obs.M :=
  Obs.h w

@[simp] theorem Observer.value_nil {Sigma : Type u}
    (Obs : Observer Sigma) :
    Obs.value [] = Obs.one := by
  exact Obs.map_nil

@[simp] theorem Observer.value_append {Sigma : Type u}
    (Obs : Observer Sigma) (x y : Word Sigma) :
    Obs.value (x ++ y) = Obs.mul (Obs.value x) (Obs.value y) := by
  exact Obs.map_append x y

end FixedHCFG
end LeanCfgProject
