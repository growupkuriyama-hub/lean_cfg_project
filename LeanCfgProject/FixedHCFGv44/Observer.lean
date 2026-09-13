import LeanCfgProject.FixedHCFG.Observer

namespace LeanCfgProject
namespace FixedHCFGv44

universe u

/-- Words over the terminal alphabet. -/
abbrev Word (Sigma : Type u) := FixedHCFG.Word Sigma

/-- Reuse the explicit finite-monoid observer from the earlier formalization. -/
abbrev Observer (Sigma : Type u) := FixedHCFG.Observer Sigma

/-- The fixed observer value of a word. -/
def obsValue {Sigma : Type u} (Obs : Observer Sigma) (w : Word Sigma) : Obs.M :=
  FixedHCFG.Observer.value Obs w

@[simp] theorem obsValue_nil {Sigma : Type u} (Obs : Observer Sigma) :
    obsValue Obs [] = Obs.one := by
  exact FixedHCFG.Observer.value_nil Obs

@[simp] theorem obsValue_append {Sigma : Type u} (Obs : Observer Sigma)
    (x y : Word Sigma) :
    obsValue Obs (x ++ y) = Obs.mul (obsValue Obs x) (obsValue Obs y) := by
  exact FixedHCFG.Observer.value_append Obs x y

end FixedHCFGv44
end LeanCfgProject
