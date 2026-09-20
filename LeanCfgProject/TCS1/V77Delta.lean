import LeanCfgProject.TCS1.FixedWindowExactEquivalence
import LeanCfgProject.TCS1.FixedHFiniteObstructions

/-!
# TCS #1 v77 delta verification facade

This lightweight facade collects theorem-facing modules added specifically
while synchronizing the Lean experiment with the v77 manuscript.  It is used
by a fast CI job during development; the full `TCS1.All` facade remains the
final integration check.
-/

namespace LeanCfgProject
namespace TCS1

theorem v77_delta_facade_loaded : True :=
  True.intro

end TCS1
end LeanCfgProject
