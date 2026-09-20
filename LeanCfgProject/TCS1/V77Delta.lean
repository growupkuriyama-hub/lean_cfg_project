import LeanCfgProject.TCS1.FixedWindowExactEquivalence
import LeanCfgProject.TCS1.FixedHFiniteObstructions
import LeanCfgProject.TCS1.FixedHRightQuotient
import LeanCfgProject.TCS1.LinearSeparatorExample
import LeanCfgProject.TCS1.LinearSeparatorTyping
import LeanCfgProject.TCS1.LinearSeparatorDistribution
import LeanCfgProject.TCS1.LinearSeparatorPowerContexts
import LeanCfgProject.TCS1.LinearSeparatorFactorSlices
import LeanCfgProject.TCS1.LinearSeparatorContextShape
import LeanCfgProject.TCS1.LinearSeparatorBoundaryFactors
import LeanCfgProject.TCS1.LinearSeparatorBalance
import LeanCfgProject.TCS1.LinearSeparatorFixedH
import LeanCfgProject.TCS1.LinearSeparatorProposition86
import LeanCfgProject.TCS1.LinearSeparatorDisplayedGrammar
import LeanCfgProject.TCS1.LinearSeparatorNonregular
import LeanCfgProject.TCS1.LinearSeparatorPreparedGrammar
import LeanCfgProject.TCS1.ClarkCongruentialKernel

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

import LeanCfgProject.TCS1.ClarkCongruentialPackaging
