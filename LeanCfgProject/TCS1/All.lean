import LeanCfgProject.TCS1.FixedHSubstitutability
import LeanCfgProject.TCS1.YieldTypedRefinementCore
import LeanCfgProject.TCS1.ReconstructionSoundness
import LeanCfgProject.TCS1.CanonicalWitnessCompleteness
import LeanCfgProject.TCS1.ConservativeGoldKernel
import LeanCfgProject.TCS1.WitnessSetConstruction
import LeanCfgProject.TCS1.ReducednessWitnessChoices
import LeanCfgProject.TCS1.GoldConvergenceClosure

import LeanCfgProject.TCS1.SSBNFThicknessBounds
import LeanCfgProject.TCS1.SSBNFNormalizationCombinatorics
import LeanCfgProject.TCS1.FixedWindowCharacteristicDataBounds
import LeanCfgProject.TCS1.FixedWindowTreeCombinatorics
import LeanCfgProject.TCS1.ShortestNonemptyPathBound
import LeanCfgProject.TCS1.FixedWindowContextPathBound

import LeanCfgProject.TCS1.TerminalIsolationKernel
import LeanCfgProject.TCS1.NormalizationLanguageBounds
import LeanCfgProject.TCS1.BinaryEpsilonElimination
import LeanCfgProject.TCS1.BinaryUnitElimination
import LeanCfgProject.TCS1.SSBNFNormalizationSemanticKernel
import LeanCfgProject.TCS1.FixedWindowTransferKernel

/-!
# TCS #1 v65 Lean verification facade

This module imports every theorem-facing kernel maintained for the current
TCS #1 working baseline. Building this one target is the fast integration
check; CI separately rejects placeholder proofs and project-level axiom declarations
inside the TCS1 namespace.
-/

namespace LeanCfgProject
namespace TCS1

/-- Marker theorem for the integrated v65 verification facade. -/
theorem v65_facade_loaded : True :=
  True.intro

end TCS1
end LeanCfgProject
