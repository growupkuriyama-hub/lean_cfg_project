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
import LeanCfgProject.TCS1.FrontEndSizeCombinatorics
import LeanCfgProject.TCS1.FixedWindowCharacteristicDataBounds
import LeanCfgProject.TCS1.FixedWindowTreeCombinatorics
import LeanCfgProject.TCS1.FixedWindowSummarySemantic
import LeanCfgProject.TCS1.FixedWindowBoundarySemantic
import LeanCfgProject.TCS1.MarkedBoundaryKernel
import LeanCfgProject.TCS1.MarkedBoundaryNormalization
import LeanCfgProject.TCS1.MarkedBoundarySelection
import LeanCfgProject.TCS1.FixedWindowBoundaryMarking
import LeanCfgProject.TCS1.ShortestNonemptyPathBound
import LeanCfgProject.TCS1.ShortestNonemptySpineSemantic
import LeanCfgProject.TCS1.FiniteSupportSpineBound
import LeanCfgProject.TCS1.BinaryGrammarFiniteRestriction
import LeanCfgProject.TCS1.FixedWindowContextPathBound
import LeanCfgProject.TCS1.FixedWindowContextSemantic

import LeanCfgProject.TCS1.TerminalIsolationKernel
import LeanCfgProject.TCS1.LeastClosedCFGLanguage
import LeanCfgProject.TCS1.GeneralCFGDerivation
import LeanCfgProject.TCS1.BinarizationKernel
import LeanCfgProject.TCS1.BinarizationLeastClosed
import LeanCfgProject.TCS1.SequenceBinaryGrammarBridge
import LeanCfgProject.TCS1.TerminalIsolationBinarizationBridge
import LeanCfgProject.TCS1.FrontEndThicknessKernel
import LeanCfgProject.TCS1.FrontEndBinaryThickness
import LeanCfgProject.TCS1.FrontEndFiniteSupportFacade
import LeanCfgProject.TCS1.FiniteCFGEncoding
import LeanCfgProject.TCS1.IndexedClosedFrontSupport
import LeanCfgProject.TCS1.IndexedFrontRuleClosure
import LeanCfgProject.TCS1.IndexedNormalizationFacade
import LeanCfgProject.TCS1.NormalizationLanguageBounds
import LeanCfgProject.TCS1.BinaryEpsilonElimination
import LeanCfgProject.TCS1.BinaryUnitElimination
import LeanCfgProject.TCS1.SSBNFNormalizationSemanticKernel
import LeanCfgProject.TCS1.UnitFreeProductiveTrim
import LeanCfgProject.TCS1.UnitFreeReachableTrim
import LeanCfgProject.TCS1.SeparatedStartSSBNF
import LeanCfgProject.TCS1.FixedWindowTransferKernel
import LeanCfgProject.TCS1.Proposition74Facade

/-!
# TCS #1 v68 Lean verification facade

This module imports every theorem-facing kernel maintained for the current
TCS #1 v68 working baseline. Building this one target is the fast integration
check; CI separately rejects placeholder proofs and project-level axiom declarations
inside the TCS1 namespace.
-/

namespace LeanCfgProject
namespace TCS1

/-- Compatibility marker for the integrated v66 verification facade. -/
theorem v66_facade_loaded : True :=
  True.intro

/-- Marker theorem for the integrated v68 verification facade. -/
theorem v68_facade_loaded : True :=
  True.intro

end TCS1
end LeanCfgProject
