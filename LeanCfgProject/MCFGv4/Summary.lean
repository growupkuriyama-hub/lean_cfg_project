import LeanCfgProject.MCFGv4.Basic
import LeanCfgProject.MCFGv4.SemanticKernel
import LeanCfgProject.MCFGv4.StandardMCFG
import LeanCfgProject.MCFGv4.StandardSemantics
import LeanCfgProject.MCFGv4.InducedOrientation
import LeanCfgProject.MCFGv4.OrientedContexts
import LeanCfgProject.MCFGv4.TupleSubstitutability
import LeanCfgProject.MCFGv4.FanoutOne
import LeanCfgProject.MCFGv4.RecognizableSlice

/-!
# MCFGv4.Summary

Aggregate build target for the isolated 2026-09-07 MCFG v4 verification.

The current target contains the independent finite-observation foundation,
fresh arbitrary-finite-rank standard MCFG syntax and tuple-generation semantics,
induced-orientation/permutation-decoration infrastructure, the concrete
orientation-sector context model, and the paper-facing semantic
tuple-substitutability core.  In particular it now includes the
orientation-sector canonicalization machinery, the identity-sector equivalence
proof, shared-context substitutability, observation-refinement monotonicity, the
exact fan-out-one specialization to ordinary two-sided distributions, and the
semantic fixed-observation result for languages recognized directly by the
observation monoid.
-/
