import LeanCfgProject.FixedHCFGv44.CanonicalWitness

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Notation bridge for the current TCS v47 manuscript.

The revision deliberately renamed the finite canonical positive witness family
from the older `CS` terminology to `W(\widetilde G)` in order to avoid
confusion with classical characteristic samples.  The established Lean
construction `CanonicalCS` already has exactly the revised four-family
semantics, so this file exposes a manuscript-facing name without duplicating
or changing the underlying proofs.
-/

/-- The current manuscript witness set `W(\widetilde G)`. -/
noncomputable def WitnessSetV47
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop) : Language Sigma :=
  CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
    (start := start) epsilonStart

/-- The manuscript-facing name is definitionally the already verified witness family. -/
theorem witnessSetV47_eq_canonicalCS
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop) :
    WitnessSetV47 (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart =
      CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart := by
  rfl

/-- The current witness set is finite. -/
theorem witnessSetV47_finite
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Finite N] [Finite Sigma]
    (epsilonStart : Prop) :
    (WitnessSetV47 (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart).Finite := by
  simpa [WitnessSetV47] using
    (canonicalCS_finite (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart)

/-- Every current canonical positive witness belongs to the target SSBNF language. -/
theorem witnessSetV47_subset_untyped
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    WitnessSetV47 (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart ⊆
      UntypedStartLanguage terminal binary start epsilonStart := by
  simpa [WitnessSetV47] using
    (canonicalCS_subset_untyped Obs terminal binary start epsilonStart)

end FixedHCFGv44
end LeanCfgProject
