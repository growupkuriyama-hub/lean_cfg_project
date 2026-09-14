import LeanCfgProject.FixedHCFGv44.CanonicalWitness

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Manuscript-facing notation bridge for TCS v49.

Version 49 keeps the four-family finite set `W(\widetilde G)` as a finite
witness set and only calls it a characteristic reconstruction sample after the
exact reconstruction theorem.  The underlying Lean object `CanonicalCS`
already has exactly these four families, so the v49 name is a thin alias over
the stable construction rather than a duplicate definition.
-/

/-- TCS v49 finite witness set `W(\widetilde G)`. -/
noncomputable def WitnessSetV49
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop) : Language Sigma :=
  CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
    (start := start) epsilonStart

/-- The v49 witness-set name is definitionally the canonical four-family set. -/
theorem witnessSetV49_eq_canonicalCS
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop) :
    WitnessSetV49 (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart =
      CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart := by
  rfl

/-- The v49 witness set is finite. -/
theorem witnessSetV49_finite
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Finite N] [Finite Sigma]
    (epsilonStart : Prop) :
    (WitnessSetV49 (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart).Finite := by
  simpa [WitnessSetV49] using
    (canonicalCS_finite (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart)

/-- Every canonical v49 witness is positive for the target SSBNF language. -/
theorem witnessSetV49_subset_untyped
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    WitnessSetV49 (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart ⊆
      UntypedStartLanguage terminal binary start epsilonStart := by
  simpa [WitnessSetV49] using
    (canonicalCS_subset_untyped Obs terminal binary start epsilonStart)

end FixedHCFGv44
end LeanCfgProject
