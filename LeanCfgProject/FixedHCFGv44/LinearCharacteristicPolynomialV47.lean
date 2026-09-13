import LeanCfgProject.FixedHCFGv44.LinearWitnessEndToEndV47

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Polynomial cardinality envelope for the v47 linear characteristic
reconstruction data.  The exact canonical witness family is covered by the
finite index family from `CharacteristicDataBounds`.  Here we bound that index
family directly: actual retained terminal productions inject into
`W × Sigma`, and actual retained binary productions inject into `W × W × W`.
Together with `|W| <= |N||M|`, this is polynomial in a finite target
presentation for fixed `h`.
-/

/-- Retained terminal productions are a subtype of state/letter pairs. -/
theorem keptTerminalProduction_card_le_v47
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype N] [Fintype Sigma] :
    Fintype.card
        (KeptTerminalProduction (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start)) ≤
      Fintype.card (KeptState Obs terminal binary start) * Fintype.card Sigma := by
  classical
  apply Fintype.card_le_of_injective
    (fun p : KeptTerminalProduction (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) => p.1)
  intro p q hpq
  exact Subtype.ext hpq

/-- Retained binary productions are a subtype of triples of retained states. -/
theorem keptBinaryProduction_card_le_v47
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype N] :
    Fintype.card
        (KeptBinaryProduction (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start)) ≤
      Fintype.card (KeptState Obs terminal binary start) ^ 3 := by
  classical
  calc
    Fintype.card
        (KeptBinaryProduction (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start)) ≤
        Fintype.card
          (KeptState Obs terminal binary start ×
            KeptState Obs terminal binary start ×
            KeptState Obs terminal binary start) := by
      apply Fintype.card_le_of_injective
        (fun p : KeptBinaryProduction (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start) => p.1)
      intro p q hpq
      exact Subtype.ext hpq
    _ = Fintype.card (KeptState Obs terminal binary start) ^ 3 := by
      simp [pow_succ, Nat.mul_assoc]

/--
Coarse polynomial size bound for the finite index family covering the exact
canonical characteristic data.  Combined with `canonicalCS_covered_by_index`,
this is the manuscript's `states + productions + 1` cardinality argument.
-/
theorem canonicalCSIndex_card_polynomial_le_v47
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype N] [Fintype Sigma] :
    Fintype.card
        (CanonicalCSIndex (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start)) ≤
      Fintype.card (KeptState Obs terminal binary start) +
      Fintype.card (KeptState Obs terminal binary start) * Fintype.card Sigma +
      Fintype.card (KeptState Obs terminal binary start) ^ 3 + 1 := by
  rw [canonicalCSIndex_card]
  have ht := keptTerminalProduction_card_le_v47
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
  have hb := keptBinaryProduction_card_le_v47
    (Obs := Obs) (terminal := terminal) (binary := binary) (start := start)
  omega

end FixedHCFGv44
end LeanCfgProject
