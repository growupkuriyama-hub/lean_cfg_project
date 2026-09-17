import Mathlib.Tactic
import LeanCfgProject.FixedHCFG.V60CanonicalBasis
import LeanCfgProject.FixedHCFG.V62ThicknessNormalization

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
# v62 fixed-window sample-count bounds

This file supplies the finite-cardinality part of manuscript Theorem
`window-thick`.  The constructive Section-7 development already bounds the
length of every canonical witness.  Here we discharge the remaining displayed
state-count estimate

`N_t <= N * |M|`

for the actual retained yield-typed state space, and record a polynomial slot
count for the four kinds of canonical witnesses (anchors, terminal-rule
witnesses, binary-rule witnesses, and the optional empty word).
-/

/--
Actual retained typed states inject into an underlying nonterminal together
with one observer value.  This is the manuscript estimate `N_t <= N |M|`.
-/
theorem v62_kept_state_card_le_base_times_observer
    {N : Type v} {Sigma : Type u}
    [Fintype N]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N) :
    Fintype.card (V60KeptState Obs terminal binary start) <=
      Fintype.card N * Fintype.card Obs.M := by
  classical
  let encode : V60KeptState Obs terminal binary start -> N × Obs.M :=
    fun X => v60TypedNTKey X.1
  have hInjective : Function.Injective encode := by
    intro X Y hXY
    apply Subtype.ext
    apply v60TypedNTKey_injective
    simpa [encode] using hXY
  simpa using Fintype.card_le_of_injective encode hInjective

/--
A grammar-independent superset of the canonical-witness indexing slots.
Rule predicates only remove slots, so this deliberately overcounts and is
sufficient for the polynomial-data theorem.
-/
abbrev V62CanonicalWitnessSlot (W : Type v) (Sigma : Type u) :=
  W ⊕ ((W × Sigma) ⊕ ((W × W × W) ⊕ Unit))

/-- Polynomial envelope for the number of canonical-witness slots. -/
def V62WindowWitnessCountEnvelope (Nt sigmaCard : Nat) : Nat :=
  Nt + (Nt * sigmaCard + (Nt * (Nt * Nt) + 1))

/-- The witness-slot type has exactly the displayed polynomial cardinality. -/
theorem v62_canonical_witness_slot_card
    {W : Type v} {Sigma : Type u}
    [Fintype W] [Fintype Sigma] :
    Fintype.card (V62CanonicalWitnessSlot W Sigma) =
      V62WindowWitnessCountEnvelope (Fintype.card W) (Fintype.card Sigma) := by
  simp [V62CanonicalWitnessSlot, V62WindowWitnessCountEnvelope]

end FixedHCFG
end LeanCfgProject
