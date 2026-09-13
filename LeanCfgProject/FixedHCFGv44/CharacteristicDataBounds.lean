import Mathlib.Tactic
import LeanCfgProject.FixedHCFGv44.LinearWitnessBounds

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Characteristic-data bounds for the linear-target argument in v44.

This layer is deliberately downstream of the canonical witness construction.
It records two manuscript-facing facts:

* the exact four-family characteristic set is covered by one index per retained
  state, one per actual retained typed production, and one optional-epsilon slot;
* once every canonical yield is at most `n` and every canonical context is at
  most `2n`, every characteristic word has length at most `4n`.

The remaining normalization bridge is responsible for supplying those two
short-witness hypotheses with `n = n_t`.
-/

/-- Actual retained typed terminal productions. -/
abbrev KeptTerminalProduction
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N} :=
  {p : KeptState Obs terminal binary start × Sigma //
    keptTerminal p.1 p.2}

/-- Actual retained typed binary productions. -/
abbrev KeptBinaryProduction
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N} :=
  {p : KeptState Obs terminal binary start ×
      KeptState Obs terminal binary start ×
      KeptState Obs terminal binary start //
    keptBinary p.1 p.2.1 p.2.2}

noncomputable instance keptTerminalProductionFintype
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype N] [Fintype Sigma] :
    Fintype (KeptTerminalProduction (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start)) := by
  classical
  exact Fintype.ofFinite _

noncomputable instance keptBinaryProductionFintype
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype N] :
    Fintype (KeptBinaryProduction (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start)) := by
  classical
  exact Fintype.ofFinite _

/--
The exact finite index envelope for `CanonicalCS`: one state anchor, one
terminal-production witness, one binary-production witness, and one epsilon
slot.  The epsilon slot may be unused.
-/
abbrev CanonicalCSIndex
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N} :=
  Sum (KeptState Obs terminal binary start)
    (Sum
      (KeptTerminalProduction (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start))
      (Sum
        (KeptBinaryProduction (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start))
        Unit))

/-- The word represented by an exact characteristic-data index. -/
noncomputable def canonicalCSIndexWord
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N} :
    CanonicalCSIndex (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) → Word Sigma
  | Sum.inl X => canonicalAnchorWord X
  | Sum.inr (Sum.inl p) =>
      canonicalTerminalObservationWord p.1.1 p.1.2
  | Sum.inr (Sum.inr (Sum.inl p)) =>
      canonicalBinaryObservationWord p.1.1 p.1.2.1 p.1.2.2
  | Sum.inr (Sum.inr (Sum.inr _)) => []

/-- Every exact canonical characteristic word is represented by its natural index. -/
theorem canonicalCS_covered_by_index
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop) {z : Word Sigma}
    (hz : CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart z) :
    ∃ i : CanonicalCSIndex (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start),
      canonicalCSIndexWord i = z := by
  rcases hz with hAnchor | hTerminal | hBinary | hEps
  · rcases hAnchor with ⟨X, rfl⟩
    exact ⟨Sum.inl X, rfl⟩
  · rcases hTerminal with ⟨X, a, hRule, rfl⟩
    let p : KeptTerminalProduction (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) := ⟨(X, a), hRule⟩
    exact ⟨Sum.inr (Sum.inl p), rfl⟩
  · rcases hBinary with ⟨X, Y, Z, hRule, rfl⟩
    let p : KeptBinaryProduction (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) := ⟨(X, Y, Z), hRule⟩
    exact ⟨Sum.inr (Sum.inr (Sum.inl p)), rfl⟩
  · rcases hEps with ⟨rfl, hEpsilon⟩
    exact ⟨Sum.inr (Sum.inr (Sum.inr ())), rfl⟩

/--
The finite index envelope has exactly the manuscript's `states + productions + 1`
shape (with the final slot unused when epsilon is absent).
-/
theorem canonicalCSIndex_card
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype N] [Fintype Sigma] :
    Fintype.card
        (CanonicalCSIndex (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start)) =
      Fintype.card (KeptState Obs terminal binary start) +
      Fintype.card
        (KeptTerminalProduction (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start)) +
      Fintype.card
        (KeptBinaryProduction (Obs := Obs) (terminal := terminal)
          (binary := binary) (start := start)) + 1 := by
  simp [CanonicalCSIndex, Nat.add_assoc]

/--
The manuscript's concluding length estimate for the general four-family
characteristic set.  The sharper wrapper/spine cases are used only to obtain
the hypotheses `hOmega` and `hCtx`; after that, a uniform `4n` bound suffices.
-/
theorem canonicalCS_word_length_le_four_mul
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop) {n : Nat} (hn : 0 < n)
    (hOmega : ∀ X : KeptState Obs terminal binary start,
      (canonicalOmega X).length ≤ n)
    (hCtx : ∀ X : KeptState Obs terminal binary start,
      (canonicalLeftCtx X).length + (canonicalRightCtx X).length ≤ 2 * n)
    {z : Word Sigma}
    (hz : CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart z) :
    z.length ≤ 4 * n := by
  rcases hz with hAnchor | hTerminal | hBinary | hEps
  · rcases hAnchor with ⟨X, rfl⟩
    have ho := hOmega X
    have hc := hCtx X
    simp only [canonicalAnchorWord, List.length_append]
    omega
  · rcases hTerminal with ⟨X, a, hRule, rfl⟩
    have hc := hCtx X
    simp only [canonicalTerminalObservationWord, List.length_append,
      List.length_singleton]
    omega
  · rcases hBinary with ⟨X, Y, Z, hRule, rfl⟩
    have hc := hCtx X
    have hy := hOmega Y
    have hz := hOmega Z
    simp only [canonicalBinaryObservationWord, List.length_append]
    omega
  · rcases hEps with ⟨rfl, hEpsilon⟩
    simp

/--
The retained-state factor in the characteristic-data envelope is already
linear in the original non-start state count and in `|M|`.
-/
theorem canonical_index_state_factor_bound
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Fintype N] :
    Fintype.card (KeptState Obs terminal binary start) ≤
      Fintype.card N * Fintype.card Obs.M := by
  exact kept_state_card_le

end FixedHCFGv44
end LeanCfgProject
