import LeanCfgProject.FixedHCFG.V60CanonicalBasis
import LeanCfgProject.FixedHCFG.V60CanonicalBounds

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Generic length bounds for the concrete v60 witness set.

The fixed-window and linear-spine sections only need to provide uniform bounds
on canonical yields and canonical contexts.  The arithmetic below then turns
those local bounds into the displayed characteristic-witness bound.
-/

/-- Length of a canonical anchor from local yield/context bounds. -/
theorem v60CanonicalAnchorWord_length_le
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start)
    {B C : Nat}
    (hOmega : (v60CanonicalOmega X).length ≤ B)
    (hCtx : (v60CanonicalLeftCtx X).length +
      (v60CanonicalRightCtx X).length ≤ C) :
    (v60CanonicalAnchorWord X).length ≤ C + B := by
  simp only [v60CanonicalAnchorWord, List.length_append]
  omega

/-- Length of a canonical terminal-rule observation. -/
theorem v60CanonicalTerminalWord_length_le
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) (a : Sigma)
    {C : Nat}
    (hCtx : (v60CanonicalLeftCtx X).length +
      (v60CanonicalRightCtx X).length ≤ C) :
    (v60CanonicalTerminalWord X a).length ≤ C + 1 := by
  simp only [v60CanonicalTerminalWord, List.length_append, List.length_singleton]
  omega

/-- Length of a canonical binary-rule observation. -/
theorem v60CanonicalBinaryWord_length_le
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X Y Z : V60KeptState Obs terminal binary start)
    {B C : Nat}
    (hOmegaY : (v60CanonicalOmega Y).length ≤ B)
    (hOmegaZ : (v60CanonicalOmega Z).length ≤ B)
    (hCtx : (v60CanonicalLeftCtx X).length +
      (v60CanonicalRightCtx X).length ≤ C) :
    (v60CanonicalBinaryWord X Y Z).length ≤ C + 2 * B := by
  simp only [v60CanonicalBinaryWord, List.length_append]
  omega

/--
Uniform local bounds imply a uniform bound for every word in the exact v60
characteristic witness set.
-/
theorem v60CanonicalWitnessSet_word_length_le
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (epsilonStart : Prop)
    (B C : Nat)
    (hOmega : ∀ X : V60KeptState Obs terminal binary start,
      (v60CanonicalOmega X).length ≤ B)
    (hCtx : ∀ X : V60KeptState Obs terminal binary start,
      (v60CanonicalLeftCtx X).length +
        (v60CanonicalRightCtx X).length ≤ C)
    {z : Word Sigma}
    (hz : V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart z) :
    z.length ≤ C + 2 * B + 1 := by
  rcases hz with hAnchor | hTerminal | hBinary | hEps
  · rcases hAnchor with ⟨X, rfl⟩
    have h := v60CanonicalAnchorWord_length_le X (hOmega X) (hCtx X)
    omega
  · rcases hTerminal with ⟨X, a, hRule, rfl⟩
    have h := v60CanonicalTerminalWord_length_le X a (hCtx X)
    omega
  · rcases hBinary with ⟨X, Y, Z, hRule, rfl⟩
    have h := v60CanonicalBinaryWord_length_le X Y Z
      (hOmega Y) (hOmega Z) (hCtx X)
    omega
  · rcases hEps with ⟨rfl, hEps⟩
    simp

/-- Existence of any short successful context transfers to the canonical one. -/
theorem v60CanonicalChi_total_length_le_of_exists
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start)
    (C : Nat)
    (hExists : ∃ u v : Word Sigma,
      V60TypedOccurs Obs terminal binary start X.1 u v ∧
        u.length + v.length ≤ C) :
    (v60CanonicalLeftCtx X).length + (v60CanonicalRightCtx X).length ≤ C := by
  rcases hExists with ⟨u, v, hOcc, hLen⟩
  exact le_trans (v60CanonicalChi_total_length_le X hOcc) hLen

/-- Existence of any short yield transfers to the canonical shortlex yield. -/
theorem v60CanonicalOmega_length_le_of_exists
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start)
    (B : Nat)
    (hExists : ∃ w : Word Sigma,
      V60YieldTypedDerives Obs terminal binary X.1 w ∧ w.length ≤ B) :
    (v60CanonicalOmega X).length ≤ B := by
  rcases hExists with ⟨w, hDeriv, hLen⟩
  exact le_trans (v60CanonicalOmega_length_le X hDeriv) hLen

end FixedHCFG
end LeanCfgProject
