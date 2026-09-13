import LeanCfgProject.FixedHCFGv44.CharacteristicDataBounds

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Manuscript-facing assembly of Lemma 7 (`short canonical witnesses`).

The cycle-deletion arithmetic and canonical-minimum bridges are already proved
in `LinearWitnessBounds`.  What remains for the normalization layer is to
supply the concrete short derivation/reaching-context candidates guaranteed by
the linear-spine shape.  This structure isolates exactly that obligation.
-/

/--
A certificate containing exactly the witnesses supplied by the two cases in
the appendix proof: spine symbols and fresh terminal wrappers.
-/
structure LinearSpineWitnessCertificate
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (n : Nat) where
  isWrapper : KeptState Obs terminal binary start → Prop
  positive : 0 < n
  wrapperTerminal : ∀ X : KeptState Obs terminal binary start,
    isWrapper X → ∃ a : Sigma, keptTerminal X a
  spineYieldCandidate : ∀ X : KeptState Obs terminal binary start,
    ¬ isWrapper X →
      ∃ z : Word Sigma,
        TypedDerives Obs terminal binary X.1 z ∧ z.length ≤ n
  spineContextCandidate : ∀ X : KeptState Obs terminal binary start,
    ¬ isWrapper X →
      ∃ l r : Word Sigma,
        TypedOccurs Obs terminal binary start X.1 l r ∧
          l.length + r.length ≤ n - 1
  wrapperContextCandidate : ∀ X : KeptState Obs terminal binary start,
    isWrapper X →
      ∃ l r : Word Sigma,
        TypedOccurs Obs terminal binary start X.1 l r ∧
          l.length + r.length < 2 * n

/-- The certificate implies the manuscript's `|omega(X)| <= n` bound. -/
theorem certified_canonicalOmega_length_le
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N} {n : Nat}
    (C : LinearSpineWitnessCertificate Obs terminal binary start n)
    (X : KeptState Obs terminal binary start) :
    (canonicalOmega X).length ≤ n := by
  classical
  by_cases hWrapper : C.isWrapper X
  · rcases C.wrapperTerminal X hWrapper with ⟨a, hRule⟩
    have hDeriv : TypedDerives Obs terminal binary X.1 [a] :=
      keptTerminal_derives X a hRule
    have hCan := canonicalOmega_length_le_of_derives X hDeriv
    simp only [List.length_singleton] at hCan
    omega
  · rcases C.spineYieldCandidate X hWrapper with ⟨z, hDeriv, hLen⟩
    exact le_trans (canonicalOmega_length_le_of_derives X hDeriv) hLen

/-- The certificate implies the manuscript's `|u_X|+|v_X| <= 2n` bound. -/
theorem certified_canonicalChi_length_le
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N} {n : Nat}
    (C : LinearSpineWitnessCertificate Obs terminal binary start n)
    (X : KeptState Obs terminal binary start) :
    (canonicalLeftCtx X).length + (canonicalRightCtx X).length ≤ 2 * n := by
  classical
  by_cases hWrapper : C.isWrapper X
  · rcases C.wrapperContextCandidate X hWrapper with
      ⟨l, r, hOcc, hLen⟩
    have hCan := canonicalChi_total_length_le_of_occurs X hOcc
    exact le_trans hCan (Nat.le_of_lt hLen)
  · rcases C.spineContextCandidate X hWrapper with
      ⟨l, r, hOcc, hLen⟩
    have hCan := canonicalChi_total_length_le_of_occurs X hOcc
    have hShort : l.length + r.length ≤ 2 * n := by omega
    exact le_trans hCan hShort

/--
Lemma 7, first two displayed inequalities, packaged exactly in the form used
by the characteristic-data argument.
-/
theorem short_canonical_witnesses
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N} {n : Nat}
    (C : LinearSpineWitnessCertificate Obs terminal binary start n) :
    (∀ X : KeptState Obs terminal binary start,
      (canonicalOmega X).length ≤ n) ∧
    (∀ X : KeptState Obs terminal binary start,
      (canonicalLeftCtx X).length + (canonicalRightCtx X).length ≤ 2 * n) := by
  constructor
  · exact certified_canonicalOmega_length_le C
  · exact certified_canonicalChi_length_le C

/--
Consequently every exact canonical characteristic word has length at most
`4n`.  This is the formal version of the final sentence of the short-witness
lemma, with an explicit constant rather than asymptotic notation.
-/
theorem certified_canonicalCS_word_length_le_four_mul
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N} {n : Nat}
    (epsilonStart : Prop)
    (C : LinearSpineWitnessCertificate Obs terminal binary start n)
    {z : Word Sigma}
    (hz : CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart z) :
    z.length ≤ 4 * n := by
  rcases short_canonical_witnesses C with ⟨hOmega, hCtx⟩
  exact canonicalCS_word_length_le_four_mul epsilonStart C.positive
    hOmega hCtx hz

end FixedHCFGv44
end LeanCfgProject
