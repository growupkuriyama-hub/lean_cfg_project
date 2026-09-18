import LeanCfgProject.FixedHCFG.V62CFGNormalizationBinaryHelper

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Thickness transfer through executable v62 binarization

The old-nonterminal summand keeps the old short witnesses.  A productive
helper `(r,i)` is first recovered as an installed chain position; its
represented suffix `r.output.drop (i+1)` then receives a short terminal
realization by the local sentential witness theorem.

If every old rule has RHS length at most `rhsBound`, this yields the explicit
uniform envelope

`tau + rhsBound * max tau 1`.

For the manuscript pipeline the old grammar at this stage is the
terminal-isolated grammar, `tau` is already bounded by `tau_R+1`, and
`rhsBound` is polynomially bounded by the input grammar size.
-/

/-- Productivity of an embedded old nonterminal projects back to the old grammar. -/
theorem v62_binarized_old_productive
    {T : Type} {g : ContextFreeGrammar T} {A : g.NT}
    (hProd : V62CFGProductive
      (v62BinarizedGrammar g) (Sum.inl A)) :
    V62CFGProductive g A := by
  rcases hProd with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  unfold V62CFGDerivesWordFrom at hw ⊢
  have hp := v62_project_binarized_derives hw
  rw [v62_binarize_project_terminal_word] at hp
  simpa [v62BinarizeProjectWord, v62BinarizeProjectSymbol] using hp

/--
A productive helper has a short terminal witness controlled by the maximum old
RHS length and the old thickness bound.
-/
theorem v62_binarized_helper_short_witness
    {T : Type} {g : ContextFreeGrammar T}
    {tau rhsBound : Nat}
    (hTau : V62CFGThicknessBound g tau)
    (hRHSProd : V62CFGRHSNonterminalsProductive g)
    (hRHSBound : ∀ r ∈ g.rules, r.output.length ≤ rhsBound)
    {r : ContextFreeRule T g.NT} {i : Nat}
    (hProd : V62CFGProductive
      (v62BinarizedGrammar g) (Sum.inr (r, i))) :
    ∃ w : List T,
      V62CFGDerivesWordFrom
        (v62BinarizedGrammar g) (Sum.inr (r, i)) w ∧
      w.length ≤ rhsBound * max tau 1 := by
  rcases v62_productive_binarized_helper_data hProd with
    ⟨hr, hsuffix, hinstalled⟩
  rcases v62_short_word_from_rule_suffix
      (i := i + 1) hTau hRHSProd hr with
    ⟨w, hold, hwlen⟩
  have htail :
      (v62BinarizedGrammar g).Derives
        [v62BinarizeHelperSymbol r i]
        ((r.output.drop (i + 1)).map v62BinarizeLiftSymbol) :=
    v62_binarize_tail_derives g r i
      (r.output.drop (i + 1)) hinstalled hsuffix
  have hsim := v62_binarization_simulates_derives hold
  have hall := htail.trans hsim
  refine ⟨w, ?_, ?_⟩
  · unfold V62CFGDerivesWordFrom
    simpa [v62BinarizeHelperSymbol] using hall
  · have hdrop :
        (r.output.drop (i + 1)).length ≤ r.output.length := by
      simp only [List.length_drop]
      omega
    have hmul₁ :
        (r.output.drop (i + 1)).length * max tau 1 ≤
          r.output.length * max tau 1 :=
      Nat.mul_le_mul_right (max tau 1) hdrop
    have hmul₂ :
        r.output.length * max tau 1 ≤
          rhsBound * max tau 1 :=
      Nat.mul_le_mul_right (max tau 1) (hRHSBound r hr)
    exact hwlen.trans (hmul₁.trans hmul₂)

/-- Explicit uniform thickness envelope for the binary stage. -/
def V62CFGBinarizationThicknessEnvelope (tau rhsBound : Nat) : Nat :=
  tau + rhsBound * max tau 1

/--
Long-rule binarization preserves a polynomial thickness bound.  The only
structural premise beyond the old thickness bound is productivity of
nonterminals appearing on installed RHSs, exactly the reducedness information
used by the manuscript.
-/
theorem v62_binarization_preserves_thickness_bound
    {T : Type} {g : ContextFreeGrammar T}
    {tau rhsBound : Nat}
    (hTau : V62CFGThicknessBound g tau)
    (hRHSProd : V62CFGRHSNonterminalsProductive g)
    (hRHSBound : ∀ r ∈ g.rules, r.output.length ≤ rhsBound) :
    V62CFGThicknessBound (v62BinarizedGrammar g)
      (V62CFGBinarizationThicknessEnvelope tau rhsBound) := by
  intro A hProd
  cases A with
  | inl B =>
      have hOldProd : V62CFGProductive g B :=
        v62_binarized_old_productive hProd
      rcases hTau B hOldProd with ⟨w, hw, hlen⟩
      refine ⟨w, v62_binarization_preserves_old_word_derivation hw, ?_⟩
      unfold V62CFGBinarizationThicknessEnvelope
      exact hlen.trans (Nat.le_add_right _ _)
  | inr p =>
      rcases p with ⟨r, i⟩
      rcases v62_binarized_helper_short_witness
          hTau hRHSProd hRHSBound hProd with
        ⟨w, hw, hlen⟩
      refine ⟨w, hw, ?_⟩
      unfold V62CFGBinarizationThicknessEnvelope
      exact hlen.trans (Nat.le_add_left _ _)

end FixedHCFG
end LeanCfgProject
