import LeanCfgProject.FixedHCFG.V62CFGNormalizationBinaryReverse

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Short terminal witnesses for productive sentential forms

The binarization-thickness argument needs a quantitative fact slightly more
general than the nonterminal thickness definition.  If every old nonterminal
is productive (the manuscript starts from a reduced CFG), then each symbol of
an old sentential form has a short terminal realization.  Concatenating those
realizations gives a terminal word of length at most

`|u| * max tau 1`.

This is the reusable quantitative core for bounding the fresh helper
nonterminals introduced by long-rule binarization.
-/

/-- Reducedness component used by the executable normalization: every NT is productive. -/
def V62CFGAllProductive {T : Type*} (g : ContextFreeGrammar T) : Prop :=
  ∀ A : g.NT, V62CFGProductive g A

/-- One grammar symbol has a terminal realization of length at most `max tau 1`. -/
theorem v62_short_word_from_symbol
    {T : Type*} {g : ContextFreeGrammar T} {tau : Nat}
    (hTau : V62CFGThicknessBound g tau)
    (hAll : V62CFGAllProductive g)
    (x : Symbol T g.NT) :
    ∃ w : List T,
      g.Derives [x] (w.map (@Symbol.terminal T g.NT)) ∧
      w.length ≤ max tau 1 := by
  cases x with
  | terminal a =>
      refine ⟨[a], ?_, ?_⟩
      · exact ContextFreeGrammar.Derives.refl _
      · simpa using (Nat.le_max_right tau 1)
  | nonterminal A =>
      rcases hTau A (hAll A) with ⟨w, hw, hlen⟩
      refine ⟨w, hw, hlen.trans ?_⟩
      exact Nat.le_max_left tau 1

/--
A whole old sentential form has a short terminal realization, with cost linear
in its number of symbols.
-/
theorem v62_short_word_from_sentential
    {T : Type*} {g : ContextFreeGrammar T} {tau : Nat}
    (hTau : V62CFGThicknessBound g tau)
    (hAll : V62CFGAllProductive g)
    (u : List (Symbol T g.NT)) :
    ∃ w : List T,
      g.Derives u (w.map (@Symbol.terminal T g.NT)) ∧
      w.length ≤ u.length * max tau 1 := by
  induction u with
  | nil =>
      refine ⟨[], ?_, by simp⟩
      exact ContextFreeGrammar.Derives.refl []
  | cons x xs ih =>
      rcases v62_short_word_from_symbol hTau hAll x with
        ⟨wx, hx, hxlen⟩
      rcases ih with ⟨ws, hs, hslen⟩
      refine ⟨wx ++ ws, ?_, ?_⟩
      · have h₁ := hx.append_right xs
        have h₂ := hs.append_left
          (wx.map (@Symbol.terminal T g.NT))
        have h := h₁.trans h₂
        simpa [List.map_append, List.append_assoc] using h
      · calc
          (wx ++ ws).length = wx.length + ws.length := by simp
          _ ≤ max tau 1 + xs.length * max tau 1 :=
            Nat.add_le_add hxlen hslen
          _ = (x :: xs).length * max tau 1 := by
            simp [Nat.succ_mul, Nat.add_comm]

end FixedHCFG
end LeanCfgProject
