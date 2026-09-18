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

/-- Every nonterminal occurring on the right-hand side of an installed rule is productive. -/
def V62CFGRHSNonterminalsProductive {T : Type*}
    (g : ContextFreeGrammar T) : Prop :=
  ∀ r ∈ g.rules, ∀ A : g.NT,
    Symbol.nonterminal A ∈ r.output → V62CFGProductive g A

/--
Local form of the sentential witness bound: global reducedness is unnecessary
when productivity is known only for the nonterminals actually occurring in the
sentential form.
-/
theorem v62_short_word_from_sentential_of_productive_members
    {T : Type*} {g : ContextFreeGrammar T} {tau : Nat}
    (hTau : V62CFGThicknessBound g tau)
    (u : List (Symbol T g.NT))
    (hProd : ∀ A : g.NT,
      Symbol.nonterminal A ∈ u → V62CFGProductive g A) :
    ∃ w : List T,
      g.Derives u (w.map (@Symbol.terminal T g.NT)) ∧
      w.length ≤ u.length * max tau 1 := by
  induction u with
  | nil =>
      refine ⟨[], ?_, by simp⟩
      exact ContextFreeGrammar.Derives.refl []
  | cons x xs ih =>
      have hProdTail : ∀ A : g.NT,
          Symbol.nonterminal A ∈ xs → V62CFGProductive g A := by
        intro A hA
        exact hProd A (by simp [hA])
      rcases ih hProdTail with ⟨ws, hs, hslen⟩
      cases x with
      | terminal a =>
          refine ⟨a :: ws, ?_, ?_⟩
          · have h := hs.append_left [Symbol.terminal a]
            simpa using h
          · calc
              (a :: ws).length = 1 + ws.length := by
                simp [Nat.add_comm]
              _ ≤ 1 + xs.length * max tau 1 :=
                Nat.add_le_add_left hslen 1
              _ ≤ max tau 1 + xs.length * max tau 1 := by
                exact Nat.add_le_add_right (Nat.le_max_right tau 1) _
              _ = (Symbol.terminal a :: xs).length * max tau 1 := by
                simp [Nat.succ_mul, Nat.add_comm]
      | nonterminal A =>
          have hA : V62CFGProductive g A :=
            hProd A (by simp)
          rcases hTau A hA with ⟨wa, ha, halen⟩
          have halen' : wa.length ≤ max tau 1 :=
            halen.trans (Nat.le_max_left tau 1)
          refine ⟨wa ++ ws, ?_, ?_⟩
          · have h₁ := ha.append_right xs
            have h₂ := hs.append_left
              (wa.map (@Symbol.terminal T g.NT))
            have h := h₁.trans h₂
            simpa [List.map_append, List.append_assoc] using h
          · calc
              (wa ++ ws).length = wa.length + ws.length := by simp
              _ ≤ max tau 1 + xs.length * max tau 1 :=
                Nat.add_le_add halen' hslen
              _ = (Symbol.nonterminal A :: xs).length * max tau 1 := by
                simp [Nat.succ_mul, Nat.add_comm]

/--
Any suffix of the RHS of an installed rule has a short terminal realization
when every RHS nonterminal of the grammar is productive.
-/
theorem v62_short_word_from_rule_suffix
    {T : Type*} {g : ContextFreeGrammar T} {tau i : Nat}
    (hTau : V62CFGThicknessBound g tau)
    (hRHSProd : V62CFGRHSNonterminalsProductive g)
    {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    ∃ w : List T,
      g.Derives (r.output.drop i)
        (w.map (@Symbol.terminal T g.NT)) ∧
      w.length ≤ (r.output.drop i).length * max tau 1 := by
  apply v62_short_word_from_sentential_of_productive_members
    hTau (r.output.drop i)
  intro A hA
  apply hRHSProd r hr A
  exact List.mem_of_mem_drop hA

end FixedHCFG
end LeanCfgProject
