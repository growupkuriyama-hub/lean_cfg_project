import LeanCfgProject.FixedHCFG.V62CFGNormalizationBinarySize

namespace LeanCfgProject
namespace FixedHCFG

/-!
# Reverse projection infrastructure for executable v62 binarization

A helper nonterminal `(r,i)` represents the still-unexpanded suffix of the
original right-hand side after the first `i+1` symbols.  We therefore project
a binary-stage symbol not to one old symbol, but to a list of old symbols.
Under this expansion every helper-chain production is an identity, while the
first production of a binarized old rule projects to that old production.

This file establishes the symbol/word projection and the helper-chain identity
lemma.  The next layer lifts it through arbitrary rewrite contexts and
derivations.
-/

/-- Expand one binary-stage symbol back to the old sentential form it denotes. -/
def v62BinarizeProjectSymbol {T N : Type*} :
    Symbol T (Sum N (ContextFreeRule T N × Nat)) → List (Symbol T N)
  | .terminal a => [.terminal a]
  | .nonterminal (.inl A) => [.nonterminal A]
  | .nonterminal (.inr (r, i)) => r.output.drop (i + 1)

/-- Expand a complete binary-stage sentential form. -/
def v62BinarizeProjectWord {T N : Type*}
    (u : List (Symbol T (Sum N (ContextFreeRule T N × Nat)))) :
    List (Symbol T N) :=
  u.flatMap v62BinarizeProjectSymbol

@[simp] theorem v62_binarize_project_lift_symbol
    {T N : Type*} (x : Symbol T N) :
    v62BinarizeProjectSymbol (v62BinarizeLiftSymbol x) = [x] := by
  cases x <;> rfl

@[simp] theorem v62_binarize_project_terminal_symbol
    {T N : Type*} (a : T) :
    v62BinarizeProjectSymbol
      (Symbol.terminal a :
        Symbol T (Sum N (ContextFreeRule T N × Nat))) =
      [Symbol.terminal a] := by
  rfl

@[simp] theorem v62_binarize_project_helper_symbol
    {T N : Type*} (r : ContextFreeRule T N) (i : Nat) :
    v62BinarizeProjectSymbol (v62BinarizeHelperSymbol r i) =
      r.output.drop (i + 1) := by
  rfl

@[simp] theorem v62_binarize_project_helper_nonterminal
    {T N : Type*} (r : ContextFreeRule T N) (i : Nat) :
    v62BinarizeProjectSymbol
        (Symbol.nonterminal (Sum.inr (r, i)) :
          Symbol T (Sum N (ContextFreeRule T N × Nat))) =
      r.output.drop (i + 1) := by
  rfl

@[simp] theorem v62_binarize_project_lift_word
    {T N : Type*} (u : List (Symbol T N)) :
    v62BinarizeProjectWord (u.map v62BinarizeLiftSymbol) = u := by
  induction u with
  | nil => rfl
  | cons x xs ih =>
      change
        v62BinarizeProjectSymbol (v62BinarizeLiftSymbol x) ++
          v62BinarizeProjectWord (xs.map v62BinarizeLiftSymbol) =
        x :: xs
      rw [v62_binarize_project_lift_symbol, ih]
      rfl

@[simp] theorem v62_binarize_project_terminal_word
    {T N : Type*} (w : List T) :
    v62BinarizeProjectWord
        (w.map (@Symbol.terminal T
          (Sum N (ContextFreeRule T N × Nat)))) =
      w.map (@Symbol.terminal T N) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      change
        v62BinarizeProjectSymbol
            (Symbol.terminal a :
              Symbol T (Sum N (ContextFreeRule T N × Nat))) ++
          v62BinarizeProjectWord
            (w.map (@Symbol.terminal T
              (Sum N (ContextFreeRule T N × Nat)))) =
        Symbol.terminal a :: w.map (@Symbol.terminal T N)
      rw [v62_binarize_project_terminal_symbol, ih]
      rfl

/--
Every helper-chain rule is invisible under suffix expansion, provided the local
suffix argument is the suffix represented by the current helper.
-/
theorem v62_binarize_tail_rule_projects_eq
    {T N : Type*} {r : ContextFreeRule T N} {i : Nat}
    {u : List (Symbol T N)}
    {q : ContextFreeRule T
      (Sum N (ContextFreeRule T N × Nat))}
    (hu : r.output.drop (i + 1) = u)
    (hq : q ∈ v62BinarizeTailRules r i u) :
    v62BinarizeProjectWord [Symbol.nonterminal q.input] =
      v62BinarizeProjectWord q.output := by
  induction u generalizing i q with
  | nil =>
      simp [v62BinarizeTailRules] at hq
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [v62BinarizeTailRules] at hq
      | cons y ys =>
          cases ys with
          | nil =>
              simp [v62BinarizeTailRules] at hq
              subst q
              simpa [v62BinarizeProjectWord] using hu
          | cons z zs =>
              simp only [v62BinarizeTailRules, List.mem_cons] at hq
              have hnext :
                  r.output.drop ((i + 1) + 1) = y :: z :: zs := by
                calc
                  r.output.drop ((i + 1) + 1) =
                      (r.output.drop (i + 1)).drop 1 := by
                    simp [List.drop_drop]
                  _ = (x :: y :: z :: zs).drop 1 := by rw [hu]
                  _ = y :: z :: zs := by rfl
              rcases hq with hq | hq
              · subst q
                simpa [v62BinarizeProjectWord, hnext] using hu
              · exact ih (i := i + 1) hnext hq

end FixedHCFG
end LeanCfgProject
