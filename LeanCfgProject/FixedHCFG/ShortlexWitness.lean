import Mathlib.Data.List.Shortlex
import Mathlib.Order.RelClasses
import LeanCfgProject.FixedHCFG.EnrichedExtraction

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-- The manuscript's shortlex order on terminal words. -/
abbrev WordShortlex {Sigma : Type u} [LT Sigma] : Word Sigma → Word Sigma → Prop :=
  List.Shortlex (fun a b : Sigma => a < b)

/-- Shortlex on words is well founded whenever the alphabet order is. -/
theorem wordShortlex_wf {Sigma : Type u} [LT Sigma] [WellFoundedLT Sigma] :
    WellFounded (WordShortlex (Sigma := Sigma)) :=
  List.Shortlex.wf wellFounded_lt

/-- Lexicographic shortlex on context pairs, as in Section 4 of the manuscript. -/
abbrev ContextShortlex {Sigma : Type u} [LT Sigma] :
    (Word Sigma × Word Sigma) → (Word Sigma × Word Sigma) → Prop :=
  Prod.Lex (WordShortlex (Sigma := Sigma)) (WordShortlex (Sigma := Sigma))

/-- Lexicographic shortlex on context pairs is well founded. -/
theorem contextShortlex_wf {Sigma : Type u} [LT Sigma] [WellFoundedLT Sigma] :
    WellFounded (ContextShortlex (Sigma := Sigma)) :=
  (wordShortlex_wf (Sigma := Sigma)).prod_lex
    (wordShortlex_wf (Sigma := Sigma))

/--
Appending the same suffix preserves strict shortlex.  Mathlib already provides
prefix compatibility; this is the companion fact needed for the canonical-yield
root decomposition.
-/
theorem wordShortlex_append_right_same
    {Sigma : Type u} [LinearOrder Sigma]
    {x y : Word Sigma} (hxy : WordShortlex x y) (t : Word Sigma) :
    WordShortlex (x ++ t) (y ++ t) := by
  rcases List.shortlex_def.mp hxy with hlen | ⟨hlen, hlex⟩
  · apply List.Shortlex.of_length_lt
    simpa [List.length_append] using Nat.add_lt_add_right hlen t.length
  · apply List.Shortlex.of_lex
    · simp [List.length_append, hlen]
    · induction hlex with
      | nil =>
          simp at hlen
      | @rel a b as bs hab =>
          exact List.Lex.rel hab
      | @cons a as bs htail ih =>
          have htailLen : as.length = bs.length := by
            simpa using hlen
          exact List.Lex.cons (ih htailLen)

/-- Terminal yields of a retained typed state. -/
def TypedYieldSet {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Set (Word Sigma) :=
  {w | TypedDerives Obs terminal binary X.1 w}

/-- Every retained state has a nonempty terminal-yield set. -/
theorem typedYieldSet_nonempty {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) :
    (TypedYieldSet X).Nonempty := by
  exact X.property.1

/-- The manuscript's shortlex-least terminal yield `omega(X)`. -/
noncomputable def shortlexOmega {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Word Sigma :=
  (wordShortlex_wf (Sigma := Sigma)).min (TypedYieldSet X)
    (typedYieldSet_nonempty X)

/-- The shortlex canonical yield is genuinely derivable. -/
theorem shortlexOmega_spec {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) :
    TypedDerives Obs terminal binary X.1 (shortlexOmega X) := by
  exact (wordShortlex_wf (Sigma := Sigma)).min_mem
    (TypedYieldSet X) (typedYieldSet_nonempty X)

/-- No derivable word is strictly shortlex-smaller than `omega(X)`. -/
theorem shortlexOmega_minimal {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start)
    {w : Word Sigma}
    (hw : TypedDerives Obs terminal binary X.1 w) :
    ¬ WordShortlex w (shortlexOmega X) := by
  simpa [shortlexOmega, TypedYieldSet] using
    ((wordShortlex_wf (Sigma := Sigma)).not_lt_min
      (TypedYieldSet X) hw)

/-- Terminal contexts in which a retained typed state occurs. -/
def TypedContextSet {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) :
    Set (Word Sigma × Word Sigma) :=
  {c | TypedOccurs Obs terminal binary start X.1 c.1 c.2}

/-- Every retained state has at least one terminal context. -/
theorem typedContextSet_nonempty {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) :
    (TypedContextSet X).Nonempty := by
  rcases X.property.2 with ⟨u, v, hOcc⟩
  exact ⟨(u, v), hOcc⟩

/-- The manuscript's lexicographic-shortlex least context pair `chi(X)`. -/
noncomputable def shortlexChi {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Word Sigma × Word Sigma :=
  (contextShortlex_wf (Sigma := Sigma)).min (TypedContextSet X)
    (typedContextSet_nonempty X)

noncomputable def shortlexLeftCtx {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Word Sigma :=
  (shortlexChi X).1

noncomputable def shortlexRightCtx {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Word Sigma :=
  (shortlexChi X).2

/-- The canonical context pair is a genuine typed occurrence. -/
theorem shortlexChi_spec {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) :
    TypedOccurs Obs terminal binary start X.1
      (shortlexLeftCtx X) (shortlexRightCtx X) := by
  exact (contextShortlex_wf (Sigma := Sigma)).min_mem
    (TypedContextSet X) (typedContextSet_nonempty X)

/-- Direct start states have the canonical empty context. -/
theorem shortlexChi_start_empty {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start)
    (hStart : keptStart X) :
    shortlexLeftCtx X = [] ∧ shortlexRightCtx X = [] := by
  have hEmpty : ([], []) ∈ TypedContextSet X := by
    exact keptStart_occurs_empty X hStart
  have hMin := (contextShortlex_wf (Sigma := Sigma)).not_lt_min
    (TypedContextSet X) hEmpty
  have hSpec := shortlexChi_spec X
  have hPair : shortlexChi X = ([], []) := by
    rcases shortlexChi X with ⟨u, v⟩
    by_cases hu : u = []
    · subst u
      by_cases hv : v = []
      · rfl
      · have hNil : WordShortlex ([] : Word Sigma) v :=
          (List.shortlex_nil_or_eq_nil v).resolve_right hv
        have hLess : ContextShortlex (Sigma := Sigma) ([], []) ([], v) :=
          Prod.Lex.right rfl hNil
        exact (hMin hLess).elim
    · have hNil : WordShortlex ([] : Word Sigma) u :=
        (List.shortlex_nil_or_eq_nil u).resolve_right hu
      have hLess : ContextShortlex (Sigma := Sigma) ([], []) (u, v) :=
        Prod.Lex.left _ _ hNil
      exact (hMin hLess).elim
  constructor
  · simpa [shortlexLeftCtx, hPair]
  · simpa [shortlexRightCtx, hPair]

/--
Shortlex root decomposition.  If the canonical yield of `X` begins with a
binary rule `X -> Y Z`, then both child yields are themselves canonical.  This
is the proof-theoretic content used in manuscript Lemma 4.8.
-/
theorem shortlexOmega_root_decomposition
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) :
    (∃ a : Sigma, keptTerminal X a ∧ shortlexOmega X = [a]) ∨
    (∃ Y Z : KeptState Obs terminal binary start,
      keptBinary X Y Z ∧
      shortlexOmega X = shortlexOmega Y ++ shortlexOmega Z) := by
  rcases X with ⟨⟨A, p, m, n⟩, hKeep⟩
  let Xs : KeptState Obs terminal binary start :=
    ⟨{ label := A, yieldType := p, leftType := m, rightType := n }, hKeep⟩
  have d := shortlexOmega_spec Xs
  cases d with
  | @terminal A a p m n hrule htype =>
      left
      exact ⟨a, ⟨hrule, htype⟩, rfl⟩
  | @binary A B C p m n q r x y hrule hproduct leftDeriv rightDeriv =>
      rcases hKeep.2 with ⟨u, v, hOcc⟩
      have hYKeep : TypedKept Obs terminal binary start
          { label := B, yieldType := q, leftType := m,
            rightType := Obs.mul r n } := by
        constructor
        · exact ⟨x, leftDeriv⟩
        · exact ⟨u, y ++ v,
            TypedOccurs.left hOcc hrule hproduct rightDeriv⟩
      have hZKeep : TypedKept Obs terminal binary start
          { label := C, yieldType := r, leftType := Obs.mul m q,
            rightType := n } := by
        constructor
        · exact ⟨y, rightDeriv⟩
        · exact ⟨u ++ x, v,
            TypedOccurs.right hOcc hrule hproduct leftDeriv⟩
      let Ys : KeptState Obs terminal binary start :=
        ⟨{ label := B, yieldType := q, leftType := m,
           rightType := Obs.mul r n }, hYKeep⟩
      let Zs : KeptState Obs terminal binary start :=
        ⟨{ label := C, yieldType := r, leftType := Obs.mul m q,
           rightType := n }, hZKeep⟩
      have hx : x = shortlexOmega Ys := by
        rcases trichotomous_of (WordShortlex (Sigma := Sigma))
            (shortlexOmega Ys) x with hsmall | heq | hlarge
        · have hNew : TypedDerives Obs terminal binary Xs.1
              (shortlexOmega Ys ++ y) :=
            TypedDerives.binary hrule hproduct
              (shortlexOmega_spec Ys) rightDeriv
          have hlt : WordShortlex
              (shortlexOmega Ys ++ y) (x ++ y) :=
            wordShortlex_append_right_same hsmall y
          exact (shortlexOmega_minimal Xs hNew hlt).elim
        · exact heq.symm
        · exact (shortlexOmega_minimal Ys leftDeriv hlarge).elim
      have hy : y = shortlexOmega Zs := by
        rcases trichotomous_of (WordShortlex (Sigma := Sigma))
            (shortlexOmega Zs) y with hsmall | heq | hlarge
        · have hNew : TypedDerives Obs terminal binary Xs.1
              (x ++ shortlexOmega Zs) :=
            TypedDerives.binary hrule hproduct
              leftDeriv (shortlexOmega_spec Zs)
          have hlt : WordShortlex
              (x ++ shortlexOmega Zs) (x ++ y) :=
            List.Shortlex.append_left hsmall x
          exact (shortlexOmega_minimal Xs hNew hlt).elim
        · exact heq.symm
        · exact (shortlexOmega_minimal Zs rightDeriv hlarge).elim
      right
      refine ⟨Ys, Zs, ?_, ?_⟩
      · exact ⟨hrule, hproduct, rfl, rfl, rfl, rfl⟩
      · simpa [hx, hy]

end FixedHCFG
end LeanCfgProject
