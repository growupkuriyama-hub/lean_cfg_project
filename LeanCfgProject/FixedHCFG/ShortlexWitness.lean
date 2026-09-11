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

/-- Equal-length lexicographic comparison is preserved by a common suffix. -/
theorem lex_append_right_same_of_length_eq
    {Sigma : Type u} [LinearOrder Sigma]
    {x y : Word Sigma}
    (hlen : x.length = y.length)
    (hlex : List.Lex (fun a b : Sigma => a < b) x y)
    (t : Word Sigma) :
    List.Lex (fun a b : Sigma => a < b) (x ++ t) (y ++ t) := by
  induction x generalizing y with
  | nil =>
      cases y with
      | nil => cases hlex
      | cons b ys => simp at hlen
  | cons a xs ih =>
      cases y with
      | nil => simp at hlen
      | cons b ys =>
          cases hlex with
          | rel hab => exact List.Lex.rel hab
          | cons htail =>
              apply List.Lex.cons
              apply ih
              · simpa using hlen
              · exact htail

/-- Appending the same suffix preserves strict shortlex. -/
theorem wordShortlex_append_right_same
    {Sigma : Type u} [LinearOrder Sigma]
    {x y : Word Sigma} (hxy : WordShortlex x y) (t : Word Sigma) :
    WordShortlex (x ++ t) (y ++ t) := by
  rcases List.shortlex_def.mp hxy with hlen | ⟨hlen, hlex⟩
  · apply List.Shortlex.of_length_lt
    simpa [List.length_append] using Nat.add_lt_add_right hlen t.length
  · apply List.Shortlex.of_lex
    · simp [List.length_append, hlen]
    · exact lex_append_right_same_of_length_eq hlen hlex t

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
  have hNoLess : ∀ c ∈ TypedContextSet X,
      ¬ ContextShortlex (Sigma := Sigma) c ([], []) := by
    intro c hc hlt
    rcases c with ⟨u, v⟩
    cases hlt with
    | left _ _ hu =>
        exact (List.not_shortlex_nil_right hu).elim
    | right hu hv =>
        exact (List.not_shortlex_nil_right hv).elim
  have hPair : shortlexChi X = ([], []) := by
    unfold shortlexChi
    exact (contextShortlex_wf (Sigma := Sigma)).min_eq_of_forall_not_lt
      hEmpty hNoLess
  constructor
  · simp [shortlexLeftCtx, hPair]
  · simp [shortlexRightCtx, hPair]

/-- A retained binary rule combines derivations of its two retained children. -/
theorem keptBinary_derives
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    {X Y Z : KeptState Obs terminal binary start}
    (hRule : keptBinary X Y Z)
    {x y : Word Sigma}
    (dx : TypedDerives Obs terminal binary Y.1 x)
    (dy : TypedDerives Obs terminal binary Z.1 y) :
    TypedDerives Obs terminal binary X.1 (x ++ y) := by
  rcases X with ⟨⟨A, p, m, n⟩, hX⟩
  rcases Y with ⟨⟨B, q, mY, nY⟩, hY⟩
  rcases Z with ⟨⟨C, r, mZ, nZ⟩, hZ⟩
  change binary A B C ∧ Obs.mul q r = p ∧
    mY = m ∧ nY = Obs.mul r n ∧
    mZ = Obs.mul m q ∧ nZ = n at hRule
  rcases hRule with ⟨hBC, hProduct, hmY, hnY, hmZ, hnZ⟩
  subst mY
  subst nY
  subst mZ
  subst nZ
  exact TypedDerives.binary hBC hProduct dx dy

/-- Root-shape inversion for a derivation from a retained typed state. -/
theorem keptDerives_root_shape
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start)
    {w : Word Sigma}
    (d : TypedDerives Obs terminal binary X.1 w) :
    (∃ a : Sigma, keptTerminal X a ∧ w = [a]) ∨
    (∃ Y Z : KeptState Obs terminal binary start,
      keptBinary X Y Z ∧
      ∃ x y : Word Sigma,
        w = x ++ y ∧
        TypedDerives Obs terminal binary Y.1 x ∧
        TypedDerives Obs terminal binary Z.1 y) := by
  rcases X with ⟨⟨A, p, m, n⟩, hKeep⟩
  cases d with
  | @terminal A a p m n hrule htype =>
      exact Or.inl ⟨a, ⟨hrule, htype⟩, rfl⟩
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
      let Y : KeptState Obs terminal binary start :=
        ⟨{ label := B, yieldType := q, leftType := m,
           rightType := Obs.mul r n }, hYKeep⟩
      let Z : KeptState Obs terminal binary start :=
        ⟨{ label := C, yieldType := r, leftType := Obs.mul m q,
           rightType := n }, hZKeep⟩
      exact Or.inr ⟨Y, Z,
        ⟨hrule, hproduct, rfl, rfl, rfl, rfl⟩,
        x, y, rfl, leftDeriv, rightDeriv⟩

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
  rcases keptDerives_root_shape X (shortlexOmega_spec X) with hTerm | hBin
  · rcases hTerm with ⟨a, hRule, hWord⟩
    exact Or.inl ⟨a, hRule, hWord⟩
  · rcases hBin with ⟨Y, Z, hRule, x, y, hWord, dx, dy⟩
    have hx : x = shortlexOmega Y := by
      rcases trichotomous_of (WordShortlex (Sigma := Sigma))
          (shortlexOmega Y) x with hsmall | heq | hlarge
      · have hNew : TypedDerives Obs terminal binary X.1
            (shortlexOmega Y ++ y) :=
          keptBinary_derives hRule (shortlexOmega_spec Y) dy
        have hlt0 : WordShortlex
            (shortlexOmega Y ++ y) (x ++ y) :=
          wordShortlex_append_right_same hsmall y
        have hlt : WordShortlex
            (shortlexOmega Y ++ y) (shortlexOmega X) := by
          rw [hWord]
          exact hlt0
        exact (shortlexOmega_minimal X hNew hlt).elim
      · exact heq.symm
      · exact (shortlexOmega_minimal Y dx hlarge).elim
    have hy : y = shortlexOmega Z := by
      rcases trichotomous_of (WordShortlex (Sigma := Sigma))
          (shortlexOmega Z) y with hsmall | heq | hlarge
      · have hNew : TypedDerives Obs terminal binary X.1
            (x ++ shortlexOmega Z) :=
          keptBinary_derives hRule dx (shortlexOmega_spec Z)
        have hlt0 : WordShortlex
            (x ++ shortlexOmega Z) (x ++ y) :=
          List.Shortlex.append_left hsmall x
        have hlt : WordShortlex
            (x ++ shortlexOmega Z) (shortlexOmega X) := by
          rw [hWord]
          exact hlt0
        exact (shortlexOmega_minimal X hNew hlt).elim
      · exact heq.symm
      · exact (shortlexOmega_minimal Z dy hlarge).elim
    exact Or.inr ⟨Y, Z, hRule, by
      calc
        shortlexOmega X = x ++ y := hWord
        _ = shortlexOmega Y ++ shortlexOmega Z := by rw [hx, hy]⟩

end FixedHCFG
end LeanCfgProject
