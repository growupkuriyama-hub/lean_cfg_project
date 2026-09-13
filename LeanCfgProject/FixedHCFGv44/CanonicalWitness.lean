import Mathlib.Data.List.Shortlex
import Mathlib.Order.RelClasses
import LeanCfgProject.FixedHCFGv44.WitnessEndToEnd

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-- The shortlex order fixed in the revised manuscript. -/
abbrev WordShortlex {Sigma : Type u} [LT Sigma] : Word Sigma → Word Sigma → Prop :=
  List.Shortlex (fun a b : Sigma => a < b)

/-- Shortlex is well founded when the fixed alphabet order is well founded. -/
theorem wordShortlex_wf
    {Sigma : Type u} [LT Sigma] [WellFoundedLT Sigma] :
    WellFounded (WordShortlex (Sigma := Sigma)) :=
  List.Shortlex.wf wellFounded_lt

/-- Shortlex tie-breaking on the left and then right context words. -/
abbrev ContextShortlex {Sigma : Type u} [LT Sigma] :
    (Word Sigma × Word Sigma) → (Word Sigma × Word Sigma) → Prop :=
  Prod.Lex (WordShortlex (Sigma := Sigma)) (WordShortlex (Sigma := Sigma))

/-- The pairwise shortlex tie-breaker is well founded. -/
theorem contextShortlex_wf
    {Sigma : Type u} [LT Sigma] [WellFoundedLT Sigma] :
    WellFounded (ContextShortlex (Sigma := Sigma)) :=
  (wordShortlex_wf (Sigma := Sigma)).prod_lex
    (wordShortlex_wf (Sigma := Sigma))

/-- Manuscript key for contexts: total length, then left shortlex, then right shortlex. -/
def contextCanonicalKey {Sigma : Type u}
    (c : Word Sigma × Word Sigma) :
    Nat × (Word Sigma × Word Sigma) :=
  (c.1.length + c.2.length, c)

/-- The exact context order used for the revised canonical witness `chi(X)`. -/
abbrev ContextCanonicalOrder {Sigma : Type u} [LT Sigma] :
    (Word Sigma × Word Sigma) → (Word Sigma × Word Sigma) → Prop :=
  fun c d =>
    Prod.Lex (fun a b : Nat => a < b) (ContextShortlex (Sigma := Sigma))
      (contextCanonicalKey c) (contextCanonicalKey d)

/-- Total-length-first context canonicality is well founded. -/
theorem contextCanonicalOrder_wf
    {Sigma : Type u} [LinearOrder Sigma] [WellFoundedLT Sigma] :
    WellFounded (ContextCanonicalOrder (Sigma := Sigma)) := by
  have hNat : WellFounded ((fun a b : Nat => a < b)) := wellFounded_lt
  have hKey : WellFounded
      (Prod.Lex (fun a b : Nat => a < b)
        (ContextShortlex (Sigma := Sigma))) :=
    hNat.prod_lex (contextShortlex_wf (Sigma := Sigma))
  exact hKey.onFun contextCanonicalKey

/-- Terminal yields of a retained yield-typed state. -/
def CanonicalYieldSet
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Set (Word Sigma) :=
  {w | TypedDerives Obs terminal binary X.1 w}

/-- The yield set of every retained state is nonempty. -/
theorem canonicalYieldSet_nonempty
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) :
    (CanonicalYieldSet X).Nonempty := by
  exact X.property.1

/-- The revised manuscript's shortlex-minimal terminal yield `omega(X)`. -/
noncomputable def canonicalOmega
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Word Sigma :=
  (wordShortlex_wf (Sigma := Sigma)).min
    (CanonicalYieldSet X) (canonicalYieldSet_nonempty X)

/-- The canonical yield is genuinely derivable. -/
theorem canonicalOmega_spec
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) :
    TypedDerives Obs terminal binary X.1 (canonicalOmega X) := by
  exact (wordShortlex_wf (Sigma := Sigma)).min_mem
    (CanonicalYieldSet X) (canonicalYieldSet_nonempty X)

/-- No derivable yield precedes `omega(X)` in shortlex. -/
theorem canonicalOmega_minimal
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start)
    {w : Word Sigma}
    (hw : TypedDerives Obs terminal binary X.1 w) :
    ¬ WordShortlex w (canonicalOmega X) := by
  simpa [canonicalOmega, CanonicalYieldSet] using
    ((wordShortlex_wf (Sigma := Sigma)).not_lt_min
      (CanonicalYieldSet X) hw)

/-- Terminal reaching contexts of a retained state. -/
def CanonicalContextSet
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) :
    Set (Word Sigma × Word Sigma) :=
  {c | TypedOccurs Obs terminal binary start X.1 c.1 c.2}

/-- Every retained state has at least one terminal reaching context. -/
theorem canonicalContextSet_nonempty
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) :
    (CanonicalContextSet X).Nonempty := by
  rcases X.property.2 with ⟨u, v, hOcc⟩
  exact ⟨(u, v), hOcc⟩

/--
The revised canonical reaching context `chi(X)`: minimum total context length,
then shortlex on the left component, then shortlex on the right component.
-/
noncomputable def canonicalChi
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Word Sigma × Word Sigma :=
  (contextCanonicalOrder_wf (Sigma := Sigma)).min
    (CanonicalContextSet X) (canonicalContextSet_nonempty X)

noncomputable def canonicalLeftCtx
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Word Sigma :=
  (canonicalChi X).1

noncomputable def canonicalRightCtx
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Word Sigma :=
  (canonicalChi X).2

/-- The canonical context is a genuine terminal reaching context. -/
theorem canonicalChi_spec
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) :
    TypedOccurs Obs terminal binary start X.1
      (canonicalLeftCtx X) (canonicalRightCtx X) := by
  exact (contextCanonicalOrder_wf (Sigma := Sigma)).min_mem
    (CanonicalContextSet X) (canonicalContextSet_nonempty X)

/-- No reaching context precedes `chi(X)` in the manuscript's canonical order. -/
theorem canonicalChi_minimal
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start)
    {u v : Word Sigma}
    (hOcc : TypedOccurs Obs terminal binary start X.1 u v) :
    ¬ ContextCanonicalOrder (u, v) (canonicalChi X) := by
  simpa [canonicalChi, CanonicalContextSet] using
    ((contextCanonicalOrder_wf (Sigma := Sigma)).not_lt_min
      (CanonicalContextSet X) hOcc)

/-- Direct start states have the canonical empty context. -/
theorem canonicalChi_start_empty
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start)
    (hStart : keptStart X) :
    canonicalLeftCtx X = [] ∧ canonicalRightCtx X = [] := by
  have hEmpty : ([], []) ∈ CanonicalContextSet X :=
    keptStart_occurs_empty X hStart
  have hNoLess : ∀ c ∈ CanonicalContextSet X,
      ¬ ContextCanonicalOrder (Sigma := Sigma) c ([], []) := by
    intro c hc hlt
    rcases c with ⟨u, v⟩
    cases hlt with
    | left _ _ hlen =>
        simpa [contextCanonicalKey] using hlen
    | right hlen hpair =>
        have htotal : u.length + v.length = 0 := by
          simpa [contextCanonicalKey] using hlen
        rcases Nat.add_eq_zero.mp htotal with ⟨huLen, hvLen⟩
        have hu : u = [] := List.length_eq_zero.mp huLen
        have hv : v = [] := List.length_eq_zero.mp hvLen
        subst u
        subst v
        cases hpair with
        | left _ _ huShort =>
            exact (List.not_shortlex_nil_right huShort).elim
        | right huEq hvShort =>
            exact (List.not_shortlex_nil_right hvShort).elim
  have hPair : canonicalChi X = ([], []) := by
    unfold canonicalChi
    exact (contextCanonicalOrder_wf (Sigma := Sigma)).min_eq_of_forall_not_lt
      hEmpty hNoLess
  constructor
  · simp [canonicalLeftCtx, hPair]
  · simp [canonicalRightCtx, hPair]

/-- Canonical anchor word from the revised manuscript. -/
noncomputable def canonicalAnchorWord
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Word Sigma :=
  canonicalLeftCtx X ++ canonicalOmega X ++ canonicalRightCtx X

/-- Canonical terminal-rule witness. -/
noncomputable def canonicalTerminalObservationWord
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) (a : Sigma) : Word Sigma :=
  canonicalLeftCtx X ++ [a] ++ canonicalRightCtx X

/-- Canonical binary-rule witness. -/
noncomputable def canonicalBinaryObservationWord
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X Y Z : KeptState Obs terminal binary start) : Word Sigma :=
  canonicalLeftCtx X ++ canonicalOmega Y ++ canonicalOmega Z ++ canonicalRightCtx X

/-- The exact four-family canonical witness set of revised v44 equation (CS). -/
noncomputable def CanonicalCS
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop) : Language Sigma :=
  fun z =>
    (∃ X : KeptState Obs terminal binary start, z = canonicalAnchorWord X) ∨
    (∃ (X : KeptState Obs terminal binary start) (a : Sigma),
      keptTerminal X a ∧ z = canonicalTerminalObservationWord X a) ∨
    (∃ X Y Z : KeptState Obs terminal binary start,
      keptBinary X Y Z ∧ z = canonicalBinaryObservationWord X Y Z) ∨
    (z = [] ∧ epsilonStart)

/-- The exact revised canonical witness set is finite for finite presentations. -/
theorem canonicalCS_finite
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Finite N] [Finite Sigma]
    (epsilonStart : Prop) :
    (CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart).Finite := by
  let W := KeptState Obs terminal binary start
  let A : Set (Word Sigma) := Set.range (fun X : W => canonicalAnchorWord X)
  let T : Set (Word Sigma) := Set.range
    (fun p : W × Sigma => canonicalTerminalObservationWord p.1 p.2)
  let R : Set (Word Sigma) := Set.range
    (fun p : W × W × W => canonicalBinaryObservationWord p.1 p.2.1 p.2.2)
  have hA : A.Finite := Set.finite_range _
  have hT : T.Finite := Set.finite_range _
  have hR : R.Finite := Set.finite_range _
  have hAll : (A ∪ T ∪ R ∪ ({[]} : Set (Word Sigma))).Finite :=
    (((hA.union hT).union hR).union (Set.finite_singleton []))
  refine hAll.subset ?_
  intro z hz
  rcases hz with hAnchor | hTerminal | hBinary | hEps
  · rcases hAnchor with ⟨X, rfl⟩
    exact Or.inl (Or.inl (Or.inl ⟨X, rfl⟩))
  · rcases hTerminal with ⟨X, a, hRule, rfl⟩
    exact Or.inl (Or.inl (Or.inr ⟨(X, a), rfl⟩))
  · rcases hBinary with ⟨X, Y, Z, hRule, rfl⟩
    exact Or.inl (Or.inr ⟨(X, Y, Z), rfl⟩)
  · rcases hEps with ⟨rfl, hStart⟩
    exact Or.inr (Set.mem_singleton [])

/-- A retained binary rule derives the concatenation of canonical child yields. -/
theorem keptBinary_canonical_derives
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X Y Z : KeptState Obs terminal binary start)
    (hRule : keptBinary X Y Z) :
    TypedDerives Obs terminal binary X.1 (canonicalOmega Y ++ canonicalOmega Z) := by
  have h := TypedDerives.binary (Obs := Obs)
    (terminal := terminal) (binary := binary)
    hRule.1 (canonicalOmega_spec Y) (canonicalOmega_spec Z)
  simpa [hRule.2] using h

/-- Every canonical witness is a positive word of the reduced typed grammar. -/
theorem canonicalCS_subset_trimmed
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart ⊆
      TrimmedTypedStartLanguage Obs terminal binary start epsilonStart := by
  intro z hz
  rcases hz with hAnchor | hTerminal | hBinary | hEps
  · rcases hAnchor with ⟨X, rfl⟩
    exact typedOccurs_plug_trimmed Obs terminal binary start epsilonStart
      (canonicalChi_spec X) (canonicalOmega_spec X)
  · rcases hTerminal with ⟨X, a, hRule, rfl⟩
    exact typedOccurs_plug_trimmed Obs terminal binary start epsilonStart
      (canonicalChi_spec X) (keptTerminal_derives X a hRule)
  · rcases hBinary with ⟨X, Y, Z, hRule, rfl⟩
    have hPlug := typedOccurs_plug_trimmed
      (X := X.1)
      (u := canonicalLeftCtx X)
      (v := canonicalRightCtx X)
      (w := canonicalOmega Y ++ canonicalOmega Z)
      Obs terminal binary start epsilonStart
      (canonicalChi_spec X) (keptBinary_canonical_derives X Y Z hRule)
    change TrimmedTypedStartLanguage Obs terminal binary start epsilonStart
      (canonicalLeftCtx X ++ canonicalOmega Y ++ canonicalOmega Z ++ canonicalRightCtx X)
    simpa only [List.append_assoc] using hPlug
  · rcases hEps with ⟨rfl, hEpsilon⟩
    exact Or.inl ⟨rfl, hEpsilon⟩

/-- Every canonical witness is positive in the original SSBNF language. -/
theorem canonicalCS_subset_untyped
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart ⊆
      UntypedStartLanguage terminal binary start epsilonStart := by
  intro z hz
  exact (typed_refinement_language_iff
    Obs terminal binary start epsilonStart z).mp
      (canonicalCS_subset_trimmed
        Obs terminal binary start epsilonStart hz)

end FixedHCFGv44
end LeanCfgProject
