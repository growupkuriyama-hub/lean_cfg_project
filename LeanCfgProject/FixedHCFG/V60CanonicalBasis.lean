import LeanCfgProject.FixedHCFG.V60CanonicalChoices
import LeanCfgProject.FixedHCFG.V60Gold

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
The manuscript-facing characteristic sample and reconstruction basis obtained
from the exact v60 canonical choices.
-/

/-- Plugging a typed derivation into a successful occurrence gives a successful full derivation. -/
theorem v60_occurs_plug_full
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    {X : V60TypedNT N Obs} {u v w : Word Sigma}
    (hOcc : V60TypedOccurs Obs terminal binary start X u v)
    (hDeriv : V60YieldTypedDerives Obs terminal binary X w) :
    V60FullTypedStartLanguage Obs terminal binary start False
      (u ++ w ++ v) := by
  induction hOcc generalizing w with
  | @start A p hStart =>
      simpa using
        (Or.inr ⟨A, p, hStart, hDeriv⟩ :
          V60FullTypedStartLanguage Obs terminal binary start False w)
  | @left A B C p q r u v y parent hrule hproduct rightDeriv ih =>
      have hParentDeriv : V60YieldTypedDerives Obs terminal binary
          { label := A, yieldType := p } (w ++ y) :=
        V60YieldTypedDerives.binary hrule hproduct hDeriv rightDeriv
      have hParent := ih hParentDeriv
      simpa [List.append_assoc] using hParent
  | @right A B C p q r u v x parent hrule hproduct leftDeriv ih =>
      have hParentDeriv : V60YieldTypedDerives Obs terminal binary
          { label := A, yieldType := p } (x ++ w) :=
        V60YieldTypedDerives.binary hrule hproduct leftDeriv hDeriv
      have hParent := ih hParentDeriv
      simpa [List.append_assoc] using hParent

/-- Canonical anchor `u_X omega(X) v_X`. -/
noncomputable def v60CanonicalAnchorWord
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) : Word Sigma :=
  v60CanonicalLeftCtx X ++ v60CanonicalOmega X ++ v60CanonicalRightCtx X

/-- Canonical terminal-rule observation `u_X a v_X`. -/
noncomputable def v60CanonicalTerminalWord
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) (a : Sigma) : Word Sigma :=
  v60CanonicalLeftCtx X ++ [a] ++ v60CanonicalRightCtx X

/-- Canonical binary-rule observation `u_X omega(Y) omega(Z) v_X`. -/
noncomputable def v60CanonicalBinaryWord
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X Y Z : V60KeptState Obs terminal binary start) : Word Sigma :=
  v60CanonicalLeftCtx X ++ v60CanonicalOmega Y ++ v60CanonicalOmega Z ++
    v60CanonicalRightCtx X

/-- The witness set `W(G~)` displayed in the v60 manuscript. -/
noncomputable def V60CanonicalWitnessSet
    {N : Type v} {Sigma : Type u}
    [LT Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (epsilonStart : Prop) : Language Sigma :=
  fun z =>
    (∃ X : V60KeptState Obs terminal binary start,
      z = v60CanonicalAnchorWord X) ∨
    (∃ (X : V60KeptState Obs terminal binary start) (a : Sigma),
      V60KeptTerminal X a ∧ z = v60CanonicalTerminalWord X a) ∨
    (∃ X Y Z : V60KeptState Obs terminal binary start,
      V60KeptBinary X Y Z ∧ z = v60CanonicalBinaryWord X Y Z) ∨
    (z = [] ∧ epsilonStart)

/-- The exact canonical reconstruction basis of the v60 manuscript. -/
noncomputable def v60CanonicalReconstructionBasis
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop) :
    V60ReconstructionBasis Obs (V60KeptState Obs terminal binary start) where
  terminal := V60KeptTerminal
  binary := V60KeptBinary
  startState := V60KeptStart
  hasEpsilon := epsilonStart
  omega := v60CanonicalOmega
  leftCtx := v60CanonicalLeftCtx
  rightCtx := v60CanonicalRightCtx
  yieldType := fun X => X.1.yieldType
  witnessSet := V60CanonicalWitnessSet epsilonStart
  omega_nonempty := by
    intro X
    exact v60CanonicalOmega_nonempty X
  omega_type := by
    intro X
    exact v60CanonicalOmega_type X
  terminal_type := by
    intro X a h
    exact h.2
  binary_yield_type := by
    intro X Y Z h
    exact h.2
  anchor_mem := by
    intro X
    exact Or.inl ⟨X, rfl⟩
  terminal_observation_mem := by
    intro X a h
    exact Or.inr (Or.inl ⟨X, a, h, rfl⟩)
  binary_observation_mem := by
    intro X Y Z h
    exact Or.inr (Or.inr (Or.inl ⟨X, Y, Z, h, rfl⟩))
  start_context := by
    intro X hStart
    exact v60CanonicalChi_start_empty Obs terminal binary start X hStart
  epsilon_mem := by
    intro h
    exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))

/-- Basis derivations for the canonical basis coincide with trimmed typed derivations. -/
theorem v60_canonical_basis_derives_iff_kept
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop)
    (X : V60KeptState Obs terminal binary start) (w : Word Sigma) :
    V60BasisDerives
        (v60CanonicalReconstructionBasis Obs terminal binary start epsilonStart)
        X w ↔
      V60KeptDerives Obs terminal binary start X w := by
  constructor
  · intro d
    induction d with
    | terminal hrule =>
        exact V60KeptDerives.terminal hrule
    | binary hrule left right ihLeft ihRight =>
        exact V60KeptDerives.binary hrule ihLeft ihRight
  · intro d
    induction d with
    | terminal hrule =>
        exact V60BasisDerives.terminal hrule
    | binary hrule left right ihLeft ihRight =>
        exact V60BasisDerives.binary hrule ihLeft ihRight

/-- The canonical reconstruction basis denotes exactly the trimmed typed language. -/
theorem v60_canonical_basis_language_iff_trimmed
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop) (w : Word Sigma) :
    V60BasisLanguage
        (v60CanonicalReconstructionBasis Obs terminal binary start epsilonStart) w ↔
      V60TrimmedTypedStartLanguage Obs terminal binary start epsilonStart w := by
  constructor
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨X, hStart, hDeriv⟩
      exact Or.inr ⟨X, hStart,
        (v60_canonical_basis_derives_iff_kept
          Obs terminal binary start epsilonStart X w).mp hDeriv⟩
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨X, hStart, hDeriv⟩
      exact Or.inr ⟨X, hStart,
        (v60_canonical_basis_derives_iff_kept
          Obs terminal binary start epsilonStart X w).mpr hDeriv⟩

/-- The canonical basis has exactly the original SSBNF language. -/
theorem v60_canonical_basis_language_iff_untyped
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop) (w : Word Sigma) :
    V60BasisLanguage
        (v60CanonicalReconstructionBasis Obs terminal binary start epsilonStart) w ↔
      V60UntypedStartLanguage terminal binary start epsilonStart w := by
  exact (v60_canonical_basis_language_iff_trimmed
    Obs terminal binary start epsilonStart w).trans
      (v60_trimmed_typed_language_iff_untyped
        Obs terminal binary start epsilonStart w)

/-- Every word in the canonical witness set is a target word. -/
theorem v60_canonical_witness_subset_untyped
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop) :
    V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart ⊆
      V60UntypedStartLanguage terminal binary start epsilonStart := by
  intro z hz
  rcases hz with hAnchor | hTerminal | hBinary | hEps
  · rcases hAnchor with ⟨X, rfl⟩
    have hFull := v60_occurs_plug_full Obs terminal binary start
      (v60CanonicalChi_spec X) (v60CanonicalOmega_spec X)
    exact (v60_full_typed_language_iff_untyped
      Obs terminal binary start epsilonStart (v60CanonicalAnchorWord X)).mp
        (by simpa [v60CanonicalAnchorWord] using hFull)
  · rcases hTerminal with ⟨X, a, hRule, rfl⟩
    have hDeriv : V60YieldTypedDerives Obs terminal binary X.1 [a] :=
      V60YieldTypedDerives.terminal hRule.1 hRule.2
    have hFull := v60_occurs_plug_full Obs terminal binary start
      (v60CanonicalChi_spec X) hDeriv
    exact (v60_full_typed_language_iff_untyped
      Obs terminal binary start epsilonStart (v60CanonicalTerminalWord X a)).mp
        (by simpa [v60CanonicalTerminalWord] using hFull)
  · rcases hBinary with ⟨X, Y, Z, hRule, rfl⟩
    have hDeriv : V60YieldTypedDerives Obs terminal binary X.1
        (v60CanonicalOmega Y ++ v60CanonicalOmega Z) :=
      V60YieldTypedDerives.binary hRule.1 hRule.2
        (v60CanonicalOmega_spec Y) (v60CanonicalOmega_spec Z)
    have hFull := v60_occurs_plug_full Obs terminal binary start
      (v60CanonicalChi_spec X) hDeriv
    exact (v60_full_typed_language_iff_untyped
      Obs terminal binary start epsilonStart
        (v60CanonicalBinaryWord X Y Z)).mp
      (by simpa [v60CanonicalBinaryWord, List.append_assoc] using hFull)
  · rcases hEps with ⟨rfl, hEps⟩
    exact Or.inl ⟨rfl, hEps⟩

/-- Yield-only typed states form a finite type when the original nonterminal type is finite. -/
def v60TypedNTKey
    {N : Type v} {Sigma : Type u} {Obs : Observer Sigma}
    (X : V60TypedNT N Obs) : N × Obs.M :=
  (X.label, X.yieldType)

/-- The component encoding of yield-only typed states is injective. -/
theorem v60TypedNTKey_injective
    {N : Type v} {Sigma : Type u} {Obs : Observer Sigma} :
    Function.Injective (v60TypedNTKey (N := N) (Obs := Obs)) := by
  intro X Y h
  rcases X with ⟨xN, xM⟩
  rcases Y with ⟨yN, yM⟩
  simp only [v60TypedNTKey] at h
  cases h
  rfl

noncomputable instance v60TypedNTFinite
    {N : Type v} {Sigma : Type u} {Obs : Observer Sigma}
    [Finite N] : Finite (V60TypedNT N Obs) :=
  Finite.of_injective (v60TypedNTKey (N := N) (Obs := Obs))
    v60TypedNTKey_injective

/-- The canonical v60 witness set is finite for a finite grammar and alphabet. -/
theorem v60_canonical_witness_finite
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    [Finite N] [Finite Sigma]
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop) :
    (V60CanonicalWitnessSet (Obs := Obs) (terminal := terminal)
      (binary := binary) (start := start) epsilonStart).Finite := by
  let W := V60KeptState Obs terminal binary start
  let A : Set (Word Sigma) := Set.range
    (fun X : W => v60CanonicalAnchorWord X)
  let T : Set (Word Sigma) := Set.range
    (fun p : W × Sigma => v60CanonicalTerminalWord p.1 p.2)
  let R : Set (Word Sigma) := Set.range
    (fun p : W × W × W => v60CanonicalBinaryWord p.1 p.2.1 p.2.2)
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

end FixedHCFG
end LeanCfgProject
