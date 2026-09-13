import LeanCfgProject.FixedHCFGv44.CanonicalWitness

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/--
A state directly licensed by the start symbol has the empty canonical context.
This uses the revised v44 ordering: total context length first, then shortlex
left/right tie-breaking.
-/
theorem canonicalChi_start_empty
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start)
    (hStart : keptStart X) :
    canonicalLeftCtx X = [] ∧ canonicalRightCtx X = [] := by
  have hEmpty : TypedOccurs Obs terminal binary start X.1 [] [] :=
    keptStart_occurs_empty X hStart
  have hMinimal := canonicalChi_minimal X hEmpty
  have hTotal :
      (canonicalChi X).1.length + (canonicalChi X).2.length = 0 := by
    by_contra hne
    have hpos : 0 < (canonicalChi X).1.length + (canonicalChi X).2.length :=
      Nat.pos_of_ne_zero hne
    apply hMinimal
    change Prod.Lex (fun a b : Nat => a < b)
      (ContextShortlex (Sigma := Sigma))
      (contextCanonicalKey ([], []))
      (contextCanonicalKey (canonicalChi X))
    exact Prod.Lex.left _ _ hpos
  have hLeftLen : (canonicalChi X).1.length = 0 := by omega
  have hRightLen : (canonicalChi X).2.length = 0 := by omega
  constructor
  · exact List.eq_nil_of_length_eq_zero hLeftLen
  · exact List.eq_nil_of_length_eq_zero hRightLen

/-- The manuscript-faithful v44 reconstruction basis. -/
noncomputable def canonicalReconstructionBasis
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    ReconstructionBasis Obs (KeptState Obs terminal binary start) where
  terminal := keptTerminal
  binary := keptBinary
  startState := keptStart
  hasEpsilon := epsilonStart
  omega := canonicalOmega
  leftCtx := canonicalLeftCtx
  rightCtx := canonicalRightCtx
  yieldType := fun X => X.1.yieldType
  CS := CanonicalCS epsilonStart
  omega_type := by
    intro X
    exact typed_yield_invariant Obs terminal binary (canonicalOmega_spec X)
  omega_internal := by
    intro X
    exact typed_derives_internal Obs terminal binary (canonicalOmega_spec X)
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
    intro X h
    exact canonicalChi_start_empty X h
  epsilon_mem := by
    intro h
    exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))

/-- Every reduced typed derivation is represented by the canonical basis. -/
theorem keptDerives_to_canonicalBasis_exists
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    {X : TypedNT N Obs} {w : Word Sigma}
    (d : KeptDerives Obs terminal binary start X w) :
    ∃ hkeep : TypedKept Obs terminal binary start X,
      BasisDerives
        (canonicalReconstructionBasis Obs terminal binary start epsilonStart)
        (⟨X, hkeep⟩ : KeptState Obs terminal binary start) w := by
  induction d with
  | @terminal A a hrule hkeep =>
      refine ⟨hkeep, ?_⟩
      exact BasisDerives.terminal ⟨hrule, rfl⟩
  | @binary A B C mu nu x y hrule hkeep left right ihLeft ihRight =>
      rcases ihLeft with ⟨hLeftKeep, hLeftBasis⟩
      rcases ihRight with ⟨hRightKeep, hRightBasis⟩
      let Xs : KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := Obs.mul mu nu }, hkeep⟩
      let Ys : KeptState Obs terminal binary start :=
        ⟨{ label := B, yieldType := mu }, hLeftKeep⟩
      let Zs : KeptState Obs terminal binary start :=
        ⟨{ label := C, yieldType := nu }, hRightKeep⟩
      have hRule : keptBinary Xs Ys Zs := ⟨hrule, rfl⟩
      refine ⟨hkeep, ?_⟩
      exact BasisDerives.binary hRule hLeftBasis hRightBasis

/-- Every canonical-basis derivation is a reduced yield-typed derivation. -/
theorem canonicalBasisDerives_to_kept
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    {X : KeptState Obs terminal binary start} {w : Word Sigma}
    (d : BasisDerives
      (canonicalReconstructionBasis Obs terminal binary start epsilonStart) X w) :
    KeptDerives Obs terminal binary start X.1 w := by
  induction d with
  | @terminal X a hrule =>
      rcases X with ⟨⟨A, mu⟩, hKeep⟩
      change terminal A a ∧ obsValue Obs [a] = mu at hrule
      rcases hrule with ⟨hTerminal, hType⟩
      subst mu
      exact KeptDerives.terminal hTerminal hKeep
  | @binary X Y Z x y hrule left right ihLeft ihRight =>
      rcases X with ⟨⟨A, rho⟩, hXKeep⟩
      rcases Y with ⟨⟨B, mu⟩, hYKeep⟩
      rcases Z with ⟨⟨C, nu⟩, hZKeep⟩
      change binary A B C ∧ Obs.mul mu nu = rho at hrule
      rcases hrule with ⟨hBinary, hType⟩
      subst rho
      exact KeptDerives.binary hBinary hXKeep ihLeft ihRight

/-- The canonical witness basis has exactly the reduced typed language. -/
theorem canonicalBasisLanguage_iff_trimmed
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (w : Word Sigma) :
    BasisLanguage
        (canonicalReconstructionBasis Obs terminal binary start epsilonStart) w ↔
      TrimmedTypedStartLanguage Obs terminal binary start epsilonStart w := by
  constructor
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨X, hStart, hDeriv⟩
      have hKept := canonicalBasisDerives_to_kept
        Obs terminal binary start epsilonStart hDeriv
      rcases X with ⟨⟨A, mu⟩, hKeep⟩
      change start A at hStart
      exact Or.inr ⟨A, mu, hStart, hKept⟩
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨A, mu, hStart, hDeriv⟩
      rcases keptDerives_to_canonicalBasis_exists
          Obs terminal binary start epsilonStart hDeriv with
        ⟨hKeep, hBasis⟩
      let X : KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := mu }, hKeep⟩
      exact Or.inr ⟨X, hStart, hBasis⟩

/-- The canonical basis has exactly the original SSBNF language. -/
theorem canonicalBasisLanguage_eq_untyped
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    BasisLanguage
        (canonicalReconstructionBasis Obs terminal binary start epsilonStart) =
      UntypedStartLanguage terminal binary start epsilonStart := by
  ext w
  exact (canonicalBasisLanguage_iff_trimmed
    Obs terminal binary start epsilonStart w).trans
      (typed_refinement_language_iff
        Obs terminal binary start epsilonStart w)

/-- Exact finite-sample reconstruction using the manuscript's canonical CS. -/
theorem canonical_exact_reconstruction_from_ssbnf
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (K : Language Sigma)
    (hCSK : CanonicalCS (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart ⊆ K)
    (hKL : K ⊆ UntypedStartLanguage terminal binary start epsilonStart)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart)) :
    HypLanguage Obs K =
      UntypedStartLanguage terminal binary start epsilonStart := by
  let B := canonicalReconstructionBasis Obs terminal binary start epsilonStart
  have hLangEq : BasisLanguage B =
      UntypedStartLanguage terminal binary start epsilonStart := by
    simpa [B] using canonicalBasisLanguage_eq_untyped
      Obs terminal binary start epsilonStart
  have hCSK' : B.CS ⊆ K := by
    simpa [B, canonicalReconstructionBasis] using hCSK
  have hKL' : K ⊆ BasisLanguage B := by
    rw [hLangEq]
    exact hKL
  have hSub' : HSubstitutable Obs (BasisLanguage B) := by
    rw [hLangEq]
    exact hSub
  calc
    HypLanguage Obs K = BasisLanguage B :=
      theorem_exact_reconstruction B K hCSK' hKL' hSub'
    _ = UntypedStartLanguage terminal binary start epsilonStart := hLangEq

/--
Manuscript-faithful v44 Gold identification: the finite locking set is exactly
the canonical four-family characteristic sample.
-/
theorem canonical_gold_identification_from_ssbnf
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    [Finite N] [Finite Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart))
    (text : Nat → Word Sigma)
    (hText : TextFor
      (UntypedStartLanguage terminal binary start epsilonStart) text) :
    ∃ N₀ : Nat, ∀ n : Nat, N₀ ≤ n →
      ConservativeHyp Obs text n =
        UntypedStartLanguage terminal binary start epsilonStart := by
  let B := canonicalReconstructionBasis Obs terminal binary start epsilonStart
  have hLangEq : BasisLanguage B =
      UntypedStartLanguage terminal binary start epsilonStart := by
    simpa [B] using canonicalBasisLanguage_eq_untyped
      Obs terminal binary start epsilonStart
  have hFinite : B.CS.Finite := by
    simpa [B, canonicalReconstructionBasis] using
      (canonicalCS_finite (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart)
  have hCSTarget : B.CS ⊆ BasisLanguage B := by
    intro z hz
    have hz' : z ∈ CanonicalCS (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart := by
      simpa [B, canonicalReconstructionBasis] using hz
    have hPos := canonicalCS_subset_untyped
      Obs terminal binary start epsilonStart hz'
    rw [hLangEq]
    exact hPos
  have hSub' : HSubstitutable Obs (BasisLanguage B) := by
    rw [hLangEq]
    exact hSub
  have hText' : TextFor (BasisLanguage B) text := by
    rw [hLangEq]
    exact hText
  obtain ⟨N₀, hN₀⟩ := corollary_gold_identification
    B hFinite hCSTarget hSub' text hText'
  refine ⟨N₀, ?_⟩
  intro n hn
  calc
    ConservativeHyp Obs text n = BasisLanguage B := hN₀ n hn
    _ = UntypedStartLanguage terminal binary start epsilonStart := hLangEq

end FixedHCFGv44
end LeanCfgProject
