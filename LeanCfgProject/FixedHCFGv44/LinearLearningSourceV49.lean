import LeanCfgProject.FixedHCFGv44.LinearCharacteristicSourceV49
import LeanCfgProject.FixedHCFGv44.CanonicalReconstruction

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Source-level learning package for the linear subclass in TCS v49.

The explicit Appendix A normalization has an infinite ambient nonterminal type,
because a stage symbol may carry an arbitrary remaining spine program.  The
actual retained yield-typed state space is finite, however.  This file uses the
retained-state finite representation from `LinearCharacteristicRetainedV49` to
recover the exact finite locking-set argument without assuming that the ambient
`LinearNormNT` type itself is finite.

Together with `LinearCharacteristicSourceV49`, this closes the semantic and
characteristic-data-size bridge from an arbitrary finite source linear CFG to
exact reconstruction and conservative Gold identification.  As elsewhere in
the v49 development, this does not introduce a machine-level runtime model.
-/

/-- The inductive and set-valued presentations of an ordinary SSBNF start
language coincide. -/
theorem genericUntypedStartLanguage_eq_untyped_v49
    {N : Type v} {Sigma : Type u}
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    GenericUntypedStartLanguage terminal binary start epsilonStart =
      UntypedStartLanguage terminal binary start epsilonStart := by
  ext w
  constructor
  · intro h
    cases h with
    | epsilon hEps =>
        exact Or.inl ⟨rfl, hEps⟩
    | @nonempty A w hStart hDeriv =>
        exact Or.inr ⟨A, hStart, hDeriv⟩
  · intro h
    rcases h with hEps | hNonempty
    · rcases hEps with ⟨rfl, hEps⟩
      exact UntypedStartDerives.epsilon hEps
    · rcases hNonempty with ⟨A, hStart, hDeriv⟩
      exact UntypedStartDerives.nonempty hStart hDeriv

/-- The ordinary SSBNF language of the explicit source normalization is exactly
the original source linear language. -/
theorem sourceNormalized_untyped_language_eq_source_v49
    {N : Type v} {Sigma : Type u} [Fintype N]
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) :
    UntypedStartLanguage
        (SourceNormalizedTerminalV49 sourceRules S)
        (SourceNormalizedBinaryV49 sourceRules S)
        (SourceNormalizedStartV49 sourceRules S)
        (SourceNullable sourceRules S) =
      SourceLinearLanguage sourceRules S := by
  calc
    UntypedStartLanguage
        (SourceNormalizedTerminalV49 sourceRules S)
        (SourceNormalizedBinaryV49 sourceRules S)
        (SourceNormalizedStartV49 sourceRules S)
        (SourceNullable sourceRules S) =
      GenericUntypedStartLanguage
        (SourceNormalizedTerminalV49 sourceRules S)
        (SourceNormalizedBinaryV49 sourceRules S)
        (SourceNormalizedStartV49 sourceRules S)
        (SourceNullable sourceRules S) := by
          symm
          exact genericUntypedStartLanguage_eq_untyped_v49
            (SourceNormalizedTerminalV49 sourceRules S)
            (SourceNormalizedBinaryV49 sourceRules S)
            (SourceNormalizedStartV49 sourceRules S)
            (SourceNullable sourceRules S)
    _ = SourceNormalizedLanguageV49 sourceRules S := by
          rfl
    _ = SourceLinearLanguage sourceRules S :=
      linearNormalization_source_language_eq_v49 sourceRules S

/-- The exact canonical characteristic set of the source normalization is
finite using only finiteness of the retained typed state space. -/
theorem sourceNormalized_canonicalCS_finite_v49
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) :
    letI := sourceNormalizedKeptStateFintypeV49 Obs sourceRules S
    (CanonicalCS
      (Obs := Obs)
      (terminal := SourceNormalizedTerminalV49 sourceRules S)
      (binary := SourceNormalizedBinaryV49 sourceRules S)
      (start := SourceNormalizedStartV49 sourceRules S)
      (SourceNullable sourceRules S)).Finite := by
  classical
  letI := sourceNormalizedKeptStateFintypeV49 Obs sourceRules S
  let F := canonicalCSFinsetRetainedV49
    (Obs := Obs)
    (terminal := SourceNormalizedTerminalV49 sourceRules S)
    (binary := SourceNormalizedBinaryV49 sourceRules S)
    (start := SourceNormalizedStartV49 sourceRules S)
    (SourceNullable sourceRules S)
  have hEq :
      CanonicalCS
          (Obs := Obs)
          (terminal := SourceNormalizedTerminalV49 sourceRules S)
          (binary := SourceNormalizedBinaryV49 sourceRules S)
          (start := SourceNormalizedStartV49 sourceRules S)
          (SourceNullable sourceRules S) =
        (↑F : Set (Word Sigma)) := by
    ext z
    change
      CanonicalCS
          (Obs := Obs)
          (terminal := SourceNormalizedTerminalV49 sourceRules S)
          (binary := SourceNormalizedBinaryV49 sourceRules S)
          (start := SourceNormalizedStartV49 sourceRules S)
          (SourceNullable sourceRules S) z ↔ z ∈ F
    exact (mem_canonicalCSFinsetRetainedV49_iff
      (Obs := Obs)
      (terminal := SourceNormalizedTerminalV49 sourceRules S)
      (binary := SourceNormalizedBinaryV49 sourceRules S)
      (start := SourceNormalizedStartV49 sourceRules S)
      (SourceNullable sourceRules S) z).symm
  rw [hEq]
  exact F.finite_toSet

/-- Exact reconstruction for the normalized source linear grammar, stated back
in the original source-language semantics. -/
theorem sourceNormalized_exact_reconstruction_v49
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N)
    (K : Language Sigma)
    (hCSK : CanonicalCS
      (Obs := Obs)
      (terminal := SourceNormalizedTerminalV49 sourceRules S)
      (binary := SourceNormalizedBinaryV49 sourceRules S)
      (start := SourceNormalizedStartV49 sourceRules S)
      (SourceNullable sourceRules S) ⊆ K)
    (hKL : K ⊆ SourceLinearLanguage sourceRules S)
    (hSub : HSubstitutable Obs (SourceLinearLanguage sourceRules S)) :
    HypLanguage Obs K = SourceLinearLanguage sourceRules S := by
  have hLang := sourceNormalized_untyped_language_eq_source_v49 sourceRules S
  have hKL' : K ⊆ UntypedStartLanguage
      (SourceNormalizedTerminalV49 sourceRules S)
      (SourceNormalizedBinaryV49 sourceRules S)
      (SourceNormalizedStartV49 sourceRules S)
      (SourceNullable sourceRules S) := by
    rw [hLang]
    exact hKL
  have hSub' : HSubstitutable Obs
      (UntypedStartLanguage
        (SourceNormalizedTerminalV49 sourceRules S)
        (SourceNormalizedBinaryV49 sourceRules S)
        (SourceNormalizedStartV49 sourceRules S)
        (SourceNullable sourceRules S)) := by
    rw [hLang]
    exact hSub
  calc
    HypLanguage Obs K =
        UntypedStartLanguage
          (SourceNormalizedTerminalV49 sourceRules S)
          (SourceNormalizedBinaryV49 sourceRules S)
          (SourceNormalizedStartV49 sourceRules S)
          (SourceNullable sourceRules S) :=
      canonical_exact_reconstruction_from_ssbnf
        Obs
        (SourceNormalizedTerminalV49 sourceRules S)
        (SourceNormalizedBinaryV49 sourceRules S)
        (SourceNormalizedStartV49 sourceRules S)
        (SourceNullable sourceRules S)
        K hCSK hKL' hSub'
    _ = SourceLinearLanguage sourceRules S := hLang

/-- Conservative Gold identification for the source linear grammar.  The proof
uses the exact retained-state finite characteristic set rather than ambient
finiteness of `LinearNormNT`. -/
theorem sourceNormalized_gold_identification_v49
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N)
    (hSub : HSubstitutable Obs (SourceLinearLanguage sourceRules S))
    (text : Nat → Word Sigma)
    (hText : TextFor (SourceLinearLanguage sourceRules S) text) :
    ∃ N₀ : Nat, ∀ n : Nat, N₀ ≤ n →
      ConservativeHyp Obs text n = SourceLinearLanguage sourceRules S := by
  classical
  let terminal := SourceNormalizedTerminalV49 sourceRules S
  let binary := SourceNormalizedBinaryV49 sourceRules S
  let start := SourceNormalizedStartV49 sourceRules S
  let epsilonStart := SourceNullable sourceRules S
  let B := canonicalReconstructionBasis Obs terminal binary start epsilonStart
  letI := sourceNormalizedKeptStateFintypeV49 Obs sourceRules S

  have hLangNorm :
      UntypedStartLanguage terminal binary start epsilonStart =
        SourceLinearLanguage sourceRules S := by
    simpa [terminal, binary, start, epsilonStart] using
      sourceNormalized_untyped_language_eq_source_v49 sourceRules S
  have hBasisLang : BasisLanguage B = SourceLinearLanguage sourceRules S := by
    calc
      BasisLanguage B = UntypedStartLanguage terminal binary start epsilonStart := by
        simpa [B] using canonicalBasisLanguage_eq_untyped
          Obs terminal binary start epsilonStart
      _ = SourceLinearLanguage sourceRules S := hLangNorm
  have hFinite : B.CS.Finite := by
    simpa [B, canonicalReconstructionBasis, terminal, binary, start, epsilonStart] using
      sourceNormalized_canonicalCS_finite_v49 Obs sourceRules S
  have hCSTarget : B.CS ⊆ BasisLanguage B := by
    intro z hz
    have hz' : CanonicalCS
        (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart z := by
      simpa [B, canonicalReconstructionBasis] using hz
    have hPos := canonicalCS_subset_untyped
      Obs terminal binary start epsilonStart hz'
    rw [hBasisLang]
    rw [← hLangNorm]
    exact hPos
  have hSub' : HSubstitutable Obs (BasisLanguage B) := by
    rw [hBasisLang]
    exact hSub
  have hText' : TextFor (BasisLanguage B) text := by
    rw [hBasisLang]
    exact hText
  obtain ⟨N₀, hN₀⟩ := corollary_gold_identification
    B hFinite hCSTarget hSub' text hText'
  refine ⟨N₀, ?_⟩
  intro n hn
  calc
    ConservativeHyp Obs text n = BasisLanguage B := hN₀ n hn
    _ = SourceLinearLanguage sourceRules S := hBasisLang

/-- Manuscript-facing source-level package for the v49 linear-subclass theorem. -/
structure SourceLinearLearningCertificateV49
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) : Prop where
  characteristicNorm :
    letI := sourceNormalizedKeptStateFintypeV49 Obs sourceRules S
    canonicalCSNormRetainedV49
        (Obs := Obs)
        (terminal := SourceNormalizedTerminalV49 sourceRules S)
        (binary := SourceNormalizedBinaryV49 sourceRules S)
        (start := SourceNormalizedStartV49 sourceRules S)
        (SourceNullable sourceRules S) ≤
      sourceNormalizedCharacteristicBudgetV49 Obs sourceRules
  sampleConsistency :
    ∀ K : Language Sigma, K ⊆ HypLanguage Obs K
  exactReconstruction :
    ∀ K : Language Sigma,
      CanonicalCS
          (Obs := Obs)
          (terminal := SourceNormalizedTerminalV49 sourceRules S)
          (binary := SourceNormalizedBinaryV49 sourceRules S)
          (start := SourceNormalizedStartV49 sourceRules S)
          (SourceNullable sourceRules S) ⊆ K →
      K ⊆ SourceLinearLanguage sourceRules S →
      HypLanguage Obs K = SourceLinearLanguage sourceRules S
  goldIdentification :
    ∀ text : Nat → Word Sigma,
      TextFor (SourceLinearLanguage sourceRules S) text →
      ∃ N₀ : Nat, ∀ n : Nat, N₀ ≤ n →
        ConservativeHyp Obs text n = SourceLinearLanguage sourceRules S

/-- All semantic and source-polynomial characteristic-data clauses of
`thm:linear-poly`, starting from an arbitrary finite source linear CFG. -/
theorem sourceLinearLearningCertificate_v49
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N)
    (hSub : HSubstitutable Obs (SourceLinearLanguage sourceRules S)) :
    SourceLinearLearningCertificateV49 Obs sourceRules S := by
  refine
    { characteristicNorm := ?_
      sampleConsistency := ?_
      exactReconstruction := ?_
      goldIdentification := ?_ }
  · exact sourceNormalized_characteristic_norm_le_sourcePolynomial_v49
      Obs sourceRules S (SourceNullable sourceRules S)
  · intro K
    exact lemma_sample_consistency Obs K
  · intro K hCSK hKL
    exact sourceNormalized_exact_reconstruction_v49
      Obs sourceRules S K hCSK hKL hSub
  · intro text hText
    exact sourceNormalized_gold_identification_v49
      Obs sourceRules S hSub text hText

end FixedHCFGv44
end LeanCfgProject
