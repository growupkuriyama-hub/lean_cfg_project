import LeanCfgProject.FixedHCFGv44.WitnessExtraction
import LeanCfgProject.FixedHCFGv44.ConservativeLearning

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-- A reduced typed derivation certifies that its root state is retained. -/
theorem keptDerives_root_kept
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    {X : TypedNT N Obs} {w : Word Sigma}
    (d : KeptDerives Obs terminal binary start X w) :
    TypedKept Obs terminal binary start X := by
  cases d with
  | terminal hrule hkeep => exact hkeep
  | binary hrule hkeep left right => exact hkeep

/-- Every reduced typed derivation is represented by the extracted witness basis. -/
theorem keptDerives_to_preferredBasis_exists
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    {X : TypedNT N Obs} {w : Word Sigma}
    (d : KeptDerives Obs terminal binary start X w) :
    ∃ hkeep : TypedKept Obs terminal binary start X,
      BasisDerives
        (preferredReconstructionBasis Obs terminal binary start epsilonStart)
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

/-- Every derivation of the extracted basis is a reduced yield-typed derivation. -/
theorem preferredBasisDerives_to_kept
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    {X : KeptState Obs terminal binary start} {w : Word Sigma}
    (d : BasisDerives
      (preferredReconstructionBasis Obs terminal binary start epsilonStart) X w) :
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

/-- The extracted basis has exactly the reduced typed language. -/
theorem preferredBasisLanguage_iff_trimmed
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (w : Word Sigma) :
    BasisLanguage
        (preferredReconstructionBasis Obs terminal binary start epsilonStart) w ↔
      TrimmedTypedStartLanguage Obs terminal binary start epsilonStart w := by
  constructor
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨X, hStart, hDeriv⟩
      have hKept := preferredBasisDerives_to_kept
        Obs terminal binary start epsilonStart hDeriv
      rcases X with ⟨⟨A, mu⟩, hKeep⟩
      change start A at hStart
      exact Or.inr ⟨A, mu, hStart, hKept⟩
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨A, mu, hStart, hDeriv⟩
      rcases keptDerives_to_preferredBasis_exists
          Obs terminal binary start epsilonStart hDeriv with
        ⟨hKeep, hBasis⟩
      let X : KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := mu }, hKeep⟩
      exact Or.inr ⟨X, hStart, hBasis⟩

/-- The extracted witness basis has exactly the original SSBNF language. -/
theorem preferredBasisLanguage_iff_untyped
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (w : Word Sigma) :
    BasisLanguage
        (preferredReconstructionBasis Obs terminal binary start epsilonStart) w ↔
      UntypedStartLanguage terminal binary start epsilonStart w := by
  exact (preferredBasisLanguage_iff_trimmed
    Obs terminal binary start epsilonStart w).trans
      (typed_refinement_language_iff
        Obs terminal binary start epsilonStart w)

/-- Set-level form of the language bridge. -/
theorem preferredBasisLanguage_eq_untyped
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    BasisLanguage
        (preferredReconstructionBasis Obs terminal binary start epsilonStart) =
      UntypedStartLanguage terminal binary start epsilonStart := by
  ext w
  exact preferredBasisLanguage_iff_untyped
    Obs terminal binary start epsilonStart w

/-- Plugging a typed subtree into a reaching occurrence yields a typed start derivation. -/
theorem typedOccurs_plug_start
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    {X : TypedNT N Obs} {u v w : Word Sigma}
    (hOcc : TypedOccurs Obs terminal binary start X u v)
    (hDeriv : TypedDerives Obs terminal binary X w) :
    ∃ (A : N) (mu : Obs.M),
      start A ∧
        TypedDerives Obs terminal binary
          { label := A, yieldType := mu } (u ++ w ++ v) := by
  induction hOcc generalizing w with
  | @start A mu hStart =>
      exact ⟨A, mu, hStart, by simpa using hDeriv⟩
  | @left A B C mu nu u v y parent hrule rightDeriv ih =>
      have hParentDeriv : TypedDerives Obs terminal binary
          { label := A, yieldType := Obs.mul mu nu } (w ++ y) :=
        TypedDerives.binary hrule hDeriv rightDeriv
      rcases ih hParentDeriv with ⟨S, rho, hS, hRoot⟩
      refine ⟨S, rho, hS, ?_⟩
      simpa [List.append_assoc] using hRoot
  | @right A B C mu nu u v x parent hrule leftDeriv ih =>
      have hParentDeriv : TypedDerives Obs terminal binary
          { label := A, yieldType := Obs.mul mu nu } (x ++ w) :=
        TypedDerives.binary hrule leftDeriv hDeriv
      rcases ih hParentDeriv with ⟨S, rho, hS, hRoot⟩
      refine ⟨S, rho, hS, ?_⟩
      simpa [List.append_assoc] using hRoot

/-- Plugging a typed occurrence and reducing gives a word of the reduced language. -/
theorem typedOccurs_plug_trimmed
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    {X : TypedNT N Obs} {u v w : Word Sigma}
    (hOcc : TypedOccurs Obs terminal binary start X u v)
    (hDeriv : TypedDerives Obs terminal binary X w) :
    TrimmedTypedStartLanguage Obs terminal binary start epsilonStart
      (u ++ w ++ v) := by
  rcases typedOccurs_plug_start Obs terminal binary start hOcc hDeriv with
    ⟨A, mu, hStart, hRoot⟩
  have hRootOcc : TypedOccurs Obs terminal binary start
      { label := A, yieldType := mu } [] [] :=
    TypedOccurs.start (mu := mu) hStart
  have hKept := successful_derivation_survives
    Obs terminal binary start hRootOcc hRoot
  exact Or.inr ⟨A, mu, hStart, hKept⟩

/-- A retained terminal rule produces its corresponding one-letter witness yield. -/
theorem keptTerminal_derives
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) (a : Sigma)
    (hRule : keptTerminal X a) :
    TypedDerives Obs terminal binary X.1 [a] := by
  have h := TypedDerives.terminal (Obs := Obs)
    (binary := binary) hRule.1
  simpa [hRule.2] using h

/-- A retained binary rule produces the concatenation of the chosen child yields. -/
theorem keptBinary_chosen_derives
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X Y Z : KeptState Obs terminal binary start)
    (hRule : keptBinary X Y Z) :
    TypedDerives Obs terminal binary X.1 (chosenOmega Y ++ chosenOmega Z) := by
  have h := TypedDerives.binary (Obs := Obs)
    (terminal := terminal) (binary := binary)
    hRule.1 (chosenOmega_spec Y) (chosenOmega_spec Z)
  simpa [hRule.2] using h

/-- Every extracted four-family witness is a positive word of the reduced grammar. -/
theorem preferredCS_subset_trimmed
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    PreferredCS (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart ⊆
      TrimmedTypedStartLanguage Obs terminal binary start epsilonStart := by
  intro z hz
  rcases hz with hAnchor | hTerminal | hBinary | hEps
  · rcases hAnchor with ⟨X, rfl⟩
    exact typedOccurs_plug_trimmed Obs terminal binary start epsilonStart
      (chosenContext_spec X).1 (chosenOmega_spec X)
  · rcases hTerminal with ⟨X, a, hRule, rfl⟩
    exact typedOccurs_plug_trimmed Obs terminal binary start epsilonStart
      (chosenContext_spec X).1 (keptTerminal_derives X a hRule)
  · rcases hBinary with ⟨X, Y, Z, hRule, rfl⟩
    exact typedOccurs_plug_trimmed Obs terminal binary start epsilonStart
      (chosenContext_spec X).1 (keptBinary_chosen_derives X Y Z hRule)
  · rcases hEps with ⟨rfl, hEpsilon⟩
    exact Or.inl ⟨rfl, hEpsilon⟩

/-- Every extracted witness is positive in the original SSBNF language. -/
theorem preferredCS_subset_untyped
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    PreferredCS (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart ⊆
      UntypedStartLanguage terminal binary start epsilonStart := by
  intro z hz
  exact (typed_refinement_language_iff
    Obs terminal binary start epsilonStart z).mp
      (preferredCS_subset_trimmed
        Obs terminal binary start epsilonStart hz)

/--
End-to-end exact reconstruction for a concrete SSBNF presentation, using the
four v44 witness families extracted from its reduced yield-typed refinement.
-/
theorem exact_reconstruction_from_ssbnf
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (K : Language Sigma)
    (hCSK : PreferredCS (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart ⊆ K)
    (hKL : K ⊆ UntypedStartLanguage terminal binary start epsilonStart)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart)) :
    HypLanguage Obs K =
      UntypedStartLanguage terminal binary start epsilonStart := by
  let B := preferredReconstructionBasis Obs terminal binary start epsilonStart
  have hLangEq : BasisLanguage B =
      UntypedStartLanguage terminal binary start epsilonStart := by
    simpa [B] using preferredBasisLanguage_eq_untyped
      Obs terminal binary start epsilonStart
  have hCSK' : B.CS ⊆ K := by
    simpa [B, preferredReconstructionBasis] using hCSK
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
End-to-end v44 Gold identification for a finite SSBNF presentation at the
preferred-witness interface.  The next layer replaces the preferred choices by
the manuscript's canonical shortlex/minimum-context witnesses.
-/
theorem gold_identification_from_ssbnf
    {N : Type v} {Sigma : Type u}
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
  let B := preferredReconstructionBasis Obs terminal binary start epsilonStart
  have hLangEq : BasisLanguage B =
      UntypedStartLanguage terminal binary start epsilonStart := by
    simpa [B] using preferredBasisLanguage_eq_untyped
      Obs terminal binary start epsilonStart
  have hFinite : B.CS.Finite := by
    simpa [B, preferredReconstructionBasis] using
      (preferredCS_finite (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart)
  have hCSTarget : B.CS ⊆ BasisLanguage B := by
    intro z hz
    have hz' : PreferredCS (Obs := Obs) (terminal := terminal)
        (binary := binary) (start := start) epsilonStart z := by
      simpa [B, preferredReconstructionBasis] using hz
    have hPos := preferredCS_subset_untyped
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
